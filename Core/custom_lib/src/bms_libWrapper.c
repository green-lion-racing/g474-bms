/*
 * bms_libWrapper.cpp
 *
 *  Created on: Nov 24, 2024
 *      Author: amrlxyz
 */

/*
 * Compatible commands
 * ADBMS2950 == ADBMS6830
 *
 * RDCFGA
 * RDCFGB
 * ADI1     = ADCV
 * ADI2     = ADSV
 * RDI      = RDFCA or RDCVA
 * RDVB     = RDFCB or RDCVB
 * RDIVB1   = RDFCC or RDCVC
 * RDIACC   = RDACA
 * RDVBACC  = RDACB
 * RDIVB1ACC= RDACC
 *
 */

/*
 * Commands Notes
 *
 * -- 6830 --
 * ADCV : Start ADC
 * ADSV : Start redundancy ADC
 * RDCVA: Read Cell Voltage A
 * RDFCA: Read Filtered Cell A
 * RDACA: Read Averaged Cell A
 *
 * -- 2950 --
 * ADIx: Start IxADC and VBxADC
 * RDI : Read Read I1ADC and I2ADC results
 *
 */


#include "bms_libWrapper.h"
#include "bms_datatypes.h"
#include "bms_utility.h"
#include "bms_mcuWrapper.h"
#include "bms_cmdlist.h"

#include <string.h>
#include <stdio.h>

#include "main.h"
#include "uartDMA.h"
#include "bms_can.h"
#include "math.h"


typedef struct
{
    ad29_cfa_t cfa_Tx;
    ad29_cfa_t cfa_Rx;
    ad29_cfb_t cfb_Tx;
    ad29_cfb_t cfb_Rx;

    float current1;
    float current2;
    float vb1;
    float vb2;

} Ic_ad29;


typedef struct
{
    // From/For Config Registers
    ad68_cfa_t cfa_Tx   [TOTAL_AD68];
    ad68_cfa_t cfa_Rx   [TOTAL_AD68];
    ad68_cfb_t cfb_Tx   [TOTAL_AD68];
    ad68_cfb_t cfb_Rx   [TOTAL_AD68];

    ad68_pwma_t pwma    [TOTAL_AD68];
    ad68_pwmb_t pwmb    [TOTAL_AD68];

    // From Read Registers
    float v_cell        [TOTAL_VOLTAGE_TYPES][TOTAL_AD68][TOTAL_CELL];        // Average of 8 samples register (C-ADC)
    // Calculated Values
    float v_cell_diff   [TOTAL_VOLTAGE_TYPES][TOTAL_AD68][TOTAL_CELL];
    float v_cell_sum    [TOTAL_VOLTAGE_TYPES][TOTAL_AD68];
    float v_cell_avg    [TOTAL_VOLTAGE_TYPES][TOTAL_AD68];
    float v_cell_min    [TOTAL_VOLTAGE_TYPES][TOTAL_AD68];
    float v_cell_max    [TOTAL_VOLTAGE_TYPES][TOTAL_AD68];
    float v_cell_delta  [TOTAL_VOLTAGE_TYPES][TOTAL_AD68];

    // From AUX measurement
    float v_segment     [TOTAL_AD68];
    float temp_cell     [TOTAL_AD68][TOTAL_TEMP];
    float temp_ic       [TOTAL_AD68];

    // flag stored in bits
    uint16_t isDischarging          [TOTAL_AD68];         // isDischarging Flag
    uint16_t isCellFaultDetected    [TOTAL_AD68];
    uint16_t isTempFaultDetected    [TOTAL_AD68];

} Ic_ad68;


typedef struct
{
    bool isFaultDetected    [TOTAL_IC];
    bool isCommsError       [TOTAL_IC];

    // Pack status
    float v_pack_total;
    float v_pack_min;
    float v_pack_max;
} Ic_common;


Ic_common   ic_common;
Ic_ad29     ic_ad29;
Ic_ad68     ic_ad68;

uint8_t  txData[TOTAL_IC][DATA_LEN];
uint8_t  rxData[TOTAL_IC][DATA_LEN];
uint16_t rxPec[TOTAL_IC];
uint8_t  rxCc[TOTAL_IC];

CanTxMsg canTxBuffer[CAN_BUFFER_LEN] = {0};

VoltageTypes dischargeVoltageType = VOLTAGE_S;
VoltageTypes monitoringVoltageType = VOLTAGE_C_FIL;

uint32_t BMS_StatusFlags = BMS_ERR_COMMS;          // Stores flags in bits

ChargerConfiguration chargerConfig = {
        .max_current = 1,
        .target_voltage = 520,
        .disable_charging = 1,
};

static const float balancingThreshold = 0.020; // Volts

static const bool DEBUG_SERIAL_VOLTAGE_ENABLED = true;
static const bool DEBUG_SERIAL_AUX_ENABLED = true;
static const bool DEBUG_SERIAL_MASTER_MEASUREMENTS = true;

volatile bool enableBalancing = false;

static void BMS_UpdateChargingControl(uint32_t errs,
                                      bool balancing_active,
                                      bool measuring_now,
                                      uint32_t now_ms);

static inline void BMS_SetFaultLed(bool on);

// set the dutycycle for each cell
static inline uint8_t diff_to_pwm4bit(float diffV, uint8_t prev_duty)
{
    const float DIFF_ON     = 0.022f;
    const float DIFF_OFF    = 0.020f;
    const float DIFF_MAX    = 0.150f;
    const float DUTY_MIN_F  = 0.40f;

    const bool was_on = (prev_duty > 0); // check if the cell was already balancing before
    bool now_on;
    if (was_on) {
        now_on = (diffV > DIFF_OFF);	// if active -> keep balancing until DIFF_OFF
    } else {
        now_on = (diffV >= DIFF_ON);
    }

    if (!now_on) return 0;

    float x = 0.0f;
    if (diffV <= DIFF_ON) x = 0.0f;
    else if (diffV >= DIFF_MAX) x = 1.0f;
    else x = (diffV - DIFF_ON) / (DIFF_MAX - DIFF_ON);

    float duty_f = DUTY_MIN_F + x * (1.0f - DUTY_MIN_F);
    int duty = (int)lroundf(duty_f * 15.0f);	// convert to a 4-bit value (0 - 15)

    if (duty < 6)  duty = 6;
    if (duty > 15) duty = 15;
    return (uint8_t)duty;
}


// function to set the pwm
static inline void set_cell_pwm_4bit(ad68_pwma_t* a, ad68_pwmb_t* b, uint8_t cell, uint8_t duty)
{
    duty &= 0x0F;
    if (cell < 12) {
        uint8_t *p = (uint8_t*)a;
        uint8_t byte_idx = cell >> 1;
        uint8_t hi = (cell & 1);
        uint8_t v  = p[byte_idx];
        p[byte_idx] = hi ? ((v & 0x0F) | (uint8_t)(duty << 4))
                         : ((v & 0xF0) | duty);
    } else {
        cell -= 12;
        uint8_t *p = (uint8_t*)b;
        uint8_t byte_idx = cell >> 1;
        uint8_t hi = (cell & 1);
        uint8_t v  = p[byte_idx];
        p[byte_idx] = hi ? ((v & 0x0F) | (uint8_t)(duty << 4))
                         : ((v & 0xF0) | duty);
    }
}



void bms_resetConfig(void)
{
    // Obtained from RDCFG after reset
    // Flipped due to Little endian
//    uint64_t const ad29_cfaDefault = 0x00 00 00 3F 3F 11;
    uint64_t const ad29_cfaDefault = 0x113F3F000000;
//    uint64_t const ad29_cfbDefault = 0x00 00 00 00 01 F0;
    uint64_t const ad29_cfbDefault = 0xF00100000000;
//    uint64_t const ad68_cfaDefault = 0x01 00 00 FF 03 00;
    uint64_t const ad68_cfaDefault = 0x0003FF000001;
//    uint64_t const ad68_cfbDefault = 0x00 F8 7F 00 00 00;
    uint64_t const ad68_cfbDefault = 0x0000007FF800;

    // Copy defaults to Tx Buffer
    if (TOTAL_AD29)
    {
        memcpy(&ic_ad29.cfa_Rx, &ad29_cfaDefault, DATA_LEN);
        memcpy(&ic_ad29.cfb_Rx, &ad29_cfbDefault, DATA_LEN);
    }

    for (int ic = 0; ic < TOTAL_AD68; ic++)
    {
        memcpy(&ic_ad68.cfa_Tx[ic], &ad68_cfaDefault, DATA_LEN);
        memcpy(&ic_ad68.cfb_Tx[ic], &ad68_cfbDefault, DATA_LEN);
    }

//    ad68_cfa_t ad68_cfaT;
//    memcpy(&ad68_cfaT, &ad68_cfaDefault, DATA_LEN);
}


void bms_writeRegister(RegisterTypes regType)
{
    uint8_t* command;

    // Use a switch statement to handle the logic for each register type
    switch (regType)
    {
        case REG_CONFIG_A:
            // Prepare data for writing to Configuration Register A
            if (TOTAL_AD29) {
                memcpy(txData[0], &ic_ad29.cfa_Tx, DATA_LEN);
            }
            for (int ic = 0; ic < TOTAL_AD68; ic++) {
                memcpy(txData[ic + TOTAL_AD29], &ic_ad68.cfa_Tx[ic], DATA_LEN);
            }
            command = WRCFGA; // Set the specific command for this operation
            break;

        case REG_CONFIG_B:
            // Prepare data for writing to Configuration Register B
            if (TOTAL_AD29) {
                memcpy(txData[0], &ic_ad29.cfb_Tx, DATA_LEN);
            }
            for (int ic = 0; ic < TOTAL_AD68; ic++) {
                memcpy(txData[ic + TOTAL_AD29], &ic_ad68.cfb_Tx[ic], DATA_LEN);
            }
            command = WRCFGB; // Set the specific command for this operation
            break;

        case REG_PWM_A:
            // Prepare data for writing to PWM Register Group A
            if (TOTAL_AD29) {
                memset(txData[0], 0x00, DATA_LEN); // PWM registers for ad29 are padded with 0
            }
            for (int ic = 0; ic < TOTAL_AD68; ic++) {
                memcpy(txData[ic + TOTAL_AD29], &ic_ad68.pwma[ic], DATA_LEN);
            }
            command = WRPWMA; // Set the specific command for this operation
            break;

        case REG_PWM_B:
            // Prepare data for writing to PWM Register Group B
            if (TOTAL_AD29) {
                memset(txData[0], 0x00, DATA_LEN); // PWM registers for ad29 are padded with 0
            }
            for (int ic = 0; ic < TOTAL_AD68; ic++) {
                memcpy(txData[ic + TOTAL_AD29], &ic_ad68.pwmb[ic], DATA_LEN);
            }
            command = WRPWMB; // Set the specific command for this operation
            break;

        default:
            // In case of an invalid regType
            Error_Handler();
            return;
    }

    // After preparing the buffer, transmit the data with the selected command.
    // This part is common to all cases.
    bms_transmitData(command, txData);
}



// Quick-PWM-OFF that keeps DCTO alive (no WRCFGB)
static void bms_quickPwmOff_keepDcto(void)
{
    for (int ic = 0; ic < TOTAL_AD68; ic++) {
        memset(&ic_ad68.pwma[ic], 0, sizeof(ic_ad68.pwma[ic]));
        memset(&ic_ad68.pwmb[ic], 0, sizeof(ic_ad68.pwmb[ic]));
        ic_ad68.cfb_Tx[ic].dcc = 0; // ensure DCC=0, PWM-only discharge disabled
    }
    // Only write PWM regs; DO NOT touch ConfigB here (keeps DCTO running)
    bms_writeRegister(REG_PWM_A);
    bms_writeRegister(REG_PWM_B);
}


// Liste der Zellen, die 100 % bekommen sollen (0-basiert)
static const uint8_t k_test_cells[] = {0};
static const size_t  k_test_cells_len = sizeof(k_test_cells)/sizeof(k_test_cells[0]);

// Erzwingt PWM 100% auf den festgelegten Zellen (für alle ICs)
void bms_forcePwmMask(void)
{
    for (int ic = 0; ic < TOTAL_AD68; ic++) {
        ad68_pwma_t pwma = (ad68_pwma_t){0};
        ad68_pwmb_t pwmb = (ad68_pwmb_t){0};

        // feste Zellen auf 100 %
        for (size_t i = 0; i < k_test_cells_len; ++i) {
            uint8_t c = k_test_cells[i];
            if (c >= TOTAL_CELL) continue;
            set_cell_pwm_4bit(&pwma, &pwmb, c, 0x0F);
            BIT_SET(ic_ad68.isDischarging[ic], c);
        }

        // DCC NIE setzen, DCTO aktiv halten
        ic_ad68.cfb_Tx[ic].dcc   = 0;
        ic_ad68.cfb_Tx[ic].dtrng = 0;   // Minuten
        ic_ad68.cfb_Tx[ic].dcto  = 15;  // 15 min
        ic_ad68.cfb_Tx[ic].dtmen = 0;

        // Shadow-Register übernehmen
        ic_ad68.pwma[ic] = pwma;
        ic_ad68.pwmb[ic] = pwmb;
    }

    // Reihenfolge: erst PWM, dann CFGB
    bms_writeRegister(REG_PWM_A);
    bms_writeRegister(REG_PWM_B);
    bms_writeRegister(REG_CONFIG_B);

    // Debug: Rücklesen
    bms_readRegister(REG_PWM_A);
    bms_readRegister(REG_PWM_B);
}


BMS_StatusTypeDef bms_init(void)
{
    bms_resetConfig();

    // For 2950 - Enable voltage measurements (Refer Schematic)
    if (TOTAL_AD29)
    {
        ic_ad29.cfa_Tx.gpo1c  = 1;      // State control
        ic_ad29.cfa_Tx.gpo1od = 0;      // 1 = Open drain, 0 = push-pull
        ic_ad29.cfa_Tx.gpo2c  = 1;      // State control
        ic_ad29.cfa_Tx.gpo2od = 0;      // 1 = Open drain, 0 = push-pull
    }

    // For 6830 Configs
    for (int ic = 0; ic < TOTAL_AD68; ic++)
    {
        ic_ad68.cfa_Tx[ic].refon = 0b1;
        ic_ad68.cfa_Tx[ic].fc = 0b001;    // 110 Hz corner freq
    }

    printfDma("\n --- BMS INIT --- \n");

    bms_wakeupChain();                                  // Wakeup needed every 4ms of Inactivity
    if (bms_readRegister(REG_SID) == BMS_ERR_COMMS)     // Make sure the comms is OK
    {
        return BMS_ERR_COMMS;
    }

    bms_writeRegister(REG_CONFIG_A);
    bms_startAdcvCont(false);            // Need to wait 8ms for the average register to fill up
    //bms_forcePwmMask();
    printfDma("BUILD MARKER A | TOTAL_AD68=%d TOTAL_CELL=%d BASE_CAN_ID=0x%lX\r\n",
              (int)TOTAL_AD68, (int)TOTAL_CELL, (unsigned long)BASE_CAN_ID);
    printfDma("SUMMARY_BASE_OFFSET = 0x%lX\r\n",
              (unsigned long)(TOTAL_AD68 * TOTAL_CELL));
    return BMS_OK;
}


void bms68_setGpo45(uint8_t twoBitIndex)
{
    // GPIO Output: 1 = No pulldown (Default), 0 = Pulldown
    // Only for pin 4 and 5
    for (int ic = 0; ic < TOTAL_AD68; ic++)
    {
        ic_ad68.cfa_Tx[ic].gpo1to8 = ((twoBitIndex) << 3) | (0xFF ^ (0x3 << 3));
    }

    bms_writeRegister(REG_CONFIG_A);
}


void bms_printRawData(uint8_t data[TOTAL_IC][DATA_LEN], uint8_t cc[TOTAL_IC])
{
    for (int ic = 0; ic < TOTAL_IC; ic++)
    {
        printfDma("IC%d ", ic+1);
        for (int j = 0; j < 6; j++)             // For every byte recieved (6 bytes)
        {
            printfDma("0x%02X, ", data[ic][j]);    // Print each of the bytes
        }
        printfDma("CC %d |   ", cc[ic]);
    }
    printfDma("\n\n");
}


bool bms_checkRxFault(uint8_t data[TOTAL_IC][DATA_LEN], uint16_t pec[TOTAL_IC], uint8_t cc[TOTAL_IC])
{
    bool faultDetected = false;
    bool* errorIndex = ic_common.isCommsError;

    if (bms_checkRxPec(data, pec, cc, errorIndex))
    {
        printfDma("WARNING! PEC ERROR - IC");
        for(int ic = 0; ic < TOTAL_IC; ic++)
        {
            if (errorIndex[ic])
            {
                printfDma(" %d,", ic+1);
            }
        }
        printfDma("\n");
        faultDetected = true;
    }

    return faultDetected;

    // TODO: Add command counter fault checker
    // TODO: Add fault handler for PEC fault
}


// used mostly for debugging purposes
BMS_StatusTypeDef bms_readRegister(RegisterTypes regType)
{
    char* title;
    uint8_t* cmd;
    switch (regType)
    {
    case REG_CONFIG_A:
        title = "Config A Register";
        cmd = RDCFGA;
        break;
    case REG_CONFIG_B:
        title = "Config B Register";
        cmd = RDCFGB;
        break;
    case REG_PWM_A:
        title = "PWM A Register";
        cmd = RDPWMA;
        break;
    case REG_PWM_B:
        title = "PWM B Register";
        cmd = RDPWMB;
        break;
    case REG_SID:
        title = "SID Register";
        cmd = RDSID;
        break;
    default:
        Error_Handler(); // Invalid Choice
        break;
    }

    bms_receiveData(cmd, rxData, rxPec, rxCc);
    if (bms_checkRxFault(rxData, rxPec, rxCc))
    {
        return BMS_ERR_COMMS;
    }

    printfDma("%s \n", title);
    bms_printRawData(rxData, rxCc);

    return BMS_OK;
}


void bms_startAdcvCont(bool enableRedundant)
{
    // 6830
    // For DCP = 0
    // If RD = 0 and CONT = 1, PWM discharge is unaffected
    // If RD = 1 and CONT = 0, (Might be wrong) PWM discharge interrupted temporarily until RD conversion finished (8ms typ)
    // If RD = 1 and CONT = 1, PWM discharge interrupted

    ADCV.CONT = 1;      // Continuous
    ADCV.DCP  = 0;      // Discharge permitted
    ADCV.RSTF = 0;      // Reset filter
    ADCV.OW   = 0b00;   // Open wire on C-ADCS and S-ADCs

    ADCV.RD   = 0;      // Redundant Measurement

    // Behaviour of 2950 (ADI1 Command)
    //

    bms_transmitCmd((uint8_t *)&ADCV);
}


void bms_parseVoltage(uint8_t rawData[TOTAL_IC][DATA_LEN], float vArr[TOTAL_IC][TOTAL_CELL], uint8_t register_index)
{
    // TODO: Read master register as well

    uint8_t cell_index = (register_index * 3);

    for (int ic = 0; ic < TOTAL_AD68; ic++)
    {
        for (int c = cell_index; c < (cell_index + 3); c++)
        {
            // Don't read cells out of range
            if (c >= TOTAL_CELL) {
                break;
            }

            vArr[ic][c] = *((int16_t *)(rawData[ic + TOTAL_AD29] + (c - cell_index)*2)) * 0.00015 + 1.5;

            if (register_index == 5) // Skip last Register since the last register only stores 1 cell
            {
                break;
            }
        }
    }
}


void bms_parseAuxVoltage(uint8_t const rawData[TOTAL_IC][DATA_LEN], float vArr[TOTAL_AD68][TOTAL_TEMP], uint8_t cell_index)
{
    // Constants for the NTC thermistor
    float R_FIXED     = 10000.0;       // Fixed resistor in ohms (10k)
    float R0          = 10000.0;       // Thermistor resistance at T0
    float BETA        = 3650.0;        // Beta constant for thermistor
    float T0_KELVIN   = 298.15;        // Reference temperature in Kelvin (25°C)

    // Supply voltage
    float V_SUPPLY    = 3.0;           // Supply voltage in volts

    // Function to convert voltage to temperature in Celsius
    float voltage_to_temperature(float v_out) {
        if (v_out <= 0.5 || v_out >= V_SUPPLY) {
            return -273.15; // Invalid voltage; return absolute zero as error
        }

        // Calculate thermistor resistance
        float r_thermistor = R_FIXED * v_out / (V_SUPPLY - v_out);

        // Calculate temperature in Kelvin using the Beta equation
        float temp_k = 1.0 / ((1.0 / T0_KELVIN) + (1.0 / BETA) * log(r_thermistor / R0));

        // Convert to Celsius
        return temp_k - 273.15;
    }

    // Does not take care of 2950

    for (int ic = 0; ic < TOTAL_AD68; ic++)
    {
        if (cell_index == 4)
        {
            ic_ad68.temp_ic[ic] = (*((int16_t *)(rawData[ic + TOTAL_AD29] + 2)) * 0.00015 + 1.5) / 0.0075 - 273;
            continue;
        }

        uint8_t cellArrIndex = cell_index*3;

        for (int c = cellArrIndex; c < (cellArrIndex + 3); c++)
        {
            vArr[ic][c] = voltage_to_temperature(*((int16_t *)(rawData[ic + TOTAL_AD29] + (c-cellArrIndex)*2)) * 0.00015 + 1.5);


            if (cell_index == 3)
            {
                ic_ad68.v_segment[ic] = (*((int16_t *)(rawData[ic + TOTAL_AD29] + 4)) * 0.00015 + 1.5) * 25;
                break;
            }
        }
    }
}


void bms_calculateStats(VoltageTypes voltageType)
{
    float total_voltage = 0;
    float pack_min =  999.0;
    float pack_max = -999.0;

    for (int ic = 0; ic < TOTAL_AD68; ic++)
    {
        float min =  999.0;
        float max = -999.0;
        float sum = 0;

        for (int c = 0; c < TOTAL_CELL; c++)
        {
            float voltage = ic_ad68.v_cell[voltageType][ic][c];
            sum += voltage;
            if (voltage > max)
            {
                max = voltage;
            }
            if (voltage < min)
            {
                min = voltage;
            }
            if (voltage > pack_max)
            {
                pack_max = voltage;
            }
            if (voltage < pack_min)
            {
                pack_min = voltage;
            }
        }

        total_voltage += sum;
        ic_ad68.v_cell_min  [voltageType][ic] = min;
        ic_ad68.v_cell_max  [voltageType][ic] = max;
        ic_ad68.v_cell_sum  [voltageType][ic] = sum;
        ic_ad68.v_cell_avg  [voltageType][ic] = sum / 16.0;
        ic_ad68.v_cell_delta[voltageType][ic] = max - min;

        for (int c = 0; c < TOTAL_CELL; c++)
        {
            ic_ad68.v_cell_diff[voltageType][ic][c] = ic_ad68.v_cell[voltageType][ic][c] - min;
        }
    }

    if (voltageType == dischargeVoltageType)
    {
        ic_common.v_pack_total = total_voltage;
        ic_common.v_pack_min = pack_min;
        ic_common.v_pack_max = pack_max;
    }

    // Calculate voltage diff from the lowest voltage cell
    for (int ic = 0; ic < TOTAL_AD68; ic++)
    {
        for (int c = 0; c < TOTAL_CELL; c++)
        {
            ic_ad68.v_cell_diff[voltageType][ic][c] = ic_ad68.v_cell[voltageType][ic][c] - pack_min;
        }
    }
}


void bms_printVoltage(VoltageTypes voltageType)
{
    float (*vArr)[TOTAL_CELL] = ic_ad68.v_cell[voltageType];
    float (*vDev)[TOTAL_CELL] = ic_ad68.v_cell_diff[voltageType];

    char* title;
    switch (voltageType)
    {
    case VOLTAGE_C:
        title = "C Voltage";
        break;
    case VOLTAGE_C_AVG:
        title = "C Average Voltage";
        break;
    case VOLTAGE_C_FIL:
        title = "C Filtered Voltage";
        break;
    case VOLTAGE_S:
        title = "S Voltage";
        break;
    case VOLTAGE_TEMP:
        title = "Temperature Sensors Voltage";
        break;
    default:
        Error_Handler();
        break;
    }
    printfDma("%s \n", title);

    printfDma("| IC |");
    for (int i = 0; i < TOTAL_CELL; i++)
    {
        printfDma("   %2d   |", i+1);
    }
    printfDma("  Sum   |  Delta |\n");

    for (int ic = 0; ic < TOTAL_AD68; ic++)
    {
        uint8_t paddingOffset;
        paddingOffset = printfDma("| %2d |", ic);
        for (int c = 0; c < TOTAL_CELL; c++)
        {
            printfDma("%8.5f|", vArr[ic][c]);
        }

        printfDma("%8.5f|", ic_ad68.v_cell_sum  [voltageType][ic]);
        printfDma("%8.5f|", ic_ad68.v_cell_delta[voltageType][ic]);
        printfDma("\n");

        printfDma("%*s", paddingOffset, "");
        for (int c = 0; c < TOTAL_CELL; c++)
        {
            printfDma("%8.5f|", vDev[ic][c]);
        }
        printfDma("\n");
    }

    // for better serial monitor
    for (int ic = 0; ic < TOTAL_AD68; ic++)
        {
            for (int c = 0; c < TOTAL_CELL; c++)
            {
                printfDma("IC%02dCELL%02d:%08.5f,", ic, c, vArr[ic][c]);
            }
            printfDma("\n");
        }
    printfDma("\n");
}


void bms_printTemps(void)
{
    printfDma("Temperature Measurement \n");
    float (*tArr)[TOTAL_TEMP] = ic_ad68.temp_cell;

    printfDma("| IC |");
    for (int i = 0; i < TOTAL_TEMP; i++)
    {
        printfDma("  %2d   |", i+1);
    }
    printfDma("  Die Temp / Segment Voltage");
    printfDma("\n");

    for (int ic = 0; ic < TOTAL_AD68; ic++)
    {
        printfDma("| %2d |", ic);
        for (int c = 0; c < TOTAL_TEMP; c++)
        {
            printfDma("%6.1f |", tArr[ic][c]);
        }
        printfDma("  %.2f C  /  %.2f V \n", ic_ad68.temp_ic[ic], ic_ad68.v_segment[ic]);
    }

    // for better serial monitor
    for (int ic = 0; ic < TOTAL_AD68; ic++)
        {
            for (int c = 0; c < TOTAL_TEMP; c++)
            {
                printfDma("IC%02dTEMP%02d:%06.1f,", ic, c, tArr[ic][c]);
            }
            printfDma("\n");
        }
    printfDma("\n");
}


uint8_t* readCellVoltageCmdList[TOTAL_VOLTAGE_TYPES][6] = {
        {RDCVA, RDCVB, RDCVC, RDCVD, RDCVE, RDCVF}, // VOLTAGE_C
        {RDACA, RDACB, RDACC, RDACD, RDACE, RDACF}, // VOLTAGE_C_AVG
        {RDFCA, RDFCB, RDFCC, RDFCD, RDFCE, RDFCF}, // VOLTAGE_FIL
        {RDSVA, RDSVB, RDSVC, RDSVD, RDSVE, RDSVF}, // VOLTAGE_S
        {} // VOLTAGE_TEMP
};

BMS_StatusTypeDef bms_readCellVoltage(VoltageTypes voltageType)
{
    uint8_t** cmdList = readCellVoltageCmdList[voltageType];

    for (int i = 0; i < 6; i++)
    {
        bms_receiveData(cmdList[i], rxData, rxPec, rxCc);
        if (bms_checkRxFault(rxData, rxPec, rxCc))
        {
            return BMS_ERR_COMMS;
        }
        bms_parseVoltage(rxData, ic_ad68.v_cell[voltageType], i);
    }

    bms_calculateStats(voltageType);

    if (DEBUG_SERIAL_VOLTAGE_ENABLED) bms_printVoltage(voltageType);

    return BMS_OK;
}


uint8_t bms_getAuxVoltage()
{
    uint8_t* cmdList[] = {RDAUXA, RDAUXB, RDAUXC, RDAUXD, RDSTATA};

    for (int i = 0; i < 5; i++)
    {
        bms_receiveData(cmdList[i], rxData, rxPec, rxCc);
        if (bms_checkRxFault(rxData, rxPec, rxCc))
        {
            return -1;
        }
        bms_parseAuxVoltage(rxData, ic_ad68.temp_cell, i);
    }
    return 0;
}


BMS_StatusTypeDef bms_getAuxMeasurement(void)
{

    ADAX.OW   = 0b0;
    ADAX.CH   = 0b0000;
    ADAX.CH4  = 0b0;
    ADAX.PUP  = 0b0;

//    bms_startTimer();
//    bms_wakeupChain();

    //bms_transmitCmd((uint8_t *)&ADAX);
    //bms_transmitPoll(PLAUX1);
    //if (bms_getAuxVoltage())
    //{
    //    return BMS_ERR_COMMS;
    //}

    bms_transmitCmd((uint8_t *)&ADAX);
    bms_transmitPoll(PLAUX1);
    if (bms_getAuxVoltage())
    {
        return BMS_ERR_COMMS;
    }
    bms68_setGpo45(0b11);           // Reset to default
    if (DEBUG_SERIAL_AUX_ENABLED) bms_printTemps();

    //bms_parseTemps();
    //bms_calculateStats(VOLTAGE_TEMP);
    //if (DEBUG_SERIAL_VOLTAGE_ENABLED)   bms_printVoltage(VOLTAGE_TEMP);
    //if (DEBUG_SERIAL_AUX_ENABLED)      bms_printTemps();

//    uint32_t time = bms_getTimCount();
//    bms_stopTimer();
//    printfDma("PT %ld us\n", time);

    return BMS_OK;
}


void bms_setPwm(uint8_t ic_index, uint8_t cell, uint8_t dutyCycle)
{
    cell++;                                 // Change from 0 indexing to 1 indexing

    switch (cell) {
        case 1:
            ic_ad68.pwma[ic_index].pwm1 = dutyCycle;
            break;
        case 2:
            ic_ad68.pwma[ic_index].pwm2 = dutyCycle;
            break;
        case 3:
            ic_ad68.pwma[ic_index].pwm3 = dutyCycle;
            break;
        case 4:
            ic_ad68.pwma[ic_index].pwm4 = dutyCycle;
            break;
        case 5:
            ic_ad68.pwma[ic_index].pwm5 = dutyCycle;
            break;
        case 6:
            ic_ad68.pwma[ic_index].pwm6 = dutyCycle;
            break;
        case 7:
            ic_ad68.pwma[ic_index].pwm7 = dutyCycle;
            break;
        case 8:
            ic_ad68.pwma[ic_index].pwm8 = dutyCycle;
            break;
        case 9:
            ic_ad68.pwma[ic_index].pwm9 = dutyCycle;
            break;
        case 10:
            ic_ad68.pwma[ic_index].pwm10 = dutyCycle;
            break;
        case 11:
            ic_ad68.pwma[ic_index].pwm11 = dutyCycle;
            break;
        case 12:
            ic_ad68.pwma[ic_index].pwm12 = dutyCycle;
            break;
        case 13:
            ic_ad68.pwmb[ic_index].pwm13 = dutyCycle;
            break;
        case 14:
            ic_ad68.pwmb[ic_index].pwm14 = dutyCycle;
            break;
        case 15:
            ic_ad68.pwmb[ic_index].pwm15 = dutyCycle;
            break;
        case 16:
            ic_ad68.pwmb[ic_index].pwm16 = dutyCycle;
            break;
        default:
            // Handle invalid cases
            break;
    }
}


/*
 * Converts delta threshold (threshold difference between all cell voltages)
 * to
 * discharge threshold (voltage at which cell stop discharging)
 */
float bms_calculateBalancing(float deltaThreshold)
{
    float min = ic_common.v_pack_min;
    float max = ic_common.v_pack_max;

    if (max - min > deltaThreshold)
    {
        return min + deltaThreshold;
    }
    else { return ic_common.v_pack_min + deltaThreshold; } // halte Auswahl stabil
}



void bms_startDischarge(float dischargeThreshold)
{
    // store last duty -> needed to avoid flicker at thresholds
    static uint8_t last_duty[TOTAL_AD68][TOTAL_CELL] = {{0}};

    // not needed here -> Threshold is set in "diff_to_pwm4bit"
    (void)dischargeThreshold;

    for (int ic = 0; ic < TOTAL_AD68; ic++)
    {
        ad68_pwma_t pwma = (ad68_pwma_t){0};
        ad68_pwmb_t pwmb = (ad68_pwmb_t){0};

        for (int c = 0; c < TOTAL_CELL; c++)
        {
            // takes S-ADC values
            const float v     = ic_ad68.v_cell[dischargeVoltageType][ic][c];
            const float diffV = v - ic_common.v_pack_min;

            // calculate duty
            const uint8_t duty = diff_to_pwm4bit(diffV, last_duty[ic][c]);

            if (duty > 0) {
                BIT_SET(ic_ad68.isDischarging[ic], c);
                set_cell_pwm_4bit(&pwma, &pwmb, (uint8_t)c, duty);
            } else {
                BIT_CLEAR(ic_ad68.isDischarging[ic], c);

            }

            last_duty[ic][c] = duty; // update state
        }

        // PWM mode: must not set static discharge bits (DCC)
        ic_ad68.cfb_Tx[ic].dcc   = 0;

        // keep discharge timer alive (DCTO)
        ic_ad68.cfb_Tx[ic].dtrng = 0;
        ic_ad68.cfb_Tx[ic].dcto  = 15;
        ic_ad68.cfb_Tx[ic].dtmen = 0;

        // Shadow-Register übernehmen
        ic_ad68.pwma[ic] = pwma;
        ic_ad68.pwmb[ic] = pwmb;
    }

    // write registers in correct order: PWM first, then ConfigB
    bms_writeRegister(REG_PWM_A);
    bms_writeRegister(REG_PWM_B);
    bms_writeRegister(REG_CONFIG_B);


    bms_readRegister(REG_PWM_A);
    bms_readRegister(REG_PWM_B);

    bms_delayMsActive(2);
}







void bms_stopDischarge(void)
{
    for (int ic = 0; ic < TOTAL_AD68; ic++)
    {
        for (int c = 0; c < TOTAL_CELL; c++)
        {
            BIT_CLEAR(ic_ad68.isDischarging[ic], c);
        }

        // The PWM discharge functionality is possible in the standby, REF-UP, extended balancing and in the measure states
        // AND while the discharge timeout has not expired (DCTO ≠ 0)
        ic_ad68.cfb_Tx[ic].dcc = 0;
        ic_ad68.cfb_Tx[ic].dcto = 0;     // DC Timer in minutes (DTRNG = 0)
        ic_ad68.cfb_Tx[ic].dtmen = 0;    // Disables Discharge Timer Monitor (DTM)

        memset(&ic_ad68.pwma[ic], 0, sizeof(ic_ad68.pwma[ic]));
        memset(&ic_ad68.pwmb[ic], 0, sizeof(ic_ad68.pwmb[ic]));
    }
    bms_writeRegister(REG_PWM_A);
    bms_writeRegister(REG_PWM_B);
    bms_writeRegister(REG_CONFIG_B);             // Send the DCTO Timer config
}


void bms_softReset(void)
{
    bms_wakeupChain();
    bms_transmitCmd(SRST);      // Put all devices to sleep
    printfDma("\n  ---  SOFT RESET  ---  \n");
}


BMS_StatusTypeDef bms29_readVB(void)
{
    if (TOTAL_AD29)
    {
        bms_receiveData(RDVB, rxData, rxPec, rxCc);
        if (bms_checkRxFault(rxData, rxPec, rxCc))
        {
            return BMS_ERR_COMMS;
        }

        ic_ad29.vb1 = *((int16_t *)(rxData[0] + 2)) *  0.000100 * 396.604395604;
        ic_ad29.vb2 = *((int16_t *)(rxData[0] + 4)) * -0.000085 * 751;
        if (DEBUG_SERIAL_MASTER_MEASUREMENTS)
        {
			printfDma("Pack Voltage %fV, %fV  \n", ic_ad29.vb1, ic_ad29.vb2);
        }
    }
    else
    {
        if (DEBUG_SERIAL_MASTER_MEASUREMENTS)
        {
			printfDma("Pack Voltage (AD29 Disabled!) \n");
        }
    }
    return BMS_OK;
}



BMS_StatusTypeDef bms29_readCurrent(void)
{
    if (TOTAL_AD29)
    {
        bms_receiveData(RDI, rxData, rxPec, rxCc);
        if (bms_checkRxFault(rxData, rxPec, rxCc))
        {
            return BMS_ERR_COMMS;
        }
    //    bms_printRawData(rxData, rxCc);

        // microvolts
        int32_t i1v = 0;
        int32_t i2v = 0;

        i1v = ((uint32_t)rxData[0][0]) | ((uint32_t)rxData[0][1] << 8) | ((int32_t)rxData[0][2] << 16);
        i2v = ((uint32_t)rxData[0][3]) | ((uint32_t)rxData[0][4] << 8) | ((int32_t)rxData[0][5] << 16);

        if (i1v & (UINT32_C(1) << 23)) { i1v |= 0xFF000000; }; // Check the sign bit (24th bit) and extend the sign
        if (i2v & (UINT32_C(1) << 23)) { i2v |= 0xFF000000; };

        const float SHUNT_RESISTANCE = 0.000050; // 50 microOhms

        ic_ad29.current1 = ((float)i1v / -1000000.0f) / SHUNT_RESISTANCE;
        ic_ad29.current2 = ((float)i2v /  1000000.0f) / SHUNT_RESISTANCE;
        if (DEBUG_SERIAL_MASTER_MEASUREMENTS)
        {
            printfDma("Current %fA, %fA  \n", ic_ad29.current1 , ic_ad29.current2);
        }
    }
    else
    {
        if (DEBUG_SERIAL_MASTER_MEASUREMENTS)
        {
            printfDma("Current (AD29 Disabled!) \n");
        }
    }
    return BMS_OK;
}



BMS_StatusTypeDef bms_balancingMeasureVoltage(void)
{
    // --- Sicherheitsnetz: DCC MUSS 0 sein, sonst übersteuert es PWM & verfälscht S ---
    bool need_cfgb_write = false;
    for (int ic = 0; ic < TOTAL_AD68; ic++) {
        if (ic_ad68.cfb_Tx[ic].dcc != 0) {
            ic_ad68.cfb_Tx[ic].dcc = 0;      // alle DCCx löschen
            need_cfgb_write = true;
        }
    }
    if (need_cfgb_write) {
        // DCTO/DTRNG/DTMEN nicht anfassen – nur DCC=0 rausgeben
        bms_writeRegister(REG_CONFIG_B);
        bms_delayMsActive(1);
    }

    // --- ADSV Single-Shot S-ADC (PWM wird temporär pausiert) ---
    ADSV.CONT = 0;      // Single-shot
    ADSV.DCP  = 0;      // Entladen erlaubt (betrifft PWM; DCC ist eh 0)
    ADSV.OW   = 0b00;   // kein Open-Wire-Test

    bms_transmitCmd((uint8_t *)&ADSV);
    bms_transmitPoll(PLSADC);

    // S-Spannungen einlesen; dischargeVoltageType sollte VOLTAGE_S sein
    if (bms_readCellVoltage(dischargeVoltageType)) {
        return BMS_ERR_COMMS;
    }

    return BMS_OK;
}



void bms_startBalancing(float deltaThreshold)
{
    float dischargeThreshold = bms_calculateBalancing(deltaThreshold);
    bms_startDischarge(dischargeThreshold);
}


void BMS_GetCanData(CanTxMsg** buff, uint32_t* len)
{
    uint32_t bufferlen = 0;
    uint32_t id = BASE_CAN_ID;
    FDCAN_TxHeaderTypeDef txHeader;

    /* Prepare Tx Header */
    txHeader.Identifier = id;
    txHeader.IdType = FDCAN_EXTENDED_ID;
    txHeader.TxFrameType = FDCAN_DATA_FRAME;
    txHeader.DataLength = 8;
    txHeader.ErrorStateIndicator = FDCAN_ESI_ACTIVE;
    txHeader.BitRateSwitch = FDCAN_BRS_OFF;
    txHeader.FDFormat = FDCAN_CLASSIC_CAN;
    txHeader.TxEventFifoControl = FDCAN_NO_TX_EVENTS;
    txHeader.MessageMarker = 0;

    for (int ic = 0; ic < TOTAL_AD68; ic++)
    {
    	int32_t v_segment = 0;
    	for (int c = 0; c < TOTAL_CELL; c++) {
    	    v_segment += (int32_t)(ic_ad68.v_cell[monitoringVoltageType][ic][c] * 1000.0f + 0.5f);
    	}
        int16_t temp_ic         = ic_ad68.temp_ic[ic]   * 100;
        uint8_t isCommsError    = ic_common.isCommsError[ic+TOTAL_AD29];
        uint8_t isFaultDetected = ic_common.isFaultDetected[ic+TOTAL_AD29];

        memcpy(&canTxBuffer[bufferlen].data[0], &v_segment, 4);
//        canTxBuffer[bufferlen].data[4] = (uint8_t)(temp_ic & 0xFF);
//        canTxBuffer[bufferlen].data[5] = (uint8_t)((temp_ic >> 8) & 0xFF);
        memcpy(&canTxBuffer[bufferlen].data[4], &temp_ic, 2);
        canTxBuffer[bufferlen].data[6] = (uint8_t)((isCommsError << 0) | (isFaultDetected << 1));

        txHeader.Identifier = BASE_CAN_ID + (TOTAL_AD68 * TOTAL_CELL) + ic;
        canTxBuffer[bufferlen].header = txHeader;
        bufferlen++;

        if (isCommsError)
        {
            continue; // Does not send cell voltage and temp as its invalid
        }

        for (int c = 0; c < TOTAL_CELL; c++)
        {
            int16_t cellVoltage = (int16_t)(ic_ad68.v_cell[monitoringVoltageType][ic][c] * 1000);
            int16_t voltageDiff = (int16_t)(ic_ad68.v_cell_diff[monitoringVoltageType][ic][c] * 1000);
            int16_t cellTemp;
            if (c < TOTAL_TEMP)
            {
            	cellTemp    = (int16_t)(ic_ad68.temp_cell[ic][c] * 100);
            }
            uint8_t isDischarging       = ((ic_ad68.isDischarging[ic]       >> c) & 0x01U);
            uint8_t isCellFaultDetected = ((ic_ad68.isCellFaultDetected[ic] >> c) & 0x01U);

            canTxBuffer[bufferlen].data[0] = (uint8_t)(cellVoltage & 0xFF);
            canTxBuffer[bufferlen].data[1] = (uint8_t)((cellVoltage >> 8) & 0xFF);
            canTxBuffer[bufferlen].data[2] = (uint8_t)(voltageDiff & 0xFF);
            canTxBuffer[bufferlen].data[3] = (uint8_t)((voltageDiff >> 8) & 0xFF);
            if (c < TOTAL_TEMP)
            {
            	canTxBuffer[bufferlen].data[4] = (uint8_t)(cellTemp & 0xFF);
            }
            if (c < TOTAL_TEMP)
            {
            	canTxBuffer[bufferlen].data[5] = (uint8_t)((cellTemp >> 8) & 0xFF);
            }
            canTxBuffer[bufferlen].data[6] = (uint8_t)((isDischarging << 0) | (isCellFaultDetected << 1));

            uint32_t id_cell_offset = ic * TOTAL_CELL + c;

            txHeader.Identifier = id + id_cell_offset;
            canTxBuffer[bufferlen].header = txHeader;
            bufferlen++;
        }
    }

    if (TOTAL_AD29)
    {
        uint8_t isCommsError    = ic_common.isCommsError[0];
        uint8_t isFaultDetected = ic_common.isFaultDetected[0];

        canTxBuffer[bufferlen].data[0] = (uint8_t)((isCommsError << 0) | (isFaultDetected << 1));
        txHeader.Identifier = BASE_CAN_ID + (TOTAL_AD68 * TOTAL_CELL) + TOTAL_AD68 + 1;
        canTxBuffer[bufferlen].header = txHeader;
        bufferlen++;

        if (!isCommsError)
        {
            int16_t packVoltage     = (ic_ad29.vb1 + ic_ad29.vb2) * 10 / 2;
            int16_t packCurrent     = (int16_t)(((ic_ad29.current1 + ic_ad29.current2) * 100.0f) / 2.0f);

            packVoltage = ic_common.v_pack_total * 10; // overwrite the pack voltage measurement from master

            canTxBuffer[bufferlen].data[0] = (packVoltage >> 0)  & 0xFF;
            canTxBuffer[bufferlen].data[1] = (packVoltage >> 8)  & 0xFF;

            canTxBuffer[bufferlen].data[2] = (packCurrent >> 0)  & 0xFF;
            canTxBuffer[bufferlen].data[3] = (packCurrent >> 8)  & 0xFF;

            txHeader.Identifier = BASE_CAN_ID + (TOTAL_AD68 * TOTAL_CELL) + TOTAL_AD68;
            canTxBuffer[bufferlen].header = txHeader;
            bufferlen++;
        }
    }

     //--- CHARGER CONFIG CAN MESSAGE --- //
    //BMS_CAN_GetChargerMsg(&chargerConfig, canTxBuffer[bufferlen].data);
    //txHeader.Identifier = CHARGER_CONFIG_CAN_ID;
    //canTxBuffer[bufferlen].header = txHeader;
    //bufferlen++;

    *len = bufferlen;
    *buff = canTxBuffer;
}


BMS_StatusTypeDef BMS_CheckTemps(void)
{
    return (BMS_StatusFlags & BMS_ERR_TEMP);
}

BMS_StatusTypeDef BMS_CheckVoltage(void)
{
    return (BMS_StatusFlags & BMS_ERR_VOLTAGE);
}

BMS_StatusTypeDef BMS_CheckCurrent(void)
{
    return (BMS_StatusFlags & BMS_ERR_CURRENT);
}

BMS_StatusTypeDef BMS_CheckCommsFault(void)
{
    return (BMS_StatusFlags & BMS_ERR_COMMS);
}

void BMS_SetCommsFault(bool state)
{
    if (state)
        BMS_StatusFlags |= BMS_ERR_COMMS;   // Set fault
    else
        BMS_StatusFlags &= ~BMS_ERR_COMMS;  // Clear fault
}


BMS_StatusTypeDef BMS_UpdateStatusFlags(void)
{

	const float MAX_VOLTAGE = 4.2;
	const float MIN_VOLTAGE = 2.7;

    const float MAX_PACK_VOLTAGE = MAX_VOLTAGE * TOTAL_CELL * TOTAL_AD68;
    const float MIN_PACK_VOLTAGE = MIN_VOLTAGE * TOTAL_CELL * TOTAL_AD68;

    const float MAX_CURRENT = 10.0;
    const float MIN_CURRENT = -MAX_CURRENT;



    const float MAX_IC_VOLTAGE = MAX_VOLTAGE * TOTAL_CELL;
    const float MIN_IC_VOLTAGE = MIN_VOLTAGE * TOTAL_CELL;

    const float MAX_TEMP = 60;
    const float MIN_TEMP = 0;

    const float MAX_IC_TEMP = 70;
    const float MIN_IC_TEMP = 0;

    BMS_StatusTypeDef status = BMS_OK;
    BMS_StatusTypeDef returnStatus = BMS_OK;

    if (TOTAL_AD29)
    {
//        float packVoltage = ic_ad29.vb1;        // TODO: Figure out how to combine 2 values
        float packVoltage = ic_common.v_pack_total;
        float packCurrent = ic_ad29.current1;
        if (packVoltage > MAX_PACK_VOLTAGE || packVoltage < MIN_PACK_VOLTAGE)
        {
            printfDma("PACK VOLTAGE FAULT %f V \n", packVoltage);
            ic_common.isFaultDetected[0] = true;
            status |= BMS_ERR_VOLTAGE;
        }

        if (packCurrent > MAX_CURRENT || packCurrent < MIN_CURRENT)
        {
            printfDma("PACK CURRENT FAULT %f C \n", packCurrent);
            ic_common.isFaultDetected[0] = true;
            status |= BMS_ERR_CURRENT;
        }

        if (status == BMS_OK)
        {
            ic_common.isFaultDetected[0] = false;
        }

        returnStatus |= status;
        status = BMS_OK;
    }

    for (int ic = 0; ic < TOTAL_AD68; ic++)
    {
        for (int c = 0; c < TOTAL_CELL; c++)
        {
            float cellVoltage = ic_ad68.v_cell[dischargeVoltageType][ic][c];

            if (cellVoltage > MAX_VOLTAGE || cellVoltage < MIN_VOLTAGE)
            {
                printfDma("CELL VOLTAGE FAULT SEG %d, CELL %d, %f \n", ic+1, c+1, cellVoltage);
                BIT_SET(ic_ad68.isCellFaultDetected[ic], c);
                status |= BMS_ERR_VOLTAGE;
            }

            if (status == BMS_OK)
            {
                BIT_CLEAR(ic_ad68.isCellFaultDetected[ic], c);
            }

            returnStatus |= status;
            status = BMS_OK;
        }

        for (int c = 0; c < TOTAL_TEMP; c++)
        {
            float cellTemp = ic_ad68.temp_cell[ic][c];

            if (cellTemp > MAX_TEMP || cellTemp < MIN_TEMP)
            {
                printfDma("CELL TEMP FAULT SEG %d, CELL %d, %f \n", ic+1, c+1, cellTemp);
                BIT_SET(ic_ad68.isTempFaultDetected[ic], c);
                status |= BMS_ERR_TEMP;
            }

            if (status == BMS_OK)
            {
                BIT_CLEAR(ic_ad68.isTempFaultDetected[ic], c);
            }

            returnStatus |= status;
            status = BMS_OK;
        }

        float icVoltage = ic_ad68.v_segment[ic];
        float icTemp = ic_ad68.temp_ic[ic];

        if (icVoltage > MAX_IC_VOLTAGE || icVoltage < MIN_IC_VOLTAGE)
        {
            printfDma("IC VOLTAGE FAULT SEG %d, %f \n", ic+1, icVoltage);
            ic_common.isFaultDetected[ic + TOTAL_AD29] = true;
            status |= BMS_ERR_VOLTAGE;
        }

        if (icTemp > MAX_IC_TEMP || icTemp < MIN_IC_TEMP)
        {
            printfDma("IC TEMP FAULT SEG %d, %f \n", ic+1, icTemp);
            ic_common.isFaultDetected[ic + TOTAL_AD29] = true;
            status |= BMS_ERR_TEMP;
        }

        if (status == BMS_OK)
        {
            ic_common.isFaultDetected[ic + TOTAL_AD29] = false;
        }

        returnStatus |= status;
        status = BMS_OK;
    }

    BMS_StatusFlags = returnStatus;
    return returnStatus;
}


BMS_StatusTypeDef BMS_ProgramLoop(void)
{
    BMS_StatusTypeDef status;

    // c filter for measuring purpose -> does not pause PWM
    bms_wakeupChain();
    if ((status = bms_readCellVoltage(monitoringVoltageType))) return status;

    uint32_t now = HAL_GetTick();

    bms_wakeupChain(); if ((status = bms_getAuxMeasurement())) return status;
    bms_wakeupChain(); if ((status = bms29_readVB()))          return status;
    bms_wakeupChain(); if ((status = bms29_readCurrent()))     return status;

    // Fault gating
    uint32_t errs       = BMS_UpdateStatusFlags();
    BMS_SetFaultLed(errs != BMS_OK);
    uint32_t hard_block = (BMS_ERR_VOLTAGE | BMS_ERR_CURRENT | BMS_ERR_COMMS | BMS_ERR_TEMP);

    // additional balancing logic
    // BAL_IDLE: to turn off PWM -> S-Measure -> if needed sets PWM for BAL_ON_MS
    // BAL_RUN: PWMs are running for BAL_ON_MS -> PWM off -> let voltages settle
    // BAL_COOL: for BAL_OFF_MS cool down -> BAL_IDLE -> get S-measurements and evaluation
    typedef enum { BAL_IDLE, BAL_RUN, BAL_COOL } bal_state_t;
    static bal_state_t bal_state = BAL_IDLE;

    static uint32_t t_run_end  = 0;   // end of 60 s window for balancing
    static uint32_t t_cool_end = 0;   // end of 5 s cool-down
    static uint32_t t_cfgb     = 0;   // next CFGB refresh during RUN

    const uint32_t BAL_ON_MS        = 60000; // 60s run
    const uint32_t BAL_OFF_MS       = 5000;  // 5s off to settle
    const uint32_t CFGB_REFRESH_MS  = 500;   // keep DCTO alive during RUN


    bool measuring_now = false; // for enabel/disable charging

    if (enableBalancing)
    {
        if ((errs & hard_block) != 0) {
            // -> PWM OFF and go idle
            bms_wakeupChain();
            bms_quickPwmOff_keepDcto();
            bal_state = BAL_IDLE;
        }
        else
        {
            switch (bal_state)
            {
            case BAL_IDLE:
                // Start evaluation, PWM off
                bms_wakeupChain();
                bms_quickPwmOff_keepDcto(); // ensure PWM = OFF
                BMS_EnableCharging(false);
                measuring_now = true;

                bms_wakeupChain();
                if ((status = bms_balancingMeasureVoltage())) return status; // clean S

                measuring_now = false;

                bms_wakeupChain();
                bms_startBalancing(balancingThreshold); // set PWMs once for BAL_ON_MS

                t_run_end = now + BAL_ON_MS;
                t_cfgb    = now + CFGB_REFRESH_MS;
                bal_state = BAL_RUN;
                break;

            case BAL_RUN:
                // No re-calculation; just keep DCTO alive
                if ((int32_t)(now - t_run_end) >= 0) {
                    // Stop PWM and enter cool-down
                    bms_wakeupChain();
                    bms_quickPwmOff_keepDcto();    // PWMs OFF for all cells -> let voltages settle
                    t_cool_end = now + BAL_OFF_MS;
                    bal_state  = BAL_COOL;
                } else if ((int32_t)(now - t_cfgb) >= 0) {
                    bms_wakeupChain();
                    bms_writeRegister(REG_CONFIG_B); // refresh DCTO -> PWMs unchanged
                    t_cfgb += CFGB_REFRESH_MS;
                }
                break;

            case BAL_COOL: // Do nothing for BAL_OFF_MS -> let pack settle

                if ((int32_t)(now - t_cool_end) >= 0) {
                    bal_state = BAL_IDLE; // After cool-down -> evaluate again
                }
                break;
            }
        }
    }
    else
    {
        // Balancing disabled: PWM OFF; periodic S for monitoring
        bms_wakeupChain();
        bms_quickPwmOff_keepDcto();
        bal_state = BAL_IDLE;

        //  for S measurement when balancing is disabled
        static uint32_t last_s_tick = 0;
        const  uint32_t S_PERIOD_MS = 10000;

        if ((int32_t)(now - last_s_tick) >= 0) {

        	measuring_now = true;
        	BMS_EnableCharging(false);
            bms_wakeupChain();
            (void)bms_balancingMeasureVoltage();       // ignore error here
            measuring_now = false;
            last_s_tick = now + S_PERIOD_MS;
        }
    }
    //
    bool balancing_active = (bal_state == BAL_RUN);
    BMS_UpdateChargingControl(errs, balancing_active, measuring_now, now);

    bms_wakeupChain();
    return BMS_OK;
}



void BMS_EnableCharging(bool enabled)
{
	static int last = -1;
    chargerConfig.disable_charging = !enabled;

    // Enable PC12 -> CHARGER_OUT
    HAL_GPIO_WritePin(BMS_CHARGER_OUT_GPIO_Port, BMS_CHARGER_OUT_Pin, enabled ? GPIO_PIN_SET : GPIO_PIN_RESET);
    if (last!=(int)enabled)
    {
    	printfDma("[CHG] %s\n", enabled ? "ENABLED" : "DISABLED");
    	last = (int)enabled;
    }
}

static inline bool BMS_IsChargingPermitted(uint32_t errs, bool balancing_active, bool measuring_now)
{
    // check for balancing, errors and measuring
    return (errs == BMS_OK) && !balancing_active && !measuring_now;
}

void BMS_UpdateChargingControl(uint32_t errs, bool balancing_active, bool measuring_now, uint32_t now_ms)
{
	static int last = -1;
    static uint32_t t_enable_ok_until = 0;
    const  uint32_t ENABLE_DELAY_MS   = 500;

    bool allow = BMS_IsChargingPermitted(errs, balancing_active, measuring_now);

    if (!allow) {
        BMS_EnableCharging(false);  // disable charging
        t_enable_ok_until = now_ms + ENABLE_DELAY_MS;  // delay for next enable
        if (last != 0)
        {
        	printfDma("[CHG] blocked\n");
            last = 0;
        }
    } else {
        if ((int32_t)(now_ms - t_enable_ok_until) >= 0) {
            BMS_EnableCharging(true);
            if (last != 1)
            {
            	printfDma("[CHG] allowed\n");
                last = 1;
            }
        }
    }
}


static inline void BMS_SetFaultLed(bool on)
{
	static int last = -1;
	HAL_GPIO_WritePin(BMS_FAULT_GPIO_Port, BMS_FAULT_Pin, on ? GPIO_PIN_RESET : GPIO_PIN_SET);
    if (last != (int)on)
    {
    	printfDma("[LED] fault %s\n", on ? "ON" : " OFF");
    	last = (int)on;
    }
}

bool BMS_IsCharging(void)
{
    return !chargerConfig.disable_charging;
}

void BMS_ChargingButtonLogic(void)
{
    // Check for charger status and enables charging
    // or disables charger if charging is enabled
    bool chargerEnabled = !chargerConfig.disable_charging;

    if (chargerEnabled)
    {
        BMS_EnableCharging(false);
        return;
    }

    bool statusOK = true;
    if (!HAL_GPIO_ReadPin(SDC_IN_GPIO_Port, SDC_IN_Pin)) statusOK = false;  // SDC is not connected
//    if (chargerStatus.hardware_fault != false)      statusOK = false;
//    if (chargerStatus.over_temp_fault != false)     statusOK = false;
//    if (chargerStatus.input_voltage_fault != false) statusOK = false;
//    if (chargerStatus.output_voltage < 300.0f)      statusOK = false;

    if (statusOK)
    {
        BMS_EnableCharging(true);
    }
    else
    {
        printfDma("Charger NOT OK to start Charging \n");
    }
}

void BMS_EnableBalancing(bool enabled)
{
    enableBalancing = enabled;
}

void BMS_ToggleBalancing(void)
{
    enableBalancing = !enableBalancing;
    if (!enableBalancing) bms_stopDischarge();
}

void BMS_WriteFaultSignal(bool state)
{
    static bool currState = 1;
    if (currState != state)
    {
        char *stateStr = (state)? "ON " : "OFF";
        printfDma("FAULT SIGNAL UPDATE %s\n", stateStr);

        HAL_GPIO_WritePin(FAULT_CTRL_GPIO_Port, FAULT_CTRL_Pin, state); // If mosfet is ON, Fault == TRUE
        currState = state;
    }
}
