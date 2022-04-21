/*
 * Licensed to the Apache Software Foundation (ASF) under one
 * or more contributor license agreements.  See the NOTICE file
 * distributed with this work for additional information
 * regarding copyright ownership.  The ASF licenses this file
 * to you under the Apache License, Version 2.0 (the
 * "License"); you may not use this file except in compliance
 * with the License.  You may obtain a copy of the License at
 *
 *  http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing,
 * software distributed under the License is distributed on an
 * "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
 * KIND, either express or implied.  See the License for the
 * specific language governing permissions and limitations
 * under the License.
 */
//  Implementation of SWD protocol with Raspberry Pi Bidirectional SPI by Lup Yuen Lee (luppy@appkaki.com)
//  Why implement SWD over Bidirectional SPI on Raspberry Pi?  Because SWD over Bit-Banging GPIO has timing issues that affect OpenOCD flashing...
//  See https://medium.com/@ly.lee/openocd-on-raspberry-pi-better-with-swd-on-spi-7dea9caeb590?source=friends_link&sk=df399bfd913d3e262447d28aa5af6b63

//  Based on https://raw.githubusercontent.com/raspberrypi/linux/rpi-3.10.y/Documentation/spi/spidev_test.c
//  SWD Overview: https://github.com/MarkDing/swd_programing_sram
//  SWD Protocol: https://github.com/MarkDing/swd_programing_sram/blob/master/Ref/ARM_debug.pdf
//  Pi SPI Hardware: https://www.raspberrypi.org/documentation/hardware/raspberrypi/spi/README.md
//  Pi SPI Kernel Driver: https://github.com/raspberrypi/linux/blob/rpi-3.12.y/drivers/spi/spi-bcm2708.c
//  BCM2835 Peripherals Datasheet: https://www.raspberrypi.org/documentation/hardware/raspberrypi/bcm2835/BCM2835-ARM-Peripherals.pdf
//  SWD mapped to SPI bytes: https://docs.google.com/spreadsheets/d/12oXe1MTTEZVIbdmFXsOgOXVFHCQnYVvIw6fRpIQZybg/edit#gid=0

//  To build:
//  cd ~/openocd-spi
//  ./bootstrap
//  ./configure --enable-sysfsgpio --enable-bcm2835spi --enable-cmsis-dap
//  make

//  To test:
//  Connect SWDIO to MOSI (Pin P1-19, Yellow)
//  Connect SWDCLK to SCLK (Pin P1-23, Blue)
//  Connect 3.3V and GND
//  sudo raspi-config
//  Interfacing Options --> SPI --> Yes
//  Finish --> Yes

//  #define LOG_SPI  //  Uncomment to log SPI requests
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#include <stdint.h>
#include <unistd.h>
#include <stdio.h>
#include <stdlib.h>
#include <getopt.h>
#include <fcntl.h>
#include <sys/ioctl.h>
#include <linux/types.h>
#include <linux/spi/spidev.h>
#include <jtag/swd.h>
#include <jtag/interface.h>
#include "bitbang.h"

static void spi_exchange_transmit(uint8_t buf[], unsigned int offset, unsigned int bit_cnt);
static void spi_exchange_receive(uint8_t buf[], unsigned int offset, unsigned int bit_cnt);
static void spi_transmit_resync(int fd);
static void spi_transmit(int fd, const uint8_t *buf, unsigned int len);
static void spi_receive(int fd, uint8_t *buf, unsigned int len);
static void push_lsb_buf(int next_bit);
static int pop_lsb_buf(void);
static bb_value_t bcm2835spi_read(void);
static int bcm2835spi_write(int tck, int tms, int tdi);
static int bcm2835spi_reset(int trst, int srst);
static int bcm2835_swdio_read(void);
static int bcm2835spi_swd_write(int swclk, int swdio);
static void bcm2835_swdio_drive(bool is_output);
static int bcm2835spi_speed(int speed);
static int bcm2835spi_speed_div(int speed, int *khz);
static int bcm2835spi_khz(int khz, int *jtag_speed);
static int bcm2835spi_init(void);
static int bcm2835spi_quit(void);
COMMAND_HANDLER(bcm2835spi_handle_speed);

//  SPI Configuration
static const char *device = "/dev/spidev0.0";  //  SPI device name. If missing, enable SPI in raspi-config.
static uint8_t mode = 0  //  Note: SPI LSB mode is not supported on Broadcom. We must flip LSB to MSB ourselves.
    | SPI_NO_CS  //  1 SPI device per bus, no Chip Select
    | SPI_3WIRE  //  Bidirectional SPI mode, data in and out pin shared
    ;            //  Data is valid on first rising edge of the clock, so CPOL=0 and CPHA=0
static uint8_t bits   = 8;         //  8 bits per SPI word
static uint speed_khz = 31200;     //  31,200 kHz (31.2 MHz) for SPI speed. Use fastest speed possible because we resend JTAG-to-SWD sequence after every read
//  static uint speed_khz = 1953;  //  Slower: 1,953 kHz (1.9 MHz)
//  static uint speed_khz = 122;   //  Slowest: 122 kHz
static uint16_t delay = 0;         //  SPI driver latency: https://www.raspberrypi.org/forums/viewtopic.php?f=44&t=19489

/// We need 2 transmit/receive buffers: One buffer in OpenOCD's LSB format, one buffer in Broadcom SPI's MSB format
#define MAX_SPI_SIZE 256
/// Bytes to be transmitted or received in LSB format (used by OpenOCD)
static uint8_t lsb_buf[MAX_SPI_SIZE];
/// Bytes to be transmitted or received in MSB format (used by Broadcom SPI)
static uint8_t msb_buf[MAX_SPI_SIZE];
/// Dummy buffer for receiving bytes during delay
static uint8_t delay_buf[MAX_SPI_SIZE];
/// Index of bit in lsb_buf currently being pushed or popped
static unsigned int lsb_buf_bit_index;
/// File descriptor for SPI device
static int spi_fd = -1;

/// SWD Sequence to Read Register 0 (IDCODE), prepadded with 2 null bits bits to fill up 6 bytes. Byte-aligned, will not cause overrun error.
/// A transaction must be followed by another transaction or at least 8 idle cycles to ensure that data is clocked through the AP.
/// After clocking out the data parity bit, continue to clock the SW-DP serial interface until it has clocked out at least 8 more clock rising edges, before stopping the clock.
static const uint8_t  swd_read_idcode_prepadded[]   = { 0x00, 0x94, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00 };  //  With null byte (8 cycles idle) before and after
static const unsigned swd_read_idcode_prepadded_len = 64;  //  Number of bits

/// SWD Sequence to Write Register 0 (ABORT). Clears all sticky flags: 
/// STICKYORUN: overrun error flag,
/// WDATAERR: write data error flag,
/// STICKYERR: sticky error flag,
/// STICKYCMP: sticky compare flag.
/// Byte-aligned, will not cause overrun error.
static const uint8_t  swd_write_abort[]   = { 0x00, 0x81, 0xd3, 0x03, 0x00, 0x00, 0x00, 0x00 };  //  With null byte (8 cycles idle) before and after
static const unsigned swd_write_abort_len = 64;  //  Number of bits

/// Only SWD transport supported
static const char * const bcm2835_transports[] = { "swd", NULL };

/// List of configuration settings
static const struct command_registration bcm2835spi_command_handlers[] = {
	{
		.name    = "bcm2835spi_speed",
		.handler = &bcm2835spi_handle_speed,
		.mode    = COMMAND_CONFIG,
		.help    = "SPEED for SPI interface (kHz).",
		.usage   = "[SPEED]",
	},
	COMMAND_REGISTRATION_DONE
};

/// Bit Bang Interface for BCM2835 SPI
static struct bitbang_interface bcm2835spi_bitbang = {
	.read        = bcm2835spi_read,
	.write       = bcm2835spi_write,
	.swdio_read  = bcm2835_swdio_read,
	.swdio_drive = bcm2835_swdio_drive,
	.swd_write   = bcm2835spi_swd_write,
	.blink       = NULL
};

/// JTAG interface
static struct jtag_interface bcm2835spi_interface = {
	.supported      = DEBUG_CAP_TMS_SEQ,
	.execute_queue  = bitbang_execute_queue,
};

/// Adapter driver
struct adapter_driver bcm2835spi_adapter_driver = {
	.name           = "bcm2835spi",
	.transports     = bcm2835_transports,
	.commands       = bcm2835spi_command_handlers,

	.init           = bcm2835spi_init,
	.quit           = bcm2835spi_quit,
	.speed          = bcm2835spi_speed,
	.khz            = bcm2835spi_khz,
	.speed_div      = bcm2835spi_speed_div,
  .reset          = bcm2835spi_reset,

  .jtag_ops = &bcm2835spi_interface,
  .swd_ops = &bitbang_swd,
};

/// Transmit or receive bit_cnt number of bits from/into buf (LSB format) starting at the bit offset.
/// If target_to_host is false: Transmit from host to target.
/// If target_to_host is true:  Receive from target to host.
/// Called by bitbang_swd_exchange() in src/jtag/drivers/bitbang.c
void spi_exchange(bool target_to_host, uint8_t buf[], unsigned int offset, unsigned int bit_cnt)
{
    if (bit_cnt == 0) { return; }
    unsigned int byte_cnt = (bit_cnt + 7) / 8;  //  Round up to next byte count.
    if (byte_cnt >= MAX_SPI_SIZE) { LOG_DEBUG("bit_cnt=%d ", bit_cnt); perror("spi_exchange: overflow"); return; }

    //  Handle delay operation.
    if (!buf) {
        //  bitbang_swd_run_queue() calls bitbang_swd_exchange() with buf=NULL and bit_cnt=8 for delay.
        //  bitbang_swd_write_reg() calls bitbang_swd_exchange() with buf=NULL and bit_cnt=255 for delay.
        //  We send the null bytes for delay.
#ifdef LOG_SPI
        LOG_DEBUG("delay %d\n", bit_cnt);
#endif  //  LOG_SPI
        memset(delay_buf, 0, byte_cnt);
        spi_transmit(spi_fd, delay_buf, byte_cnt);
        return;
    }
    //  if (!buf) { LOG_DEBUG("offset=%d, bit_cnt=%d, ", offset, bit_cnt); perror("spi_exchange: null buffer"); return; }

    //  If target_to_host is true, receive from target to host. Else transmit from host to target.
    if (target_to_host) {
        spi_exchange_receive(buf, offset, bit_cnt);
    } else {
        spi_exchange_transmit(buf, offset, bit_cnt);
    }
    //  static int count = 0;  if (++count == 300) { perror("Exit for testing"); } ////
}

/// Transmit bit_cnt number of bits from buf (LSB format) starting at the bit offset.
/// Transmit to target is always byte-aligned with trailing bits=0, so will not cause overrun error.
static void spi_exchange_transmit(uint8_t buf[], unsigned int offset, unsigned int bit_cnt)
{
    //  Handle SWD Write Data, which is 33 bits and not byte-aligned:
    //  ** host -> trgt offset 5 bits 33: d3 03 00 00 80
    //  This happens right after SWD Write Ack (5 bits), which doesn't receive SPI bytes. We compensate the SWD Write Ack before SWD Write Data.  
    if (offset == 5 && bit_cnt == 33) {
        //  SWD Write Ack (5 bits) + SWD Write Data (33 bits) = 38 bits. Then pad later by 2 bits to 40 bits to align by byte.
        offset = 0;
        bit_cnt = 38;
    }
    //  Otherwise we must be transmitting the SWD Command Header, which is 8 bits and byte-aligned:
    //  ** host -> trgt offset 0 bits  8: 81
    //  Or JTAG-To-SWD, which is 136 bits and byte-aligned:
    //  ** host -> trgt offset 0 bits 136: ff ff ff ff ff ff ff 9e e7 ff ff ff ff ff ff ff 00

    unsigned int byte_cnt = (bit_cnt + 7) / 8;  //  Round up to next byte count.
    memset(lsb_buf, 0, sizeof(lsb_buf));
    lsb_buf_bit_index = 0;

    //  Consolidate the bits into LSB buffer before transmitting.
	for (unsigned int i = offset; i < bit_cnt + offset; i++) {
		int bytec = i/8;
		int bcval = 1 << (i % 8);
		int next_bit = buf[bytec] & bcval;
        //  If next_bit is true, push bit 1. Else push bit 0.
        if (next_bit) {
            push_lsb_buf(1);
        } else {
            push_lsb_buf(0);
        }
	}

    //  Pad with null bits until the whole byte is populated.  Should be 2 bits for SWD Write Command.
    int i = 0;
    while (lsb_buf_bit_index % 8 != 0) {        
        push_lsb_buf(0);
        i++;
    }
#ifdef LOG_SPI
    if (i > 0) { LOG_DEBUG("  pad %d\n", i); }
#endif  //  LOG_SPI

    if (bit_cnt == 38) {  //  SWD Write Command
        //  Add 8 clock cycles before stopping the clock.  A transaction must be followed by another transaction or at least 8 idle cycles to ensure that data is clocked through the AP.
        //  After clocking out the data parity bit, continue to clock the SW-DP serial interface until it has clocked out at least 8 more clock rising edges, before stopping the clock.
        //  LOG_DEBUG("**** Add 8 cycles after write\n");
        for (i = 0; i < 8; i++) { push_lsb_buf(0); }
        byte_cnt++;
    }

    //  Transmit the consolidated LSB buffer to target.
    spi_transmit(spi_fd, lsb_buf, byte_cnt);
}

/// Receive bit_cnt number of bits into buf (LSB format) starting at the bit offset.
/// SWD Read Data request is not byte-aligned, so this will always cause overrun error. We clear the error in spi_transmit_resync().
static void spi_exchange_receive(uint8_t buf[], unsigned int offset, unsigned int bit_cnt)
{
    //  Handle SWD Write Ack, which is 5 bits and not byte-aligned:
    //  ** trgt -> host offset 0 bits  5: 13
    //  We always force return OK (0x13) without actually receiving SPI bytes. We compensate the 5 bits during SWD Write Data later (33 bits).
    if (offset == 0 && bit_cnt == 5) {
        //  LOG_DEBUG("write ack force OK\n");
        buf[0] = (buf[0] & 0b11100000) | 0x13;  //  Force lower 5 bits to be 0x13
        return;
    }
    //  Otherwise we must be receiving SWD Read Data, which is 38 bits and not byte-aligned. We will resync by transmitting JTAG-To-SWD below.
    //  ** trgt -> host offset 0 bits 38: 73 47 01 ba a2
    //  Or receiving SWD Run Queue, which is 8 bits and byte-aligned.

    unsigned int byte_cnt = (bit_cnt + 7) / 8;  //  Round up to next byte count.
    //  Fill the missing bits with 0.
    memset(lsb_buf, 0, sizeof(lsb_buf));
    lsb_buf_bit_index = 0;

    if (bit_cnt == 38) {  //  SWD Read Command
        //  Add 8 clock cycles before stopping the clock.  A transaction must be followed by another transaction or at least 8 idle cycles to ensure that data is clocked through the AP.
        //  After clocking out the data parity bit, continue to clock the SW-DP serial interface until it has clocked out at least 8 more clock rising edges, before stopping the clock.
        //  LOG_DEBUG("**** Add 8 clock cycles after read\n");
        byte_cnt++;
    }

    //  Receive the LSB buffer from target.
    spi_receive(spi_fd, lsb_buf, byte_cnt);

    //  Populate LSB buf from the received LSB bits.
	for (unsigned int i = offset; i < bit_cnt + offset; i++) {
		int bytec = i/8;
		int bcval = 1 << (i % 8);
        int next_bit = pop_lsb_buf();
        //  If next_bit is true, push bit 1. Else push bit 0.
        if (next_bit) {
            buf[bytec] |= bcval;
        } else {
            buf[bytec] &= ~bcval;
        }
	}

    //  Handle SWD Read Data, which is 38 bits and not byte-aligned:
    //  ** trgt -> host offset 0 bits 38: 73 47 01 ba a2
    //  Since the target is in garbled state, we will resync by transmitting JTAG-To-SWD and Read IDCODE.
    if (offset == 0 && bit_cnt == 38) {
#ifdef LOG_SPI
        LOG_DEBUG("Resync after read\n");
#endif  //  LOG_SPI
        spi_transmit_resync(spi_fd);
    } else {
        LOG_DEBUG("offset=%d, bit_cnt=%d, ", offset, bit_cnt);
        perror("spi_exchange_receive: unknown msg");
    }
}

/// Transmit resync sequence to reset SWD connection with target
static void spi_transmit_resync(int fd) {
    //  LOG_DEBUG("**** spi_transmit_resync\n");

    //  Transmit JTAG-to-SWD sequence. Need to transmit every time because the SWD read/write command has extra 2 undefined bits that will confuse the target.
    spi_transmit(fd, swd_seq_jtag_to_swd, swd_seq_jtag_to_swd_len / 8);

    //  Transmit command to read Register 0 (IDCODE).  This is mandatory after JTAG-to-SWD sequence, according to SWD protocol.  We prepad with 2 null bits so that the next command will be byte-aligned.
    spi_transmit(fd, swd_read_idcode_prepadded, swd_read_idcode_prepadded_len / 8);

    //  Transmit command to write Register 0 (ABORT) and clear all sticky flags.  Error flags must be cleared before sending next transaction to target.
    //  We expect overrun errors because SWD Read requests are not byte-aligned. So we clear the error here.
    spi_transmit(fd, swd_write_abort, swd_write_abort_len / 8);
}

/// The byte at index i is the value of i with all bits flipped. https://stackoverflow.com/questions/746171/efficient-algorithm-for-bit-reversal-from-msb-lsb-to-lsb-msb-in-c
static const uint8_t reverse_byte[] = {  
  0x00, 0x80, 0x40, 0xC0, 0x20, 0xA0, 0x60, 0xE0, 0x10, 0x90, 0x50, 0xD0, 0x30, 0xB0, 0x70, 0xF0, 
  0x08, 0x88, 0x48, 0xC8, 0x28, 0xA8, 0x68, 0xE8, 0x18, 0x98, 0x58, 0xD8, 0x38, 0xB8, 0x78, 0xF8, 
  0x04, 0x84, 0x44, 0xC4, 0x24, 0xA4, 0x64, 0xE4, 0x14, 0x94, 0x54, 0xD4, 0x34, 0xB4, 0x74, 0xF4, 
  0x0C, 0x8C, 0x4C, 0xCC, 0x2C, 0xAC, 0x6C, 0xEC, 0x1C, 0x9C, 0x5C, 0xDC, 0x3C, 0xBC, 0x7C, 0xFC, 
  0x02, 0x82, 0x42, 0xC2, 0x22, 0xA2, 0x62, 0xE2, 0x12, 0x92, 0x52, 0xD2, 0x32, 0xB2, 0x72, 0xF2, 
  0x0A, 0x8A, 0x4A, 0xCA, 0x2A, 0xAA, 0x6A, 0xEA, 0x1A, 0x9A, 0x5A, 0xDA, 0x3A, 0xBA, 0x7A, 0xFA,
  0x06, 0x86, 0x46, 0xC6, 0x26, 0xA6, 0x66, 0xE6, 0x16, 0x96, 0x56, 0xD6, 0x36, 0xB6, 0x76, 0xF6, 
  0x0E, 0x8E, 0x4E, 0xCE, 0x2E, 0xAE, 0x6E, 0xEE, 0x1E, 0x9E, 0x5E, 0xDE, 0x3E, 0xBE, 0x7E, 0xFE,
  0x01, 0x81, 0x41, 0xC1, 0x21, 0xA1, 0x61, 0xE1, 0x11, 0x91, 0x51, 0xD1, 0x31, 0xB1, 0x71, 0xF1,
  0x09, 0x89, 0x49, 0xC9, 0x29, 0xA9, 0x69, 0xE9, 0x19, 0x99, 0x59, 0xD9, 0x39, 0xB9, 0x79, 0xF9, 
  0x05, 0x85, 0x45, 0xC5, 0x25, 0xA5, 0x65, 0xE5, 0x15, 0x95, 0x55, 0xD5, 0x35, 0xB5, 0x75, 0xF5,
  0x0D, 0x8D, 0x4D, 0xCD, 0x2D, 0xAD, 0x6D, 0xED, 0x1D, 0x9D, 0x5D, 0xDD, 0x3D, 0xBD, 0x7D, 0xFD,
  0x03, 0x83, 0x43, 0xC3, 0x23, 0xA3, 0x63, 0xE3, 0x13, 0x93, 0x53, 0xD3, 0x33, 0xB3, 0x73, 0xF3, 
  0x0B, 0x8B, 0x4B, 0xCB, 0x2B, 0xAB, 0x6B, 0xEB, 0x1B, 0x9B, 0x5B, 0xDB, 0x3B, 0xBB, 0x7B, 0xFB,
  0x07, 0x87, 0x47, 0xC7, 0x27, 0xA7, 0x67, 0xE7, 0x17, 0x97, 0x57, 0xD7, 0x37, 0xB7, 0x77, 0xF7, 
  0x0F, 0x8F, 0x4F, 0xCF, 0x2F, 0xAF, 0x6F, 0xEF, 0x1F, 0x9F, 0x5F, 0xDF, 0x3F, 0xBF, 0x7F, 0xFF
};

/* From https://www.raspberrypi.org/documentation/hardware/raspberrypi/spi/README.md:
    Bidirectional or "3-wire" mode is supported by the spi-bcm2835 kernel module. 
    Please note that in this mode, either the tx or rx field of the spi_transfer 
    struct must be a NULL pointer, since only half-duplex communication is possible. 
    Otherwise, the transfer will fail. The spidev_test.c source code does not consider 
    this correctly, and therefore does not work at all in 3-wire mode. */

/// Transmit len bytes of buf (assumed to be in LSB format) to the SPI device in MSB format
static void spi_transmit(int fd, const uint8_t *buf, unsigned int len) {
    //  Reverse LSB to MSB for LSB buf into MSB buffer.
    if (len >= MAX_SPI_SIZE) { LOG_DEBUG("len=%d ", len); perror("spi_transmit overflow"); return; }
    for (unsigned int i = 0; i < len; i++) {
        uint8_t b = buf[i];
        msb_buf[i] = reverse_byte[(uint8_t) b];
    }
#ifdef LOG_SPI
    {
        LOG_DEBUG("spi_transmit: len=%d\n  ", len);
        for (unsigned int i = 0; i < len; i++) {
            if (i > 0 && i % 8 == 0) { LOG_DEBUG("\n  "); }
            LOG_DEBUG("%.2X ", msb_buf[i]);
        }
        LOG_DEBUG("\n");
    }
#endif  //  LOG_SPI
    //  Transmit the MSB buffer to SPI device.
	struct spi_ioc_transfer tr = {
		.tx_buf = (unsigned long) msb_buf,
		.rx_buf = (unsigned long) NULL,
		.len = len,
		.delay_usecs = delay,
		.speed_hz = speed_khz * 1000,
		.bits_per_word = bits,
	};
	int ret = ioctl(fd, SPI_IOC_MESSAGE(1), &tr);
    //  Check SPI result.
	if (ret < 1) { perror("spi_transmit failed"); }
}

/// Receive len bytes from SPI device (assumed to be in MSB format) and write into buf in LSB format
static void spi_receive(int fd, uint8_t *buf, unsigned int len) {
    //  Receive the MSB buffer from SPI device.
#ifdef LOG_SPI
    LOG_DEBUG("spi_receive: len=%d\n  ", len);
#endif  //  LOG_SPI
    if (len >= MAX_SPI_SIZE) { LOG_DEBUG("len=%d ", len); perror("spi_receive overflow"); return; }
	struct spi_ioc_transfer tr = {
		.tx_buf = (unsigned long) NULL,
		.rx_buf = (unsigned long) msb_buf,
		.len = len,
		.delay_usecs = delay,
		.speed_hz = speed_khz * 1000,
		.bits_per_word = bits,
	};
	int ret = ioctl(fd, SPI_IOC_MESSAGE(1), &tr);
    //  Check SPI result.
	if (ret < 1) { perror("spi_receive failed"); }
    //  Reverse MSB to LSB from MSB buffer into LSB buf.
    for (unsigned int i = 0; i < len; i++) {
        uint8_t b = msb_buf[i];
        buf[i] = reverse_byte[(uint8_t) b];
    }
#ifdef LOG_SPI
    {
        for (unsigned int i = 0; i < len; i++) {
            if (i > 0 && i % 8 == 0) { LOG_DEBUG("\n  "); }
            LOG_DEBUG("%.2X ", buf[i]);
        }
        puts("");
    }
#endif  //  LOG_SPI
}

/// Push the bit to the lsb_buf
static void push_lsb_buf(int next_bit) {
    unsigned int byte_cnt = (lsb_buf_bit_index + 7) / 8;  //  Round up to next byte count.
    if (byte_cnt >= MAX_SPI_SIZE) { perror("push_lsb_buf: overflow"); return; }

    int bytec = lsb_buf_bit_index / 8;
    int bcval = 1 << (lsb_buf_bit_index % 8);
    if (next_bit) {
        lsb_buf[bytec] |= bcval;
    } else {
        lsb_buf[bytec] &= ~bcval;
    }
    lsb_buf_bit_index++;
}

/// Pop the next bit from the lsb_buf
static int pop_lsb_buf(void) {
    unsigned int byte_cnt = (lsb_buf_bit_index + 7) / 8;  //  Round up to next byte count.
    if (byte_cnt >= MAX_SPI_SIZE) { perror("pop_lsb_buf: overflow"); return -1; }

    int bytec = lsb_buf_bit_index / 8;
    int bcval = 1 << (lsb_buf_bit_index % 8);
    int next_bit = lsb_buf[bytec] & bcval;
    lsb_buf_bit_index++;
    if (next_bit) { return 1; }
    return 0;
}

/// Read one JTAG bit (not used)
static bb_value_t bcm2835spi_read(void)
{
	return 0;
}

/// Write one JTAG bit (not used)
static int bcm2835spi_write(int tck, int tms, int tdi)
{
	return ERROR_OK;
}

/// Set SWDIO direction (not used)
static void bcm2835_swdio_drive(bool is_output)
{
}

/// Read one SWDIO bit (not used)
static int bcm2835_swdio_read(void)
{
	return 0;
}

/// Write one SWD bit (not used)
static int bcm2835spi_swd_write(int swclk, int swdio)
{
	return ERROR_OK;
}

/// (1) assert or (0) deassert reset lines (not used)
static int bcm2835spi_reset(int trst, int srst)
{
	return ERROR_OK;
}

/// Set JTAG speed (not used)
static int bcm2835spi_khz(int khz, int *jtag_speed)
{
	//  TODO
	if (!khz) {
		LOG_DEBUG("RCLK not supported");
		return ERROR_FAIL;
	}
	*jtag_speed = 0;
	return ERROR_OK;
}

/// Set speed div
static int bcm2835spi_speed_div(int speed, int *khz)
{
	*khz = speed_khz;
	return ERROR_OK;
}

/// Set JTAG delay (not used)
static int bcm2835spi_speed(int speed)
{
	return ERROR_OK;
}

/// Parse the SPI speed
COMMAND_HANDLER(bcm2835spi_handle_speed)
{
	if (CMD_ARGC == 1) {
		COMMAND_PARSE_NUMBER(uint, CMD_ARGV[0], speed_khz);
	}

	command_print(CMD, "BCM2835 SPI: speed = %d kHz", speed_khz);
	return ERROR_OK;
}

/// Is SWD transport supported
static bool bcm2835spi_swd_mode_possible(void)
{
	return 1;
}

/// Init driver
static int bcm2835spi_init(void)
{
	bitbang_interface = &bcm2835spi_bitbang;

	LOG_INFO("BCM2835 SPI SWD driver");

	if (bcm2835spi_swd_mode_possible()) {
		LOG_INFO("SWD only mode enabled");
	} else {
		LOG_ERROR("Mode not supported");
		return ERROR_JTAG_INIT_FAILED;
	}

    if (spi_fd >= 0) { return ERROR_OK; }  //  Init only once

    //  Open SPI device.
	spi_fd = open(device, O_RDWR);
	if (spi_fd < 0) { perror("can't open device"); }

    //  Set SPI mode to read and write.
	int ret = ioctl(spi_fd, SPI_IOC_WR_MODE, &mode);
	if (ret == -1) { perror("can't set spi write mode"); }
	ret = ioctl(spi_fd, SPI_IOC_RD_MODE, &mode);
	if (ret == -1) { perror("can't set spi read mode"); }

    //  Set SPI read and write bits per word.
	ret = ioctl(spi_fd, SPI_IOC_WR_BITS_PER_WORD, &bits);
	if (ret == -1) { perror("can't set write bits per word"); }
	ret = ioctl(spi_fd, SPI_IOC_RD_BITS_PER_WORD, &bits);
	if (ret == -1) { perror("can't set read bits per word"); }

    //  Set SPI read and write max speed.
    uint32_t speed = speed_khz * 1000;
	ret = ioctl(spi_fd, SPI_IOC_WR_MAX_SPEED_HZ, &speed);
	if (ret == -1) { perror("can't set max write speed"); }
	ret = ioctl(spi_fd, SPI_IOC_RD_MAX_SPEED_HZ, &speed);
	if (ret == -1) { perror("can't set max read speed"); }

	return ERROR_OK;
}

/// Terminate driver
static int bcm2835spi_quit(void)
{
    //  Close SPI device.
    if (spi_fd < 0) { return ERROR_OK; }  //  Terminate only once
    close(spi_fd);
	spi_fd = -1;
	return ERROR_OK;
}
