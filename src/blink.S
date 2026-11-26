.section .text.riscfree_start, "ax"
.balign 4
.global riscfree_start
.type riscfree_start, @function

.option push
.option norvc
.option norelax

# ESP32-C3 Technical Reference Manual, IO MUX and GPIO Matrix chapter.
.equ GPIO_BASE,             0x60004000
.equ IO_MUX_GPIO12,         0x60009034
.equ GPIO_OUT_W1TS,         0x08
.equ GPIO_OUT_W1TC,         0x0c
.equ GPIO_ENABLE_W1TS,      0x24
.equ GPIO_PIN12,            0xa4
.equ GPIO_FUNC12_OUT_SEL,   0x584
.equ GPIO_MATRIX_GPIO,     128
.equ GPIO12_MASK,           1 << 12
.equ DELAY,                 5000000

# ESP32-C3 RTC watchdog registers and write-protection keys.
.equ RTC_CNTL_BASE,         0x60008000
.equ RTC_WDT_CONFIG0,       0x90
.equ RTC_WDT_WPROTECT,      0xa8
.equ RTC_SWD_CONF,          0xac
.equ RTC_SWD_WPROTECT,      0xb0
.equ RTC_WDT_KEY,           0x50d83aa1
.equ RTC_SWD_KEY,           0x8f1d312a
.equ RTC_SWD_AUTO_FEED,     0x80000000

riscfree_start:
    # Clear mstatus.MIE to disable machine interrupts.
    csrci mstatus, 8

    # The standalone app has no ESP-IDF startup to stop the boot watchdog.
    li t0, RTC_CNTL_BASE               # Address the RTC control registers.
    li t1, RTC_WDT_KEY                 # Load the RTC watchdog unlock key.
    sw t1, RTC_WDT_WPROTECT(t0)        # Unlock the RTC watchdog registers.
    lw t1, RTC_WDT_CONFIG0(t0)         # Read the current watchdog configuration.
    li t2, 0x7fffffff                  # Mask off only the RTC watchdog enable bit.
    and t1, t1, t2                     # Clear the enable bit.
    sw t1, RTC_WDT_CONFIG0(t0)         # Stop the RTC watchdog.
    sw zero, RTC_WDT_WPROTECT(t0)      # Restore RTC watchdog write protection.

    li t1, RTC_SWD_KEY                 # Load the super watchdog unlock key.
    sw t1, RTC_SWD_WPROTECT(t0)        # Unlock the super watchdog registers.
    li t1, RTC_SWD_AUTO_FEED           # Select automatic super watchdog feeding.
    sw t1, RTC_SWD_CONF(t0)            # Apply the same setting as esp_hal::init().
    sw zero, RTC_SWD_WPROTECT(t0)      # Restore super watchdog write protection.

    li t0, GPIO_BASE                  # Address the GPIO registers.
    li t1, GPIO12_MASK                # Select only GPIO12 for set/clear writes.

    li t2, IO_MUX_GPIO12              # Address the GPIO12 IO MUX register.
    li t3, 0x1800                     # Select GPIO function 1 and drive strength 2.
    sw t3, 0(t2)                      # Apply the pad configuration.

    li t3, GPIO_MATRIX_GPIO          # Signal 128 selects GPIO_OUT and GPIO_ENABLE.
    sw t3, GPIO_FUNC12_OUT_SEL(t0)    # Route both signals without inversion.
    sw zero, GPIO_PIN12(t0)           # Clear open-drain and pin interrupts.
    sw t1, GPIO_OUT_W1TC(t0)           # Set the output latch low before enabling it.
    sw t1, GPIO_ENABLE_W1TS(t0)        # Enable GPIO12 output.

    li t2, DELAY                      # Hold each LED state for this many iterations.

.Lblink:
    sw t1, GPIO_OUT_W1TS(t0)           # Drive GPIO12 high to turn D4 on.
    mv t3, t2                         # Reload the on-time counter.
.Ldelay_on:
    addi t3, t3, -1                   # Count down one iteration.
    bne t3, zero, .Ldelay_on          # Keep waiting until the counter is zero.

    sw t1, GPIO_OUT_W1TC(t0)           # Drive GPIO12 low to turn D4 off.
    mv t3, t2                         # Reload the off-time counter.
.Ldelay_off:
    addi t3, t3, -1                   # Count down one iteration.
    bne t3, zero, .Ldelay_off         # Keep waiting until the counter is zero.

    j .Lblink                         # Repeat forever.

.size riscfree_start, . - riscfree_start
.option pop
