.section .text.stop_boot_watchdogs, "ax"
.balign 4
.global stop_boot_watchdogs
.type stop_boot_watchdogs, @function

# ESP32-C3 RTC watchdog registers and write-protection keys.
.equ RTC_CNTL_BASE,         0x60008000
.equ RTC_WDT_CONFIG0,       0x90
.equ RTC_WDT_WPROTECT,      0xa8
.equ RTC_SWD_CONF,          0xac
.equ RTC_SWD_WPROTECT,      0xb0
.equ RTC_WDT_KEY,           0x50d83aa1
.equ RTC_SWD_KEY,           0x8f1d312a
.equ RTC_SWD_AUTO_FEED,     0x80000000

stop_boot_watchdogs:
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
    ret                               # Return to the Rust harness.

.size stop_boot_watchdogs, . - stop_boot_watchdogs
