//! A minimal machine-mode runtime for QEMU's `virt` board: the reset entry,
//! a trap report, UART output, and exit through the SiFive test device.
//! No interrupts are enabled.

use core::{
    arch::global_asm,
    fmt::{self, Arguments, Write},
    hint::spin_loop,
    panic::PanicInfo,
    ptr,
};

// The NS16550A UART on QEMU's `virt` board.
const UART_BASE: usize = 0x1000_0000;
// QEMU's SiFive test device. A write to it ends the emulation.
const TEST_BASE: usize = 0x10_0000;

global_asm!(
    r#"
.section .text.start, "ax"
.global _start
.option push
.option norelax

_start:
    la sp, _stack_top           # Start the stack at the end of RAM.
    la t0, trap_entry           # Load the address of the trap entry.
    csrw mtvec, t0              # Send every exception there, in direct mode.
    call start_rust             # Run the harness. It never returns.

.balign 4
trap_entry:
    la sp, _stack_top           # Use a fresh stack in case sp caused the trap.
    csrr a0, mcause             # Pass the trap cause as the first argument.
    csrr a1, mepc               # Pass the trapping PC as the second argument.
    csrr a2, mtval              # Pass the trap value as the third argument.
    j trap                      # Report the trap and exit. It never returns.

.option pop
"#
);

/// Print one line on the UART.
pub fn println(arguments: Arguments<'_>) {
    Uart.write_fmt(format_args!("{arguments}\n"))
        .expect("the UART writer never fails");
}

#[unsafe(no_mangle)]
extern "C" fn start_rust() -> ! {
    crate::main();
    exit(Exit::Pass)
}

#[unsafe(no_mangle)]
extern "C" fn trap(cause: u32, pc: u32, value: u32) -> ! {
    println(format_args!(
        "FAIL: trap mcause=0x{cause:08x} mepc=0x{pc:08x} mtval=0x{value:08x}"
    ));
    exit(Exit::Trap)
}

#[panic_handler]
fn panic(info: &PanicInfo<'_>) -> ! {
    println(format_args!("FAIL: {info}"));
    exit(Exit::Panic)
}

struct Uart;

impl Write for Uart {
    fn write_str(&mut self, text: &str) -> fmt::Result {
        const LINE_STATUS: usize = UART_BASE + 5;
        const TRANSMIT_EMPTY: u8 = 1 << 5;
        for byte in text.bytes() {
            // SAFETY: QEMU's `virt` board maps the UART's byte registers at
            // UART_BASE. Reading the line status and writing the transmit
            // register have no effect on Rust-visible memory.
            unsafe {
                while ptr::read_volatile(LINE_STATUS as *const u8) & TRANSMIT_EMPTY == 0 {
                    spin_loop();
                }
                ptr::write_volatile(UART_BASE as *mut u8, byte);
            }
        }
        Ok(())
    }
}

/// How the run ends. QEMU exits with 0, 1, or 2 respectively.
enum Exit {
    Pass,
    Panic,
    Trap,
}

fn exit(exit: Exit) -> ! {
    const PASS: u32 = 0x5555;
    const FAIL: u32 = 0x3333;
    let command = match exit {
        Exit::Pass => PASS,
        Exit::Panic => 1 << 16 | FAIL,
        Exit::Trap => 2 << 16 | FAIL,
    };
    // SAFETY: QEMU's `virt` board maps the SiFive test device at TEST_BASE.
    // This write ends the emulation with the encoded status.
    unsafe { ptr::write_volatile(TEST_BASE as *mut u32, command) };
    loop {
        spin_loop();
    }
}
