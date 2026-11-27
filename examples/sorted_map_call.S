# Calling shims for the sorted-map routines. They are assembled into their own
# object and linked after the sorted-map routines (see `build.rs`), so they move
# none of the verified routines. Like the removal shims, they are copies of the
# verified insertion shim in `raw_vec_call.S` and are not proved themselves.
# Each gives its routine a word-aligned return address even when the Rust demo
# caller uses halfword-aligned compressed instructions.

.section .text.call_sorted_map_lower_bound, "ax"
.balign 4
.global call_sorted_map_lower_bound
.type call_sorted_map_lower_bound, @function

.option push
.option norvc
.option norelax

call_sorted_map_lower_bound:
    addi sp, sp, -16      # Reserve an ABI-aligned stack frame.
    sw ra, 12(sp)         # Preserve the Rust caller's return address.
    call sorted_map_lower_bound  # Forward a0–a1 and set a word-aligned return address.
    lw ra, 12(sp)         # Restore the Rust caller's return address.
    addi sp, sp, 16       # Release the stack frame, keeping the result in a0.
    ret                   # Return to the Rust demo.

.size call_sorted_map_lower_bound, . - call_sorted_map_lower_bound
.option pop

.section .text.call_sorted_map_upper_bound, "ax"
.balign 4
.global call_sorted_map_upper_bound
.type call_sorted_map_upper_bound, @function

.option push
.option norvc
.option norelax

call_sorted_map_upper_bound:
    addi sp, sp, -16      # Reserve an ABI-aligned stack frame.
    sw ra, 12(sp)         # Preserve the Rust caller's return address.
    call sorted_map_upper_bound  # Forward a0–a1 and set a word-aligned return address.
    lw ra, 12(sp)         # Restore the Rust caller's return address.
    addi sp, sp, 16       # Release the stack frame, keeping the result in a0.
    ret                   # Return to the Rust demo.

.size call_sorted_map_upper_bound, . - call_sorted_map_upper_bound
.option pop

.section .text.call_sorted_map_insert, "ax"
.balign 4
.global call_sorted_map_insert
.type call_sorted_map_insert, @function

.option push
.option norvc
.option norelax

call_sorted_map_insert:
    addi sp, sp, -16      # Reserve an ABI-aligned stack frame.
    sw ra, 12(sp)         # Preserve the Rust caller's return address.
    call sorted_map_insert  # Forward a0–a2 and set a word-aligned return address.
    lw ra, 12(sp)         # Restore the Rust caller's return address.
    addi sp, sp, 16       # Release the stack frame, keeping the result in a0.
    ret                   # Return to the Rust demo.

.size call_sorted_map_insert, . - call_sorted_map_insert
.option pop

.section .text.call_sorted_map_remove, "ax"
.balign 4
.global call_sorted_map_remove
.type call_sorted_map_remove, @function

.option push
.option norvc
.option norelax

call_sorted_map_remove:
    addi sp, sp, -16      # Reserve an ABI-aligned stack frame.
    sw ra, 12(sp)         # Preserve the Rust caller's return address.
    call sorted_map_remove  # Forward a0–a1 and set a word-aligned return address.
    lw ra, 12(sp)         # Restore the Rust caller's return address.
    addi sp, sp, 16       # Release the stack frame, keeping the result in a0.
    ret                   # Return to the Rust demo.

.size call_sorted_map_remove, . - call_sorted_map_remove
.option pop
