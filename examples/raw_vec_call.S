.section .text.call_raw_vec_u32_insert, "ax"
.balign 4
.global call_raw_vec_u32_insert
.type call_raw_vec_u32_insert, @function

.option push
.option norvc
.option norelax

# The pinned Sail configuration disables compressed instructions.
# Give the verified routine a word-aligned return address even when
# the Rust demo caller uses halfword-aligned compressed instructions.
call_raw_vec_u32_insert:
    addi sp, sp, -16        # Reserve an ABI-aligned stack frame.
    sw ra, 12(sp)          # Preserve the Rust caller's return address.
    call raw_vec_u32_insert # Forward a0–a2 and set a word-aligned return address.
    lw ra, 12(sp)          # Restore the Rust caller's return address.
    addi sp, sp, 16        # Release the stack frame, keeping the status in a0.
    ret                   # Return to the Rust demo.

.size call_raw_vec_u32_insert, . - call_raw_vec_u32_insert
.option pop
