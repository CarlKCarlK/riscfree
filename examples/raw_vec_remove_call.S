# Calling shims for the RawVec removal routines. They are assembled into their
# own object and linked after the routines (see `build.rs`), so they do not move
# the verified insertion shim in `raw_vec_call.S` or its `call` offset.
# These shims are not proved; only `call_raw_vec_u32_insert` has a proof
# (proof/RawVec/Shim.lean).

.section .text.call_raw_vec_u32_remove, "ax"
.balign 4
.global call_raw_vec_u32_remove
.type call_raw_vec_u32_remove, @function

.option push
.option norvc
.option norelax

# The pinned Sail configuration disables compressed instructions.
# Give the verified routine a word-aligned return address even when
# the Rust demo caller uses halfword-aligned compressed instructions.
call_raw_vec_u32_remove:
    addi sp, sp, -16        # Reserve an ABI-aligned stack frame.
    sw ra, 12(sp)          # Preserve the Rust caller's return address.
    call raw_vec_u32_remove # Forward a0–a1 and set a word-aligned return address.
    lw ra, 12(sp)          # Restore the Rust caller's return address.
    addi sp, sp, 16        # Release the stack frame, keeping the status in a0.
    ret                   # Return to the Rust demo.

.size call_raw_vec_u32_remove, . - call_raw_vec_u32_remove
.option pop

.section .text.call_raw_vec_pair_remove, "ax"
.balign 4
.global call_raw_vec_pair_remove
.type call_raw_vec_pair_remove, @function

.option push
.option norvc
.option norelax

# The same shim for the pair routine.
call_raw_vec_pair_remove:
    addi sp, sp, -16         # Reserve an ABI-aligned stack frame.
    sw ra, 12(sp)           # Preserve the Rust caller's return address.
    call raw_vec_pair_remove # Forward a0–a1 and set a word-aligned return address.
    lw ra, 12(sp)           # Restore the Rust caller's return address.
    addi sp, sp, 16         # Release the stack frame, keeping the status in a0.
    ret                    # Return to the Rust demo.

.size call_raw_vec_pair_remove, . - call_raw_vec_pair_remove
.option pop
