# Give the uncompressed range insertion routine a word-aligned return address.
.section .text.call_range_insert_u32, "ax"
.balign 4
.global call_range_insert_u32
.type call_range_insert_u32, @function

.option push
.option norvc
.option norelax

call_range_insert_u32:
    addi sp, sp, -16       # Reserve an ABI-aligned stack frame.
    sw ra, 12(sp)          # Save the ESP32-C3 caller's return address.
    call range_insert_u32  # Forward a0–a5 and set a word-aligned return address.
    lw ra, 12(sp)          # Restore the ESP32-C3 caller's return address.
    addi sp, sp, 16        # Release the frame.
    ret                    # Return to the caller.

.size call_range_insert_u32, . - call_range_insert_u32
.option pop
