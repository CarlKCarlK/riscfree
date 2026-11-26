.section .text.popcount128, "ax"
.balign 4
.global popcount128
.type popcount128, @function

.option push
.option norvc
.option norelax

# a0 points to 16 readable bytes aligned to 4 bytes. ra holds the return address.
# Return the count in a0. Only a0 and t0-t4 are modified.
popcount128:
    li t0, 4                      # Count the four 32-bit words.
    li t1, 0                      # Start the total at zero.
.Lword:
    lw t2, 0(a0)                  # Read the next word.
    li t3, 32                     # Examine all 32 bits in this word.
.Lbit:
    andi t4, t2, 1                # Extract the low bit.
    add t1, t1, t4                # Add that bit to the total.
    srli t2, t2, 1                # Shift the next bit into the low position.
    addi t3, t3, -1               # Count one fewer bit to examine.
    bnez t3, .Lbit                # Repeat until all 32 bits are counted.

    addi a0, a0, 4                # Advance to the next word.
    addi t0, t0, -1               # Count one fewer word to read.
    bnez t0, .Lword               # Repeat until all four words are counted.

    mv a0, t1                     # Return the total (0 through 128).
    ret                           # Jump back to the address in ra.

.size popcount128, . - popcount128
.option pop
