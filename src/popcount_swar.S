.section .text.popcount128_swar, "ax"
.balign 4
.global popcount128_swar
.type popcount128_swar, @function

.option push
.option norvc
.option norelax

# a0 points to four aligned words. Return their population count in a0.
popcount128_swar:
    li      a1, 0           # Clear the total.
    lui     a2, 349525      # Load the upper bits of 0x55555555.
    addi    a6, a0, 16      # Save the end of the input.
    lui     a4, 209715      # Load the upper bits of 0x33333333.
    addi    a7, a2, 1365    # Complete the alternating-bit mask.
    addi    a4, a4, 819     # Complete the two-bit lane mask.
    lui     a5, 61681       # Load the rounded upper bits of 0x0f0f0f0f.
    lui     a2, 4112        # Load the upper bits of 0x01010101.
    addi    t0, a5, -241    # Complete the low-nibble mask.
    addi    a2, a2, 257     # Complete the byte reduction multiplier.
.Lswar_word:
    lw      a5, 0(a0)       # Read the next word.
    addi    a0, a0, 4       # Advance the input pointer.
    srli    a3, a5, 1       # Align each high bit with its pair.
    and     a3, a3, a7      # Isolate high bits of the pairs.
    sub     a5, a5, a3      # Count each pair of bits.
    srli    a3, a5, 2       # Align adjacent two-bit counts.
    and     a5, a5, a4      # Keep the lower pair of each nibble.
    and     a3, a3, a4      # Keep the higher pair of each nibble.
    add     a3, a3, a5      # Count each nibble.
    srli    a5, a3, 4       # Align adjacent nibble counts.
    add     a3, a3, a5      # Sum the two nibble counts in each byte.
    and     a3, a3, t0      # Keep the per-byte counts.
    mul     a3, a3, a2      # Sum the byte counts into the highest byte.
    srli    a3, a3, 24      # Extract the word's population count.
    add     a1, a1, a3      # Add it to the total.
    bne     a0, a6, .Lswar_word  # Repeat until all four words are counted.
    zext.b  a0, a1          # Return the unsigned byte.
    ret                     # Return to the caller.

.size popcount128_swar, . - popcount128_swar
.option pop
