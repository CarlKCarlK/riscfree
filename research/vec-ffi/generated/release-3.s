	.attribute	4, 16
	.attribute	5, "rv32i2p1_m2p0_zmmul1p0"
	.file	"vec_ffi_research.ac3268d5878012a4-cgu.0"
	.section	.text.custom_pair_insert,"ax",@progbits
	.globl	custom_pair_insert
	.p2align	2
	.type	custom_pair_insert,@function
custom_pair_insert:
	lw	a4, 4(a0)
	lw	a5, 8(a0)
	bgeu	a5, a4, .LBB0_2
	li	a0, 3
	ret
.LBB0_2:
	bgeu	a4, a1, .LBB0_4
	li	a0, 2
	ret
.LBB0_4:
	bne	a4, a5, .LBB0_6
	li	a0, 1
	ret
.LBB0_6:
	addi	sp, sp, -32
	sw	ra, 28(sp)
	sw	s0, 24(sp)
	sw	s1, 20(sp)
	sw	s2, 16(sp)
	sw	s3, 12(sp)
	lw	s0, 0(a0)
	slli	a5, a1, 3
	sub	a4, a4, a1
	add	s0, s0, a5
	addi	a1, s0, 8
	slli	a4, a4, 3
	mv	s1, a0
	mv	a0, a1
	mv	a1, s0
	mv	s2, a2
	mv	a2, a4
	mv	s3, a3
	call	memmove
	li	a0, 0
	sw	s2, 0(s0)
	sw	s3, 4(s0)
	lw	a1, 4(s1)
	addi	a1, a1, 1
	sw	a1, 4(s1)
	lw	ra, 28(sp)
	lw	s0, 24(sp)
	lw	s1, 20(sp)
	lw	s2, 16(sp)
	lw	s3, 12(sp)
	addi	sp, sp, 32
	ret
.Lfunc_end0:
	.size	custom_pair_insert, .Lfunc_end0-custom_pair_insert

	.section	.text.custom_pair_insert_loop,"ax",@progbits
	.globl	custom_pair_insert_loop
	.p2align	2
	.type	custom_pair_insert_loop,@function
custom_pair_insert_loop:
	lw	a4, 4(a0)
	lw	a5, 8(a0)
	bgeu	a5, a4, .LBB1_2
	li	a0, 3
	ret
.LBB1_2:
	bgeu	a4, a1, .LBB1_4
	li	a0, 2
	ret
.LBB1_4:
	bne	a4, a5, .LBB1_6
	li	a0, 1
	ret
.LBB1_6:
	bgeu	a1, a4, .LBB1_9
	slli	a5, a4, 3
.LBB1_8:
	lw	a6, 0(a0)
	add	a6, a6, a5
	lw	a7, -8(a6)
	lw	t0, -4(a6)
	addi	a4, a4, -1
	sw	a7, 0(a6)
	sw	t0, 4(a6)
	addi	a5, a5, -8
	bltu	a1, a4, .LBB1_8
.LBB1_9:
	lw	a5, 0(a0)
	slli	a1, a1, 3
	add	a1, a5, a1
	sw	a2, 0(a1)
	sw	a3, 4(a1)
	lw	a1, 4(a0)
	addi	a1, a1, 1
	sw	a1, 4(a0)
	li	a0, 0
	ret
.Lfunc_end1:
	.size	custom_pair_insert_loop, .Lfunc_end1-custom_pair_insert_loop

	.section	.text.custom_pair_push,"ax",@progbits
	.globl	custom_pair_push
	.p2align	2
	.type	custom_pair_push,@function
custom_pair_push:
	lw	a3, 4(a0)
	lw	a4, 8(a0)
	bgeu	a4, a3, .LBB2_2
	li	a0, 3
	ret
.LBB2_2:
	bne	a3, a4, .LBB2_4
	li	a0, 1
	ret
.LBB2_4:
	mv	a4, a0
	li	a0, 0
	lw	a5, 0(a4)
	slli	a3, a3, 3
	add	a3, a5, a3
	sw	a1, 0(a3)
	sw	a2, 4(a3)
	lw	a1, 4(a4)
	addi	a1, a1, 1
	sw	a1, 4(a4)
	ret
.Lfunc_end2:
	.size	custom_pair_push, .Lfunc_end2-custom_pair_push

	.section	.text.custom_u32_insert,"ax",@progbits
	.globl	custom_u32_insert
	.p2align	2
	.type	custom_u32_insert,@function
custom_u32_insert:
	lw	a3, 4(a0)
	lw	a4, 8(a0)
	bgeu	a4, a3, .LBB3_2
	li	a0, 3
	ret
.LBB3_2:
	bgeu	a3, a1, .LBB3_4
	li	a0, 2
	ret
.LBB3_4:
	bne	a3, a4, .LBB3_6
	li	a0, 1
	ret
.LBB3_6:
	addi	sp, sp, -16
	sw	ra, 12(sp)
	sw	s0, 8(sp)
	sw	s1, 4(sp)
	sw	s2, 0(sp)
	lw	s0, 0(a0)
	slli	a4, a1, 2
	sub	a3, a3, a1
	add	s0, s0, a4
	addi	a1, s0, 4
	slli	a3, a3, 2
	mv	s1, a0
	mv	a0, a1
	mv	a1, s0
	mv	s2, a2
	mv	a2, a3
	call	memmove
	li	a0, 0
	sw	s2, 0(s0)
	lw	a1, 4(s1)
	addi	a1, a1, 1
	sw	a1, 4(s1)
	lw	ra, 12(sp)
	lw	s0, 8(sp)
	lw	s1, 4(sp)
	lw	s2, 0(sp)
	addi	sp, sp, 16
	ret
.Lfunc_end3:
	.size	custom_u32_insert, .Lfunc_end3-custom_u32_insert

	.section	.text.custom_u32_insert_loop,"ax",@progbits
	.globl	custom_u32_insert_loop
	.p2align	2
	.type	custom_u32_insert_loop,@function
custom_u32_insert_loop:
	lw	a3, 4(a0)
	lw	a4, 8(a0)
	bgeu	a4, a3, .LBB4_2
	li	a0, 3
	ret
.LBB4_2:
	bgeu	a3, a1, .LBB4_4
	li	a0, 2
	ret
.LBB4_4:
	bne	a3, a4, .LBB4_6
	li	a0, 1
	ret
.LBB4_6:
	bgeu	a1, a3, .LBB4_9
	slli	a4, a3, 2
.LBB4_8:
	lw	a5, 0(a0)
	add	a5, a5, a4
	lw	a6, -4(a5)
	addi	a3, a3, -1
	sw	a6, 0(a5)
	addi	a4, a4, -4
	bltu	a1, a3, .LBB4_8
.LBB4_9:
	lw	a4, 0(a0)
	slli	a1, a1, 2
	add	a1, a4, a1
	sw	a2, 0(a1)
	lw	a1, 4(a0)
	addi	a1, a1, 1
	sw	a1, 4(a0)
	li	a0, 0
	ret
.Lfunc_end4:
	.size	custom_u32_insert_loop, .Lfunc_end4-custom_u32_insert_loop

	.section	.text.custom_u32_push,"ax",@progbits
	.globl	custom_u32_push
	.p2align	2
	.type	custom_u32_push,@function
custom_u32_push:
	lw	a2, 4(a0)
	lw	a3, 8(a0)
	bgeu	a3, a2, .LBB5_2
	li	a0, 3
	ret
.LBB5_2:
	bne	a2, a3, .LBB5_4
	li	a0, 1
	ret
.LBB5_4:
	mv	a3, a0
	li	a0, 0
	lw	a4, 0(a3)
	slli	a2, a2, 2
	add	a2, a4, a2
	sw	a1, 0(a2)
	lw	a1, 4(a3)
	addi	a1, a1, 1
	sw	a1, 4(a3)
	ret
.Lfunc_end5:
	.size	custom_u32_push, .Lfunc_end5-custom_u32_push

	.section	.text.heapless_pair_align,"ax",@progbits
	.globl	heapless_pair_align
	.p2align	2
	.type	heapless_pair_align,@function
heapless_pair_align:
	li	a0, 4
	ret
.Lfunc_end6:
	.size	heapless_pair_align, .Lfunc_end6-heapless_pair_align

	.section	.text.heapless_pair_init,"ax",@progbits
	.globl	heapless_pair_init
	.p2align	2
	.type	heapless_pair_init,@function
heapless_pair_init:
	sw	zero, 0(a0)
	ret
.Lfunc_end7:
	.size	heapless_pair_init, .Lfunc_end7-heapless_pair_init

	.section	.text.heapless_pair_insert,"ax",@progbits
	.globl	heapless_pair_insert
	.p2align	2
	.type	heapless_pair_insert,@function
heapless_pair_insert:
	addi	sp, sp, -32
	sw	ra, 28(sp)
	sw	s0, 24(sp)
	sw	s1, 20(sp)
	sw	s2, 16(sp)
	sw	s3, 12(sp)
	sw	s4, 8(sp)
	lw	s1, 0(a0)
	bgeu	s1, a1, .LBB8_2
	li	a0, 2
	j	.LBB8_5
.LBB8_2:
	li	a4, 16
	bne	s1, a4, .LBB8_4
	li	a0, 1
	j	.LBB8_5
.LBB8_4:
	addi	s0, a0, 4
	slli	a4, a1, 3
	add	s0, s0, a4
	sub	a4, s1, a1
	addi	a1, s0, 8
	slli	a4, a4, 3
	mv	s2, a0
	mv	a0, a1
	mv	a1, s0
	mv	s3, a2
	mv	a2, a4
	mv	s4, a3
	call	memmove
	li	a0, 0
	addi	s1, s1, 1
	sw	s1, 0(s2)
	sw	s3, 0(s0)
	sw	s4, 4(s0)
.LBB8_5:
	lw	ra, 28(sp)
	lw	s0, 24(sp)
	lw	s1, 20(sp)
	lw	s2, 16(sp)
	lw	s3, 12(sp)
	lw	s4, 8(sp)
	addi	sp, sp, 32
	ret
.Lfunc_end8:
	.size	heapless_pair_insert, .Lfunc_end8-heapless_pair_insert

	.section	.text.heapless_pair_push,"ax",@progbits
	.globl	heapless_pair_push
	.p2align	2
	.type	heapless_pair_push,@function
heapless_pair_push:
	mv	a3, a0
	lw	a4, 0(a0)
	li	a0, 15
	bltu	a0, a4, .LBB9_2
	li	a0, 0
	slli	a5, a4, 3
	addi	a4, a4, 1
	add	a5, a3, a5
	sw	a4, 0(a3)
	sw	a1, 4(a5)
	sw	a2, 8(a5)
	ret
.LBB9_2:
	li	a0, 1
	ret
.Lfunc_end9:
	.size	heapless_pair_push, .Lfunc_end9-heapless_pair_push

	.section	.text.heapless_pair_size,"ax",@progbits
	.globl	heapless_pair_size
	.p2align	2
	.type	heapless_pair_size,@function
heapless_pair_size:
	li	a0, 132
	ret
.Lfunc_end10:
	.size	heapless_pair_size, .Lfunc_end10-heapless_pair_size

	.section	.text.heapless_u32_insert,"ax",@progbits
	.globl	heapless_u32_insert
	.p2align	2
	.type	heapless_u32_insert,@function
heapless_u32_insert:
	addi	sp, sp, -32
	sw	ra, 28(sp)
	sw	s0, 24(sp)
	sw	s1, 20(sp)
	sw	s2, 16(sp)
	sw	s3, 12(sp)
	lw	s1, 0(a0)
	bgeu	s1, a1, .LBB11_2
	li	a0, 2
	j	.LBB11_5
.LBB11_2:
	li	a3, 16
	bne	s1, a3, .LBB11_4
	li	a0, 1
	j	.LBB11_5
.LBB11_4:
	addi	s0, a0, 4
	slli	a3, a1, 2
	add	s0, s0, a3
	sub	a3, s1, a1
	addi	a1, s0, 4
	slli	a3, a3, 2
	mv	s2, a0
	mv	a0, a1
	mv	a1, s0
	mv	s3, a2
	mv	a2, a3
	call	memmove
	li	a0, 0
	addi	s1, s1, 1
	sw	s1, 0(s2)
	sw	s3, 0(s0)
.LBB11_5:
	lw	ra, 28(sp)
	lw	s0, 24(sp)
	lw	s1, 20(sp)
	lw	s2, 16(sp)
	lw	s3, 12(sp)
	addi	sp, sp, 32
	ret
.Lfunc_end11:
	.size	heapless_u32_insert, .Lfunc_end11-heapless_u32_insert

	.section	.text.heapless_u32_push,"ax",@progbits
	.globl	heapless_u32_push
	.p2align	2
	.type	heapless_u32_push,@function
heapless_u32_push:
	mv	a2, a0
	lw	a3, 0(a0)
	li	a0, 15
	bltu	a0, a3, .LBB12_2
	li	a0, 0
	slli	a4, a3, 2
	add	a4, a2, a4
	addi	a3, a3, 1
	sw	a3, 0(a2)
	sw	a1, 4(a4)
	ret
.LBB12_2:
	li	a0, 1
	ret
.Lfunc_end12:
	.size	heapless_u32_push, .Lfunc_end12-heapless_u32_push

	.section	.text.heapless_u32_size,"ax",@progbits
	.globl	heapless_u32_size
	.p2align	2
	.type	heapless_u32_size,@function
heapless_u32_size:
	li	a0, 68
	ret
.Lfunc_end13:
	.size	heapless_u32_size, .Lfunc_end13-heapless_u32_size

	.section	.text.heapless_view_u32_insert_cap16,"ax",@progbits
	.globl	heapless_view_u32_insert_cap16
	.p2align	2
	.type	heapless_view_u32_insert_cap16,@function
heapless_view_u32_insert_cap16:
	addi	sp, sp, -32
	sw	ra, 28(sp)
	sw	s0, 24(sp)
	sw	s1, 20(sp)
	sw	s2, 16(sp)
	sw	s3, 12(sp)
	lw	s1, 0(a0)
	bgeu	s1, a1, .LBB14_2
	li	a0, 2
	j	.LBB14_5
.LBB14_2:
	li	a3, 16
	bne	s1, a3, .LBB14_4
	li	a0, 1
	j	.LBB14_5
.LBB14_4:
	addi	s0, a0, 4
	slli	a3, a1, 2
	add	s0, s0, a3
	sub	a3, s1, a1
	addi	a1, s0, 4
	slli	a3, a3, 2
	mv	s2, a0
	mv	a0, a1
	mv	a1, s0
	mv	s3, a2
	mv	a2, a3
	call	memmove
	li	a0, 0
	addi	s1, s1, 1
	sw	s1, 0(s2)
	sw	s3, 0(s0)
.LBB14_5:
	lw	ra, 28(sp)
	lw	s0, 24(sp)
	lw	s1, 20(sp)
	lw	s2, 16(sp)
	lw	s3, 12(sp)
	addi	sp, sp, 32
	ret
.Lfunc_end14:
	.size	heapless_view_u32_insert_cap16, .Lfunc_end14-heapless_view_u32_insert_cap16

	.section	.text.heapless_view_u32_insert_rust_abi,"ax",@progbits
	.globl	heapless_view_u32_insert_rust_abi
	.p2align	2
	.type	heapless_view_u32_insert_rust_abi,@function
heapless_view_u32_insert_rust_abi:
	addi	sp, sp, -32
	sw	ra, 28(sp)
	sw	s0, 24(sp)
	sw	s1, 20(sp)
	sw	s2, 16(sp)
	sw	s3, 12(sp)
	lw	s1, 0(a0)
	bgeu	s1, a2, .LBB15_2
	li	a0, 2
	j	.LBB15_5
.LBB15_2:
	bne	s1, a1, .LBB15_4
	li	a0, 1
	j	.LBB15_5
.LBB15_4:
	addi	s0, a0, 4
	slli	a1, a2, 2
	add	s0, s0, a1
	sub	a2, s1, a2
	addi	a1, s0, 4
	slli	a2, a2, 2
	mv	s2, a0
	mv	a0, a1
	mv	a1, s0
	mv	s3, a3
	call	memmove
	li	a0, 0
	addi	s1, s1, 1
	sw	s1, 0(s2)
	sw	s3, 0(s0)
.LBB15_5:
	lw	ra, 28(sp)
	lw	s0, 24(sp)
	lw	s1, 20(sp)
	lw	s2, 16(sp)
	lw	s3, 12(sp)
	addi	sp, sp, 32
	ret
.Lfunc_end15:
	.size	heapless_view_u32_insert_rust_abi, .Lfunc_end15-heapless_view_u32_insert_rust_abi

	.globl	heapless_u32_init
	.type	heapless_u32_init,@function
heapless_u32_init = heapless_pair_init
	.globl	heapless_u32_align
	.type	heapless_u32_align,@function
heapless_u32_align = heapless_pair_align
	.ident	"rustc version 1.100.0 (0ef1bc386 2026-11-09)"
	.section	".note.GNU-stack","",@progbits
