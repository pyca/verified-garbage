// The functions of `src/sm4_gcm.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sm4_ctr32:
	.option push
	.option arch, +m, +c
	addi sp, sp, -2032
	addi sp, sp, -1200
	addi t0, sp, 0
	sd s1, 0(t0)
	sd s2, 8(t0)
	sd s3, 16(t0)
	sd s4, 24(t0)
	addi s4, t0, 0
	addi s1, a1, 0
	addi s2, a1, 0
	addi s3, a3, 0
	lbu t0, 0(s2)
	lbu t2, 1(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 32(s4)
	srli t2, t0, 8
	sb t2, 33(s4)
	srli t2, t0, 16
	sb t2, 34(s4)
	srli t2, t0, 24
	sb t2, 35(s4)
	lbu t0, 4(s2)
	lbu t2, 5(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 36(s4)
	srli t2, t0, 8
	sb t2, 37(s4)
	srli t2, t0, 16
	sb t2, 38(s4)
	srli t2, t0, 24
	sb t2, 39(s4)
	lbu t0, 8(s2)
	lbu t2, 9(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 10(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 11(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 40(s4)
	srli t2, t0, 8
	sb t2, 41(s4)
	srli t2, t0, 16
	sb t2, 42(s4)
	srli t2, t0, 24
	sb t2, 43(s4)
	lbu t0, 12(s2)
	lbu t2, 13(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 14(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 15(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 44(s4)
	srli t2, t0, 8
	sb t2, 45(s4)
	srli t2, t0, 16
	sb t2, 46(s4)
	srli t2, t0, 24
	sb t2, 47(s4)
	addi s2, a2, 0
	sd a0, 48(s4)
	addi a5, s4, 56
	addi t0, a5, 2040
	addi t0, t0, 1032
	sd s0, 0(t0)
	sd s1, 8(t0)
	sd s2, 16(t0)
	sd s3, 24(t0)
	sd s4, 32(t0)
	sd s5, 40(t0)
	sd s6, 48(t0)
	sd s7, 56(t0)
	sd s8, 64(t0)
	sd s9, 72(t0)
	sd s10, 80(t0)
	sd s11, 88(t0)
	lui t0, 4080
	addiw t0, t0, 255
	slli t0, t0, 32
	lui t1, 4080
	addiw t1, t1, 255
	add t0, t0, t1
	sd t0, 320(a5)
	lui t0, 1044496
	addiw t0, t0, -255
	slli t0, t0, 32
	lui t1, 1044496
	addiw t1, t1, -256
	add t0, t0, t1
	sd t0, 328(a5)
	lui t0, 16
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 336(a5)
	lui t0, 0
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 344(a5)
	lui t0, 16
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, 1
	add t0, t0, t1
	sd t0, 352(a5)
	lui t0, 0
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 360(a5)
	lui t0, 16
	addiw t0, t0, -256
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, -256
	add t0, t0, t1
	sd t0, 368(a5)
	lui t0, 4080
	addiw t0, t0, 255
	slli t0, t0, 32
	lui t1, 4080
	addiw t1, t1, 255
	add t0, t0, t1
	sd t0, 376(a5)
	lui t0, 349525
	addiw t0, t0, 1365
	slli t0, t0, 32
	lui t1, 349525
	addiw t1, t1, 1365
	add t0, t0, t1
	sd t0, 384(a5)
	lui t0, 209715
	addiw t0, t0, 819
	slli t0, t0, 32
	lui t1, 209715
	addiw t1, t1, 819
	add t0, t0, t1
	sd t0, 392(a5)
	lui t0, 61681
	addiw t0, t0, -241
	slli t0, t0, 32
	lui t1, 61681
	addiw t1, t1, -241
	add t0, t0, t1
	sd t0, 400(a5)
	addi a1, s1, 0
	addi a2, s2, 0
	addi a4, s3, 0
	addi t1, a0, 0
	addi t2, a5, 768
	addi t3, zero, 128
	or t4, t1, t2
	andi t4, t4, 7
	beqz t4, 20f
22:
	lbu t4, 0(t1)
	sb t4, 0(t2)
	addi t1, t1, 1
	addi t2, t2, 1
	addi t3, t3, -1
	bnez t3, 22b
	j 21f
20:
	srli t3, t3, 3
23:
	ld t4, 0(t1)
	sd t4, 0(t2)
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 23b
21:
	addi a0, a5, 768
	addi a3, a5, 1024
	ld t1, 0(a0)
	ld a6, 344(a5)
	and t1, t1, a6
	ld t3, 336(a5)
	srli a7, t1, 48
	slli t0, t1, 16
	xor t0, t0, a7
	xor t1, t1, t0
	and t1, t1, t3
	ld t4, 320(a5)
	and t5, t4, t3
	srli a7, t3, 16
	slli t2, t3, 48
	xor t2, t2, a7
	and t4, t4, t2
	srli a7, t1, 16
	slli t0, t1, 48
	xor t0, t0, a7
	and t0, t0, t4
	srli a7, t1, 40
	slli t1, t1, 24
	xor t1, t1, a7
	and t1, t1, t5
	xor t1, t1, t0
	ld t6, 352(a5)
	and s0, t1, t6
	srli s1, t1, 1
	and s1, s1, t6
	srli s2, t1, 2
	and s2, s2, t6
	srli s3, t1, 3
	and s3, s3, t6
	srli s4, t1, 4
	and s4, s4, t6
	srli s5, t1, 5
	and s5, s5, t6
	srli s6, t1, 6
	and s6, s6, t6
	srli s7, t1, 7
	and s7, s7, t6
	slli t0, s0, 16
	sub s0, t0, s0
	slli t0, s1, 16
	sub s1, t0, s1
	slli t0, s2, 16
	sub s2, t0, s2
	slli t0, s3, 16
	sub s3, t0, s3
	slli t0, s4, 16
	sub s4, t0, s4
	slli t0, s5, 16
	sub s5, t0, s5
	slli t0, s6, 16
	sub s6, t0, s6
	slli t0, s7, 16
	sub s7, t0, s7
	sd s0, 0(a3)
	sd s1, 8(a3)
	sd s2, 16(a3)
	sd s3, 24(a3)
	sd s4, 32(a3)
	sd s5, 40(a3)
	sd s6, 48(a3)
	sd s7, 56(a3)
	addi a3, a3, 64
	ld t1, 0(a0)
	srli t1, t1, 32
	ld t3, 336(a5)
	srli a7, t1, 48
	slli t0, t1, 16
	xor t0, t0, a7
	xor t1, t1, t0
	and t1, t1, t3
	ld t4, 320(a5)
	and t5, t4, t3
	srli a7, t3, 16
	slli t2, t3, 48
	xor t2, t2, a7
	and t4, t4, t2
	srli a7, t1, 16
	slli t0, t1, 48
	xor t0, t0, a7
	and t0, t0, t4
	srli a7, t1, 40
	slli t1, t1, 24
	xor t1, t1, a7
	and t1, t1, t5
	xor t1, t1, t0
	ld t6, 352(a5)
	and s0, t1, t6
	srli s1, t1, 1
	and s1, s1, t6
	srli s2, t1, 2
	and s2, s2, t6
	srli s3, t1, 3
	and s3, s3, t6
	srli s4, t1, 4
	and s4, s4, t6
	srli s5, t1, 5
	and s5, s5, t6
	srli s6, t1, 6
	and s6, s6, t6
	srli s7, t1, 7
	and s7, s7, t6
	slli t0, s0, 16
	sub s0, t0, s0
	slli t0, s1, 16
	sub s1, t0, s1
	slli t0, s2, 16
	sub s2, t0, s2
	slli t0, s3, 16
	sub s3, t0, s3
	slli t0, s4, 16
	sub s4, t0, s4
	slli t0, s5, 16
	sub s5, t0, s5
	slli t0, s6, 16
	sub s6, t0, s6
	slli t0, s7, 16
	sub s7, t0, s7
	sd s0, 0(a3)
	sd s1, 8(a3)
	sd s2, 16(a3)
	sd s3, 24(a3)
	sd s4, 32(a3)
	sd s5, 40(a3)
	sd s6, 48(a3)
	sd s7, 56(a3)
	addi a3, a3, 64
	addi a0, a0, 8
	ld t1, 0(a0)
	ld a6, 344(a5)
	and t1, t1, a6
	ld t3, 336(a5)
	srli a7, t1, 48
	slli t0, t1, 16
	xor t0, t0, a7
	xor t1, t1, t0
	and t1, t1, t3
	ld t4, 320(a5)
	and t5, t4, t3
	srli a7, t3, 16
	slli t2, t3, 48
	xor t2, t2, a7
	and t4, t4, t2
	srli a7, t1, 16
	slli t0, t1, 48
	xor t0, t0, a7
	and t0, t0, t4
	srli a7, t1, 40
	slli t1, t1, 24
	xor t1, t1, a7
	and t1, t1, t5
	xor t1, t1, t0
	ld t6, 352(a5)
	and s0, t1, t6
	srli s1, t1, 1
	and s1, s1, t6
	srli s2, t1, 2
	and s2, s2, t6
	srli s3, t1, 3
	and s3, s3, t6
	srli s4, t1, 4
	and s4, s4, t6
	srli s5, t1, 5
	and s5, s5, t6
	srli s6, t1, 6
	and s6, s6, t6
	srli s7, t1, 7
	and s7, s7, t6
	slli t0, s0, 16
	sub s0, t0, s0
	slli t0, s1, 16
	sub s1, t0, s1
	slli t0, s2, 16
	sub s2, t0, s2
	slli t0, s3, 16
	sub s3, t0, s3
	slli t0, s4, 16
	sub s4, t0, s4
	slli t0, s5, 16
	sub s5, t0, s5
	slli t0, s6, 16
	sub s6, t0, s6
	slli t0, s7, 16
	sub s7, t0, s7
	sd s0, 0(a3)
	sd s1, 8(a3)
	sd s2, 16(a3)
	sd s3, 24(a3)
	sd s4, 32(a3)
	sd s5, 40(a3)
	sd s6, 48(a3)
	sd s7, 56(a3)
	addi a3, a3, 64
	ld t1, 0(a0)
	srli t1, t1, 32
	ld t3, 336(a5)
	srli a7, t1, 48
	slli t0, t1, 16
	xor t0, t0, a7
	xor t1, t1, t0
	and t1, t1, t3
	ld t4, 320(a5)
	and t5, t4, t3
	srli a7, t3, 16
	slli t2, t3, 48
	xor t2, t2, a7
	and t4, t4, t2
	srli a7, t1, 16
	slli t0, t1, 48
	xor t0, t0, a7
	and t0, t0, t4
	srli a7, t1, 40
	slli t1, t1, 24
	xor t1, t1, a7
	and t1, t1, t5
	xor t1, t1, t0
	ld t6, 352(a5)
	and s0, t1, t6
	srli s1, t1, 1
	and s1, s1, t6
	srli s2, t1, 2
	and s2, s2, t6
	srli s3, t1, 3
	and s3, s3, t6
	srli s4, t1, 4
	and s4, s4, t6
	srli s5, t1, 5
	and s5, s5, t6
	srli s6, t1, 6
	and s6, s6, t6
	srli s7, t1, 7
	and s7, s7, t6
	slli t0, s0, 16
	sub s0, t0, s0
	slli t0, s1, 16
	sub s1, t0, s1
	slli t0, s2, 16
	sub s2, t0, s2
	slli t0, s3, 16
	sub s3, t0, s3
	slli t0, s4, 16
	sub s4, t0, s4
	slli t0, s5, 16
	sub s5, t0, s5
	slli t0, s6, 16
	sub s6, t0, s6
	slli t0, s7, 16
	sub s7, t0, s7
	sd s0, 0(a3)
	sd s1, 8(a3)
	sd s2, 16(a3)
	sd s3, 24(a3)
	sd s4, 32(a3)
	sd s5, 40(a3)
	sd s6, 48(a3)
	sd s7, 56(a3)
	addi a3, a3, 64
	addi a0, a0, 8
	ld t1, 0(a0)
	ld a6, 344(a5)
	and t1, t1, a6
	ld t3, 336(a5)
	srli a7, t1, 48
	slli t0, t1, 16
	xor t0, t0, a7
	xor t1, t1, t0
	and t1, t1, t3
	ld t4, 320(a5)
	and t5, t4, t3
	srli a7, t3, 16
	slli t2, t3, 48
	xor t2, t2, a7
	and t4, t4, t2
	srli a7, t1, 16
	slli t0, t1, 48
	xor t0, t0, a7
	and t0, t0, t4
	srli a7, t1, 40
	slli t1, t1, 24
	xor t1, t1, a7
	and t1, t1, t5
	xor t1, t1, t0
	ld t6, 352(a5)
	and s0, t1, t6
	srli s1, t1, 1
	and s1, s1, t6
	srli s2, t1, 2
	and s2, s2, t6
	srli s3, t1, 3
	and s3, s3, t6
	srli s4, t1, 4
	and s4, s4, t6
	srli s5, t1, 5
	and s5, s5, t6
	srli s6, t1, 6
	and s6, s6, t6
	srli s7, t1, 7
	and s7, s7, t6
	slli t0, s0, 16
	sub s0, t0, s0
	slli t0, s1, 16
	sub s1, t0, s1
	slli t0, s2, 16
	sub s2, t0, s2
	slli t0, s3, 16
	sub s3, t0, s3
	slli t0, s4, 16
	sub s4, t0, s4
	slli t0, s5, 16
	sub s5, t0, s5
	slli t0, s6, 16
	sub s6, t0, s6
	slli t0, s7, 16
	sub s7, t0, s7
	sd s0, 0(a3)
	sd s1, 8(a3)
	sd s2, 16(a3)
	sd s3, 24(a3)
	sd s4, 32(a3)
	sd s5, 40(a3)
	sd s6, 48(a3)
	sd s7, 56(a3)
	addi a3, a3, 64
	ld t1, 0(a0)
	srli t1, t1, 32
	ld t3, 336(a5)
	srli a7, t1, 48
	slli t0, t1, 16
	xor t0, t0, a7
	xor t1, t1, t0
	and t1, t1, t3
	ld t4, 320(a5)
	and t5, t4, t3
	srli a7, t3, 16
	slli t2, t3, 48
	xor t2, t2, a7
	and t4, t4, t2
	srli a7, t1, 16
	slli t0, t1, 48
	xor t0, t0, a7
	and t0, t0, t4
	srli a7, t1, 40
	slli t1, t1, 24
	xor t1, t1, a7
	and t1, t1, t5
	xor t1, t1, t0
	ld t6, 352(a5)
	and s0, t1, t6
	srli s1, t1, 1
	and s1, s1, t6
	srli s2, t1, 2
	and s2, s2, t6
	srli s3, t1, 3
	and s3, s3, t6
	srli s4, t1, 4
	and s4, s4, t6
	srli s5, t1, 5
	and s5, s5, t6
	srli s6, t1, 6
	and s6, s6, t6
	srli s7, t1, 7
	and s7, s7, t6
	slli t0, s0, 16
	sub s0, t0, s0
	slli t0, s1, 16
	sub s1, t0, s1
	slli t0, s2, 16
	sub s2, t0, s2
	slli t0, s3, 16
	sub s3, t0, s3
	slli t0, s4, 16
	sub s4, t0, s4
	slli t0, s5, 16
	sub s5, t0, s5
	slli t0, s6, 16
	sub s6, t0, s6
	slli t0, s7, 16
	sub s7, t0, s7
	sd s0, 0(a3)
	sd s1, 8(a3)
	sd s2, 16(a3)
	sd s3, 24(a3)
	sd s4, 32(a3)
	sd s5, 40(a3)
	sd s6, 48(a3)
	sd s7, 56(a3)
	addi a3, a3, 64
	addi a0, a0, 8
	ld t1, 0(a0)
	ld a6, 344(a5)
	and t1, t1, a6
	ld t3, 336(a5)
	srli a7, t1, 48
	slli t0, t1, 16
	xor t0, t0, a7
	xor t1, t1, t0
	and t1, t1, t3
	ld t4, 320(a5)
	and t5, t4, t3
	srli a7, t3, 16
	slli t2, t3, 48
	xor t2, t2, a7
	and t4, t4, t2
	srli a7, t1, 16
	slli t0, t1, 48
	xor t0, t0, a7
	and t0, t0, t4
	srli a7, t1, 40
	slli t1, t1, 24
	xor t1, t1, a7
	and t1, t1, t5
	xor t1, t1, t0
	ld t6, 352(a5)
	and s0, t1, t6
	srli s1, t1, 1
	and s1, s1, t6
	srli s2, t1, 2
	and s2, s2, t6
	srli s3, t1, 3
	and s3, s3, t6
	srli s4, t1, 4
	and s4, s4, t6
	srli s5, t1, 5
	and s5, s5, t6
	srli s6, t1, 6
	and s6, s6, t6
	srli s7, t1, 7
	and s7, s7, t6
	slli t0, s0, 16
	sub s0, t0, s0
	slli t0, s1, 16
	sub s1, t0, s1
	slli t0, s2, 16
	sub s2, t0, s2
	slli t0, s3, 16
	sub s3, t0, s3
	slli t0, s4, 16
	sub s4, t0, s4
	slli t0, s5, 16
	sub s5, t0, s5
	slli t0, s6, 16
	sub s6, t0, s6
	slli t0, s7, 16
	sub s7, t0, s7
	sd s0, 0(a3)
	sd s1, 8(a3)
	sd s2, 16(a3)
	sd s3, 24(a3)
	sd s4, 32(a3)
	sd s5, 40(a3)
	sd s6, 48(a3)
	sd s7, 56(a3)
	addi a3, a3, 64
	ld t1, 0(a0)
	srli t1, t1, 32
	ld t3, 336(a5)
	srli a7, t1, 48
	slli t0, t1, 16
	xor t0, t0, a7
	xor t1, t1, t0
	and t1, t1, t3
	ld t4, 320(a5)
	and t5, t4, t3
	srli a7, t3, 16
	slli t2, t3, 48
	xor t2, t2, a7
	and t4, t4, t2
	srli a7, t1, 16
	slli t0, t1, 48
	xor t0, t0, a7
	and t0, t0, t4
	srli a7, t1, 40
	slli t1, t1, 24
	xor t1, t1, a7
	and t1, t1, t5
	xor t1, t1, t0
	ld t6, 352(a5)
	and s0, t1, t6
	srli s1, t1, 1
	and s1, s1, t6
	srli s2, t1, 2
	and s2, s2, t6
	srli s3, t1, 3
	and s3, s3, t6
	srli s4, t1, 4
	and s4, s4, t6
	srli s5, t1, 5
	and s5, s5, t6
	srli s6, t1, 6
	and s6, s6, t6
	srli s7, t1, 7
	and s7, s7, t6
	slli t0, s0, 16
	sub s0, t0, s0
	slli t0, s1, 16
	sub s1, t0, s1
	slli t0, s2, 16
	sub s2, t0, s2
	slli t0, s3, 16
	sub s3, t0, s3
	slli t0, s4, 16
	sub s4, t0, s4
	slli t0, s5, 16
	sub s5, t0, s5
	slli t0, s6, 16
	sub s6, t0, s6
	slli t0, s7, 16
	sub s7, t0, s7
	sd s0, 0(a3)
	sd s1, 8(a3)
	sd s2, 16(a3)
	sd s3, 24(a3)
	sd s4, 32(a3)
	sd s5, 40(a3)
	sd s6, 48(a3)
	sd s7, 56(a3)
	addi a3, a3, 64
	addi a0, a0, 8
	ld t1, 0(a0)
	ld a6, 344(a5)
	and t1, t1, a6
	ld t3, 336(a5)
	srli a7, t1, 48
	slli t0, t1, 16
	xor t0, t0, a7
	xor t1, t1, t0
	and t1, t1, t3
	ld t4, 320(a5)
	and t5, t4, t3
	srli a7, t3, 16
	slli t2, t3, 48
	xor t2, t2, a7
	and t4, t4, t2
	srli a7, t1, 16
	slli t0, t1, 48
	xor t0, t0, a7
	and t0, t0, t4
	srli a7, t1, 40
	slli t1, t1, 24
	xor t1, t1, a7
	and t1, t1, t5
	xor t1, t1, t0
	ld t6, 352(a5)
	and s0, t1, t6
	srli s1, t1, 1
	and s1, s1, t6
	srli s2, t1, 2
	and s2, s2, t6
	srli s3, t1, 3
	and s3, s3, t6
	srli s4, t1, 4
	and s4, s4, t6
	srli s5, t1, 5
	and s5, s5, t6
	srli s6, t1, 6
	and s6, s6, t6
	srli s7, t1, 7
	and s7, s7, t6
	slli t0, s0, 16
	sub s0, t0, s0
	slli t0, s1, 16
	sub s1, t0, s1
	slli t0, s2, 16
	sub s2, t0, s2
	slli t0, s3, 16
	sub s3, t0, s3
	slli t0, s4, 16
	sub s4, t0, s4
	slli t0, s5, 16
	sub s5, t0, s5
	slli t0, s6, 16
	sub s6, t0, s6
	slli t0, s7, 16
	sub s7, t0, s7
	sd s0, 0(a3)
	sd s1, 8(a3)
	sd s2, 16(a3)
	sd s3, 24(a3)
	sd s4, 32(a3)
	sd s5, 40(a3)
	sd s6, 48(a3)
	sd s7, 56(a3)
	addi a3, a3, 64
	ld t1, 0(a0)
	srli t1, t1, 32
	ld t3, 336(a5)
	srli a7, t1, 48
	slli t0, t1, 16
	xor t0, t0, a7
	xor t1, t1, t0
	and t1, t1, t3
	ld t4, 320(a5)
	and t5, t4, t3
	srli a7, t3, 16
	slli t2, t3, 48
	xor t2, t2, a7
	and t4, t4, t2
	srli a7, t1, 16
	slli t0, t1, 48
	xor t0, t0, a7
	and t0, t0, t4
	srli a7, t1, 40
	slli t1, t1, 24
	xor t1, t1, a7
	and t1, t1, t5
	xor t1, t1, t0
	ld t6, 352(a5)
	and s0, t1, t6
	srli s1, t1, 1
	and s1, s1, t6
	srli s2, t1, 2
	and s2, s2, t6
	srli s3, t1, 3
	and s3, s3, t6
	srli s4, t1, 4
	and s4, s4, t6
	srli s5, t1, 5
	and s5, s5, t6
	srli s6, t1, 6
	and s6, s6, t6
	srli s7, t1, 7
	and s7, s7, t6
	slli t0, s0, 16
	sub s0, t0, s0
	slli t0, s1, 16
	sub s1, t0, s1
	slli t0, s2, 16
	sub s2, t0, s2
	slli t0, s3, 16
	sub s3, t0, s3
	slli t0, s4, 16
	sub s4, t0, s4
	slli t0, s5, 16
	sub s5, t0, s5
	slli t0, s6, 16
	sub s6, t0, s6
	slli t0, s7, 16
	sub s7, t0, s7
	sd s0, 0(a3)
	sd s1, 8(a3)
	sd s2, 16(a3)
	sd s3, 24(a3)
	sd s4, 32(a3)
	sd s5, 40(a3)
	sd s6, 48(a3)
	sd s7, 56(a3)
	addi a3, a3, 64
	addi a0, a0, 8
	ld t1, 0(a0)
	ld a6, 344(a5)
	and t1, t1, a6
	ld t3, 336(a5)
	srli a7, t1, 48
	slli t0, t1, 16
	xor t0, t0, a7
	xor t1, t1, t0
	and t1, t1, t3
	ld t4, 320(a5)
	and t5, t4, t3
	srli a7, t3, 16
	slli t2, t3, 48
	xor t2, t2, a7
	and t4, t4, t2
	srli a7, t1, 16
	slli t0, t1, 48
	xor t0, t0, a7
	and t0, t0, t4
	srli a7, t1, 40
	slli t1, t1, 24
	xor t1, t1, a7
	and t1, t1, t5
	xor t1, t1, t0
	ld t6, 352(a5)
	and s0, t1, t6
	srli s1, t1, 1
	and s1, s1, t6
	srli s2, t1, 2
	and s2, s2, t6
	srli s3, t1, 3
	and s3, s3, t6
	srli s4, t1, 4
	and s4, s4, t6
	srli s5, t1, 5
	and s5, s5, t6
	srli s6, t1, 6
	and s6, s6, t6
	srli s7, t1, 7
	and s7, s7, t6
	slli t0, s0, 16
	sub s0, t0, s0
	slli t0, s1, 16
	sub s1, t0, s1
	slli t0, s2, 16
	sub s2, t0, s2
	slli t0, s3, 16
	sub s3, t0, s3
	slli t0, s4, 16
	sub s4, t0, s4
	slli t0, s5, 16
	sub s5, t0, s5
	slli t0, s6, 16
	sub s6, t0, s6
	slli t0, s7, 16
	sub s7, t0, s7
	sd s0, 0(a3)
	sd s1, 8(a3)
	sd s2, 16(a3)
	sd s3, 24(a3)
	sd s4, 32(a3)
	sd s5, 40(a3)
	sd s6, 48(a3)
	sd s7, 56(a3)
	addi a3, a3, 64
	ld t1, 0(a0)
	srli t1, t1, 32
	ld t3, 336(a5)
	srli a7, t1, 48
	slli t0, t1, 16
	xor t0, t0, a7
	xor t1, t1, t0
	and t1, t1, t3
	ld t4, 320(a5)
	and t5, t4, t3
	srli a7, t3, 16
	slli t2, t3, 48
	xor t2, t2, a7
	and t4, t4, t2
	srli a7, t1, 16
	slli t0, t1, 48
	xor t0, t0, a7
	and t0, t0, t4
	srli a7, t1, 40
	slli t1, t1, 24
	xor t1, t1, a7
	and t1, t1, t5
	xor t1, t1, t0
	ld t6, 352(a5)
	and s0, t1, t6
	srli s1, t1, 1
	and s1, s1, t6
	srli s2, t1, 2
	and s2, s2, t6
	srli s3, t1, 3
	and s3, s3, t6
	srli s4, t1, 4
	and s4, s4, t6
	srli s5, t1, 5
	and s5, s5, t6
	srli s6, t1, 6
	and s6, s6, t6
	srli s7, t1, 7
	and s7, s7, t6
	slli t0, s0, 16
	sub s0, t0, s0
	slli t0, s1, 16
	sub s1, t0, s1
	slli t0, s2, 16
	sub s2, t0, s2
	slli t0, s3, 16
	sub s3, t0, s3
	slli t0, s4, 16
	sub s4, t0, s4
	slli t0, s5, 16
	sub s5, t0, s5
	slli t0, s6, 16
	sub s6, t0, s6
	slli t0, s7, 16
	sub s7, t0, s7
	sd s0, 0(a3)
	sd s1, 8(a3)
	sd s2, 16(a3)
	sd s3, 24(a3)
	sd s4, 32(a3)
	sd s5, 40(a3)
	sd s6, 48(a3)
	sd s7, 56(a3)
	addi a3, a3, 64
	addi a0, a0, 8
	ld t1, 0(a0)
	ld a6, 344(a5)
	and t1, t1, a6
	ld t3, 336(a5)
	srli a7, t1, 48
	slli t0, t1, 16
	xor t0, t0, a7
	xor t1, t1, t0
	and t1, t1, t3
	ld t4, 320(a5)
	and t5, t4, t3
	srli a7, t3, 16
	slli t2, t3, 48
	xor t2, t2, a7
	and t4, t4, t2
	srli a7, t1, 16
	slli t0, t1, 48
	xor t0, t0, a7
	and t0, t0, t4
	srli a7, t1, 40
	slli t1, t1, 24
	xor t1, t1, a7
	and t1, t1, t5
	xor t1, t1, t0
	ld t6, 352(a5)
	and s0, t1, t6
	srli s1, t1, 1
	and s1, s1, t6
	srli s2, t1, 2
	and s2, s2, t6
	srli s3, t1, 3
	and s3, s3, t6
	srli s4, t1, 4
	and s4, s4, t6
	srli s5, t1, 5
	and s5, s5, t6
	srli s6, t1, 6
	and s6, s6, t6
	srli s7, t1, 7
	and s7, s7, t6
	slli t0, s0, 16
	sub s0, t0, s0
	slli t0, s1, 16
	sub s1, t0, s1
	slli t0, s2, 16
	sub s2, t0, s2
	slli t0, s3, 16
	sub s3, t0, s3
	slli t0, s4, 16
	sub s4, t0, s4
	slli t0, s5, 16
	sub s5, t0, s5
	slli t0, s6, 16
	sub s6, t0, s6
	slli t0, s7, 16
	sub s7, t0, s7
	sd s0, 0(a3)
	sd s1, 8(a3)
	sd s2, 16(a3)
	sd s3, 24(a3)
	sd s4, 32(a3)
	sd s5, 40(a3)
	sd s6, 48(a3)
	sd s7, 56(a3)
	addi a3, a3, 64
	ld t1, 0(a0)
	srli t1, t1, 32
	ld t3, 336(a5)
	srli a7, t1, 48
	slli t0, t1, 16
	xor t0, t0, a7
	xor t1, t1, t0
	and t1, t1, t3
	ld t4, 320(a5)
	and t5, t4, t3
	srli a7, t3, 16
	slli t2, t3, 48
	xor t2, t2, a7
	and t4, t4, t2
	srli a7, t1, 16
	slli t0, t1, 48
	xor t0, t0, a7
	and t0, t0, t4
	srli a7, t1, 40
	slli t1, t1, 24
	xor t1, t1, a7
	and t1, t1, t5
	xor t1, t1, t0
	ld t6, 352(a5)
	and s0, t1, t6
	srli s1, t1, 1
	and s1, s1, t6
	srli s2, t1, 2
	and s2, s2, t6
	srli s3, t1, 3
	and s3, s3, t6
	srli s4, t1, 4
	and s4, s4, t6
	srli s5, t1, 5
	and s5, s5, t6
	srli s6, t1, 6
	and s6, s6, t6
	srli s7, t1, 7
	and s7, s7, t6
	slli t0, s0, 16
	sub s0, t0, s0
	slli t0, s1, 16
	sub s1, t0, s1
	slli t0, s2, 16
	sub s2, t0, s2
	slli t0, s3, 16
	sub s3, t0, s3
	slli t0, s4, 16
	sub s4, t0, s4
	slli t0, s5, 16
	sub s5, t0, s5
	slli t0, s6, 16
	sub s6, t0, s6
	slli t0, s7, 16
	sub s7, t0, s7
	sd s0, 0(a3)
	sd s1, 8(a3)
	sd s2, 16(a3)
	sd s3, 24(a3)
	sd s4, 32(a3)
	sd s5, 40(a3)
	sd s6, 48(a3)
	sd s7, 56(a3)
	addi a3, a3, 64
	addi a0, a0, 8
	ld t1, 0(a0)
	ld a6, 344(a5)
	and t1, t1, a6
	ld t3, 336(a5)
	srli a7, t1, 48
	slli t0, t1, 16
	xor t0, t0, a7
	xor t1, t1, t0
	and t1, t1, t3
	ld t4, 320(a5)
	and t5, t4, t3
	srli a7, t3, 16
	slli t2, t3, 48
	xor t2, t2, a7
	and t4, t4, t2
	srli a7, t1, 16
	slli t0, t1, 48
	xor t0, t0, a7
	and t0, t0, t4
	srli a7, t1, 40
	slli t1, t1, 24
	xor t1, t1, a7
	and t1, t1, t5
	xor t1, t1, t0
	ld t6, 352(a5)
	and s0, t1, t6
	srli s1, t1, 1
	and s1, s1, t6
	srli s2, t1, 2
	and s2, s2, t6
	srli s3, t1, 3
	and s3, s3, t6
	srli s4, t1, 4
	and s4, s4, t6
	srli s5, t1, 5
	and s5, s5, t6
	srli s6, t1, 6
	and s6, s6, t6
	srli s7, t1, 7
	and s7, s7, t6
	slli t0, s0, 16
	sub s0, t0, s0
	slli t0, s1, 16
	sub s1, t0, s1
	slli t0, s2, 16
	sub s2, t0, s2
	slli t0, s3, 16
	sub s3, t0, s3
	slli t0, s4, 16
	sub s4, t0, s4
	slli t0, s5, 16
	sub s5, t0, s5
	slli t0, s6, 16
	sub s6, t0, s6
	slli t0, s7, 16
	sub s7, t0, s7
	sd s0, 0(a3)
	sd s1, 8(a3)
	sd s2, 16(a3)
	sd s3, 24(a3)
	sd s4, 32(a3)
	sd s5, 40(a3)
	sd s6, 48(a3)
	sd s7, 56(a3)
	addi a3, a3, 64
	ld t1, 0(a0)
	srli t1, t1, 32
	ld t3, 336(a5)
	srli a7, t1, 48
	slli t0, t1, 16
	xor t0, t0, a7
	xor t1, t1, t0
	and t1, t1, t3
	ld t4, 320(a5)
	and t5, t4, t3
	srli a7, t3, 16
	slli t2, t3, 48
	xor t2, t2, a7
	and t4, t4, t2
	srli a7, t1, 16
	slli t0, t1, 48
	xor t0, t0, a7
	and t0, t0, t4
	srli a7, t1, 40
	slli t1, t1, 24
	xor t1, t1, a7
	and t1, t1, t5
	xor t1, t1, t0
	ld t6, 352(a5)
	and s0, t1, t6
	srli s1, t1, 1
	and s1, s1, t6
	srli s2, t1, 2
	and s2, s2, t6
	srli s3, t1, 3
	and s3, s3, t6
	srli s4, t1, 4
	and s4, s4, t6
	srli s5, t1, 5
	and s5, s5, t6
	srli s6, t1, 6
	and s6, s6, t6
	srli s7, t1, 7
	and s7, s7, t6
	slli t0, s0, 16
	sub s0, t0, s0
	slli t0, s1, 16
	sub s1, t0, s1
	slli t0, s2, 16
	sub s2, t0, s2
	slli t0, s3, 16
	sub s3, t0, s3
	slli t0, s4, 16
	sub s4, t0, s4
	slli t0, s5, 16
	sub s5, t0, s5
	slli t0, s6, 16
	sub s6, t0, s6
	slli t0, s7, 16
	sub s7, t0, s7
	sd s0, 0(a3)
	sd s1, 8(a3)
	sd s2, 16(a3)
	sd s3, 24(a3)
	sd s4, 32(a3)
	sd s5, 40(a3)
	sd s6, 48(a3)
	sd s7, 56(a3)
	addi a3, a3, 64
	addi a0, a0, 8
	ld t1, 0(a0)
	ld a6, 344(a5)
	and t1, t1, a6
	ld t3, 336(a5)
	srli a7, t1, 48
	slli t0, t1, 16
	xor t0, t0, a7
	xor t1, t1, t0
	and t1, t1, t3
	ld t4, 320(a5)
	and t5, t4, t3
	srli a7, t3, 16
	slli t2, t3, 48
	xor t2, t2, a7
	and t4, t4, t2
	srli a7, t1, 16
	slli t0, t1, 48
	xor t0, t0, a7
	and t0, t0, t4
	srli a7, t1, 40
	slli t1, t1, 24
	xor t1, t1, a7
	and t1, t1, t5
	xor t1, t1, t0
	ld t6, 352(a5)
	and s0, t1, t6
	srli s1, t1, 1
	and s1, s1, t6
	srli s2, t1, 2
	and s2, s2, t6
	srli s3, t1, 3
	and s3, s3, t6
	srli s4, t1, 4
	and s4, s4, t6
	srli s5, t1, 5
	and s5, s5, t6
	srli s6, t1, 6
	and s6, s6, t6
	srli s7, t1, 7
	and s7, s7, t6
	slli t0, s0, 16
	sub s0, t0, s0
	slli t0, s1, 16
	sub s1, t0, s1
	slli t0, s2, 16
	sub s2, t0, s2
	slli t0, s3, 16
	sub s3, t0, s3
	slli t0, s4, 16
	sub s4, t0, s4
	slli t0, s5, 16
	sub s5, t0, s5
	slli t0, s6, 16
	sub s6, t0, s6
	slli t0, s7, 16
	sub s7, t0, s7
	sd s0, 0(a3)
	sd s1, 8(a3)
	sd s2, 16(a3)
	sd s3, 24(a3)
	sd s4, 32(a3)
	sd s5, 40(a3)
	sd s6, 48(a3)
	sd s7, 56(a3)
	addi a3, a3, 64
	ld t1, 0(a0)
	srli t1, t1, 32
	ld t3, 336(a5)
	srli a7, t1, 48
	slli t0, t1, 16
	xor t0, t0, a7
	xor t1, t1, t0
	and t1, t1, t3
	ld t4, 320(a5)
	and t5, t4, t3
	srli a7, t3, 16
	slli t2, t3, 48
	xor t2, t2, a7
	and t4, t4, t2
	srli a7, t1, 16
	slli t0, t1, 48
	xor t0, t0, a7
	and t0, t0, t4
	srli a7, t1, 40
	slli t1, t1, 24
	xor t1, t1, a7
	and t1, t1, t5
	xor t1, t1, t0
	ld t6, 352(a5)
	and s0, t1, t6
	srli s1, t1, 1
	and s1, s1, t6
	srli s2, t1, 2
	and s2, s2, t6
	srli s3, t1, 3
	and s3, s3, t6
	srli s4, t1, 4
	and s4, s4, t6
	srli s5, t1, 5
	and s5, s5, t6
	srli s6, t1, 6
	and s6, s6, t6
	srli s7, t1, 7
	and s7, s7, t6
	slli t0, s0, 16
	sub s0, t0, s0
	slli t0, s1, 16
	sub s1, t0, s1
	slli t0, s2, 16
	sub s2, t0, s2
	slli t0, s3, 16
	sub s3, t0, s3
	slli t0, s4, 16
	sub s4, t0, s4
	slli t0, s5, 16
	sub s5, t0, s5
	slli t0, s6, 16
	sub s6, t0, s6
	slli t0, s7, 16
	sub s7, t0, s7
	sd s0, 0(a3)
	sd s1, 8(a3)
	sd s2, 16(a3)
	sd s3, 24(a3)
	sd s4, 32(a3)
	sd s5, 40(a3)
	sd s6, 48(a3)
	sd s7, 56(a3)
	addi a3, a3, 64
	addi a0, a0, 8
	ld t1, 0(a0)
	ld a6, 344(a5)
	and t1, t1, a6
	ld t3, 336(a5)
	srli a7, t1, 48
	slli t0, t1, 16
	xor t0, t0, a7
	xor t1, t1, t0
	and t1, t1, t3
	ld t4, 320(a5)
	and t5, t4, t3
	srli a7, t3, 16
	slli t2, t3, 48
	xor t2, t2, a7
	and t4, t4, t2
	srli a7, t1, 16
	slli t0, t1, 48
	xor t0, t0, a7
	and t0, t0, t4
	srli a7, t1, 40
	slli t1, t1, 24
	xor t1, t1, a7
	and t1, t1, t5
	xor t1, t1, t0
	ld t6, 352(a5)
	and s0, t1, t6
	srli s1, t1, 1
	and s1, s1, t6
	srli s2, t1, 2
	and s2, s2, t6
	srli s3, t1, 3
	and s3, s3, t6
	srli s4, t1, 4
	and s4, s4, t6
	srli s5, t1, 5
	and s5, s5, t6
	srli s6, t1, 6
	and s6, s6, t6
	srli s7, t1, 7
	and s7, s7, t6
	slli t0, s0, 16
	sub s0, t0, s0
	slli t0, s1, 16
	sub s1, t0, s1
	slli t0, s2, 16
	sub s2, t0, s2
	slli t0, s3, 16
	sub s3, t0, s3
	slli t0, s4, 16
	sub s4, t0, s4
	slli t0, s5, 16
	sub s5, t0, s5
	slli t0, s6, 16
	sub s6, t0, s6
	slli t0, s7, 16
	sub s7, t0, s7
	sd s0, 0(a3)
	sd s1, 8(a3)
	sd s2, 16(a3)
	sd s3, 24(a3)
	sd s4, 32(a3)
	sd s5, 40(a3)
	sd s6, 48(a3)
	sd s7, 56(a3)
	addi a3, a3, 64
	ld t1, 0(a0)
	srli t1, t1, 32
	ld t3, 336(a5)
	srli a7, t1, 48
	slli t0, t1, 16
	xor t0, t0, a7
	xor t1, t1, t0
	and t1, t1, t3
	ld t4, 320(a5)
	and t5, t4, t3
	srli a7, t3, 16
	slli t2, t3, 48
	xor t2, t2, a7
	and t4, t4, t2
	srli a7, t1, 16
	slli t0, t1, 48
	xor t0, t0, a7
	and t0, t0, t4
	srli a7, t1, 40
	slli t1, t1, 24
	xor t1, t1, a7
	and t1, t1, t5
	xor t1, t1, t0
	ld t6, 352(a5)
	and s0, t1, t6
	srli s1, t1, 1
	and s1, s1, t6
	srli s2, t1, 2
	and s2, s2, t6
	srli s3, t1, 3
	and s3, s3, t6
	srli s4, t1, 4
	and s4, s4, t6
	srli s5, t1, 5
	and s5, s5, t6
	srli s6, t1, 6
	and s6, s6, t6
	srli s7, t1, 7
	and s7, s7, t6
	slli t0, s0, 16
	sub s0, t0, s0
	slli t0, s1, 16
	sub s1, t0, s1
	slli t0, s2, 16
	sub s2, t0, s2
	slli t0, s3, 16
	sub s3, t0, s3
	slli t0, s4, 16
	sub s4, t0, s4
	slli t0, s5, 16
	sub s5, t0, s5
	slli t0, s6, 16
	sub s6, t0, s6
	slli t0, s7, 16
	sub s7, t0, s7
	sd s0, 0(a3)
	sd s1, 8(a3)
	sd s2, 16(a3)
	sd s3, 24(a3)
	sd s4, 32(a3)
	sd s5, 40(a3)
	sd s6, 48(a3)
	sd s7, 56(a3)
	addi a3, a3, 64
	addi a0, a0, 8
	ld t1, 0(a0)
	ld a6, 344(a5)
	and t1, t1, a6
	ld t3, 336(a5)
	srli a7, t1, 48
	slli t0, t1, 16
	xor t0, t0, a7
	xor t1, t1, t0
	and t1, t1, t3
	ld t4, 320(a5)
	and t5, t4, t3
	srli a7, t3, 16
	slli t2, t3, 48
	xor t2, t2, a7
	and t4, t4, t2
	srli a7, t1, 16
	slli t0, t1, 48
	xor t0, t0, a7
	and t0, t0, t4
	srli a7, t1, 40
	slli t1, t1, 24
	xor t1, t1, a7
	and t1, t1, t5
	xor t1, t1, t0
	ld t6, 352(a5)
	and s0, t1, t6
	srli s1, t1, 1
	and s1, s1, t6
	srli s2, t1, 2
	and s2, s2, t6
	srli s3, t1, 3
	and s3, s3, t6
	srli s4, t1, 4
	and s4, s4, t6
	srli s5, t1, 5
	and s5, s5, t6
	srli s6, t1, 6
	and s6, s6, t6
	srli s7, t1, 7
	and s7, s7, t6
	slli t0, s0, 16
	sub s0, t0, s0
	slli t0, s1, 16
	sub s1, t0, s1
	slli t0, s2, 16
	sub s2, t0, s2
	slli t0, s3, 16
	sub s3, t0, s3
	slli t0, s4, 16
	sub s4, t0, s4
	slli t0, s5, 16
	sub s5, t0, s5
	slli t0, s6, 16
	sub s6, t0, s6
	slli t0, s7, 16
	sub s7, t0, s7
	sd s0, 0(a3)
	sd s1, 8(a3)
	sd s2, 16(a3)
	sd s3, 24(a3)
	sd s4, 32(a3)
	sd s5, 40(a3)
	sd s6, 48(a3)
	sd s7, 56(a3)
	addi a3, a3, 64
	ld t1, 0(a0)
	srli t1, t1, 32
	ld t3, 336(a5)
	srli a7, t1, 48
	slli t0, t1, 16
	xor t0, t0, a7
	xor t1, t1, t0
	and t1, t1, t3
	ld t4, 320(a5)
	and t5, t4, t3
	srli a7, t3, 16
	slli t2, t3, 48
	xor t2, t2, a7
	and t4, t4, t2
	srli a7, t1, 16
	slli t0, t1, 48
	xor t0, t0, a7
	and t0, t0, t4
	srli a7, t1, 40
	slli t1, t1, 24
	xor t1, t1, a7
	and t1, t1, t5
	xor t1, t1, t0
	ld t6, 352(a5)
	and s0, t1, t6
	srli s1, t1, 1
	and s1, s1, t6
	srli s2, t1, 2
	and s2, s2, t6
	srli s3, t1, 3
	and s3, s3, t6
	srli s4, t1, 4
	and s4, s4, t6
	srli s5, t1, 5
	and s5, s5, t6
	srli s6, t1, 6
	and s6, s6, t6
	srli s7, t1, 7
	and s7, s7, t6
	slli t0, s0, 16
	sub s0, t0, s0
	slli t0, s1, 16
	sub s1, t0, s1
	slli t0, s2, 16
	sub s2, t0, s2
	slli t0, s3, 16
	sub s3, t0, s3
	slli t0, s4, 16
	sub s4, t0, s4
	slli t0, s5, 16
	sub s5, t0, s5
	slli t0, s6, 16
	sub s6, t0, s6
	slli t0, s7, 16
	sub s7, t0, s7
	sd s0, 0(a3)
	sd s1, 8(a3)
	sd s2, 16(a3)
	sd s3, 24(a3)
	sd s4, 32(a3)
	sd s5, 40(a3)
	sd s6, 48(a3)
	sd s7, 56(a3)
	addi a3, a3, 64
	addi a0, a0, 8
	ld t1, 0(a0)
	ld a6, 344(a5)
	and t1, t1, a6
	ld t3, 336(a5)
	srli a7, t1, 48
	slli t0, t1, 16
	xor t0, t0, a7
	xor t1, t1, t0
	and t1, t1, t3
	ld t4, 320(a5)
	and t5, t4, t3
	srli a7, t3, 16
	slli t2, t3, 48
	xor t2, t2, a7
	and t4, t4, t2
	srli a7, t1, 16
	slli t0, t1, 48
	xor t0, t0, a7
	and t0, t0, t4
	srli a7, t1, 40
	slli t1, t1, 24
	xor t1, t1, a7
	and t1, t1, t5
	xor t1, t1, t0
	ld t6, 352(a5)
	and s0, t1, t6
	srli s1, t1, 1
	and s1, s1, t6
	srli s2, t1, 2
	and s2, s2, t6
	srli s3, t1, 3
	and s3, s3, t6
	srli s4, t1, 4
	and s4, s4, t6
	srli s5, t1, 5
	and s5, s5, t6
	srli s6, t1, 6
	and s6, s6, t6
	srli s7, t1, 7
	and s7, s7, t6
	slli t0, s0, 16
	sub s0, t0, s0
	slli t0, s1, 16
	sub s1, t0, s1
	slli t0, s2, 16
	sub s2, t0, s2
	slli t0, s3, 16
	sub s3, t0, s3
	slli t0, s4, 16
	sub s4, t0, s4
	slli t0, s5, 16
	sub s5, t0, s5
	slli t0, s6, 16
	sub s6, t0, s6
	slli t0, s7, 16
	sub s7, t0, s7
	sd s0, 0(a3)
	sd s1, 8(a3)
	sd s2, 16(a3)
	sd s3, 24(a3)
	sd s4, 32(a3)
	sd s5, 40(a3)
	sd s6, 48(a3)
	sd s7, 56(a3)
	addi a3, a3, 64
	ld t1, 0(a0)
	srli t1, t1, 32
	ld t3, 336(a5)
	srli a7, t1, 48
	slli t0, t1, 16
	xor t0, t0, a7
	xor t1, t1, t0
	and t1, t1, t3
	ld t4, 320(a5)
	and t5, t4, t3
	srli a7, t3, 16
	slli t2, t3, 48
	xor t2, t2, a7
	and t4, t4, t2
	srli a7, t1, 16
	slli t0, t1, 48
	xor t0, t0, a7
	and t0, t0, t4
	srli a7, t1, 40
	slli t1, t1, 24
	xor t1, t1, a7
	and t1, t1, t5
	xor t1, t1, t0
	ld t6, 352(a5)
	and s0, t1, t6
	srli s1, t1, 1
	and s1, s1, t6
	srli s2, t1, 2
	and s2, s2, t6
	srli s3, t1, 3
	and s3, s3, t6
	srli s4, t1, 4
	and s4, s4, t6
	srli s5, t1, 5
	and s5, s5, t6
	srli s6, t1, 6
	and s6, s6, t6
	srli s7, t1, 7
	and s7, s7, t6
	slli t0, s0, 16
	sub s0, t0, s0
	slli t0, s1, 16
	sub s1, t0, s1
	slli t0, s2, 16
	sub s2, t0, s2
	slli t0, s3, 16
	sub s3, t0, s3
	slli t0, s4, 16
	sub s4, t0, s4
	slli t0, s5, 16
	sub s5, t0, s5
	slli t0, s6, 16
	sub s6, t0, s6
	slli t0, s7, 16
	sub s7, t0, s7
	sd s0, 0(a3)
	sd s1, 8(a3)
	sd s2, 16(a3)
	sd s3, 24(a3)
	sd s4, 32(a3)
	sd s5, 40(a3)
	sd s6, 48(a3)
	sd s7, 56(a3)
	addi a3, a3, 64
	addi a0, a0, 8
	ld t1, 0(a0)
	ld a6, 344(a5)
	and t1, t1, a6
	ld t3, 336(a5)
	srli a7, t1, 48
	slli t0, t1, 16
	xor t0, t0, a7
	xor t1, t1, t0
	and t1, t1, t3
	ld t4, 320(a5)
	and t5, t4, t3
	srli a7, t3, 16
	slli t2, t3, 48
	xor t2, t2, a7
	and t4, t4, t2
	srli a7, t1, 16
	slli t0, t1, 48
	xor t0, t0, a7
	and t0, t0, t4
	srli a7, t1, 40
	slli t1, t1, 24
	xor t1, t1, a7
	and t1, t1, t5
	xor t1, t1, t0
	ld t6, 352(a5)
	and s0, t1, t6
	srli s1, t1, 1
	and s1, s1, t6
	srli s2, t1, 2
	and s2, s2, t6
	srli s3, t1, 3
	and s3, s3, t6
	srli s4, t1, 4
	and s4, s4, t6
	srli s5, t1, 5
	and s5, s5, t6
	srli s6, t1, 6
	and s6, s6, t6
	srli s7, t1, 7
	and s7, s7, t6
	slli t0, s0, 16
	sub s0, t0, s0
	slli t0, s1, 16
	sub s1, t0, s1
	slli t0, s2, 16
	sub s2, t0, s2
	slli t0, s3, 16
	sub s3, t0, s3
	slli t0, s4, 16
	sub s4, t0, s4
	slli t0, s5, 16
	sub s5, t0, s5
	slli t0, s6, 16
	sub s6, t0, s6
	slli t0, s7, 16
	sub s7, t0, s7
	sd s0, 0(a3)
	sd s1, 8(a3)
	sd s2, 16(a3)
	sd s3, 24(a3)
	sd s4, 32(a3)
	sd s5, 40(a3)
	sd s6, 48(a3)
	sd s7, 56(a3)
	addi a3, a3, 64
	ld t1, 0(a0)
	srli t1, t1, 32
	ld t3, 336(a5)
	srli a7, t1, 48
	slli t0, t1, 16
	xor t0, t0, a7
	xor t1, t1, t0
	and t1, t1, t3
	ld t4, 320(a5)
	and t5, t4, t3
	srli a7, t3, 16
	slli t2, t3, 48
	xor t2, t2, a7
	and t4, t4, t2
	srli a7, t1, 16
	slli t0, t1, 48
	xor t0, t0, a7
	and t0, t0, t4
	srli a7, t1, 40
	slli t1, t1, 24
	xor t1, t1, a7
	and t1, t1, t5
	xor t1, t1, t0
	ld t6, 352(a5)
	and s0, t1, t6
	srli s1, t1, 1
	and s1, s1, t6
	srli s2, t1, 2
	and s2, s2, t6
	srli s3, t1, 3
	and s3, s3, t6
	srli s4, t1, 4
	and s4, s4, t6
	srli s5, t1, 5
	and s5, s5, t6
	srli s6, t1, 6
	and s6, s6, t6
	srli s7, t1, 7
	and s7, s7, t6
	slli t0, s0, 16
	sub s0, t0, s0
	slli t0, s1, 16
	sub s1, t0, s1
	slli t0, s2, 16
	sub s2, t0, s2
	slli t0, s3, 16
	sub s3, t0, s3
	slli t0, s4, 16
	sub s4, t0, s4
	slli t0, s5, 16
	sub s5, t0, s5
	slli t0, s6, 16
	sub s6, t0, s6
	slli t0, s7, 16
	sub s7, t0, s7
	sd s0, 0(a3)
	sd s1, 8(a3)
	sd s2, 16(a3)
	sd s3, 24(a3)
	sd s4, 32(a3)
	sd s5, 40(a3)
	sd s6, 48(a3)
	sd s7, 56(a3)
	addi a3, a3, 64
	addi a0, a0, 8
	ld t1, 0(a0)
	ld a6, 344(a5)
	and t1, t1, a6
	ld t3, 336(a5)
	srli a7, t1, 48
	slli t0, t1, 16
	xor t0, t0, a7
	xor t1, t1, t0
	and t1, t1, t3
	ld t4, 320(a5)
	and t5, t4, t3
	srli a7, t3, 16
	slli t2, t3, 48
	xor t2, t2, a7
	and t4, t4, t2
	srli a7, t1, 16
	slli t0, t1, 48
	xor t0, t0, a7
	and t0, t0, t4
	srli a7, t1, 40
	slli t1, t1, 24
	xor t1, t1, a7
	and t1, t1, t5
	xor t1, t1, t0
	ld t6, 352(a5)
	and s0, t1, t6
	srli s1, t1, 1
	and s1, s1, t6
	srli s2, t1, 2
	and s2, s2, t6
	srli s3, t1, 3
	and s3, s3, t6
	srli s4, t1, 4
	and s4, s4, t6
	srli s5, t1, 5
	and s5, s5, t6
	srli s6, t1, 6
	and s6, s6, t6
	srli s7, t1, 7
	and s7, s7, t6
	slli t0, s0, 16
	sub s0, t0, s0
	slli t0, s1, 16
	sub s1, t0, s1
	slli t0, s2, 16
	sub s2, t0, s2
	slli t0, s3, 16
	sub s3, t0, s3
	slli t0, s4, 16
	sub s4, t0, s4
	slli t0, s5, 16
	sub s5, t0, s5
	slli t0, s6, 16
	sub s6, t0, s6
	slli t0, s7, 16
	sub s7, t0, s7
	sd s0, 0(a3)
	sd s1, 8(a3)
	sd s2, 16(a3)
	sd s3, 24(a3)
	sd s4, 32(a3)
	sd s5, 40(a3)
	sd s6, 48(a3)
	sd s7, 56(a3)
	addi a3, a3, 64
	ld t1, 0(a0)
	srli t1, t1, 32
	ld t3, 336(a5)
	srli a7, t1, 48
	slli t0, t1, 16
	xor t0, t0, a7
	xor t1, t1, t0
	and t1, t1, t3
	ld t4, 320(a5)
	and t5, t4, t3
	srli a7, t3, 16
	slli t2, t3, 48
	xor t2, t2, a7
	and t4, t4, t2
	srli a7, t1, 16
	slli t0, t1, 48
	xor t0, t0, a7
	and t0, t0, t4
	srli a7, t1, 40
	slli t1, t1, 24
	xor t1, t1, a7
	and t1, t1, t5
	xor t1, t1, t0
	ld t6, 352(a5)
	and s0, t1, t6
	srli s1, t1, 1
	and s1, s1, t6
	srli s2, t1, 2
	and s2, s2, t6
	srli s3, t1, 3
	and s3, s3, t6
	srli s4, t1, 4
	and s4, s4, t6
	srli s5, t1, 5
	and s5, s5, t6
	srli s6, t1, 6
	and s6, s6, t6
	srli s7, t1, 7
	and s7, s7, t6
	slli t0, s0, 16
	sub s0, t0, s0
	slli t0, s1, 16
	sub s1, t0, s1
	slli t0, s2, 16
	sub s2, t0, s2
	slli t0, s3, 16
	sub s3, t0, s3
	slli t0, s4, 16
	sub s4, t0, s4
	slli t0, s5, 16
	sub s5, t0, s5
	slli t0, s6, 16
	sub s6, t0, s6
	slli t0, s7, 16
	sub s7, t0, s7
	sd s0, 0(a3)
	sd s1, 8(a3)
	sd s2, 16(a3)
	sd s3, 24(a3)
	sd s4, 32(a3)
	sd s5, 40(a3)
	sd s6, 48(a3)
	sd s7, 56(a3)
	addi a3, a3, 64
	addi a0, a0, 8
	ld t1, 0(a0)
	ld a6, 344(a5)
	and t1, t1, a6
	ld t3, 336(a5)
	srli a7, t1, 48
	slli t0, t1, 16
	xor t0, t0, a7
	xor t1, t1, t0
	and t1, t1, t3
	ld t4, 320(a5)
	and t5, t4, t3
	srli a7, t3, 16
	slli t2, t3, 48
	xor t2, t2, a7
	and t4, t4, t2
	srli a7, t1, 16
	slli t0, t1, 48
	xor t0, t0, a7
	and t0, t0, t4
	srli a7, t1, 40
	slli t1, t1, 24
	xor t1, t1, a7
	and t1, t1, t5
	xor t1, t1, t0
	ld t6, 352(a5)
	and s0, t1, t6
	srli s1, t1, 1
	and s1, s1, t6
	srli s2, t1, 2
	and s2, s2, t6
	srli s3, t1, 3
	and s3, s3, t6
	srli s4, t1, 4
	and s4, s4, t6
	srli s5, t1, 5
	and s5, s5, t6
	srli s6, t1, 6
	and s6, s6, t6
	srli s7, t1, 7
	and s7, s7, t6
	slli t0, s0, 16
	sub s0, t0, s0
	slli t0, s1, 16
	sub s1, t0, s1
	slli t0, s2, 16
	sub s2, t0, s2
	slli t0, s3, 16
	sub s3, t0, s3
	slli t0, s4, 16
	sub s4, t0, s4
	slli t0, s5, 16
	sub s5, t0, s5
	slli t0, s6, 16
	sub s6, t0, s6
	slli t0, s7, 16
	sub s7, t0, s7
	sd s0, 0(a3)
	sd s1, 8(a3)
	sd s2, 16(a3)
	sd s3, 24(a3)
	sd s4, 32(a3)
	sd s5, 40(a3)
	sd s6, 48(a3)
	sd s7, 56(a3)
	addi a3, a3, 64
	ld t1, 0(a0)
	srli t1, t1, 32
	ld t3, 336(a5)
	srli a7, t1, 48
	slli t0, t1, 16
	xor t0, t0, a7
	xor t1, t1, t0
	and t1, t1, t3
	ld t4, 320(a5)
	and t5, t4, t3
	srli a7, t3, 16
	slli t2, t3, 48
	xor t2, t2, a7
	and t4, t4, t2
	srli a7, t1, 16
	slli t0, t1, 48
	xor t0, t0, a7
	and t0, t0, t4
	srli a7, t1, 40
	slli t1, t1, 24
	xor t1, t1, a7
	and t1, t1, t5
	xor t1, t1, t0
	ld t6, 352(a5)
	and s0, t1, t6
	srli s1, t1, 1
	and s1, s1, t6
	srli s2, t1, 2
	and s2, s2, t6
	srli s3, t1, 3
	and s3, s3, t6
	srli s4, t1, 4
	and s4, s4, t6
	srli s5, t1, 5
	and s5, s5, t6
	srli s6, t1, 6
	and s6, s6, t6
	srli s7, t1, 7
	and s7, s7, t6
	slli t0, s0, 16
	sub s0, t0, s0
	slli t0, s1, 16
	sub s1, t0, s1
	slli t0, s2, 16
	sub s2, t0, s2
	slli t0, s3, 16
	sub s3, t0, s3
	slli t0, s4, 16
	sub s4, t0, s4
	slli t0, s5, 16
	sub s5, t0, s5
	slli t0, s6, 16
	sub s6, t0, s6
	slli t0, s7, 16
	sub s7, t0, s7
	sd s0, 0(a3)
	sd s1, 8(a3)
	sd s2, 16(a3)
	sd s3, 24(a3)
	sd s4, 32(a3)
	sd s5, 40(a3)
	sd s6, 48(a3)
	sd s7, 56(a3)
	addi a3, a3, 64
	addi a0, a0, 8
	ld t1, 0(a0)
	ld a6, 344(a5)
	and t1, t1, a6
	ld t3, 336(a5)
	srli a7, t1, 48
	slli t0, t1, 16
	xor t0, t0, a7
	xor t1, t1, t0
	and t1, t1, t3
	ld t4, 320(a5)
	and t5, t4, t3
	srli a7, t3, 16
	slli t2, t3, 48
	xor t2, t2, a7
	and t4, t4, t2
	srli a7, t1, 16
	slli t0, t1, 48
	xor t0, t0, a7
	and t0, t0, t4
	srli a7, t1, 40
	slli t1, t1, 24
	xor t1, t1, a7
	and t1, t1, t5
	xor t1, t1, t0
	ld t6, 352(a5)
	and s0, t1, t6
	srli s1, t1, 1
	and s1, s1, t6
	srli s2, t1, 2
	and s2, s2, t6
	srli s3, t1, 3
	and s3, s3, t6
	srli s4, t1, 4
	and s4, s4, t6
	srli s5, t1, 5
	and s5, s5, t6
	srli s6, t1, 6
	and s6, s6, t6
	srli s7, t1, 7
	and s7, s7, t6
	slli t0, s0, 16
	sub s0, t0, s0
	slli t0, s1, 16
	sub s1, t0, s1
	slli t0, s2, 16
	sub s2, t0, s2
	slli t0, s3, 16
	sub s3, t0, s3
	slli t0, s4, 16
	sub s4, t0, s4
	slli t0, s5, 16
	sub s5, t0, s5
	slli t0, s6, 16
	sub s6, t0, s6
	slli t0, s7, 16
	sub s7, t0, s7
	sd s0, 0(a3)
	sd s1, 8(a3)
	sd s2, 16(a3)
	sd s3, 24(a3)
	sd s4, 32(a3)
	sd s5, 40(a3)
	sd s6, 48(a3)
	sd s7, 56(a3)
	addi a3, a3, 64
	ld t1, 0(a0)
	srli t1, t1, 32
	ld t3, 336(a5)
	srli a7, t1, 48
	slli t0, t1, 16
	xor t0, t0, a7
	xor t1, t1, t0
	and t1, t1, t3
	ld t4, 320(a5)
	and t5, t4, t3
	srli a7, t3, 16
	slli t2, t3, 48
	xor t2, t2, a7
	and t4, t4, t2
	srli a7, t1, 16
	slli t0, t1, 48
	xor t0, t0, a7
	and t0, t0, t4
	srli a7, t1, 40
	slli t1, t1, 24
	xor t1, t1, a7
	and t1, t1, t5
	xor t1, t1, t0
	ld t6, 352(a5)
	and s0, t1, t6
	srli s1, t1, 1
	and s1, s1, t6
	srli s2, t1, 2
	and s2, s2, t6
	srli s3, t1, 3
	and s3, s3, t6
	srli s4, t1, 4
	and s4, s4, t6
	srli s5, t1, 5
	and s5, s5, t6
	srli s6, t1, 6
	and s6, s6, t6
	srli s7, t1, 7
	and s7, s7, t6
	slli t0, s0, 16
	sub s0, t0, s0
	slli t0, s1, 16
	sub s1, t0, s1
	slli t0, s2, 16
	sub s2, t0, s2
	slli t0, s3, 16
	sub s3, t0, s3
	slli t0, s4, 16
	sub s4, t0, s4
	slli t0, s5, 16
	sub s5, t0, s5
	slli t0, s6, 16
	sub s6, t0, s6
	slli t0, s7, 16
	sub s7, t0, s7
	sd s0, 0(a3)
	sd s1, 8(a3)
	sd s2, 16(a3)
	sd s3, 24(a3)
	sd s4, 32(a3)
	sd s5, 40(a3)
	sd s6, 48(a3)
	sd s7, 56(a3)
	addi a3, a3, 64
	addi a0, a0, 8
	addi a0, a5, 2040
	addi a0, a0, 1032
	addi t0, a5, 2040
	addi t0, t0, 1032
	ld s0, 0(t0)
	ld s1, 8(t0)
	ld s2, 16(t0)
	ld s3, 24(t0)
	ld s4, 32(t0)
	ld s5, 40(t0)
	ld s6, 48(t0)
	ld s7, 56(t0)
	ld s8, 64(t0)
	ld s9, 72(t0)
	ld s10, 80(t0)
	ld s11, 88(t0)
	addi s1, a1, 0
	addi s2, a2, 0
	addi s3, a4, 0
	addi s4, a5, -56
	ld a0, 48(s4)
	beqz s3, 24f
26:
	lbu t0, 32(s4)
	lbu t2, 33(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 34(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 35(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 824(s4)
	srli t2, t0, 8
	sb t2, 825(s4)
	srli t2, t0, 16
	sb t2, 826(s4)
	srli t2, t0, 24
	sb t2, 827(s4)
	lbu t0, 36(s4)
	lbu t2, 37(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 38(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 39(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 828(s4)
	srli t2, t0, 8
	sb t2, 829(s4)
	srli t2, t0, 16
	sb t2, 830(s4)
	srli t2, t0, 24
	sb t2, 831(s4)
	lbu t0, 40(s4)
	lbu t2, 41(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 42(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 43(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 832(s4)
	srli t2, t0, 8
	sb t2, 833(s4)
	srli t2, t0, 16
	sb t2, 834(s4)
	srli t2, t0, 24
	sb t2, 835(s4)
	lbu t0, 44(s4)
	lbu t2, 45(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 46(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 47(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 836(s4)
	srli t2, t0, 8
	sb t2, 837(s4)
	srli t2, t0, 16
	sb t2, 838(s4)
	srli t2, t0, 24
	sb t2, 839(s4)
	addi a5, s4, 56
	addi t0, a5, 2040
	addi t0, t0, 1032
	sd s0, 0(t0)
	sd s1, 8(t0)
	sd s2, 16(t0)
	sd s3, 24(t0)
	sd s4, 32(t0)
	sd s5, 40(t0)
	sd s6, 48(t0)
	sd s7, 56(t0)
	sd s8, 64(t0)
	sd s9, 72(t0)
	sd s10, 80(t0)
	sd s11, 88(t0)
	addi a1, s1, 0
	addi a2, s2, 0
	addi a4, s3, 0
	addi a0, a5, 2040
	addi a0, a0, 1032
	ld t3, 360(a5)
	ld t4, 368(a5)
	ld t5, 376(a5)
	ld t6, 384(a5)
	ld a6, 392(a5)
	ld a7, 400(a5)
	ld s0, 768(a5)
	ld s4, 896(a5)
	ld s1, 784(a5)
	ld s5, 912(a5)
	ld s2, 800(a5)
	ld s6, 928(a5)
	ld s3, 816(a5)
	ld s7, 944(a5)
	srli t0, s0, 16
	xor t0, t0, s0
	and t0, t0, t3
	xor s0, s0, t0
	slli t0, t0, 16
	xor s0, s0, t0
	srli t0, s1, 16
	xor t0, t0, s1
	and t0, t0, t3
	xor s1, s1, t0
	slli t0, t0, 16
	xor s1, s1, t0
	srli t0, s2, 16
	xor t0, t0, s2
	and t0, t0, t3
	xor s2, s2, t0
	slli t0, t0, 16
	xor s2, s2, t0
	srli t0, s3, 16
	xor t0, t0, s3
	and t0, t0, t3
	xor s3, s3, t0
	slli t0, t0, 16
	xor s3, s3, t0
	srli t0, s4, 16
	xor t0, t0, s4
	and t0, t0, t3
	xor s4, s4, t0
	slli t0, t0, 16
	xor s4, s4, t0
	srli t0, s5, 16
	xor t0, t0, s5
	and t0, t0, t3
	xor s5, s5, t0
	slli t0, t0, 16
	xor s5, s5, t0
	srli t0, s6, 16
	xor t0, t0, s6
	and t0, t0, t3
	xor s6, s6, t0
	slli t0, t0, 16
	xor s6, s6, t0
	srli t0, s7, 16
	xor t0, t0, s7
	and t0, t0, t3
	xor s7, s7, t0
	slli t0, t0, 16
	xor s7, s7, t0
	srli t0, s0, 8
	xor t0, t0, s0
	and t0, t0, t4
	xor s0, s0, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s1
	and t0, t0, t4
	xor s1, s1, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s2
	and t0, t0, t4
	xor s2, s2, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s3
	and t0, t0, t4
	xor s3, s3, t0
	slli t0, t0, 8
	xor s3, s3, t0
	srli t0, s4, 8
	xor t0, t0, s4
	and t0, t0, t4
	xor s4, s4, t0
	slli t0, t0, 8
	xor s4, s4, t0
	srli t0, s5, 8
	xor t0, t0, s5
	and t0, t0, t4
	xor s5, s5, t0
	slli t0, t0, 8
	xor s5, s5, t0
	srli t0, s6, 8
	xor t0, t0, s6
	and t0, t0, t4
	xor s6, s6, t0
	slli t0, t0, 8
	xor s6, s6, t0
	srli t0, s7, 8
	xor t0, t0, s7
	and t0, t0, t4
	xor s7, s7, t0
	slli t0, t0, 8
	xor s7, s7, t0
	srli t0, s0, 8
	xor t0, t0, s4
	and t0, t0, t5
	xor s4, s4, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s5
	and t0, t0, t5
	xor s5, s5, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s6
	and t0, t0, t5
	xor s6, s6, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s7
	and t0, t0, t5
	xor s7, s7, t0
	slli t0, t0, 8
	xor s3, s3, t0
	sd s0, 768(a5)
	sd s4, 896(a5)
	sd s1, 784(a5)
	sd s5, 912(a5)
	sd s2, 800(a5)
	sd s6, 928(a5)
	sd s3, 816(a5)
	sd s7, 944(a5)
	ld s0, 832(a5)
	ld s4, 960(a5)
	ld s1, 848(a5)
	ld s5, 976(a5)
	ld s2, 864(a5)
	ld s6, 992(a5)
	ld s3, 880(a5)
	ld s7, 1008(a5)
	srli t0, s0, 16
	xor t0, t0, s0
	and t0, t0, t3
	xor s0, s0, t0
	slli t0, t0, 16
	xor s0, s0, t0
	srli t0, s1, 16
	xor t0, t0, s1
	and t0, t0, t3
	xor s1, s1, t0
	slli t0, t0, 16
	xor s1, s1, t0
	srli t0, s2, 16
	xor t0, t0, s2
	and t0, t0, t3
	xor s2, s2, t0
	slli t0, t0, 16
	xor s2, s2, t0
	srli t0, s3, 16
	xor t0, t0, s3
	and t0, t0, t3
	xor s3, s3, t0
	slli t0, t0, 16
	xor s3, s3, t0
	srli t0, s4, 16
	xor t0, t0, s4
	and t0, t0, t3
	xor s4, s4, t0
	slli t0, t0, 16
	xor s4, s4, t0
	srli t0, s5, 16
	xor t0, t0, s5
	and t0, t0, t3
	xor s5, s5, t0
	slli t0, t0, 16
	xor s5, s5, t0
	srli t0, s6, 16
	xor t0, t0, s6
	and t0, t0, t3
	xor s6, s6, t0
	slli t0, t0, 16
	xor s6, s6, t0
	srli t0, s7, 16
	xor t0, t0, s7
	and t0, t0, t3
	xor s7, s7, t0
	slli t0, t0, 16
	xor s7, s7, t0
	srli t0, s0, 8
	xor t0, t0, s0
	and t0, t0, t4
	xor s0, s0, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s1
	and t0, t0, t4
	xor s1, s1, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s2
	and t0, t0, t4
	xor s2, s2, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s3
	and t0, t0, t4
	xor s3, s3, t0
	slli t0, t0, 8
	xor s3, s3, t0
	srli t0, s4, 8
	xor t0, t0, s4
	and t0, t0, t4
	xor s4, s4, t0
	slli t0, t0, 8
	xor s4, s4, t0
	srli t0, s5, 8
	xor t0, t0, s5
	and t0, t0, t4
	xor s5, s5, t0
	slli t0, t0, 8
	xor s5, s5, t0
	srli t0, s6, 8
	xor t0, t0, s6
	and t0, t0, t4
	xor s6, s6, t0
	slli t0, t0, 8
	xor s6, s6, t0
	srli t0, s7, 8
	xor t0, t0, s7
	and t0, t0, t4
	xor s7, s7, t0
	slli t0, t0, 8
	xor s7, s7, t0
	srli t0, s0, 8
	xor t0, t0, s4
	and t0, t0, t5
	xor s4, s4, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s5
	and t0, t0, t5
	xor s5, s5, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s6
	and t0, t0, t5
	xor s6, s6, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s7
	and t0, t0, t5
	xor s7, s7, t0
	slli t0, t0, 8
	xor s3, s3, t0
	sd s0, 832(a5)
	sd s4, 960(a5)
	sd s1, 848(a5)
	sd s5, 976(a5)
	sd s2, 864(a5)
	sd s6, 992(a5)
	sd s3, 880(a5)
	sd s7, 1008(a5)
	ld s0, 776(a5)
	ld s4, 904(a5)
	ld s1, 792(a5)
	ld s5, 920(a5)
	ld s2, 808(a5)
	ld s6, 936(a5)
	ld s3, 824(a5)
	ld s7, 952(a5)
	srli t0, s0, 16
	xor t0, t0, s0
	and t0, t0, t3
	xor s0, s0, t0
	slli t0, t0, 16
	xor s0, s0, t0
	srli t0, s1, 16
	xor t0, t0, s1
	and t0, t0, t3
	xor s1, s1, t0
	slli t0, t0, 16
	xor s1, s1, t0
	srli t0, s2, 16
	xor t0, t0, s2
	and t0, t0, t3
	xor s2, s2, t0
	slli t0, t0, 16
	xor s2, s2, t0
	srli t0, s3, 16
	xor t0, t0, s3
	and t0, t0, t3
	xor s3, s3, t0
	slli t0, t0, 16
	xor s3, s3, t0
	srli t0, s4, 16
	xor t0, t0, s4
	and t0, t0, t3
	xor s4, s4, t0
	slli t0, t0, 16
	xor s4, s4, t0
	srli t0, s5, 16
	xor t0, t0, s5
	and t0, t0, t3
	xor s5, s5, t0
	slli t0, t0, 16
	xor s5, s5, t0
	srli t0, s6, 16
	xor t0, t0, s6
	and t0, t0, t3
	xor s6, s6, t0
	slli t0, t0, 16
	xor s6, s6, t0
	srli t0, s7, 16
	xor t0, t0, s7
	and t0, t0, t3
	xor s7, s7, t0
	slli t0, t0, 16
	xor s7, s7, t0
	srli t0, s0, 8
	xor t0, t0, s0
	and t0, t0, t4
	xor s0, s0, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s1
	and t0, t0, t4
	xor s1, s1, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s2
	and t0, t0, t4
	xor s2, s2, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s3
	and t0, t0, t4
	xor s3, s3, t0
	slli t0, t0, 8
	xor s3, s3, t0
	srli t0, s4, 8
	xor t0, t0, s4
	and t0, t0, t4
	xor s4, s4, t0
	slli t0, t0, 8
	xor s4, s4, t0
	srli t0, s5, 8
	xor t0, t0, s5
	and t0, t0, t4
	xor s5, s5, t0
	slli t0, t0, 8
	xor s5, s5, t0
	srli t0, s6, 8
	xor t0, t0, s6
	and t0, t0, t4
	xor s6, s6, t0
	slli t0, t0, 8
	xor s6, s6, t0
	srli t0, s7, 8
	xor t0, t0, s7
	and t0, t0, t4
	xor s7, s7, t0
	slli t0, t0, 8
	xor s7, s7, t0
	srli t0, s0, 8
	xor t0, t0, s4
	and t0, t0, t5
	xor s4, s4, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s5
	and t0, t0, t5
	xor s5, s5, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s6
	and t0, t0, t5
	xor s6, s6, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s7
	and t0, t0, t5
	xor s7, s7, t0
	slli t0, t0, 8
	xor s3, s3, t0
	sd s0, 776(a5)
	sd s4, 904(a5)
	sd s1, 792(a5)
	sd s5, 920(a5)
	sd s2, 808(a5)
	sd s6, 936(a5)
	sd s3, 824(a5)
	sd s7, 952(a5)
	ld s0, 840(a5)
	ld s4, 968(a5)
	ld s1, 856(a5)
	ld s5, 984(a5)
	ld s2, 872(a5)
	ld s6, 1000(a5)
	ld s3, 888(a5)
	ld s7, 1016(a5)
	srli t0, s0, 16
	xor t0, t0, s0
	and t0, t0, t3
	xor s0, s0, t0
	slli t0, t0, 16
	xor s0, s0, t0
	srli t0, s1, 16
	xor t0, t0, s1
	and t0, t0, t3
	xor s1, s1, t0
	slli t0, t0, 16
	xor s1, s1, t0
	srli t0, s2, 16
	xor t0, t0, s2
	and t0, t0, t3
	xor s2, s2, t0
	slli t0, t0, 16
	xor s2, s2, t0
	srli t0, s3, 16
	xor t0, t0, s3
	and t0, t0, t3
	xor s3, s3, t0
	slli t0, t0, 16
	xor s3, s3, t0
	srli t0, s4, 16
	xor t0, t0, s4
	and t0, t0, t3
	xor s4, s4, t0
	slli t0, t0, 16
	xor s4, s4, t0
	srli t0, s5, 16
	xor t0, t0, s5
	and t0, t0, t3
	xor s5, s5, t0
	slli t0, t0, 16
	xor s5, s5, t0
	srli t0, s6, 16
	xor t0, t0, s6
	and t0, t0, t3
	xor s6, s6, t0
	slli t0, t0, 16
	xor s6, s6, t0
	srli t0, s7, 16
	xor t0, t0, s7
	and t0, t0, t3
	xor s7, s7, t0
	slli t0, t0, 16
	xor s7, s7, t0
	srli t0, s0, 8
	xor t0, t0, s0
	and t0, t0, t4
	xor s0, s0, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s1
	and t0, t0, t4
	xor s1, s1, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s2
	and t0, t0, t4
	xor s2, s2, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s3
	and t0, t0, t4
	xor s3, s3, t0
	slli t0, t0, 8
	xor s3, s3, t0
	srli t0, s4, 8
	xor t0, t0, s4
	and t0, t0, t4
	xor s4, s4, t0
	slli t0, t0, 8
	xor s4, s4, t0
	srli t0, s5, 8
	xor t0, t0, s5
	and t0, t0, t4
	xor s5, s5, t0
	slli t0, t0, 8
	xor s5, s5, t0
	srli t0, s6, 8
	xor t0, t0, s6
	and t0, t0, t4
	xor s6, s6, t0
	slli t0, t0, 8
	xor s6, s6, t0
	srli t0, s7, 8
	xor t0, t0, s7
	and t0, t0, t4
	xor s7, s7, t0
	slli t0, t0, 8
	xor s7, s7, t0
	srli t0, s0, 8
	xor t0, t0, s4
	and t0, t0, t5
	xor s4, s4, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s5
	and t0, t0, t5
	xor s5, s5, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s6
	and t0, t0, t5
	xor s6, s6, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s7
	and t0, t0, t5
	xor s7, s7, t0
	slli t0, t0, 8
	xor s3, s3, t0
	sd s0, 840(a5)
	sd s4, 968(a5)
	sd s1, 856(a5)
	sd s5, 984(a5)
	sd s2, 872(a5)
	sd s6, 1000(a5)
	sd s3, 888(a5)
	sd s7, 1016(a5)
	ld s0, 768(a5)
	ld s1, 784(a5)
	ld s2, 800(a5)
	ld s3, 816(a5)
	ld s4, 832(a5)
	ld s5, 848(a5)
	ld s6, 864(a5)
	ld s7, 880(a5)
	srli t0, s0, 1
	xor t0, t0, s1
	and t0, t0, t6
	xor s1, s1, t0
	slli t0, t0, 1
	xor s0, s0, t0
	srli t0, s2, 1
	xor t0, t0, s3
	and t0, t0, t6
	xor s3, s3, t0
	slli t0, t0, 1
	xor s2, s2, t0
	srli t0, s4, 1
	xor t0, t0, s5
	and t0, t0, t6
	xor s5, s5, t0
	slli t0, t0, 1
	xor s4, s4, t0
	srli t0, s6, 1
	xor t0, t0, s7
	and t0, t0, t6
	xor s7, s7, t0
	slli t0, t0, 1
	xor s6, s6, t0
	srli t0, s0, 2
	xor t0, t0, s2
	and t0, t0, a6
	xor s2, s2, t0
	slli t0, t0, 2
	xor s0, s0, t0
	srli t0, s1, 2
	xor t0, t0, s3
	and t0, t0, a6
	xor s3, s3, t0
	slli t0, t0, 2
	xor s1, s1, t0
	srli t0, s4, 2
	xor t0, t0, s6
	and t0, t0, a6
	xor s6, s6, t0
	slli t0, t0, 2
	xor s4, s4, t0
	srli t0, s5, 2
	xor t0, t0, s7
	and t0, t0, a6
	xor s7, s7, t0
	slli t0, t0, 2
	xor s5, s5, t0
	srli t0, s0, 4
	xor t0, t0, s4
	and t0, t0, a7
	xor s4, s4, t0
	slli t0, t0, 4
	xor s0, s0, t0
	srli t0, s1, 4
	xor t0, t0, s5
	and t0, t0, a7
	xor s5, s5, t0
	slli t0, t0, 4
	xor s1, s1, t0
	srli t0, s2, 4
	xor t0, t0, s6
	and t0, t0, a7
	xor s6, s6, t0
	slli t0, t0, 4
	xor s2, s2, t0
	srli t0, s3, 4
	xor t0, t0, s7
	and t0, t0, a7
	xor s7, s7, t0
	slli t0, t0, 4
	xor s3, s3, t0
	sd s0, 512(a5)
	sd s1, 520(a5)
	sd s2, 528(a5)
	sd s3, 536(a5)
	sd s4, 544(a5)
	sd s5, 552(a5)
	sd s6, 560(a5)
	sd s7, 568(a5)
	ld s0, 896(a5)
	ld s1, 912(a5)
	ld s2, 928(a5)
	ld s3, 944(a5)
	ld s4, 960(a5)
	ld s5, 976(a5)
	ld s6, 992(a5)
	ld s7, 1008(a5)
	srli t0, s0, 1
	xor t0, t0, s1
	and t0, t0, t6
	xor s1, s1, t0
	slli t0, t0, 1
	xor s0, s0, t0
	srli t0, s2, 1
	xor t0, t0, s3
	and t0, t0, t6
	xor s3, s3, t0
	slli t0, t0, 1
	xor s2, s2, t0
	srli t0, s4, 1
	xor t0, t0, s5
	and t0, t0, t6
	xor s5, s5, t0
	slli t0, t0, 1
	xor s4, s4, t0
	srli t0, s6, 1
	xor t0, t0, s7
	and t0, t0, t6
	xor s7, s7, t0
	slli t0, t0, 1
	xor s6, s6, t0
	srli t0, s0, 2
	xor t0, t0, s2
	and t0, t0, a6
	xor s2, s2, t0
	slli t0, t0, 2
	xor s0, s0, t0
	srli t0, s1, 2
	xor t0, t0, s3
	and t0, t0, a6
	xor s3, s3, t0
	slli t0, t0, 2
	xor s1, s1, t0
	srli t0, s4, 2
	xor t0, t0, s6
	and t0, t0, a6
	xor s6, s6, t0
	slli t0, t0, 2
	xor s4, s4, t0
	srli t0, s5, 2
	xor t0, t0, s7
	and t0, t0, a6
	xor s7, s7, t0
	slli t0, t0, 2
	xor s5, s5, t0
	srli t0, s0, 4
	xor t0, t0, s4
	and t0, t0, a7
	xor s4, s4, t0
	slli t0, t0, 4
	xor s0, s0, t0
	srli t0, s1, 4
	xor t0, t0, s5
	and t0, t0, a7
	xor s5, s5, t0
	slli t0, t0, 4
	xor s1, s1, t0
	srli t0, s2, 4
	xor t0, t0, s6
	and t0, t0, a7
	xor s6, s6, t0
	slli t0, t0, 4
	xor s2, s2, t0
	srli t0, s3, 4
	xor t0, t0, s7
	and t0, t0, a7
	xor s7, s7, t0
	slli t0, t0, 4
	xor s3, s3, t0
	sd s0, 576(a5)
	sd s1, 584(a5)
	sd s2, 592(a5)
	sd s3, 600(a5)
	sd s4, 608(a5)
	sd s5, 616(a5)
	sd s6, 624(a5)
	sd s7, 632(a5)
	ld s0, 776(a5)
	ld s1, 792(a5)
	ld s2, 808(a5)
	ld s3, 824(a5)
	ld s4, 840(a5)
	ld s5, 856(a5)
	ld s6, 872(a5)
	ld s7, 888(a5)
	srli t0, s0, 1
	xor t0, t0, s1
	and t0, t0, t6
	xor s1, s1, t0
	slli t0, t0, 1
	xor s0, s0, t0
	srli t0, s2, 1
	xor t0, t0, s3
	and t0, t0, t6
	xor s3, s3, t0
	slli t0, t0, 1
	xor s2, s2, t0
	srli t0, s4, 1
	xor t0, t0, s5
	and t0, t0, t6
	xor s5, s5, t0
	slli t0, t0, 1
	xor s4, s4, t0
	srli t0, s6, 1
	xor t0, t0, s7
	and t0, t0, t6
	xor s7, s7, t0
	slli t0, t0, 1
	xor s6, s6, t0
	srli t0, s0, 2
	xor t0, t0, s2
	and t0, t0, a6
	xor s2, s2, t0
	slli t0, t0, 2
	xor s0, s0, t0
	srli t0, s1, 2
	xor t0, t0, s3
	and t0, t0, a6
	xor s3, s3, t0
	slli t0, t0, 2
	xor s1, s1, t0
	srli t0, s4, 2
	xor t0, t0, s6
	and t0, t0, a6
	xor s6, s6, t0
	slli t0, t0, 2
	xor s4, s4, t0
	srli t0, s5, 2
	xor t0, t0, s7
	and t0, t0, a6
	xor s7, s7, t0
	slli t0, t0, 2
	xor s5, s5, t0
	srli t0, s0, 4
	xor t0, t0, s4
	and t0, t0, a7
	xor s4, s4, t0
	slli t0, t0, 4
	xor s0, s0, t0
	srli t0, s1, 4
	xor t0, t0, s5
	and t0, t0, a7
	xor s5, s5, t0
	slli t0, t0, 4
	xor s1, s1, t0
	srli t0, s2, 4
	xor t0, t0, s6
	and t0, t0, a7
	xor s6, s6, t0
	slli t0, t0, 4
	xor s2, s2, t0
	srli t0, s3, 4
	xor t0, t0, s7
	and t0, t0, a7
	xor s7, s7, t0
	slli t0, t0, 4
	xor s3, s3, t0
	sd s0, 640(a5)
	sd s1, 648(a5)
	sd s2, 656(a5)
	sd s3, 664(a5)
	sd s4, 672(a5)
	sd s5, 680(a5)
	sd s6, 688(a5)
	sd s7, 696(a5)
	ld s0, 904(a5)
	ld s1, 920(a5)
	ld s2, 936(a5)
	ld s3, 952(a5)
	ld s4, 968(a5)
	ld s5, 984(a5)
	ld s6, 1000(a5)
	ld s7, 1016(a5)
	srli t0, s0, 1
	xor t0, t0, s1
	and t0, t0, t6
	xor s1, s1, t0
	slli t0, t0, 1
	xor s0, s0, t0
	srli t0, s2, 1
	xor t0, t0, s3
	and t0, t0, t6
	xor s3, s3, t0
	slli t0, t0, 1
	xor s2, s2, t0
	srli t0, s4, 1
	xor t0, t0, s5
	and t0, t0, t6
	xor s5, s5, t0
	slli t0, t0, 1
	xor s4, s4, t0
	srli t0, s6, 1
	xor t0, t0, s7
	and t0, t0, t6
	xor s7, s7, t0
	slli t0, t0, 1
	xor s6, s6, t0
	srli t0, s0, 2
	xor t0, t0, s2
	and t0, t0, a6
	xor s2, s2, t0
	slli t0, t0, 2
	xor s0, s0, t0
	srli t0, s1, 2
	xor t0, t0, s3
	and t0, t0, a6
	xor s3, s3, t0
	slli t0, t0, 2
	xor s1, s1, t0
	srli t0, s4, 2
	xor t0, t0, s6
	and t0, t0, a6
	xor s6, s6, t0
	slli t0, t0, 2
	xor s4, s4, t0
	srli t0, s5, 2
	xor t0, t0, s7
	and t0, t0, a6
	xor s7, s7, t0
	slli t0, t0, 2
	xor s5, s5, t0
	srli t0, s0, 4
	xor t0, t0, s4
	and t0, t0, a7
	xor s4, s4, t0
	slli t0, t0, 4
	xor s0, s0, t0
	srli t0, s1, 4
	xor t0, t0, s5
	and t0, t0, a7
	xor s5, s5, t0
	slli t0, t0, 4
	xor s1, s1, t0
	srli t0, s2, 4
	xor t0, t0, s6
	and t0, t0, a7
	xor s6, s6, t0
	slli t0, t0, 4
	xor s2, s2, t0
	srli t0, s3, 4
	xor t0, t0, s7
	and t0, t0, a7
	xor s7, s7, t0
	slli t0, t0, 4
	xor s3, s3, t0
	sd s0, 704(a5)
	sd s1, 712(a5)
	sd s2, 720(a5)
	sd s3, 728(a5)
	sd s4, 736(a5)
	sd s5, 744(a5)
	sd s6, 752(a5)
	sd s7, 760(a5)
	addi a3, a5, 1024
27:
	ld s0, 576(a5)
	ld t0, 640(a5)
	xor s0, s0, t0
	ld t0, 704(a5)
	xor s0, s0, t0
	ld t0, 0(a3)
	xor s0, s0, t0
	ld s1, 584(a5)
	ld t0, 648(a5)
	xor s1, s1, t0
	ld t0, 712(a5)
	xor s1, s1, t0
	ld t0, 8(a3)
	xor s1, s1, t0
	ld s2, 592(a5)
	ld t0, 656(a5)
	xor s2, s2, t0
	ld t0, 720(a5)
	xor s2, s2, t0
	ld t0, 16(a3)
	xor s2, s2, t0
	ld s3, 600(a5)
	ld t0, 664(a5)
	xor s3, s3, t0
	ld t0, 728(a5)
	xor s3, s3, t0
	ld t0, 24(a3)
	xor s3, s3, t0
	ld s4, 608(a5)
	ld t0, 672(a5)
	xor s4, s4, t0
	ld t0, 736(a5)
	xor s4, s4, t0
	ld t0, 32(a3)
	xor s4, s4, t0
	ld s5, 616(a5)
	ld t0, 680(a5)
	xor s5, s5, t0
	ld t0, 744(a5)
	xor s5, s5, t0
	ld t0, 40(a3)
	xor s5, s5, t0
	ld s6, 624(a5)
	ld t0, 688(a5)
	xor s6, s6, t0
	ld t0, 752(a5)
	xor s6, s6, t0
	ld t0, 48(a3)
	xor s6, s6, t0
	ld s7, 632(a5)
	ld t0, 696(a5)
	xor s7, s7, t0
	ld t0, 760(a5)
	xor s7, s7, t0
	ld t0, 56(a3)
	xor s7, s7, t0
	xor t0, s4, s2
	xor t1, s3, s0
	xor t2, s1, t1
	xor t3, s7, t0
	xor t4, s5, t2
	xor t5, s6, s2
	xor s4, s7, s4
	xor t6, s5, t3
	xor a6, s6, t6
	xor a7, s7, s3
	xor s8, s6, s4
	xor s9, s5, t0
	xor t6, s1, t6
	xori t6, t6, -1
	xor s10, t1, t3
	xor s11, s0, s8
	xor s8, t4, s8
	sd s8, 0(a5)
	xor s8, s1, t5
	xor s6, s6, s10
	xor s0, s0, t3
	xori s0, s0, -1
	xor s10, s1, a7
	xor s3, s3, s9
	xori s3, s3, -1
	xor s4, t2, s4
	sd t3, 8(a5)
	xor t3, t0, t4
	sd t3, 16(a5)
	xor t3, t4, t5
	xor s2, s7, s2
	xori s2, s2, -1
	xor s11, s1, s11
	xori s11, s11, -1
	xor t1, t1, s9
	xor s5, s5, a7
	xori s5, s5, -1
	xor a7, s1, a6
	xor t0, t0, t2
	xori t0, t0, -1
	xor s7, s7, t2
	xori s7, s7, -1
	and t2, a7, t6
	and s9, t4, s3
	xor s9, s9, t2
	sd t4, 24(a5)
	and t4, s6, s10
	xor t4, t4, t2
	and t2, s1, t1
	sd s1, 32(a5)
	and s1, t5, s5
	xor s1, s1, t2
	sd t5, 40(a5)
	and t5, s8, s0
	xor t5, t5, t2
	and t2, s4, t0
	sd s4, 48(a5)
	and s4, a6, s7
	xor s4, s4, t2
	sd a6, 56(a5)
	ld a6, 8(a5)
	sd s8, 64(a5)
	and s8, t3, a6
	xor s8, s8, t2
	xor s9, s9, s4
	xor t4, t4, s8
	xor s1, s1, s4
	xor t5, t5, s8
	xor s9, s9, s2
	ld s2, 0(a5)
	xor t4, t4, s2
	ld s2, 16(a5)
	xor s1, s1, s2
	xor t5, t5, s11
	xor s11, s9, t4
	and s9, s9, s1
	xor s2, t5, s9
	and s8, s11, s2
	xor s8, s8, t4
	xor s4, s1, t5
	xor t4, t4, s9
	and t4, t4, s4
	xor t4, t4, t5
	xor s1, s1, t4
	xor s4, s2, t4
	and t5, t5, s4
	xor s1, t5, s1
	xor s2, s2, t5
	and s2, s8, s2
	xor s11, s11, s2
	xor s2, s11, s1
	xor t5, s8, t4
	xor s4, s8, s11
	xor s9, t4, s1
	xor t2, t5, s2
	and t6, s9, t6
	and s3, s1, s3
	and s10, t4, s10
	and t1, s4, t1
	and s5, s11, s5
	and s0, s8, s0
	and t0, t5, t0
	and s7, t2, s7
	and a6, s2, a6
	and s9, s9, a7
	ld a7, 24(a5)
	and s1, s1, a7
	and t4, t4, s6
	ld s6, 32(a5)
	and s4, s4, s6
	ld s6, 40(a5)
	and s11, s11, s6
	ld s6, 64(a5)
	and s8, s8, s6
	ld s6, 48(a5)
	and t5, t5, s6
	ld s6, 56(a5)
	and t2, t2, s6
	and s2, s2, t3
	xor s9, s9, t5
	xor t0, t0, s1
	xor s0, t6, s0
	xor t3, s11, t0
	xor s8, s8, t3
	xor a6, s3, a6
	xor t3, s7, s8
	xor s2, s2, s9
	xor s6, s5, s0
	xor a7, t3, s2
	sd s5, 56(a5)
	xor s5, t4, s6
	sd a7, 48(a5)
	xor a7, t2, a6
	xor s9, s9, a7
	xor s0, t1, s0
	xor s0, s9, s0
	xor t4, t4, s2
	xor s11, s11, t2
	xor s4, s4, t5
	xor t0, t0, s6
	xor a6, a6, s5
	xor s8, s8, a6
	xori s8, s8, -1
	xor s1, s1, s0
	xor s10, s10, t3
	xor s0, s7, s1
	xori s0, s0, -1
	xor s7, s11, s4
	xori s7, s7, -1
	xor t6, t6, s3
	ld s3, 48(a5)
	xor t1, t1, s3
	xor s3, s3, t6
	xor s6, s5, s10
	xori s6, s6, -1
	ld s10, 56(a5)
	xor s2, s10, t1
	xor s4, s9, t0
	xori s4, s4, -1
	addi s5, s3, 0
	addi s3, t4, 0
	addi s1, s8, 0
	srli a7, s6, 16
	slli t2, s6, 48
	xor t2, t2, a7
	srli a7, t2, 16
	slli t1, t2, 48
	xor t1, t1, a7
	xor t0, t2, t1
	srli a7, t2, 32
	slli t1, t2, 32
	xor t1, t1, a7
	xor t0, t0, t1
	xor t0, t0, s0
	srli a7, s0, 48
	slli t1, s0, 16
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 512(a5)
	xor t0, t0, t1
	sd t0, 512(a5)
	srli a7, s7, 16
	slli t2, s7, 48
	xor t2, t2, a7
	srli a7, t2, 16
	slli t1, t2, 48
	xor t1, t1, a7
	xor t0, t2, t1
	srli a7, t2, 32
	slli t1, t2, 32
	xor t1, t1, a7
	xor t0, t0, t1
	xor t0, t0, s1
	srli a7, s1, 48
	slli t1, s1, 16
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 520(a5)
	xor t0, t0, t1
	sd t0, 520(a5)
	srli a7, s0, 16
	slli t1, s0, 48
	xor t1, t1, a7
	xor t0, s0, t1
	srli a7, s0, 32
	slli t1, s0, 32
	xor t1, t1, a7
	xor t0, t0, t1
	xor t0, t0, s2
	srli a7, s2, 48
	slli t1, s2, 16
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 528(a5)
	xor t0, t0, t1
	sd t0, 528(a5)
	srli a7, s1, 16
	slli t1, s1, 48
	xor t1, t1, a7
	xor t0, s1, t1
	srli a7, s1, 32
	slli t1, s1, 32
	xor t1, t1, a7
	xor t0, t0, t1
	xor t0, t0, s3
	srli a7, s3, 48
	slli t1, s3, 16
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 536(a5)
	xor t0, t0, t1
	sd t0, 536(a5)
	srli a7, s2, 16
	slli t1, s2, 48
	xor t1, t1, a7
	xor t0, s2, t1
	srli a7, s2, 32
	slli t1, s2, 32
	xor t1, t1, a7
	xor t0, t0, t1
	xor t0, t0, s4
	srli a7, s4, 48
	slli t1, s4, 16
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 544(a5)
	xor t0, t0, t1
	sd t0, 544(a5)
	srli a7, s3, 16
	slli t1, s3, 48
	xor t1, t1, a7
	xor t0, s3, t1
	srli a7, s3, 32
	slli t1, s3, 32
	xor t1, t1, a7
	xor t0, t0, t1
	xor t0, t0, s5
	srli a7, s5, 48
	slli t1, s5, 16
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 552(a5)
	xor t0, t0, t1
	sd t0, 552(a5)
	srli a7, s4, 16
	slli t1, s4, 48
	xor t1, t1, a7
	xor t0, s4, t1
	srli a7, s4, 32
	slli t1, s4, 32
	xor t1, t1, a7
	xor t0, t0, t1
	xor t0, t0, s6
	srli a7, s6, 48
	slli t1, s6, 16
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 560(a5)
	xor t0, t0, t1
	sd t0, 560(a5)
	srli a7, s5, 16
	slli t1, s5, 48
	xor t1, t1, a7
	xor t0, s5, t1
	srli a7, s5, 32
	slli t1, s5, 32
	xor t1, t1, a7
	xor t0, t0, t1
	xor t0, t0, s7
	srli a7, s7, 48
	slli t1, s7, 16
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 568(a5)
	xor t0, t0, t1
	sd t0, 568(a5)
	ld s0, 640(a5)
	ld t0, 704(a5)
	xor s0, s0, t0
	ld t0, 512(a5)
	xor s0, s0, t0
	ld t0, 64(a3)
	xor s0, s0, t0
	ld s1, 648(a5)
	ld t0, 712(a5)
	xor s1, s1, t0
	ld t0, 520(a5)
	xor s1, s1, t0
	ld t0, 72(a3)
	xor s1, s1, t0
	ld s2, 656(a5)
	ld t0, 720(a5)
	xor s2, s2, t0
	ld t0, 528(a5)
	xor s2, s2, t0
	ld t0, 80(a3)
	xor s2, s2, t0
	ld s3, 664(a5)
	ld t0, 728(a5)
	xor s3, s3, t0
	ld t0, 536(a5)
	xor s3, s3, t0
	ld t0, 88(a3)
	xor s3, s3, t0
	ld s4, 672(a5)
	ld t0, 736(a5)
	xor s4, s4, t0
	ld t0, 544(a5)
	xor s4, s4, t0
	ld t0, 96(a3)
	xor s4, s4, t0
	ld s5, 680(a5)
	ld t0, 744(a5)
	xor s5, s5, t0
	ld t0, 552(a5)
	xor s5, s5, t0
	ld t0, 104(a3)
	xor s5, s5, t0
	ld s6, 688(a5)
	ld t0, 752(a5)
	xor s6, s6, t0
	ld t0, 560(a5)
	xor s6, s6, t0
	ld t0, 112(a3)
	xor s6, s6, t0
	ld s7, 696(a5)
	ld t0, 760(a5)
	xor s7, s7, t0
	ld t0, 568(a5)
	xor s7, s7, t0
	ld t0, 120(a3)
	xor s7, s7, t0
	xor t0, s4, s2
	xor t1, s3, s0
	xor t2, s1, t1
	xor t3, s7, t0
	xor t4, s5, t2
	xor t5, s6, s2
	xor s4, s7, s4
	xor t6, s5, t3
	xor a6, s6, t6
	xor a7, s7, s3
	xor s8, s6, s4
	xor s9, s5, t0
	xor t6, s1, t6
	xori t6, t6, -1
	xor s10, t1, t3
	xor s11, s0, s8
	xor s8, t4, s8
	sd s8, 0(a5)
	xor s8, s1, t5
	xor s6, s6, s10
	xor s0, s0, t3
	xori s0, s0, -1
	xor s10, s1, a7
	xor s3, s3, s9
	xori s3, s3, -1
	xor s4, t2, s4
	sd t3, 8(a5)
	xor t3, t0, t4
	sd t3, 16(a5)
	xor t3, t4, t5
	xor s2, s7, s2
	xori s2, s2, -1
	xor s11, s1, s11
	xori s11, s11, -1
	xor t1, t1, s9
	xor s5, s5, a7
	xori s5, s5, -1
	xor a7, s1, a6
	xor t0, t0, t2
	xori t0, t0, -1
	xor s7, s7, t2
	xori s7, s7, -1
	and t2, a7, t6
	and s9, t4, s3
	xor s9, s9, t2
	sd t4, 24(a5)
	and t4, s6, s10
	xor t4, t4, t2
	and t2, s1, t1
	sd s1, 32(a5)
	and s1, t5, s5
	xor s1, s1, t2
	sd t5, 40(a5)
	and t5, s8, s0
	xor t5, t5, t2
	and t2, s4, t0
	sd s4, 48(a5)
	and s4, a6, s7
	xor s4, s4, t2
	sd a6, 56(a5)
	ld a6, 8(a5)
	sd s8, 64(a5)
	and s8, t3, a6
	xor s8, s8, t2
	xor s9, s9, s4
	xor t4, t4, s8
	xor s1, s1, s4
	xor t5, t5, s8
	xor s9, s9, s2
	ld s2, 0(a5)
	xor t4, t4, s2
	ld s2, 16(a5)
	xor s1, s1, s2
	xor t5, t5, s11
	xor s11, s9, t4
	and s9, s9, s1
	xor s2, t5, s9
	and s8, s11, s2
	xor s8, s8, t4
	xor s4, s1, t5
	xor t4, t4, s9
	and t4, t4, s4
	xor t4, t4, t5
	xor s1, s1, t4
	xor s4, s2, t4
	and t5, t5, s4
	xor s1, t5, s1
	xor s2, s2, t5
	and s2, s8, s2
	xor s11, s11, s2
	xor s2, s11, s1
	xor t5, s8, t4
	xor s4, s8, s11
	xor s9, t4, s1
	xor t2, t5, s2
	and t6, s9, t6
	and s3, s1, s3
	and s10, t4, s10
	and t1, s4, t1
	and s5, s11, s5
	and s0, s8, s0
	and t0, t5, t0
	and s7, t2, s7
	and a6, s2, a6
	and s9, s9, a7
	ld a7, 24(a5)
	and s1, s1, a7
	and t4, t4, s6
	ld s6, 32(a5)
	and s4, s4, s6
	ld s6, 40(a5)
	and s11, s11, s6
	ld s6, 64(a5)
	and s8, s8, s6
	ld s6, 48(a5)
	and t5, t5, s6
	ld s6, 56(a5)
	and t2, t2, s6
	and s2, s2, t3
	xor s9, s9, t5
	xor t0, t0, s1
	xor s0, t6, s0
	xor t3, s11, t0
	xor s8, s8, t3
	xor a6, s3, a6
	xor t3, s7, s8
	xor s2, s2, s9
	xor s6, s5, s0
	xor a7, t3, s2
	sd s5, 56(a5)
	xor s5, t4, s6
	sd a7, 48(a5)
	xor a7, t2, a6
	xor s9, s9, a7
	xor s0, t1, s0
	xor s0, s9, s0
	xor t4, t4, s2
	xor s11, s11, t2
	xor s4, s4, t5
	xor t0, t0, s6
	xor a6, a6, s5
	xor s8, s8, a6
	xori s8, s8, -1
	xor s1, s1, s0
	xor s10, s10, t3
	xor s0, s7, s1
	xori s0, s0, -1
	xor s7, s11, s4
	xori s7, s7, -1
	xor t6, t6, s3
	ld s3, 48(a5)
	xor t1, t1, s3
	xor s3, s3, t6
	xor s6, s5, s10
	xori s6, s6, -1
	ld s10, 56(a5)
	xor s2, s10, t1
	xor s4, s9, t0
	xori s4, s4, -1
	addi s5, s3, 0
	addi s3, t4, 0
	addi s1, s8, 0
	srli a7, s6, 16
	slli t2, s6, 48
	xor t2, t2, a7
	srli a7, t2, 16
	slli t1, t2, 48
	xor t1, t1, a7
	xor t0, t2, t1
	srli a7, t2, 32
	slli t1, t2, 32
	xor t1, t1, a7
	xor t0, t0, t1
	xor t0, t0, s0
	srli a7, s0, 48
	slli t1, s0, 16
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 576(a5)
	xor t0, t0, t1
	sd t0, 576(a5)
	srli a7, s7, 16
	slli t2, s7, 48
	xor t2, t2, a7
	srli a7, t2, 16
	slli t1, t2, 48
	xor t1, t1, a7
	xor t0, t2, t1
	srli a7, t2, 32
	slli t1, t2, 32
	xor t1, t1, a7
	xor t0, t0, t1
	xor t0, t0, s1
	srli a7, s1, 48
	slli t1, s1, 16
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 584(a5)
	xor t0, t0, t1
	sd t0, 584(a5)
	srli a7, s0, 16
	slli t1, s0, 48
	xor t1, t1, a7
	xor t0, s0, t1
	srli a7, s0, 32
	slli t1, s0, 32
	xor t1, t1, a7
	xor t0, t0, t1
	xor t0, t0, s2
	srli a7, s2, 48
	slli t1, s2, 16
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 592(a5)
	xor t0, t0, t1
	sd t0, 592(a5)
	srli a7, s1, 16
	slli t1, s1, 48
	xor t1, t1, a7
	xor t0, s1, t1
	srli a7, s1, 32
	slli t1, s1, 32
	xor t1, t1, a7
	xor t0, t0, t1
	xor t0, t0, s3
	srli a7, s3, 48
	slli t1, s3, 16
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 600(a5)
	xor t0, t0, t1
	sd t0, 600(a5)
	srli a7, s2, 16
	slli t1, s2, 48
	xor t1, t1, a7
	xor t0, s2, t1
	srli a7, s2, 32
	slli t1, s2, 32
	xor t1, t1, a7
	xor t0, t0, t1
	xor t0, t0, s4
	srli a7, s4, 48
	slli t1, s4, 16
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 608(a5)
	xor t0, t0, t1
	sd t0, 608(a5)
	srli a7, s3, 16
	slli t1, s3, 48
	xor t1, t1, a7
	xor t0, s3, t1
	srli a7, s3, 32
	slli t1, s3, 32
	xor t1, t1, a7
	xor t0, t0, t1
	xor t0, t0, s5
	srli a7, s5, 48
	slli t1, s5, 16
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 616(a5)
	xor t0, t0, t1
	sd t0, 616(a5)
	srli a7, s4, 16
	slli t1, s4, 48
	xor t1, t1, a7
	xor t0, s4, t1
	srli a7, s4, 32
	slli t1, s4, 32
	xor t1, t1, a7
	xor t0, t0, t1
	xor t0, t0, s6
	srli a7, s6, 48
	slli t1, s6, 16
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 624(a5)
	xor t0, t0, t1
	sd t0, 624(a5)
	srli a7, s5, 16
	slli t1, s5, 48
	xor t1, t1, a7
	xor t0, s5, t1
	srli a7, s5, 32
	slli t1, s5, 32
	xor t1, t1, a7
	xor t0, t0, t1
	xor t0, t0, s7
	srli a7, s7, 48
	slli t1, s7, 16
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 632(a5)
	xor t0, t0, t1
	sd t0, 632(a5)
	ld s0, 704(a5)
	ld t0, 512(a5)
	xor s0, s0, t0
	ld t0, 576(a5)
	xor s0, s0, t0
	ld t0, 128(a3)
	xor s0, s0, t0
	ld s1, 712(a5)
	ld t0, 520(a5)
	xor s1, s1, t0
	ld t0, 584(a5)
	xor s1, s1, t0
	ld t0, 136(a3)
	xor s1, s1, t0
	ld s2, 720(a5)
	ld t0, 528(a5)
	xor s2, s2, t0
	ld t0, 592(a5)
	xor s2, s2, t0
	ld t0, 144(a3)
	xor s2, s2, t0
	ld s3, 728(a5)
	ld t0, 536(a5)
	xor s3, s3, t0
	ld t0, 600(a5)
	xor s3, s3, t0
	ld t0, 152(a3)
	xor s3, s3, t0
	ld s4, 736(a5)
	ld t0, 544(a5)
	xor s4, s4, t0
	ld t0, 608(a5)
	xor s4, s4, t0
	ld t0, 160(a3)
	xor s4, s4, t0
	ld s5, 744(a5)
	ld t0, 552(a5)
	xor s5, s5, t0
	ld t0, 616(a5)
	xor s5, s5, t0
	ld t0, 168(a3)
	xor s5, s5, t0
	ld s6, 752(a5)
	ld t0, 560(a5)
	xor s6, s6, t0
	ld t0, 624(a5)
	xor s6, s6, t0
	ld t0, 176(a3)
	xor s6, s6, t0
	ld s7, 760(a5)
	ld t0, 568(a5)
	xor s7, s7, t0
	ld t0, 632(a5)
	xor s7, s7, t0
	ld t0, 184(a3)
	xor s7, s7, t0
	xor t0, s4, s2
	xor t1, s3, s0
	xor t2, s1, t1
	xor t3, s7, t0
	xor t4, s5, t2
	xor t5, s6, s2
	xor s4, s7, s4
	xor t6, s5, t3
	xor a6, s6, t6
	xor a7, s7, s3
	xor s8, s6, s4
	xor s9, s5, t0
	xor t6, s1, t6
	xori t6, t6, -1
	xor s10, t1, t3
	xor s11, s0, s8
	xor s8, t4, s8
	sd s8, 0(a5)
	xor s8, s1, t5
	xor s6, s6, s10
	xor s0, s0, t3
	xori s0, s0, -1
	xor s10, s1, a7
	xor s3, s3, s9
	xori s3, s3, -1
	xor s4, t2, s4
	sd t3, 8(a5)
	xor t3, t0, t4
	sd t3, 16(a5)
	xor t3, t4, t5
	xor s2, s7, s2
	xori s2, s2, -1
	xor s11, s1, s11
	xori s11, s11, -1
	xor t1, t1, s9
	xor s5, s5, a7
	xori s5, s5, -1
	xor a7, s1, a6
	xor t0, t0, t2
	xori t0, t0, -1
	xor s7, s7, t2
	xori s7, s7, -1
	and t2, a7, t6
	and s9, t4, s3
	xor s9, s9, t2
	sd t4, 24(a5)
	and t4, s6, s10
	xor t4, t4, t2
	and t2, s1, t1
	sd s1, 32(a5)
	and s1, t5, s5
	xor s1, s1, t2
	sd t5, 40(a5)
	and t5, s8, s0
	xor t5, t5, t2
	and t2, s4, t0
	sd s4, 48(a5)
	and s4, a6, s7
	xor s4, s4, t2
	sd a6, 56(a5)
	ld a6, 8(a5)
	sd s8, 64(a5)
	and s8, t3, a6
	xor s8, s8, t2
	xor s9, s9, s4
	xor t4, t4, s8
	xor s1, s1, s4
	xor t5, t5, s8
	xor s9, s9, s2
	ld s2, 0(a5)
	xor t4, t4, s2
	ld s2, 16(a5)
	xor s1, s1, s2
	xor t5, t5, s11
	xor s11, s9, t4
	and s9, s9, s1
	xor s2, t5, s9
	and s8, s11, s2
	xor s8, s8, t4
	xor s4, s1, t5
	xor t4, t4, s9
	and t4, t4, s4
	xor t4, t4, t5
	xor s1, s1, t4
	xor s4, s2, t4
	and t5, t5, s4
	xor s1, t5, s1
	xor s2, s2, t5
	and s2, s8, s2
	xor s11, s11, s2
	xor s2, s11, s1
	xor t5, s8, t4
	xor s4, s8, s11
	xor s9, t4, s1
	xor t2, t5, s2
	and t6, s9, t6
	and s3, s1, s3
	and s10, t4, s10
	and t1, s4, t1
	and s5, s11, s5
	and s0, s8, s0
	and t0, t5, t0
	and s7, t2, s7
	and a6, s2, a6
	and s9, s9, a7
	ld a7, 24(a5)
	and s1, s1, a7
	and t4, t4, s6
	ld s6, 32(a5)
	and s4, s4, s6
	ld s6, 40(a5)
	and s11, s11, s6
	ld s6, 64(a5)
	and s8, s8, s6
	ld s6, 48(a5)
	and t5, t5, s6
	ld s6, 56(a5)
	and t2, t2, s6
	and s2, s2, t3
	xor s9, s9, t5
	xor t0, t0, s1
	xor s0, t6, s0
	xor t3, s11, t0
	xor s8, s8, t3
	xor a6, s3, a6
	xor t3, s7, s8
	xor s2, s2, s9
	xor s6, s5, s0
	xor a7, t3, s2
	sd s5, 56(a5)
	xor s5, t4, s6
	sd a7, 48(a5)
	xor a7, t2, a6
	xor s9, s9, a7
	xor s0, t1, s0
	xor s0, s9, s0
	xor t4, t4, s2
	xor s11, s11, t2
	xor s4, s4, t5
	xor t0, t0, s6
	xor a6, a6, s5
	xor s8, s8, a6
	xori s8, s8, -1
	xor s1, s1, s0
	xor s10, s10, t3
	xor s0, s7, s1
	xori s0, s0, -1
	xor s7, s11, s4
	xori s7, s7, -1
	xor t6, t6, s3
	ld s3, 48(a5)
	xor t1, t1, s3
	xor s3, s3, t6
	xor s6, s5, s10
	xori s6, s6, -1
	ld s10, 56(a5)
	xor s2, s10, t1
	xor s4, s9, t0
	xori s4, s4, -1
	addi s5, s3, 0
	addi s3, t4, 0
	addi s1, s8, 0
	srli a7, s6, 16
	slli t2, s6, 48
	xor t2, t2, a7
	srli a7, t2, 16
	slli t1, t2, 48
	xor t1, t1, a7
	xor t0, t2, t1
	srli a7, t2, 32
	slli t1, t2, 32
	xor t1, t1, a7
	xor t0, t0, t1
	xor t0, t0, s0
	srli a7, s0, 48
	slli t1, s0, 16
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 640(a5)
	xor t0, t0, t1
	sd t0, 640(a5)
	srli a7, s7, 16
	slli t2, s7, 48
	xor t2, t2, a7
	srli a7, t2, 16
	slli t1, t2, 48
	xor t1, t1, a7
	xor t0, t2, t1
	srli a7, t2, 32
	slli t1, t2, 32
	xor t1, t1, a7
	xor t0, t0, t1
	xor t0, t0, s1
	srli a7, s1, 48
	slli t1, s1, 16
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 648(a5)
	xor t0, t0, t1
	sd t0, 648(a5)
	srli a7, s0, 16
	slli t1, s0, 48
	xor t1, t1, a7
	xor t0, s0, t1
	srli a7, s0, 32
	slli t1, s0, 32
	xor t1, t1, a7
	xor t0, t0, t1
	xor t0, t0, s2
	srli a7, s2, 48
	slli t1, s2, 16
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 656(a5)
	xor t0, t0, t1
	sd t0, 656(a5)
	srli a7, s1, 16
	slli t1, s1, 48
	xor t1, t1, a7
	xor t0, s1, t1
	srli a7, s1, 32
	slli t1, s1, 32
	xor t1, t1, a7
	xor t0, t0, t1
	xor t0, t0, s3
	srli a7, s3, 48
	slli t1, s3, 16
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 664(a5)
	xor t0, t0, t1
	sd t0, 664(a5)
	srli a7, s2, 16
	slli t1, s2, 48
	xor t1, t1, a7
	xor t0, s2, t1
	srli a7, s2, 32
	slli t1, s2, 32
	xor t1, t1, a7
	xor t0, t0, t1
	xor t0, t0, s4
	srli a7, s4, 48
	slli t1, s4, 16
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 672(a5)
	xor t0, t0, t1
	sd t0, 672(a5)
	srli a7, s3, 16
	slli t1, s3, 48
	xor t1, t1, a7
	xor t0, s3, t1
	srli a7, s3, 32
	slli t1, s3, 32
	xor t1, t1, a7
	xor t0, t0, t1
	xor t0, t0, s5
	srli a7, s5, 48
	slli t1, s5, 16
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 680(a5)
	xor t0, t0, t1
	sd t0, 680(a5)
	srli a7, s4, 16
	slli t1, s4, 48
	xor t1, t1, a7
	xor t0, s4, t1
	srli a7, s4, 32
	slli t1, s4, 32
	xor t1, t1, a7
	xor t0, t0, t1
	xor t0, t0, s6
	srli a7, s6, 48
	slli t1, s6, 16
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 688(a5)
	xor t0, t0, t1
	sd t0, 688(a5)
	srli a7, s5, 16
	slli t1, s5, 48
	xor t1, t1, a7
	xor t0, s5, t1
	srli a7, s5, 32
	slli t1, s5, 32
	xor t1, t1, a7
	xor t0, t0, t1
	xor t0, t0, s7
	srli a7, s7, 48
	slli t1, s7, 16
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 696(a5)
	xor t0, t0, t1
	sd t0, 696(a5)
	ld s0, 512(a5)
	ld t0, 576(a5)
	xor s0, s0, t0
	ld t0, 640(a5)
	xor s0, s0, t0
	ld t0, 192(a3)
	xor s0, s0, t0
	ld s1, 520(a5)
	ld t0, 584(a5)
	xor s1, s1, t0
	ld t0, 648(a5)
	xor s1, s1, t0
	ld t0, 200(a3)
	xor s1, s1, t0
	ld s2, 528(a5)
	ld t0, 592(a5)
	xor s2, s2, t0
	ld t0, 656(a5)
	xor s2, s2, t0
	ld t0, 208(a3)
	xor s2, s2, t0
	ld s3, 536(a5)
	ld t0, 600(a5)
	xor s3, s3, t0
	ld t0, 664(a5)
	xor s3, s3, t0
	ld t0, 216(a3)
	xor s3, s3, t0
	ld s4, 544(a5)
	ld t0, 608(a5)
	xor s4, s4, t0
	ld t0, 672(a5)
	xor s4, s4, t0
	ld t0, 224(a3)
	xor s4, s4, t0
	ld s5, 552(a5)
	ld t0, 616(a5)
	xor s5, s5, t0
	ld t0, 680(a5)
	xor s5, s5, t0
	ld t0, 232(a3)
	xor s5, s5, t0
	ld s6, 560(a5)
	ld t0, 624(a5)
	xor s6, s6, t0
	ld t0, 688(a5)
	xor s6, s6, t0
	ld t0, 240(a3)
	xor s6, s6, t0
	ld s7, 568(a5)
	ld t0, 632(a5)
	xor s7, s7, t0
	ld t0, 696(a5)
	xor s7, s7, t0
	ld t0, 248(a3)
	xor s7, s7, t0
	xor t0, s4, s2
	xor t1, s3, s0
	xor t2, s1, t1
	xor t3, s7, t0
	xor t4, s5, t2
	xor t5, s6, s2
	xor s4, s7, s4
	xor t6, s5, t3
	xor a6, s6, t6
	xor a7, s7, s3
	xor s8, s6, s4
	xor s9, s5, t0
	xor t6, s1, t6
	xori t6, t6, -1
	xor s10, t1, t3
	xor s11, s0, s8
	xor s8, t4, s8
	sd s8, 0(a5)
	xor s8, s1, t5
	xor s6, s6, s10
	xor s0, s0, t3
	xori s0, s0, -1
	xor s10, s1, a7
	xor s3, s3, s9
	xori s3, s3, -1
	xor s4, t2, s4
	sd t3, 8(a5)
	xor t3, t0, t4
	sd t3, 16(a5)
	xor t3, t4, t5
	xor s2, s7, s2
	xori s2, s2, -1
	xor s11, s1, s11
	xori s11, s11, -1
	xor t1, t1, s9
	xor s5, s5, a7
	xori s5, s5, -1
	xor a7, s1, a6
	xor t0, t0, t2
	xori t0, t0, -1
	xor s7, s7, t2
	xori s7, s7, -1
	and t2, a7, t6
	and s9, t4, s3
	xor s9, s9, t2
	sd t4, 24(a5)
	and t4, s6, s10
	xor t4, t4, t2
	and t2, s1, t1
	sd s1, 32(a5)
	and s1, t5, s5
	xor s1, s1, t2
	sd t5, 40(a5)
	and t5, s8, s0
	xor t5, t5, t2
	and t2, s4, t0
	sd s4, 48(a5)
	and s4, a6, s7
	xor s4, s4, t2
	sd a6, 56(a5)
	ld a6, 8(a5)
	sd s8, 64(a5)
	and s8, t3, a6
	xor s8, s8, t2
	xor s9, s9, s4
	xor t4, t4, s8
	xor s1, s1, s4
	xor t5, t5, s8
	xor s9, s9, s2
	ld s2, 0(a5)
	xor t4, t4, s2
	ld s2, 16(a5)
	xor s1, s1, s2
	xor t5, t5, s11
	xor s11, s9, t4
	and s9, s9, s1
	xor s2, t5, s9
	and s8, s11, s2
	xor s8, s8, t4
	xor s4, s1, t5
	xor t4, t4, s9
	and t4, t4, s4
	xor t4, t4, t5
	xor s1, s1, t4
	xor s4, s2, t4
	and t5, t5, s4
	xor s1, t5, s1
	xor s2, s2, t5
	and s2, s8, s2
	xor s11, s11, s2
	xor s2, s11, s1
	xor t5, s8, t4
	xor s4, s8, s11
	xor s9, t4, s1
	xor t2, t5, s2
	and t6, s9, t6
	and s3, s1, s3
	and s10, t4, s10
	and t1, s4, t1
	and s5, s11, s5
	and s0, s8, s0
	and t0, t5, t0
	and s7, t2, s7
	and a6, s2, a6
	and s9, s9, a7
	ld a7, 24(a5)
	and s1, s1, a7
	and t4, t4, s6
	ld s6, 32(a5)
	and s4, s4, s6
	ld s6, 40(a5)
	and s11, s11, s6
	ld s6, 64(a5)
	and s8, s8, s6
	ld s6, 48(a5)
	and t5, t5, s6
	ld s6, 56(a5)
	and t2, t2, s6
	and s2, s2, t3
	xor s9, s9, t5
	xor t0, t0, s1
	xor s0, t6, s0
	xor t3, s11, t0
	xor s8, s8, t3
	xor a6, s3, a6
	xor t3, s7, s8
	xor s2, s2, s9
	xor s6, s5, s0
	xor a7, t3, s2
	sd s5, 56(a5)
	xor s5, t4, s6
	sd a7, 48(a5)
	xor a7, t2, a6
	xor s9, s9, a7
	xor s0, t1, s0
	xor s0, s9, s0
	xor t4, t4, s2
	xor s11, s11, t2
	xor s4, s4, t5
	xor t0, t0, s6
	xor a6, a6, s5
	xor s8, s8, a6
	xori s8, s8, -1
	xor s1, s1, s0
	xor s10, s10, t3
	xor s0, s7, s1
	xori s0, s0, -1
	xor s7, s11, s4
	xori s7, s7, -1
	xor t6, t6, s3
	ld s3, 48(a5)
	xor t1, t1, s3
	xor s3, s3, t6
	xor s6, s5, s10
	xori s6, s6, -1
	ld s10, 56(a5)
	xor s2, s10, t1
	xor s4, s9, t0
	xori s4, s4, -1
	addi s5, s3, 0
	addi s3, t4, 0
	addi s1, s8, 0
	srli a7, s6, 16
	slli t2, s6, 48
	xor t2, t2, a7
	srli a7, t2, 16
	slli t1, t2, 48
	xor t1, t1, a7
	xor t0, t2, t1
	srli a7, t2, 32
	slli t1, t2, 32
	xor t1, t1, a7
	xor t0, t0, t1
	xor t0, t0, s0
	srli a7, s0, 48
	slli t1, s0, 16
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 704(a5)
	xor t0, t0, t1
	sd t0, 704(a5)
	srli a7, s7, 16
	slli t2, s7, 48
	xor t2, t2, a7
	srli a7, t2, 16
	slli t1, t2, 48
	xor t1, t1, a7
	xor t0, t2, t1
	srli a7, t2, 32
	slli t1, t2, 32
	xor t1, t1, a7
	xor t0, t0, t1
	xor t0, t0, s1
	srli a7, s1, 48
	slli t1, s1, 16
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 712(a5)
	xor t0, t0, t1
	sd t0, 712(a5)
	srli a7, s0, 16
	slli t1, s0, 48
	xor t1, t1, a7
	xor t0, s0, t1
	srli a7, s0, 32
	slli t1, s0, 32
	xor t1, t1, a7
	xor t0, t0, t1
	xor t0, t0, s2
	srli a7, s2, 48
	slli t1, s2, 16
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 720(a5)
	xor t0, t0, t1
	sd t0, 720(a5)
	srli a7, s1, 16
	slli t1, s1, 48
	xor t1, t1, a7
	xor t0, s1, t1
	srli a7, s1, 32
	slli t1, s1, 32
	xor t1, t1, a7
	xor t0, t0, t1
	xor t0, t0, s3
	srli a7, s3, 48
	slli t1, s3, 16
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 728(a5)
	xor t0, t0, t1
	sd t0, 728(a5)
	srli a7, s2, 16
	slli t1, s2, 48
	xor t1, t1, a7
	xor t0, s2, t1
	srli a7, s2, 32
	slli t1, s2, 32
	xor t1, t1, a7
	xor t0, t0, t1
	xor t0, t0, s4
	srli a7, s4, 48
	slli t1, s4, 16
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 736(a5)
	xor t0, t0, t1
	sd t0, 736(a5)
	srli a7, s3, 16
	slli t1, s3, 48
	xor t1, t1, a7
	xor t0, s3, t1
	srli a7, s3, 32
	slli t1, s3, 32
	xor t1, t1, a7
	xor t0, t0, t1
	xor t0, t0, s5
	srli a7, s5, 48
	slli t1, s5, 16
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 744(a5)
	xor t0, t0, t1
	sd t0, 744(a5)
	srli a7, s4, 16
	slli t1, s4, 48
	xor t1, t1, a7
	xor t0, s4, t1
	srli a7, s4, 32
	slli t1, s4, 32
	xor t1, t1, a7
	xor t0, t0, t1
	xor t0, t0, s6
	srli a7, s6, 48
	slli t1, s6, 16
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 752(a5)
	xor t0, t0, t1
	sd t0, 752(a5)
	srli a7, s5, 16
	slli t1, s5, 48
	xor t1, t1, a7
	xor t0, s5, t1
	srli a7, s5, 32
	slli t1, s5, 32
	xor t1, t1, a7
	xor t0, t0, t1
	xor t0, t0, s7
	srli a7, s7, 48
	slli t1, s7, 16
	xor t1, t1, a7
	xor t0, t0, t1
	ld t1, 760(a5)
	xor t0, t0, t1
	sd t0, 760(a5)
	addi a3, a3, 256
	sub t0, a3, a0
	bnez t0, 27b
	ld t3, 360(a5)
	ld t4, 368(a5)
	ld t5, 376(a5)
	ld t6, 384(a5)
	ld a6, 392(a5)
	ld a7, 400(a5)
	ld s0, 704(a5)
	ld s1, 712(a5)
	ld s2, 720(a5)
	ld s3, 728(a5)
	ld s4, 736(a5)
	ld s5, 744(a5)
	ld s6, 752(a5)
	ld s7, 760(a5)
	srli t0, s0, 1
	xor t0, t0, s1
	and t0, t0, t6
	xor s1, s1, t0
	slli t0, t0, 1
	xor s0, s0, t0
	srli t0, s2, 1
	xor t0, t0, s3
	and t0, t0, t6
	xor s3, s3, t0
	slli t0, t0, 1
	xor s2, s2, t0
	srli t0, s4, 1
	xor t0, t0, s5
	and t0, t0, t6
	xor s5, s5, t0
	slli t0, t0, 1
	xor s4, s4, t0
	srli t0, s6, 1
	xor t0, t0, s7
	and t0, t0, t6
	xor s7, s7, t0
	slli t0, t0, 1
	xor s6, s6, t0
	srli t0, s0, 2
	xor t0, t0, s2
	and t0, t0, a6
	xor s2, s2, t0
	slli t0, t0, 2
	xor s0, s0, t0
	srli t0, s1, 2
	xor t0, t0, s3
	and t0, t0, a6
	xor s3, s3, t0
	slli t0, t0, 2
	xor s1, s1, t0
	srli t0, s4, 2
	xor t0, t0, s6
	and t0, t0, a6
	xor s6, s6, t0
	slli t0, t0, 2
	xor s4, s4, t0
	srli t0, s5, 2
	xor t0, t0, s7
	and t0, t0, a6
	xor s7, s7, t0
	slli t0, t0, 2
	xor s5, s5, t0
	srli t0, s0, 4
	xor t0, t0, s4
	and t0, t0, a7
	xor s4, s4, t0
	slli t0, t0, 4
	xor s0, s0, t0
	srli t0, s1, 4
	xor t0, t0, s5
	and t0, t0, a7
	xor s5, s5, t0
	slli t0, t0, 4
	xor s1, s1, t0
	srli t0, s2, 4
	xor t0, t0, s6
	and t0, t0, a7
	xor s6, s6, t0
	slli t0, t0, 4
	xor s2, s2, t0
	srli t0, s3, 4
	xor t0, t0, s7
	and t0, t0, a7
	xor s7, s7, t0
	slli t0, t0, 4
	xor s3, s3, t0
	sd s0, 768(a5)
	sd s1, 784(a5)
	sd s2, 800(a5)
	sd s3, 816(a5)
	sd s4, 832(a5)
	sd s5, 848(a5)
	sd s6, 864(a5)
	sd s7, 880(a5)
	ld s0, 640(a5)
	ld s1, 648(a5)
	ld s2, 656(a5)
	ld s3, 664(a5)
	ld s4, 672(a5)
	ld s5, 680(a5)
	ld s6, 688(a5)
	ld s7, 696(a5)
	srli t0, s0, 1
	xor t0, t0, s1
	and t0, t0, t6
	xor s1, s1, t0
	slli t0, t0, 1
	xor s0, s0, t0
	srli t0, s2, 1
	xor t0, t0, s3
	and t0, t0, t6
	xor s3, s3, t0
	slli t0, t0, 1
	xor s2, s2, t0
	srli t0, s4, 1
	xor t0, t0, s5
	and t0, t0, t6
	xor s5, s5, t0
	slli t0, t0, 1
	xor s4, s4, t0
	srli t0, s6, 1
	xor t0, t0, s7
	and t0, t0, t6
	xor s7, s7, t0
	slli t0, t0, 1
	xor s6, s6, t0
	srli t0, s0, 2
	xor t0, t0, s2
	and t0, t0, a6
	xor s2, s2, t0
	slli t0, t0, 2
	xor s0, s0, t0
	srli t0, s1, 2
	xor t0, t0, s3
	and t0, t0, a6
	xor s3, s3, t0
	slli t0, t0, 2
	xor s1, s1, t0
	srli t0, s4, 2
	xor t0, t0, s6
	and t0, t0, a6
	xor s6, s6, t0
	slli t0, t0, 2
	xor s4, s4, t0
	srli t0, s5, 2
	xor t0, t0, s7
	and t0, t0, a6
	xor s7, s7, t0
	slli t0, t0, 2
	xor s5, s5, t0
	srli t0, s0, 4
	xor t0, t0, s4
	and t0, t0, a7
	xor s4, s4, t0
	slli t0, t0, 4
	xor s0, s0, t0
	srli t0, s1, 4
	xor t0, t0, s5
	and t0, t0, a7
	xor s5, s5, t0
	slli t0, t0, 4
	xor s1, s1, t0
	srli t0, s2, 4
	xor t0, t0, s6
	and t0, t0, a7
	xor s6, s6, t0
	slli t0, t0, 4
	xor s2, s2, t0
	srli t0, s3, 4
	xor t0, t0, s7
	and t0, t0, a7
	xor s7, s7, t0
	slli t0, t0, 4
	xor s3, s3, t0
	sd s0, 896(a5)
	sd s1, 912(a5)
	sd s2, 928(a5)
	sd s3, 944(a5)
	sd s4, 960(a5)
	sd s5, 976(a5)
	sd s6, 992(a5)
	sd s7, 1008(a5)
	ld s0, 576(a5)
	ld s1, 584(a5)
	ld s2, 592(a5)
	ld s3, 600(a5)
	ld s4, 608(a5)
	ld s5, 616(a5)
	ld s6, 624(a5)
	ld s7, 632(a5)
	srli t0, s0, 1
	xor t0, t0, s1
	and t0, t0, t6
	xor s1, s1, t0
	slli t0, t0, 1
	xor s0, s0, t0
	srli t0, s2, 1
	xor t0, t0, s3
	and t0, t0, t6
	xor s3, s3, t0
	slli t0, t0, 1
	xor s2, s2, t0
	srli t0, s4, 1
	xor t0, t0, s5
	and t0, t0, t6
	xor s5, s5, t0
	slli t0, t0, 1
	xor s4, s4, t0
	srli t0, s6, 1
	xor t0, t0, s7
	and t0, t0, t6
	xor s7, s7, t0
	slli t0, t0, 1
	xor s6, s6, t0
	srli t0, s0, 2
	xor t0, t0, s2
	and t0, t0, a6
	xor s2, s2, t0
	slli t0, t0, 2
	xor s0, s0, t0
	srli t0, s1, 2
	xor t0, t0, s3
	and t0, t0, a6
	xor s3, s3, t0
	slli t0, t0, 2
	xor s1, s1, t0
	srli t0, s4, 2
	xor t0, t0, s6
	and t0, t0, a6
	xor s6, s6, t0
	slli t0, t0, 2
	xor s4, s4, t0
	srli t0, s5, 2
	xor t0, t0, s7
	and t0, t0, a6
	xor s7, s7, t0
	slli t0, t0, 2
	xor s5, s5, t0
	srli t0, s0, 4
	xor t0, t0, s4
	and t0, t0, a7
	xor s4, s4, t0
	slli t0, t0, 4
	xor s0, s0, t0
	srli t0, s1, 4
	xor t0, t0, s5
	and t0, t0, a7
	xor s5, s5, t0
	slli t0, t0, 4
	xor s1, s1, t0
	srli t0, s2, 4
	xor t0, t0, s6
	and t0, t0, a7
	xor s6, s6, t0
	slli t0, t0, 4
	xor s2, s2, t0
	srli t0, s3, 4
	xor t0, t0, s7
	and t0, t0, a7
	xor s7, s7, t0
	slli t0, t0, 4
	xor s3, s3, t0
	sd s0, 776(a5)
	sd s1, 792(a5)
	sd s2, 808(a5)
	sd s3, 824(a5)
	sd s4, 840(a5)
	sd s5, 856(a5)
	sd s6, 872(a5)
	sd s7, 888(a5)
	ld s0, 512(a5)
	ld s1, 520(a5)
	ld s2, 528(a5)
	ld s3, 536(a5)
	ld s4, 544(a5)
	ld s5, 552(a5)
	ld s6, 560(a5)
	ld s7, 568(a5)
	srli t0, s0, 1
	xor t0, t0, s1
	and t0, t0, t6
	xor s1, s1, t0
	slli t0, t0, 1
	xor s0, s0, t0
	srli t0, s2, 1
	xor t0, t0, s3
	and t0, t0, t6
	xor s3, s3, t0
	slli t0, t0, 1
	xor s2, s2, t0
	srli t0, s4, 1
	xor t0, t0, s5
	and t0, t0, t6
	xor s5, s5, t0
	slli t0, t0, 1
	xor s4, s4, t0
	srli t0, s6, 1
	xor t0, t0, s7
	and t0, t0, t6
	xor s7, s7, t0
	slli t0, t0, 1
	xor s6, s6, t0
	srli t0, s0, 2
	xor t0, t0, s2
	and t0, t0, a6
	xor s2, s2, t0
	slli t0, t0, 2
	xor s0, s0, t0
	srli t0, s1, 2
	xor t0, t0, s3
	and t0, t0, a6
	xor s3, s3, t0
	slli t0, t0, 2
	xor s1, s1, t0
	srli t0, s4, 2
	xor t0, t0, s6
	and t0, t0, a6
	xor s6, s6, t0
	slli t0, t0, 2
	xor s4, s4, t0
	srli t0, s5, 2
	xor t0, t0, s7
	and t0, t0, a6
	xor s7, s7, t0
	slli t0, t0, 2
	xor s5, s5, t0
	srli t0, s0, 4
	xor t0, t0, s4
	and t0, t0, a7
	xor s4, s4, t0
	slli t0, t0, 4
	xor s0, s0, t0
	srli t0, s1, 4
	xor t0, t0, s5
	and t0, t0, a7
	xor s5, s5, t0
	slli t0, t0, 4
	xor s1, s1, t0
	srli t0, s2, 4
	xor t0, t0, s6
	and t0, t0, a7
	xor s6, s6, t0
	slli t0, t0, 4
	xor s2, s2, t0
	srli t0, s3, 4
	xor t0, t0, s7
	and t0, t0, a7
	xor s7, s7, t0
	slli t0, t0, 4
	xor s3, s3, t0
	sd s0, 904(a5)
	sd s1, 920(a5)
	sd s2, 936(a5)
	sd s3, 952(a5)
	sd s4, 968(a5)
	sd s5, 984(a5)
	sd s6, 1000(a5)
	sd s7, 1016(a5)
	ld s0, 768(a5)
	ld s4, 896(a5)
	ld s1, 784(a5)
	ld s5, 912(a5)
	ld s2, 800(a5)
	ld s6, 928(a5)
	ld s3, 816(a5)
	ld s7, 944(a5)
	srli t0, s0, 8
	xor t0, t0, s4
	and t0, t0, t5
	xor s4, s4, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s5
	and t0, t0, t5
	xor s5, s5, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s6
	and t0, t0, t5
	xor s6, s6, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s7
	and t0, t0, t5
	xor s7, s7, t0
	slli t0, t0, 8
	xor s3, s3, t0
	srli t0, s0, 8
	xor t0, t0, s0
	and t0, t0, t4
	xor s0, s0, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s1
	and t0, t0, t4
	xor s1, s1, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s2
	and t0, t0, t4
	xor s2, s2, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s3
	and t0, t0, t4
	xor s3, s3, t0
	slli t0, t0, 8
	xor s3, s3, t0
	srli t0, s4, 8
	xor t0, t0, s4
	and t0, t0, t4
	xor s4, s4, t0
	slli t0, t0, 8
	xor s4, s4, t0
	srli t0, s5, 8
	xor t0, t0, s5
	and t0, t0, t4
	xor s5, s5, t0
	slli t0, t0, 8
	xor s5, s5, t0
	srli t0, s6, 8
	xor t0, t0, s6
	and t0, t0, t4
	xor s6, s6, t0
	slli t0, t0, 8
	xor s6, s6, t0
	srli t0, s7, 8
	xor t0, t0, s7
	and t0, t0, t4
	xor s7, s7, t0
	slli t0, t0, 8
	xor s7, s7, t0
	srli t0, s0, 16
	xor t0, t0, s0
	and t0, t0, t3
	xor s0, s0, t0
	slli t0, t0, 16
	xor s0, s0, t0
	srli t0, s1, 16
	xor t0, t0, s1
	and t0, t0, t3
	xor s1, s1, t0
	slli t0, t0, 16
	xor s1, s1, t0
	srli t0, s2, 16
	xor t0, t0, s2
	and t0, t0, t3
	xor s2, s2, t0
	slli t0, t0, 16
	xor s2, s2, t0
	srli t0, s3, 16
	xor t0, t0, s3
	and t0, t0, t3
	xor s3, s3, t0
	slli t0, t0, 16
	xor s3, s3, t0
	srli t0, s4, 16
	xor t0, t0, s4
	and t0, t0, t3
	xor s4, s4, t0
	slli t0, t0, 16
	xor s4, s4, t0
	srli t0, s5, 16
	xor t0, t0, s5
	and t0, t0, t3
	xor s5, s5, t0
	slli t0, t0, 16
	xor s5, s5, t0
	srli t0, s6, 16
	xor t0, t0, s6
	and t0, t0, t3
	xor s6, s6, t0
	slli t0, t0, 16
	xor s6, s6, t0
	srli t0, s7, 16
	xor t0, t0, s7
	and t0, t0, t3
	xor s7, s7, t0
	slli t0, t0, 16
	xor s7, s7, t0
	sd s0, 768(a5)
	sd s4, 896(a5)
	sd s1, 784(a5)
	sd s5, 912(a5)
	sd s2, 800(a5)
	sd s6, 928(a5)
	sd s3, 816(a5)
	sd s7, 944(a5)
	ld s0, 832(a5)
	ld s4, 960(a5)
	ld s1, 848(a5)
	ld s5, 976(a5)
	ld s2, 864(a5)
	ld s6, 992(a5)
	ld s3, 880(a5)
	ld s7, 1008(a5)
	srli t0, s0, 8
	xor t0, t0, s4
	and t0, t0, t5
	xor s4, s4, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s5
	and t0, t0, t5
	xor s5, s5, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s6
	and t0, t0, t5
	xor s6, s6, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s7
	and t0, t0, t5
	xor s7, s7, t0
	slli t0, t0, 8
	xor s3, s3, t0
	srli t0, s0, 8
	xor t0, t0, s0
	and t0, t0, t4
	xor s0, s0, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s1
	and t0, t0, t4
	xor s1, s1, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s2
	and t0, t0, t4
	xor s2, s2, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s3
	and t0, t0, t4
	xor s3, s3, t0
	slli t0, t0, 8
	xor s3, s3, t0
	srli t0, s4, 8
	xor t0, t0, s4
	and t0, t0, t4
	xor s4, s4, t0
	slli t0, t0, 8
	xor s4, s4, t0
	srli t0, s5, 8
	xor t0, t0, s5
	and t0, t0, t4
	xor s5, s5, t0
	slli t0, t0, 8
	xor s5, s5, t0
	srli t0, s6, 8
	xor t0, t0, s6
	and t0, t0, t4
	xor s6, s6, t0
	slli t0, t0, 8
	xor s6, s6, t0
	srli t0, s7, 8
	xor t0, t0, s7
	and t0, t0, t4
	xor s7, s7, t0
	slli t0, t0, 8
	xor s7, s7, t0
	srli t0, s0, 16
	xor t0, t0, s0
	and t0, t0, t3
	xor s0, s0, t0
	slli t0, t0, 16
	xor s0, s0, t0
	srli t0, s1, 16
	xor t0, t0, s1
	and t0, t0, t3
	xor s1, s1, t0
	slli t0, t0, 16
	xor s1, s1, t0
	srli t0, s2, 16
	xor t0, t0, s2
	and t0, t0, t3
	xor s2, s2, t0
	slli t0, t0, 16
	xor s2, s2, t0
	srli t0, s3, 16
	xor t0, t0, s3
	and t0, t0, t3
	xor s3, s3, t0
	slli t0, t0, 16
	xor s3, s3, t0
	srli t0, s4, 16
	xor t0, t0, s4
	and t0, t0, t3
	xor s4, s4, t0
	slli t0, t0, 16
	xor s4, s4, t0
	srli t0, s5, 16
	xor t0, t0, s5
	and t0, t0, t3
	xor s5, s5, t0
	slli t0, t0, 16
	xor s5, s5, t0
	srli t0, s6, 16
	xor t0, t0, s6
	and t0, t0, t3
	xor s6, s6, t0
	slli t0, t0, 16
	xor s6, s6, t0
	srli t0, s7, 16
	xor t0, t0, s7
	and t0, t0, t3
	xor s7, s7, t0
	slli t0, t0, 16
	xor s7, s7, t0
	sd s0, 832(a5)
	sd s4, 960(a5)
	sd s1, 848(a5)
	sd s5, 976(a5)
	sd s2, 864(a5)
	sd s6, 992(a5)
	sd s3, 880(a5)
	sd s7, 1008(a5)
	ld s0, 776(a5)
	ld s4, 904(a5)
	ld s1, 792(a5)
	ld s5, 920(a5)
	ld s2, 808(a5)
	ld s6, 936(a5)
	ld s3, 824(a5)
	ld s7, 952(a5)
	srli t0, s0, 8
	xor t0, t0, s4
	and t0, t0, t5
	xor s4, s4, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s5
	and t0, t0, t5
	xor s5, s5, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s6
	and t0, t0, t5
	xor s6, s6, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s7
	and t0, t0, t5
	xor s7, s7, t0
	slli t0, t0, 8
	xor s3, s3, t0
	srli t0, s0, 8
	xor t0, t0, s0
	and t0, t0, t4
	xor s0, s0, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s1
	and t0, t0, t4
	xor s1, s1, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s2
	and t0, t0, t4
	xor s2, s2, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s3
	and t0, t0, t4
	xor s3, s3, t0
	slli t0, t0, 8
	xor s3, s3, t0
	srli t0, s4, 8
	xor t0, t0, s4
	and t0, t0, t4
	xor s4, s4, t0
	slli t0, t0, 8
	xor s4, s4, t0
	srli t0, s5, 8
	xor t0, t0, s5
	and t0, t0, t4
	xor s5, s5, t0
	slli t0, t0, 8
	xor s5, s5, t0
	srli t0, s6, 8
	xor t0, t0, s6
	and t0, t0, t4
	xor s6, s6, t0
	slli t0, t0, 8
	xor s6, s6, t0
	srli t0, s7, 8
	xor t0, t0, s7
	and t0, t0, t4
	xor s7, s7, t0
	slli t0, t0, 8
	xor s7, s7, t0
	srli t0, s0, 16
	xor t0, t0, s0
	and t0, t0, t3
	xor s0, s0, t0
	slli t0, t0, 16
	xor s0, s0, t0
	srli t0, s1, 16
	xor t0, t0, s1
	and t0, t0, t3
	xor s1, s1, t0
	slli t0, t0, 16
	xor s1, s1, t0
	srli t0, s2, 16
	xor t0, t0, s2
	and t0, t0, t3
	xor s2, s2, t0
	slli t0, t0, 16
	xor s2, s2, t0
	srli t0, s3, 16
	xor t0, t0, s3
	and t0, t0, t3
	xor s3, s3, t0
	slli t0, t0, 16
	xor s3, s3, t0
	srli t0, s4, 16
	xor t0, t0, s4
	and t0, t0, t3
	xor s4, s4, t0
	slli t0, t0, 16
	xor s4, s4, t0
	srli t0, s5, 16
	xor t0, t0, s5
	and t0, t0, t3
	xor s5, s5, t0
	slli t0, t0, 16
	xor s5, s5, t0
	srli t0, s6, 16
	xor t0, t0, s6
	and t0, t0, t3
	xor s6, s6, t0
	slli t0, t0, 16
	xor s6, s6, t0
	srli t0, s7, 16
	xor t0, t0, s7
	and t0, t0, t3
	xor s7, s7, t0
	slli t0, t0, 16
	xor s7, s7, t0
	sd s0, 776(a5)
	sd s4, 904(a5)
	sd s1, 792(a5)
	sd s5, 920(a5)
	sd s2, 808(a5)
	sd s6, 936(a5)
	sd s3, 824(a5)
	sd s7, 952(a5)
	ld s0, 840(a5)
	ld s4, 968(a5)
	ld s1, 856(a5)
	ld s5, 984(a5)
	ld s2, 872(a5)
	ld s6, 1000(a5)
	ld s3, 888(a5)
	ld s7, 1016(a5)
	srli t0, s0, 8
	xor t0, t0, s4
	and t0, t0, t5
	xor s4, s4, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s5
	and t0, t0, t5
	xor s5, s5, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s6
	and t0, t0, t5
	xor s6, s6, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s7
	and t0, t0, t5
	xor s7, s7, t0
	slli t0, t0, 8
	xor s3, s3, t0
	srli t0, s0, 8
	xor t0, t0, s0
	and t0, t0, t4
	xor s0, s0, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s1
	and t0, t0, t4
	xor s1, s1, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s2
	and t0, t0, t4
	xor s2, s2, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s3
	and t0, t0, t4
	xor s3, s3, t0
	slli t0, t0, 8
	xor s3, s3, t0
	srli t0, s4, 8
	xor t0, t0, s4
	and t0, t0, t4
	xor s4, s4, t0
	slli t0, t0, 8
	xor s4, s4, t0
	srli t0, s5, 8
	xor t0, t0, s5
	and t0, t0, t4
	xor s5, s5, t0
	slli t0, t0, 8
	xor s5, s5, t0
	srli t0, s6, 8
	xor t0, t0, s6
	and t0, t0, t4
	xor s6, s6, t0
	slli t0, t0, 8
	xor s6, s6, t0
	srli t0, s7, 8
	xor t0, t0, s7
	and t0, t0, t4
	xor s7, s7, t0
	slli t0, t0, 8
	xor s7, s7, t0
	srli t0, s0, 16
	xor t0, t0, s0
	and t0, t0, t3
	xor s0, s0, t0
	slli t0, t0, 16
	xor s0, s0, t0
	srli t0, s1, 16
	xor t0, t0, s1
	and t0, t0, t3
	xor s1, s1, t0
	slli t0, t0, 16
	xor s1, s1, t0
	srli t0, s2, 16
	xor t0, t0, s2
	and t0, t0, t3
	xor s2, s2, t0
	slli t0, t0, 16
	xor s2, s2, t0
	srli t0, s3, 16
	xor t0, t0, s3
	and t0, t0, t3
	xor s3, s3, t0
	slli t0, t0, 16
	xor s3, s3, t0
	srli t0, s4, 16
	xor t0, t0, s4
	and t0, t0, t3
	xor s4, s4, t0
	slli t0, t0, 16
	xor s4, s4, t0
	srli t0, s5, 16
	xor t0, t0, s5
	and t0, t0, t3
	xor s5, s5, t0
	slli t0, t0, 16
	xor s5, s5, t0
	srli t0, s6, 16
	xor t0, t0, s6
	and t0, t0, t3
	xor s6, s6, t0
	slli t0, t0, 16
	xor s6, s6, t0
	srli t0, s7, 16
	xor t0, t0, s7
	and t0, t0, t3
	xor s7, s7, t0
	slli t0, t0, 16
	xor s7, s7, t0
	sd s0, 840(a5)
	sd s4, 968(a5)
	sd s1, 856(a5)
	sd s5, 984(a5)
	sd s2, 872(a5)
	sd s6, 1000(a5)
	sd s3, 888(a5)
	sd s7, 1016(a5)
	addi t0, a5, 2040
	addi t0, t0, 1032
	ld s0, 0(t0)
	ld s1, 8(t0)
	ld s2, 16(t0)
	ld s3, 24(t0)
	ld s4, 32(t0)
	ld s5, 40(t0)
	ld s6, 48(t0)
	ld s7, 56(t0)
	ld s8, 64(t0)
	ld s9, 72(t0)
	ld s10, 80(t0)
	ld s11, 88(t0)
	addi s1, a1, 0
	addi s2, a2, 0
	addi s3, a4, 0
	addi s4, a5, -56
	ld a0, 48(s4)
	lbu t0, 0(s2)
	lbu t2, 1(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 824(s4)
	lbu t2, 825(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 826(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 827(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 0(s2)
	srli t2, t0, 8
	sb t2, 1(s2)
	srli t2, t0, 16
	sb t2, 2(s2)
	srli t2, t0, 24
	sb t2, 3(s2)
	lbu t0, 4(s2)
	lbu t2, 5(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 828(s4)
	lbu t2, 829(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 830(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 831(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 4(s2)
	srli t2, t0, 8
	sb t2, 5(s2)
	srli t2, t0, 16
	sb t2, 6(s2)
	srli t2, t0, 24
	sb t2, 7(s2)
	lbu t0, 8(s2)
	lbu t2, 9(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 10(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 11(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 832(s4)
	lbu t2, 833(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 834(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 835(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 8(s2)
	srli t2, t0, 8
	sb t2, 9(s2)
	srli t2, t0, 16
	sb t2, 10(s2)
	srli t2, t0, 24
	sb t2, 11(s2)
	lbu t0, 12(s2)
	lbu t2, 13(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 14(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 15(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 836(s4)
	lbu t2, 837(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 838(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 839(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 12(s2)
	srli t2, t0, 8
	sb t2, 13(s2)
	srli t2, t0, 16
	sb t2, 14(s2)
	srli t2, t0, 24
	sb t2, 15(s2)
	addi t1, zero, 1
	lbu t0, 47(s4)
	add t0, t0, t1
	sb t0, 47(s4)
	srli t1, t0, 8
	lbu t0, 46(s4)
	add t0, t0, t1
	sb t0, 46(s4)
	srli t1, t0, 8
	lbu t0, 45(s4)
	add t0, t0, t1
	sb t0, 45(s4)
	srli t1, t0, 8
	lbu t0, 44(s4)
	add t0, t0, t1
	sb t0, 44(s4)
	srli t1, t0, 8
	addi s2, s2, 16
	addi s3, s3, -1
	bnez s3, 26b
	j 25f
24:
25:
	addi s2, s1, 0
	lbu t0, 32(s4)
	lbu t2, 33(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 34(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 35(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 0(s2)
	srli t2, t0, 8
	sb t2, 1(s2)
	srli t2, t0, 16
	sb t2, 2(s2)
	srli t2, t0, 24
	sb t2, 3(s2)
	lbu t0, 36(s4)
	lbu t2, 37(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 38(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 39(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 4(s2)
	srli t2, t0, 8
	sb t2, 5(s2)
	srli t2, t0, 16
	sb t2, 6(s2)
	srli t2, t0, 24
	sb t2, 7(s2)
	lbu t0, 40(s4)
	lbu t2, 41(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 42(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 43(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 8(s2)
	srli t2, t0, 8
	sb t2, 9(s2)
	srli t2, t0, 16
	sb t2, 10(s2)
	srli t2, t0, 24
	sb t2, 11(s2)
	lbu t0, 44(s4)
	lbu t2, 45(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 46(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 47(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 12(s2)
	srli t2, t0, 8
	sb t2, 13(s2)
	srli t2, t0, 16
	sb t2, 14(s2)
	srli t2, t0, 24
	sb t2, 15(s2)
	addi t3, s4, 0
	ld s1, 0(t3)
	ld s2, 8(t3)
	ld s3, 16(t3)
	ld s4, 24(t3)
	addi t0, zero, 0
	addi t1, t3, 0
	addi t2, zero, 404
28:
	sd t0, 0(t1)
	addi t1, t1, 8
	addi t2, t2, -1
	bnez t2, 28b
	addi sp, sp, 1200
	addi sp, sp, 2032
	ret
	.option pop

vg_sm4_gcm_init:
	.option push
	.option arch, +m, +c
	addi sp, sp, -2032
	addi sp, sp, -528
	addi a2, sp, 0
	sd s0, 128(a2)
	sd s1, 136(a2)
	sd s2, 144(a2)
	sd s3, 152(a2)
	sd s4, 160(a2)
	sd s5, 168(a2)
	sd s6, 176(a2)
	sd s7, 184(a2)
	sd s8, 192(a2)
	sd s9, 200(a2)
	sd s10, 208(a2)
	sd s11, 216(a2)
	sd ra, 224(a2)
	addi s0, a2, 0
	addi s2, a1, 0
	call {vg_sm4_expand_key}
	addi t0, zero, 0
	sd t0, 240(s2)
	sd t0, 248(s2)
	sd t0, 96(s0)
	sd t0, 104(s0)
	addi a0, s2, 0
	addi a1, s0, 96
	addi a2, s2, 240
	addi a3, zero, 1
	call {vg_sm4_ctr32}
	addi t1, s0, 0
	ld s0, 128(t1)
	ld s1, 136(t1)
	ld s2, 144(t1)
	ld s3, 152(t1)
	ld s4, 160(t1)
	ld s5, 168(t1)
	ld s6, 176(t1)
	ld s7, 184(t1)
	ld s8, 192(t1)
	ld s9, 200(t1)
	ld s10, 208(t1)
	ld s11, 216(t1)
	ld ra, 224(t1)
	addi sp, sp, 528
	addi sp, sp, 2032
	ret
	.option pop

vg_sm4_gcm_seal:
	.option push
	.option arch, +m, +c
	addi sp, sp, -2032
	addi sp, sp, -544
	addi t0, sp, 0
	addi t1, t0, 8
	sd t1, 0(t0)
	addi t1, sp, 0
	ld t1, 0(t1)
	sd s0, 128(t1)
	sd s1, 136(t1)
	sd s2, 144(t1)
	sd s3, 152(t1)
	sd s4, 160(t1)
	sd s5, 168(t1)
	sd s6, 176(t1)
	sd s7, 184(t1)
	sd s8, 192(t1)
	sd s9, 200(t1)
	sd s10, 208(t1)
	sd s11, 216(t1)
	sd ra, 224(t1)
	addi s0, t1, 0
	addi s2, a0, 0
	addi s1, s0, 16
	addi s4, a1, 0
	addi s5, a2, 0
	addi s7, a2, 0
	sd a3, 232(s0)
	addi s10, a4, 0
	sd a5, 240(s0)
	addi s11, a6, 0
	addi s9, a7, 0
	addi a2, s5, -12
	beqz a2, 20f
	addi t0, zero, 0
	sd t0, 0(s1)
	sd t0, 8(s1)
	addi s6, zero, 0
	beqz s5, 22f
	beqz s6, 24f
	addi a2, zero, 16
	sub a2, a2, s6
	srli a3, s5, 4
	bnez a3, 26f
	sub a3, s5, a2
	srli a3, a3, 63
	bnez a3, 28f
	j 29f
28:
	addi a2, s5, 0
29:
	j 27f
26:
27:
	addi a1, s1, 32
	add a1, a1, s6
	addi a0, s4, 0
	add s4, s4, a2
	sub s5, s5, a2
	add s6, s6, a2
210:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 210b
	addi a3, s6, -16
	beqz a3, 211f
	j 212f
211:
	addi a0, s2, 240
	addi a1, s1, 0
	addi a2, s1, 32
	addi a3, zero, 1
	addi a4, s0, 512
	call {vg_ghash}
212:
	j 25f
24:
25:
	addi a2, s4, 0
	srli a3, s5, 4
	andi a5, s5, 15
	sub a6, s5, a5
	add s4, s4, a6
	addi s5, a5, 0
	beqz a3, 213f
	addi a0, s2, 240
	addi a1, s1, 0
	addi a4, s0, 512
	call {vg_ghash}
	j 214f
213:
214:
	beqz s5, 215f
	addi a0, s4, 0
	addi a1, s1, 32
	addi a2, s5, 0
217:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 217b
	j 216f
215:
216:
	j 23f
22:
23:
	andi s6, s7, 15
	beqz s6, 218f
	addi t0, zero, 0
	sd t0, 96(s0)
	sd t0, 104(s0)
	addi a0, s1, 32
	addi a1, s0, 96
	addi a2, s6, 0
220:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 220b
	addi a0, s2, 240
	addi a1, s1, 0
	addi a2, s0, 96
	addi a3, zero, 1
	addi a4, s0, 512
	call {vg_ghash}
	j 219f
218:
219:
	addi s4, zero, 0
	addi s6, s7, 0
	slli a0, s4, 3
	slli a1, s6, 3
	srli t0, a0, 56
	sb t0, 96(s0)
	srli t0, a0, 48
	sb t0, 97(s0)
	srli t0, a0, 40
	sb t0, 98(s0)
	srli t0, a0, 32
	sb t0, 99(s0)
	srli t0, a0, 24
	sb t0, 100(s0)
	srli t0, a0, 16
	sb t0, 101(s0)
	srli t0, a0, 8
	sb t0, 102(s0)
	srli t0, a0, 0
	sb t0, 103(s0)
	srli t0, a1, 56
	sb t0, 104(s0)
	srli t0, a1, 48
	sb t0, 105(s0)
	srli t0, a1, 40
	sb t0, 106(s0)
	srli t0, a1, 32
	sb t0, 107(s0)
	srli t0, a1, 24
	sb t0, 108(s0)
	srli t0, a1, 16
	sb t0, 109(s0)
	srli t0, a1, 8
	sb t0, 110(s0)
	srli t0, a1, 0
	sb t0, 111(s0)
	addi a0, s2, 240
	addi a1, s1, 0
	addi a2, s0, 96
	addi a3, zero, 1
	addi a4, s0, 512
	call {vg_ghash}
	j 21f
20:
	lbu t0, 0(s4)
	sb t0, 0(s1)
	lbu t0, 1(s4)
	sb t0, 1(s1)
	lbu t0, 2(s4)
	sb t0, 2(s1)
	lbu t0, 3(s4)
	sb t0, 3(s1)
	lbu t0, 4(s4)
	sb t0, 4(s1)
	lbu t0, 5(s4)
	sb t0, 5(s1)
	lbu t0, 6(s4)
	sb t0, 6(s1)
	lbu t0, 7(s4)
	sb t0, 7(s1)
	lbu t0, 8(s4)
	sb t0, 8(s1)
	lbu t0, 9(s4)
	sb t0, 9(s1)
	lbu t0, 10(s4)
	sb t0, 10(s1)
	lbu t0, 11(s4)
	sb t0, 11(s1)
	addi t0, zero, 0
	sb t0, 12(s1)
	addi t0, zero, 0
	sb t0, 13(s1)
	addi t0, zero, 0
	sb t0, 14(s1)
	addi t0, zero, 1
	sb t0, 15(s1)
21:
	ld t0, 0(s1)
	sd t0, 48(s1)
	lwu t0, 8(s1)
	sw t0, 56(s1)
	lbu a0, 12(s1)
	slli a0, a0, 24
	lbu t0, 13(s1)
	slli t0, t0, 16
	or a0, a0, t0
	lbu t0, 14(s1)
	slli t0, t0, 8
	or a0, a0, t0
	lbu t0, 15(s1)
	or a0, a0, t0
	addi a0, a0, 1
	srli t0, a0, 24
	sb t0, 60(s1)
	srli t0, a0, 16
	sb t0, 61(s1)
	srli t0, a0, 8
	sb t0, 62(s1)
	srli t0, a0, 0
	sb t0, 63(s1)
	addi t0, zero, 0
	sd t0, 16(s1)
	sd t0, 24(s1)
	ld s4, 232(s0)
	addi s5, s10, 0
	addi s6, zero, 0
	beqz s5, 221f
	beqz s6, 223f
	addi a2, zero, 16
	sub a2, a2, s6
	srli a3, s5, 4
	bnez a3, 225f
	sub a3, s5, a2
	srli a3, a3, 63
	bnez a3, 227f
	j 228f
227:
	addi a2, s5, 0
228:
	j 226f
225:
226:
	addi a1, s1, 32
	add a1, a1, s6
	addi a0, s4, 0
	add s4, s4, a2
	sub s5, s5, a2
	add s6, s6, a2
229:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 229b
	addi a3, s6, -16
	beqz a3, 230f
	j 231f
230:
	addi a0, s2, 240
	addi a1, s1, 16
	addi a2, s1, 32
	addi a3, zero, 1
	addi a4, s0, 512
	call {vg_ghash}
231:
	j 224f
223:
224:
	addi a2, s4, 0
	srli a3, s5, 4
	andi a5, s5, 15
	sub a6, s5, a5
	add s4, s4, a6
	addi s5, a5, 0
	beqz a3, 232f
	addi a0, s2, 240
	addi a1, s1, 16
	addi a4, s0, 512
	call {vg_ghash}
	j 233f
232:
233:
	beqz s5, 234f
	addi a0, s4, 0
	addi a1, s1, 32
	addi a2, s5, 0
236:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 236b
	j 235f
234:
235:
	j 222f
221:
222:
	andi s6, s10, 15
	beqz s6, 237f
	addi t0, zero, 0
	sd t0, 96(s0)
	sd t0, 104(s0)
	addi a0, s1, 32
	addi a1, s0, 96
	addi a2, s6, 0
239:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 239b
	addi a0, s2, 240
	addi a1, s1, 16
	addi a2, s0, 96
	addi a3, zero, 1
	addi a4, s0, 512
	call {vg_ghash}
	j 238f
237:
238:
	ld s4, 240(s0)
	addi s5, s11, 0
	addi s6, zero, 0
	beqz s5, 240f
	beqz s6, 242f
	addi a2, zero, 16
	sub a2, a2, s6
	srli a3, s5, 4
	bnez a3, 244f
	sub a3, s5, a2
	srli a3, a3, 63
	bnez a3, 246f
	j 247f
246:
	addi a2, s5, 0
247:
	j 245f
244:
245:
	addi a0, s1, 64
	add a0, a0, s6
	addi a1, s4, 0
	add s4, s4, a2
	sub s5, s5, a2
248:
	lbu t0, 0(a1)
	lbu a3, 0(a0)
	xor t0, t0, a3
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 248b
	j 243f
242:
243:
	addi a3, s4, 0
	srli a4, s5, 4
	andi a5, s5, 15
	sub a6, s5, a5
	add s4, s4, a6
	addi s5, a5, 0
	beqz a4, 249f
	addi a0, s2, 0
	addi a1, s1, 48
	addi a2, a3, 0
	addi a3, a4, 0
	call {vg_sm4_ctr32}
	j 250f
249:
250:
	beqz s5, 251f
	addi t0, zero, 0
	sd t0, 64(s1)
	sd t0, 72(s1)
	addi a3, s1, 64
	addi a4, zero, 1
	addi a0, s2, 0
	addi a1, s1, 48
	addi a2, a3, 0
	addi a3, a4, 0
	call {vg_sm4_ctr32}
	addi a0, s1, 64
	addi a1, s4, 0
	addi a2, s5, 0
253:
	lbu t0, 0(a1)
	lbu a3, 0(a0)
	xor t0, t0, a3
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 253b
	j 252f
251:
252:
	j 241f
240:
241:
	ld s4, 240(s0)
	addi s5, s11, 0
	addi s6, zero, 0
	beqz s5, 254f
	beqz s6, 256f
	addi a2, zero, 16
	sub a2, a2, s6
	srli a3, s5, 4
	bnez a3, 258f
	sub a3, s5, a2
	srli a3, a3, 63
	bnez a3, 260f
	j 261f
260:
	addi a2, s5, 0
261:
	j 259f
258:
259:
	addi a1, s1, 32
	add a1, a1, s6
	addi a0, s4, 0
	add s4, s4, a2
	sub s5, s5, a2
	add s6, s6, a2
262:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 262b
	addi a3, s6, -16
	beqz a3, 263f
	j 264f
263:
	addi a0, s2, 240
	addi a1, s1, 16
	addi a2, s1, 32
	addi a3, zero, 1
	addi a4, s0, 512
	call {vg_ghash}
264:
	j 257f
256:
257:
	addi a2, s4, 0
	srli a3, s5, 4
	andi a5, s5, 15
	sub a6, s5, a5
	add s4, s4, a6
	addi s5, a5, 0
	beqz a3, 265f
	addi a0, s2, 240
	addi a1, s1, 16
	addi a4, s0, 512
	call {vg_ghash}
	j 266f
265:
266:
	beqz s5, 267f
	addi a0, s4, 0
	addi a1, s1, 32
	addi a2, s5, 0
269:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 269b
	j 268f
267:
268:
	j 255f
254:
255:
	andi s6, s11, 15
	beqz s6, 270f
	addi t0, zero, 0
	sd t0, 96(s0)
	sd t0, 104(s0)
	addi a0, s1, 32
	addi a1, s0, 96
	addi a2, s6, 0
272:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 272b
	addi a0, s2, 240
	addi a1, s1, 16
	addi a2, s0, 96
	addi a3, zero, 1
	addi a4, s0, 512
	call {vg_ghash}
	j 271f
270:
271:
	addi s4, s10, 0
	addi s6, s11, 0
	slli a0, s4, 3
	slli a1, s6, 3
	srli t0, a0, 56
	sb t0, 96(s0)
	srli t0, a0, 48
	sb t0, 97(s0)
	srli t0, a0, 40
	sb t0, 98(s0)
	srli t0, a0, 32
	sb t0, 99(s0)
	srli t0, a0, 24
	sb t0, 100(s0)
	srli t0, a0, 16
	sb t0, 101(s0)
	srli t0, a0, 8
	sb t0, 102(s0)
	srli t0, a0, 0
	sb t0, 103(s0)
	srli t0, a1, 56
	sb t0, 104(s0)
	srli t0, a1, 48
	sb t0, 105(s0)
	srli t0, a1, 40
	sb t0, 106(s0)
	srli t0, a1, 32
	sb t0, 107(s0)
	srli t0, a1, 24
	sb t0, 108(s0)
	srli t0, a1, 16
	sb t0, 109(s0)
	srli t0, a1, 8
	sb t0, 110(s0)
	srli t0, a1, 0
	sb t0, 111(s0)
	addi a0, s2, 240
	addi a1, s1, 16
	addi a2, s0, 96
	addi a3, zero, 1
	addi a4, s0, 512
	call {vg_ghash}
	ld t0, 16(s1)
	sd t0, 0(s0)
	ld t0, 24(s1)
	sd t0, 8(s0)
	addi a0, s2, 0
	addi a1, s1, 0
	addi a2, s0, 0
	addi a3, zero, 1
	call {vg_sm4_ctr32}
	lbu t0, 0(s0)
	sb t0, 0(s9)
	lbu t0, 1(s0)
	sb t0, 1(s9)
	lbu t0, 2(s0)
	sb t0, 2(s9)
	lbu t0, 3(s0)
	sb t0, 3(s9)
	lbu t0, 4(s0)
	sb t0, 4(s9)
	lbu t0, 5(s0)
	sb t0, 5(s9)
	lbu t0, 6(s0)
	sb t0, 6(s9)
	lbu t0, 7(s0)
	sb t0, 7(s9)
	lbu t0, 8(s0)
	sb t0, 8(s9)
	lbu t0, 9(s0)
	sb t0, 9(s9)
	lbu t0, 10(s0)
	sb t0, 10(s9)
	lbu t0, 11(s0)
	sb t0, 11(s9)
	lbu t0, 12(s0)
	sb t0, 12(s9)
	lbu t0, 13(s0)
	sb t0, 13(s9)
	lbu t0, 14(s0)
	sb t0, 14(s9)
	lbu t0, 15(s0)
	sb t0, 15(s9)
	addi t1, s0, 0
	ld s0, 128(t1)
	ld s1, 136(t1)
	ld s2, 144(t1)
	ld s3, 152(t1)
	ld s4, 160(t1)
	ld s5, 168(t1)
	ld s6, 176(t1)
	ld s7, 184(t1)
	ld s8, 192(t1)
	ld s9, 200(t1)
	ld s10, 208(t1)
	ld s11, 216(t1)
	ld ra, 224(t1)
	addi sp, sp, 544
	addi sp, sp, 2032
	ret
	.option pop

vg_sm4_gcm_open:
	.option push
	.option arch, +m, +c
	addi sp, sp, -2032
	addi sp, sp, -544
	addi t0, sp, 0
	addi t1, t0, 2032
	ld t1, 544(t1)
	sd t1, 0(t0)
	addi t1, t0, 16
	sd t1, 8(t0)
	addi t1, sp, 0
	ld t1, 8(t1)
	sd s0, 128(t1)
	sd s1, 136(t1)
	sd s2, 144(t1)
	sd s3, 152(t1)
	sd s4, 160(t1)
	sd s5, 168(t1)
	sd s6, 176(t1)
	sd s7, 184(t1)
	sd s8, 192(t1)
	sd s9, 200(t1)
	sd s10, 208(t1)
	sd s11, 216(t1)
	sd ra, 224(t1)
	addi s0, t1, 0
	addi s2, a0, 0
	addi s1, s0, 16
	addi s4, a1, 0
	addi s5, a2, 0
	addi s7, a2, 0
	sd a3, 232(s0)
	addi s10, a4, 0
	sd a5, 240(s0)
	addi s11, a6, 0
	addi s9, a7, 0
	addi t1, sp, 0
	ld s8, 0(t1)
	addi s5, zero, 0
	srli t0, s8, 2
	beqz t0, 20f
	srli t0, s8, 4
	beqz t0, 22f
	addi t0, s8, -16
	beqz t0, 24f
	j 25f
24:
	addi s5, zero, 1
25:
	j 23f
22:
	addi s5, zero, 1
23:
	j 21f
20:
21:
	beqz s5, 26f
	addi s5, s7, 0
	addi a2, s5, -12
	beqz a2, 28f
	addi t0, zero, 0
	sd t0, 0(s1)
	sd t0, 8(s1)
	addi s6, zero, 0
	beqz s5, 210f
	beqz s6, 212f
	addi a2, zero, 16
	sub a2, a2, s6
	srli a3, s5, 4
	bnez a3, 214f
	sub a3, s5, a2
	srli a3, a3, 63
	bnez a3, 216f
	j 217f
216:
	addi a2, s5, 0
217:
	j 215f
214:
215:
	addi a1, s1, 32
	add a1, a1, s6
	addi a0, s4, 0
	add s4, s4, a2
	sub s5, s5, a2
	add s6, s6, a2
218:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 218b
	addi a3, s6, -16
	beqz a3, 219f
	j 220f
219:
	addi a0, s2, 240
	addi a1, s1, 0
	addi a2, s1, 32
	addi a3, zero, 1
	addi a4, s0, 512
	call {vg_ghash}
220:
	j 213f
212:
213:
	addi a2, s4, 0
	srli a3, s5, 4
	andi a5, s5, 15
	sub a6, s5, a5
	add s4, s4, a6
	addi s5, a5, 0
	beqz a3, 221f
	addi a0, s2, 240
	addi a1, s1, 0
	addi a4, s0, 512
	call {vg_ghash}
	j 222f
221:
222:
	beqz s5, 223f
	addi a0, s4, 0
	addi a1, s1, 32
	addi a2, s5, 0
225:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 225b
	j 224f
223:
224:
	j 211f
210:
211:
	andi s6, s7, 15
	beqz s6, 226f
	addi t0, zero, 0
	sd t0, 96(s0)
	sd t0, 104(s0)
	addi a0, s1, 32
	addi a1, s0, 96
	addi a2, s6, 0
228:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 228b
	addi a0, s2, 240
	addi a1, s1, 0
	addi a2, s0, 96
	addi a3, zero, 1
	addi a4, s0, 512
	call {vg_ghash}
	j 227f
226:
227:
	addi s4, zero, 0
	addi s6, s7, 0
	slli a0, s4, 3
	slli a1, s6, 3
	srli t0, a0, 56
	sb t0, 96(s0)
	srli t0, a0, 48
	sb t0, 97(s0)
	srli t0, a0, 40
	sb t0, 98(s0)
	srli t0, a0, 32
	sb t0, 99(s0)
	srli t0, a0, 24
	sb t0, 100(s0)
	srli t0, a0, 16
	sb t0, 101(s0)
	srli t0, a0, 8
	sb t0, 102(s0)
	srli t0, a0, 0
	sb t0, 103(s0)
	srli t0, a1, 56
	sb t0, 104(s0)
	srli t0, a1, 48
	sb t0, 105(s0)
	srli t0, a1, 40
	sb t0, 106(s0)
	srli t0, a1, 32
	sb t0, 107(s0)
	srli t0, a1, 24
	sb t0, 108(s0)
	srli t0, a1, 16
	sb t0, 109(s0)
	srli t0, a1, 8
	sb t0, 110(s0)
	srli t0, a1, 0
	sb t0, 111(s0)
	addi a0, s2, 240
	addi a1, s1, 0
	addi a2, s0, 96
	addi a3, zero, 1
	addi a4, s0, 512
	call {vg_ghash}
	j 29f
28:
	lbu t0, 0(s4)
	sb t0, 0(s1)
	lbu t0, 1(s4)
	sb t0, 1(s1)
	lbu t0, 2(s4)
	sb t0, 2(s1)
	lbu t0, 3(s4)
	sb t0, 3(s1)
	lbu t0, 4(s4)
	sb t0, 4(s1)
	lbu t0, 5(s4)
	sb t0, 5(s1)
	lbu t0, 6(s4)
	sb t0, 6(s1)
	lbu t0, 7(s4)
	sb t0, 7(s1)
	lbu t0, 8(s4)
	sb t0, 8(s1)
	lbu t0, 9(s4)
	sb t0, 9(s1)
	lbu t0, 10(s4)
	sb t0, 10(s1)
	lbu t0, 11(s4)
	sb t0, 11(s1)
	addi t0, zero, 0
	sb t0, 12(s1)
	addi t0, zero, 0
	sb t0, 13(s1)
	addi t0, zero, 0
	sb t0, 14(s1)
	addi t0, zero, 1
	sb t0, 15(s1)
29:
	ld t0, 0(s1)
	sd t0, 48(s1)
	lwu t0, 8(s1)
	sw t0, 56(s1)
	lbu a0, 12(s1)
	slli a0, a0, 24
	lbu t0, 13(s1)
	slli t0, t0, 16
	or a0, a0, t0
	lbu t0, 14(s1)
	slli t0, t0, 8
	or a0, a0, t0
	lbu t0, 15(s1)
	or a0, a0, t0
	addi a0, a0, 1
	srli t0, a0, 24
	sb t0, 60(s1)
	srli t0, a0, 16
	sb t0, 61(s1)
	srli t0, a0, 8
	sb t0, 62(s1)
	srli t0, a0, 0
	sb t0, 63(s1)
	addi t0, zero, 0
	sd t0, 16(s1)
	sd t0, 24(s1)
	ld s4, 232(s0)
	addi s5, s10, 0
	addi s6, zero, 0
	beqz s5, 229f
	beqz s6, 231f
	addi a2, zero, 16
	sub a2, a2, s6
	srli a3, s5, 4
	bnez a3, 233f
	sub a3, s5, a2
	srli a3, a3, 63
	bnez a3, 235f
	j 236f
235:
	addi a2, s5, 0
236:
	j 234f
233:
234:
	addi a1, s1, 32
	add a1, a1, s6
	addi a0, s4, 0
	add s4, s4, a2
	sub s5, s5, a2
	add s6, s6, a2
237:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 237b
	addi a3, s6, -16
	beqz a3, 238f
	j 239f
238:
	addi a0, s2, 240
	addi a1, s1, 16
	addi a2, s1, 32
	addi a3, zero, 1
	addi a4, s0, 512
	call {vg_ghash}
239:
	j 232f
231:
232:
	addi a2, s4, 0
	srli a3, s5, 4
	andi a5, s5, 15
	sub a6, s5, a5
	add s4, s4, a6
	addi s5, a5, 0
	beqz a3, 240f
	addi a0, s2, 240
	addi a1, s1, 16
	addi a4, s0, 512
	call {vg_ghash}
	j 241f
240:
241:
	beqz s5, 242f
	addi a0, s4, 0
	addi a1, s1, 32
	addi a2, s5, 0
244:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 244b
	j 243f
242:
243:
	j 230f
229:
230:
	andi s6, s10, 15
	beqz s6, 245f
	addi t0, zero, 0
	sd t0, 96(s0)
	sd t0, 104(s0)
	addi a0, s1, 32
	addi a1, s0, 96
	addi a2, s6, 0
247:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 247b
	addi a0, s2, 240
	addi a1, s1, 16
	addi a2, s0, 96
	addi a3, zero, 1
	addi a4, s0, 512
	call {vg_ghash}
	j 246f
245:
246:
	ld s4, 240(s0)
	addi s5, s11, 0
	addi s6, zero, 0
	beqz s5, 248f
	beqz s6, 250f
	addi a2, zero, 16
	sub a2, a2, s6
	srli a3, s5, 4
	bnez a3, 252f
	sub a3, s5, a2
	srli a3, a3, 63
	bnez a3, 254f
	j 255f
254:
	addi a2, s5, 0
255:
	j 253f
252:
253:
	addi a1, s1, 32
	add a1, a1, s6
	addi a0, s4, 0
	add s4, s4, a2
	sub s5, s5, a2
	add s6, s6, a2
256:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 256b
	addi a3, s6, -16
	beqz a3, 257f
	j 258f
257:
	addi a0, s2, 240
	addi a1, s1, 16
	addi a2, s1, 32
	addi a3, zero, 1
	addi a4, s0, 512
	call {vg_ghash}
258:
	j 251f
250:
251:
	addi a2, s4, 0
	srli a3, s5, 4
	andi a5, s5, 15
	sub a6, s5, a5
	add s4, s4, a6
	addi s5, a5, 0
	beqz a3, 259f
	addi a0, s2, 240
	addi a1, s1, 16
	addi a4, s0, 512
	call {vg_ghash}
	j 260f
259:
260:
	beqz s5, 261f
	addi a0, s4, 0
	addi a1, s1, 32
	addi a2, s5, 0
263:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 263b
	j 262f
261:
262:
	j 249f
248:
249:
	andi s6, s11, 15
	beqz s6, 264f
	addi t0, zero, 0
	sd t0, 96(s0)
	sd t0, 104(s0)
	addi a0, s1, 32
	addi a1, s0, 96
	addi a2, s6, 0
266:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 266b
	addi a0, s2, 240
	addi a1, s1, 16
	addi a2, s0, 96
	addi a3, zero, 1
	addi a4, s0, 512
	call {vg_ghash}
	j 265f
264:
265:
	addi s4, s10, 0
	addi s6, s11, 0
	slli a0, s4, 3
	slli a1, s6, 3
	srli t0, a0, 56
	sb t0, 96(s0)
	srli t0, a0, 48
	sb t0, 97(s0)
	srli t0, a0, 40
	sb t0, 98(s0)
	srli t0, a0, 32
	sb t0, 99(s0)
	srli t0, a0, 24
	sb t0, 100(s0)
	srli t0, a0, 16
	sb t0, 101(s0)
	srli t0, a0, 8
	sb t0, 102(s0)
	srli t0, a0, 0
	sb t0, 103(s0)
	srli t0, a1, 56
	sb t0, 104(s0)
	srli t0, a1, 48
	sb t0, 105(s0)
	srli t0, a1, 40
	sb t0, 106(s0)
	srli t0, a1, 32
	sb t0, 107(s0)
	srli t0, a1, 24
	sb t0, 108(s0)
	srli t0, a1, 16
	sb t0, 109(s0)
	srli t0, a1, 8
	sb t0, 110(s0)
	srli t0, a1, 0
	sb t0, 111(s0)
	addi a0, s2, 240
	addi a1, s1, 16
	addi a2, s0, 96
	addi a3, zero, 1
	addi a4, s0, 512
	call {vg_ghash}
	ld t0, 16(s1)
	sd t0, 112(s0)
	ld t0, 24(s1)
	sd t0, 120(s0)
	addi a0, s2, 0
	addi a1, s1, 0
	addi a2, s0, 112
	addi a3, zero, 1
	call {vg_sm4_ctr32}
	addi t0, zero, 0
	sd t0, 256(s0)
	sd t0, 264(s0)
	addi a0, s9, 0
	addi a1, s0, 256
	addi a2, s8, 0
267:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 267b
	addi t0, zero, 0
	sd t0, 272(s0)
	sd t0, 280(s0)
	addi a0, s0, 112
	addi a1, s0, 272
	addi a2, s8, 0
268:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 268b
	ld a0, 272(s0)
	ld a1, 256(s0)
	xor a0, a0, a1
	ld a1, 280(s0)
	ld a2, 264(s0)
	xor a1, a1, a2
	or a0, a0, a1
	addi a1, zero, 0
	sub a1, a1, a0
	or a0, a0, a1
	srli a0, a0, 63
	addi a1, zero, 1
	sub a0, a1, a0
	addi s8, a0, 0
	beqz s8, 269f
	ld s4, 240(s0)
	addi s5, s11, 0
	addi s6, zero, 0
	beqz s5, 271f
	beqz s6, 273f
	addi a2, zero, 16
	sub a2, a2, s6
	srli a3, s5, 4
	bnez a3, 275f
	sub a3, s5, a2
	srli a3, a3, 63
	bnez a3, 277f
	j 278f
277:
	addi a2, s5, 0
278:
	j 276f
275:
276:
	addi a0, s1, 64
	add a0, a0, s6
	addi a1, s4, 0
	add s4, s4, a2
	sub s5, s5, a2
279:
	lbu t0, 0(a1)
	lbu a3, 0(a0)
	xor t0, t0, a3
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 279b
	j 274f
273:
274:
	addi a3, s4, 0
	srli a4, s5, 4
	andi a5, s5, 15
	sub a6, s5, a5
	add s4, s4, a6
	addi s5, a5, 0
	beqz a4, 280f
	addi a0, s2, 0
	addi a1, s1, 48
	addi a2, a3, 0
	addi a3, a4, 0
	call {vg_sm4_ctr32}
	j 281f
280:
281:
	beqz s5, 282f
	addi t0, zero, 0
	sd t0, 64(s1)
	sd t0, 72(s1)
	addi a3, s1, 64
	addi a4, zero, 1
	addi a0, s2, 0
	addi a1, s1, 48
	addi a2, a3, 0
	addi a3, a4, 0
	call {vg_sm4_ctr32}
	addi a0, s1, 64
	addi a1, s4, 0
	addi a2, s5, 0
284:
	lbu t0, 0(a1)
	lbu a3, 0(a0)
	xor t0, t0, a3
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 284b
	j 283f
282:
283:
	j 272f
271:
272:
	j 270f
269:
270:
	addi a0, s8, 0
	j 27f
26:
	addi a0, zero, 0
27:
	addi t1, s0, 0
	ld s0, 128(t1)
	ld s1, 136(t1)
	ld s2, 144(t1)
	ld s3, 152(t1)
	ld s4, 160(t1)
	ld s5, 168(t1)
	ld s6, 176(t1)
	ld s7, 184(t1)
	ld s8, 192(t1)
	ld s9, 200(t1)
	ld s10, 208(t1)
	ld s11, 216(t1)
	ld ra, 224(t1)
	addi sp, sp, 544
	addi sp, sp, 2032
	ret
	.option pop

vg_sm4_gcm_stream_init:
	.option push
	.option arch, +m, +c
	addi sp, sp, -2032
	addi sp, sp, -528
	addi a4, sp, 0
	sd s0, 128(a4)
	sd s1, 136(a4)
	sd s2, 144(a4)
	sd s3, 152(a4)
	sd s4, 160(a4)
	sd s5, 168(a4)
	sd s6, 176(a4)
	sd s7, 184(a4)
	sd s8, 192(a4)
	sd s9, 200(a4)
	sd s10, 208(a4)
	sd s11, 216(a4)
	sd ra, 224(a4)
	addi s0, a4, 0
	addi s1, a3, 0
	addi s2, a0, 0
	addi s4, a1, 0
	addi s5, a2, 0
	addi s7, a2, 0
	addi a2, s5, -12
	beqz a2, 20f
	addi t0, zero, 0
	sd t0, 0(s1)
	sd t0, 8(s1)
	addi s6, zero, 0
	beqz s5, 22f
	beqz s6, 24f
	addi a2, zero, 16
	sub a2, a2, s6
	srli a3, s5, 4
	bnez a3, 26f
	sub a3, s5, a2
	srli a3, a3, 63
	bnez a3, 28f
	j 29f
28:
	addi a2, s5, 0
29:
	j 27f
26:
27:
	addi a1, s1, 32
	add a1, a1, s6
	addi a0, s4, 0
	add s4, s4, a2
	sub s5, s5, a2
	add s6, s6, a2
210:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 210b
	addi a3, s6, -16
	beqz a3, 211f
	j 212f
211:
	addi a0, s2, 240
	addi a1, s1, 0
	addi a2, s1, 32
	addi a3, zero, 1
	addi a4, s0, 512
	call {vg_ghash}
212:
	j 25f
24:
25:
	addi a2, s4, 0
	srli a3, s5, 4
	andi a5, s5, 15
	sub a6, s5, a5
	add s4, s4, a6
	addi s5, a5, 0
	beqz a3, 213f
	addi a0, s2, 240
	addi a1, s1, 0
	addi a4, s0, 512
	call {vg_ghash}
	j 214f
213:
214:
	beqz s5, 215f
	addi a0, s4, 0
	addi a1, s1, 32
	addi a2, s5, 0
217:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 217b
	j 216f
215:
216:
	j 23f
22:
23:
	andi s6, s7, 15
	beqz s6, 218f
	addi t0, zero, 0
	sd t0, 96(s0)
	sd t0, 104(s0)
	addi a0, s1, 32
	addi a1, s0, 96
	addi a2, s6, 0
220:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 220b
	addi a0, s2, 240
	addi a1, s1, 0
	addi a2, s0, 96
	addi a3, zero, 1
	addi a4, s0, 512
	call {vg_ghash}
	j 219f
218:
219:
	addi s4, zero, 0
	addi s6, s7, 0
	slli a0, s4, 3
	slli a1, s6, 3
	srli t0, a0, 56
	sb t0, 96(s0)
	srli t0, a0, 48
	sb t0, 97(s0)
	srli t0, a0, 40
	sb t0, 98(s0)
	srli t0, a0, 32
	sb t0, 99(s0)
	srli t0, a0, 24
	sb t0, 100(s0)
	srli t0, a0, 16
	sb t0, 101(s0)
	srli t0, a0, 8
	sb t0, 102(s0)
	srli t0, a0, 0
	sb t0, 103(s0)
	srli t0, a1, 56
	sb t0, 104(s0)
	srli t0, a1, 48
	sb t0, 105(s0)
	srli t0, a1, 40
	sb t0, 106(s0)
	srli t0, a1, 32
	sb t0, 107(s0)
	srli t0, a1, 24
	sb t0, 108(s0)
	srli t0, a1, 16
	sb t0, 109(s0)
	srli t0, a1, 8
	sb t0, 110(s0)
	srli t0, a1, 0
	sb t0, 111(s0)
	addi a0, s2, 240
	addi a1, s1, 0
	addi a2, s0, 96
	addi a3, zero, 1
	addi a4, s0, 512
	call {vg_ghash}
	j 21f
20:
	lbu t0, 0(s4)
	sb t0, 0(s1)
	lbu t0, 1(s4)
	sb t0, 1(s1)
	lbu t0, 2(s4)
	sb t0, 2(s1)
	lbu t0, 3(s4)
	sb t0, 3(s1)
	lbu t0, 4(s4)
	sb t0, 4(s1)
	lbu t0, 5(s4)
	sb t0, 5(s1)
	lbu t0, 6(s4)
	sb t0, 6(s1)
	lbu t0, 7(s4)
	sb t0, 7(s1)
	lbu t0, 8(s4)
	sb t0, 8(s1)
	lbu t0, 9(s4)
	sb t0, 9(s1)
	lbu t0, 10(s4)
	sb t0, 10(s1)
	lbu t0, 11(s4)
	sb t0, 11(s1)
	addi t0, zero, 0
	sb t0, 12(s1)
	addi t0, zero, 0
	sb t0, 13(s1)
	addi t0, zero, 0
	sb t0, 14(s1)
	addi t0, zero, 1
	sb t0, 15(s1)
21:
	ld t0, 0(s1)
	sd t0, 48(s1)
	lwu t0, 8(s1)
	sw t0, 56(s1)
	lbu a0, 12(s1)
	slli a0, a0, 24
	lbu t0, 13(s1)
	slli t0, t0, 16
	or a0, a0, t0
	lbu t0, 14(s1)
	slli t0, t0, 8
	or a0, a0, t0
	lbu t0, 15(s1)
	or a0, a0, t0
	addi a0, a0, 1
	srli t0, a0, 24
	sb t0, 60(s1)
	srli t0, a0, 16
	sb t0, 61(s1)
	srli t0, a0, 8
	sb t0, 62(s1)
	srli t0, a0, 0
	sb t0, 63(s1)
	addi t0, zero, 0
	sd t0, 16(s1)
	sd t0, 24(s1)
	addi t1, s0, 0
	ld s0, 128(t1)
	ld s1, 136(t1)
	ld s2, 144(t1)
	ld s3, 152(t1)
	ld s4, 160(t1)
	ld s5, 168(t1)
	ld s6, 176(t1)
	ld s7, 184(t1)
	ld s8, 192(t1)
	ld s9, 200(t1)
	ld s10, 208(t1)
	ld s11, 216(t1)
	ld ra, 224(t1)
	addi sp, sp, 528
	addi sp, sp, 2032
	ret
	.option pop

vg_sm4_gcm_stream_aad:
	.option push
	.option arch, +m, +c
	addi sp, sp, -2032
	addi sp, sp, -528
	addi a5, sp, 0
	sd s0, 128(a5)
	sd s1, 136(a5)
	sd s2, 144(a5)
	sd s3, 152(a5)
	sd s4, 160(a5)
	sd s5, 168(a5)
	sd s6, 176(a5)
	sd s7, 184(a5)
	sd s8, 192(a5)
	sd s9, 200(a5)
	sd s10, 208(a5)
	sd s11, 216(a5)
	sd ra, 224(a5)
	addi s0, a5, 0
	addi s1, a1, 0
	addi s2, a0, 0
	addi s4, a3, 0
	addi s5, a4, 0
	andi s6, a2, 15
	beqz s5, 20f
	beqz s6, 22f
	addi a2, zero, 16
	sub a2, a2, s6
	srli a3, s5, 4
	bnez a3, 24f
	sub a3, s5, a2
	srli a3, a3, 63
	bnez a3, 26f
	j 27f
26:
	addi a2, s5, 0
27:
	j 25f
24:
25:
	addi a1, s1, 32
	add a1, a1, s6
	addi a0, s4, 0
	add s4, s4, a2
	sub s5, s5, a2
	add s6, s6, a2
28:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 28b
	addi a3, s6, -16
	beqz a3, 29f
	j 210f
29:
	addi a0, s2, 240
	addi a1, s1, 16
	addi a2, s1, 32
	addi a3, zero, 1
	addi a4, s0, 512
	call {vg_ghash}
210:
	j 23f
22:
23:
	addi a2, s4, 0
	srli a3, s5, 4
	andi a5, s5, 15
	sub a6, s5, a5
	add s4, s4, a6
	addi s5, a5, 0
	beqz a3, 211f
	addi a0, s2, 240
	addi a1, s1, 16
	addi a4, s0, 512
	call {vg_ghash}
	j 212f
211:
212:
	beqz s5, 213f
	addi a0, s4, 0
	addi a1, s1, 32
	addi a2, s5, 0
215:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 215b
	j 214f
213:
214:
	j 21f
20:
21:
	addi t1, s0, 0
	ld s0, 128(t1)
	ld s1, 136(t1)
	ld s2, 144(t1)
	ld s3, 152(t1)
	ld s4, 160(t1)
	ld s5, 168(t1)
	ld s6, 176(t1)
	ld s7, 184(t1)
	ld s8, 192(t1)
	ld s9, 200(t1)
	ld s10, 208(t1)
	ld s11, 216(t1)
	ld ra, 224(t1)
	addi sp, sp, 528
	addi sp, sp, 2032
	ret
	.option pop

vg_sm4_gcm_stream_encrypt:
	.option push
	.option arch, +m, +c
	addi sp, sp, -2032
	addi sp, sp, -528
	addi a6, sp, 0
	sd s0, 128(a6)
	sd s1, 136(a6)
	sd s2, 144(a6)
	sd s3, 152(a6)
	sd s4, 160(a6)
	sd s5, 168(a6)
	sd s6, 176(a6)
	sd s7, 184(a6)
	sd s8, 192(a6)
	sd s9, 200(a6)
	sd s10, 208(a6)
	sd s11, 216(a6)
	sd ra, 224(a6)
	addi s0, a6, 0
	addi s1, a1, 0
	addi s2, a0, 0
	addi s10, a2, 0
	addi s11, a3, 0
	addi s9, a4, 0
	addi s8, a5, 0
	addi s4, s9, 0
	addi s5, s8, 0
	andi s6, s11, 15
	beqz s5, 20f
	beqz s6, 22f
	addi a2, zero, 16
	sub a2, a2, s6
	srli a3, s5, 4
	bnez a3, 24f
	sub a3, s5, a2
	srli a3, a3, 63
	bnez a3, 26f
	j 27f
26:
	addi a2, s5, 0
27:
	j 25f
24:
25:
	addi a0, s1, 64
	add a0, a0, s6
	addi a1, s4, 0
	add s4, s4, a2
	sub s5, s5, a2
28:
	lbu t0, 0(a1)
	lbu a3, 0(a0)
	xor t0, t0, a3
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 28b
	j 23f
22:
23:
	addi a3, s4, 0
	srli a4, s5, 4
	andi a5, s5, 15
	sub a6, s5, a5
	add s4, s4, a6
	addi s5, a5, 0
	beqz a4, 29f
	addi a0, s2, 0
	addi a1, s1, 48
	addi a2, a3, 0
	addi a3, a4, 0
	call {vg_sm4_ctr32}
	j 210f
29:
210:
	beqz s5, 211f
	addi t0, zero, 0
	sd t0, 64(s1)
	sd t0, 72(s1)
	addi a3, s1, 64
	addi a4, zero, 1
	addi a0, s2, 0
	addi a1, s1, 48
	addi a2, a3, 0
	addi a3, a4, 0
	call {vg_sm4_ctr32}
	addi a0, s1, 64
	addi a1, s4, 0
	addi a2, s5, 0
213:
	lbu t0, 0(a1)
	lbu a3, 0(a0)
	xor t0, t0, a3
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 213b
	j 212f
211:
212:
	j 21f
20:
21:
	beqz s8, 214f
	beqz s11, 216f
	j 217f
216:
	andi s6, s10, 15
	beqz s6, 218f
	addi t0, zero, 0
	sd t0, 96(s0)
	sd t0, 104(s0)
	addi a0, s1, 32
	addi a1, s0, 96
	addi a2, s6, 0
220:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 220b
	addi a0, s2, 240
	addi a1, s1, 16
	addi a2, s0, 96
	addi a3, zero, 1
	addi a4, s0, 512
	call {vg_ghash}
	j 219f
218:
219:
217:
	addi s4, s9, 0
	addi s5, s8, 0
	andi s6, s11, 15
	beqz s5, 221f
	beqz s6, 223f
	addi a2, zero, 16
	sub a2, a2, s6
	srli a3, s5, 4
	bnez a3, 225f
	sub a3, s5, a2
	srli a3, a3, 63
	bnez a3, 227f
	j 228f
227:
	addi a2, s5, 0
228:
	j 226f
225:
226:
	addi a1, s1, 32
	add a1, a1, s6
	addi a0, s4, 0
	add s4, s4, a2
	sub s5, s5, a2
	add s6, s6, a2
229:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 229b
	addi a3, s6, -16
	beqz a3, 230f
	j 231f
230:
	addi a0, s2, 240
	addi a1, s1, 16
	addi a2, s1, 32
	addi a3, zero, 1
	addi a4, s0, 512
	call {vg_ghash}
231:
	j 224f
223:
224:
	addi a2, s4, 0
	srli a3, s5, 4
	andi a5, s5, 15
	sub a6, s5, a5
	add s4, s4, a6
	addi s5, a5, 0
	beqz a3, 232f
	addi a0, s2, 240
	addi a1, s1, 16
	addi a4, s0, 512
	call {vg_ghash}
	j 233f
232:
233:
	beqz s5, 234f
	addi a0, s4, 0
	addi a1, s1, 32
	addi a2, s5, 0
236:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 236b
	j 235f
234:
235:
	j 222f
221:
222:
	j 215f
214:
215:
	addi t1, s0, 0
	ld s0, 128(t1)
	ld s1, 136(t1)
	ld s2, 144(t1)
	ld s3, 152(t1)
	ld s4, 160(t1)
	ld s5, 168(t1)
	ld s6, 176(t1)
	ld s7, 184(t1)
	ld s8, 192(t1)
	ld s9, 200(t1)
	ld s10, 208(t1)
	ld s11, 216(t1)
	ld ra, 224(t1)
	addi sp, sp, 528
	addi sp, sp, 2032
	ret
	.option pop

vg_sm4_gcm_stream_decrypt:
	.option push
	.option arch, +m, +c
	addi sp, sp, -2032
	addi sp, sp, -528
	addi a6, sp, 0
	sd s0, 128(a6)
	sd s1, 136(a6)
	sd s2, 144(a6)
	sd s3, 152(a6)
	sd s4, 160(a6)
	sd s5, 168(a6)
	sd s6, 176(a6)
	sd s7, 184(a6)
	sd s8, 192(a6)
	sd s9, 200(a6)
	sd s10, 208(a6)
	sd s11, 216(a6)
	sd ra, 224(a6)
	addi s0, a6, 0
	addi s1, a1, 0
	addi s2, a0, 0
	addi s10, a2, 0
	addi s11, a3, 0
	addi s9, a4, 0
	addi s8, a5, 0
	beqz s8, 20f
	beqz s11, 22f
	j 23f
22:
	andi s6, s10, 15
	beqz s6, 24f
	addi t0, zero, 0
	sd t0, 96(s0)
	sd t0, 104(s0)
	addi a0, s1, 32
	addi a1, s0, 96
	addi a2, s6, 0
26:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 26b
	addi a0, s2, 240
	addi a1, s1, 16
	addi a2, s0, 96
	addi a3, zero, 1
	addi a4, s0, 512
	call {vg_ghash}
	j 25f
24:
25:
23:
	addi s4, s9, 0
	addi s5, s8, 0
	andi s6, s11, 15
	beqz s5, 27f
	beqz s6, 29f
	addi a2, zero, 16
	sub a2, a2, s6
	srli a3, s5, 4
	bnez a3, 211f
	sub a3, s5, a2
	srli a3, a3, 63
	bnez a3, 213f
	j 214f
213:
	addi a2, s5, 0
214:
	j 212f
211:
212:
	addi a1, s1, 32
	add a1, a1, s6
	addi a0, s4, 0
	add s4, s4, a2
	sub s5, s5, a2
	add s6, s6, a2
215:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 215b
	addi a3, s6, -16
	beqz a3, 216f
	j 217f
216:
	addi a0, s2, 240
	addi a1, s1, 16
	addi a2, s1, 32
	addi a3, zero, 1
	addi a4, s0, 512
	call {vg_ghash}
217:
	j 210f
29:
210:
	addi a2, s4, 0
	srli a3, s5, 4
	andi a5, s5, 15
	sub a6, s5, a5
	add s4, s4, a6
	addi s5, a5, 0
	beqz a3, 218f
	addi a0, s2, 240
	addi a1, s1, 16
	addi a4, s0, 512
	call {vg_ghash}
	j 219f
218:
219:
	beqz s5, 220f
	addi a0, s4, 0
	addi a1, s1, 32
	addi a2, s5, 0
222:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 222b
	j 221f
220:
221:
	j 28f
27:
28:
	j 21f
20:
21:
	addi s4, s9, 0
	addi s5, s8, 0
	andi s6, s11, 15
	beqz s5, 223f
	beqz s6, 225f
	addi a2, zero, 16
	sub a2, a2, s6
	srli a3, s5, 4
	bnez a3, 227f
	sub a3, s5, a2
	srli a3, a3, 63
	bnez a3, 229f
	j 230f
229:
	addi a2, s5, 0
230:
	j 228f
227:
228:
	addi a0, s1, 64
	add a0, a0, s6
	addi a1, s4, 0
	add s4, s4, a2
	sub s5, s5, a2
231:
	lbu t0, 0(a1)
	lbu a3, 0(a0)
	xor t0, t0, a3
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 231b
	j 226f
225:
226:
	addi a3, s4, 0
	srli a4, s5, 4
	andi a5, s5, 15
	sub a6, s5, a5
	add s4, s4, a6
	addi s5, a5, 0
	beqz a4, 232f
	addi a0, s2, 0
	addi a1, s1, 48
	addi a2, a3, 0
	addi a3, a4, 0
	call {vg_sm4_ctr32}
	j 233f
232:
233:
	beqz s5, 234f
	addi t0, zero, 0
	sd t0, 64(s1)
	sd t0, 72(s1)
	addi a3, s1, 64
	addi a4, zero, 1
	addi a0, s2, 0
	addi a1, s1, 48
	addi a2, a3, 0
	addi a3, a4, 0
	call {vg_sm4_ctr32}
	addi a0, s1, 64
	addi a1, s4, 0
	addi a2, s5, 0
236:
	lbu t0, 0(a1)
	lbu a3, 0(a0)
	xor t0, t0, a3
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 236b
	j 235f
234:
235:
	j 224f
223:
224:
	addi t1, s0, 0
	ld s0, 128(t1)
	ld s1, 136(t1)
	ld s2, 144(t1)
	ld s3, 152(t1)
	ld s4, 160(t1)
	ld s5, 168(t1)
	ld s6, 176(t1)
	ld s7, 184(t1)
	ld s8, 192(t1)
	ld s9, 200(t1)
	ld s10, 208(t1)
	ld s11, 216(t1)
	ld ra, 224(t1)
	addi sp, sp, 528
	addi sp, sp, 2032
	ret
	.option pop

vg_sm4_gcm_stream_finish:
	.option push
	.option arch, +m, +c
	addi sp, sp, -2032
	addi sp, sp, -528
	addi a5, sp, 0
	sd s0, 128(a5)
	sd s1, 136(a5)
	sd s2, 144(a5)
	sd s3, 152(a5)
	sd s4, 160(a5)
	sd s5, 168(a5)
	sd s6, 176(a5)
	sd s7, 184(a5)
	sd s8, 192(a5)
	sd s9, 200(a5)
	sd s10, 208(a5)
	sd s11, 216(a5)
	sd ra, 224(a5)
	addi s0, a5, 0
	addi s1, a1, 0
	addi s2, a0, 0
	addi s10, a2, 0
	addi s11, a3, 0
	addi s9, a4, 0
	beqz s11, 20f
	andi s6, s11, 15
	j 21f
20:
	andi s6, s10, 15
21:
	beqz s6, 22f
	addi t0, zero, 0
	sd t0, 96(s0)
	sd t0, 104(s0)
	addi a0, s1, 32
	addi a1, s0, 96
	addi a2, s6, 0
24:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 24b
	addi a0, s2, 240
	addi a1, s1, 16
	addi a2, s0, 96
	addi a3, zero, 1
	addi a4, s0, 512
	call {vg_ghash}
	j 23f
22:
23:
	addi s4, s10, 0
	addi s6, s11, 0
	slli a0, s4, 3
	slli a1, s6, 3
	srli t0, a0, 56
	sb t0, 96(s0)
	srli t0, a0, 48
	sb t0, 97(s0)
	srli t0, a0, 40
	sb t0, 98(s0)
	srli t0, a0, 32
	sb t0, 99(s0)
	srli t0, a0, 24
	sb t0, 100(s0)
	srli t0, a0, 16
	sb t0, 101(s0)
	srli t0, a0, 8
	sb t0, 102(s0)
	srli t0, a0, 0
	sb t0, 103(s0)
	srli t0, a1, 56
	sb t0, 104(s0)
	srli t0, a1, 48
	sb t0, 105(s0)
	srli t0, a1, 40
	sb t0, 106(s0)
	srli t0, a1, 32
	sb t0, 107(s0)
	srli t0, a1, 24
	sb t0, 108(s0)
	srli t0, a1, 16
	sb t0, 109(s0)
	srli t0, a1, 8
	sb t0, 110(s0)
	srli t0, a1, 0
	sb t0, 111(s0)
	addi a0, s2, 240
	addi a1, s1, 16
	addi a2, s0, 96
	addi a3, zero, 1
	addi a4, s0, 512
	call {vg_ghash}
	ld t0, 16(s1)
	sd t0, 0(s0)
	ld t0, 24(s1)
	sd t0, 8(s0)
	addi a0, s2, 0
	addi a1, s1, 0
	addi a2, s0, 0
	addi a3, zero, 1
	call {vg_sm4_ctr32}
	lbu t0, 0(s0)
	sb t0, 0(s9)
	lbu t0, 1(s0)
	sb t0, 1(s9)
	lbu t0, 2(s0)
	sb t0, 2(s9)
	lbu t0, 3(s0)
	sb t0, 3(s9)
	lbu t0, 4(s0)
	sb t0, 4(s9)
	lbu t0, 5(s0)
	sb t0, 5(s9)
	lbu t0, 6(s0)
	sb t0, 6(s9)
	lbu t0, 7(s0)
	sb t0, 7(s9)
	lbu t0, 8(s0)
	sb t0, 8(s9)
	lbu t0, 9(s0)
	sb t0, 9(s9)
	lbu t0, 10(s0)
	sb t0, 10(s9)
	lbu t0, 11(s0)
	sb t0, 11(s9)
	lbu t0, 12(s0)
	sb t0, 12(s9)
	lbu t0, 13(s0)
	sb t0, 13(s9)
	lbu t0, 14(s0)
	sb t0, 14(s9)
	lbu t0, 15(s0)
	sb t0, 15(s9)
	addi t1, s0, 0
	ld s0, 128(t1)
	ld s1, 136(t1)
	ld s2, 144(t1)
	ld s3, 152(t1)
	ld s4, 160(t1)
	ld s5, 168(t1)
	ld s6, 176(t1)
	ld s7, 184(t1)
	ld s8, 192(t1)
	ld s9, 200(t1)
	ld s10, 208(t1)
	ld s11, 216(t1)
	ld ra, 224(t1)
	addi sp, sp, 528
	addi sp, sp, 2032
	ret
	.option pop

vg_sm4_gcm_stream_verify:
	.option push
	.option arch, +m, +c
	addi sp, sp, -2032
	addi sp, sp, -528
	addi a6, sp, 0
	sd s0, 128(a6)
	sd s1, 136(a6)
	sd s2, 144(a6)
	sd s3, 152(a6)
	sd s4, 160(a6)
	sd s5, 168(a6)
	sd s6, 176(a6)
	sd s7, 184(a6)
	sd s8, 192(a6)
	sd s9, 200(a6)
	sd s10, 208(a6)
	sd s11, 216(a6)
	sd ra, 224(a6)
	addi s0, a6, 0
	addi s1, a1, 0
	addi s2, a0, 0
	addi s10, a2, 0
	addi s11, a3, 0
	addi s9, a4, 0
	addi s8, a5, 0
	addi s5, zero, 0
	srli t0, s8, 2
	beqz t0, 20f
	srli t0, s8, 4
	beqz t0, 22f
	addi t0, s8, -16
	beqz t0, 24f
	j 25f
24:
	addi s5, zero, 1
25:
	j 23f
22:
	addi s5, zero, 1
23:
	j 21f
20:
21:
	beqz s5, 26f
	addi t0, zero, 0
	sd t0, 256(s0)
	sd t0, 264(s0)
	addi a0, s9, 0
	addi a1, s0, 256
	addi a2, s8, 0
28:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 28b
	beqz s11, 29f
	andi s6, s11, 15
	j 210f
29:
	andi s6, s10, 15
210:
	beqz s6, 211f
	addi t0, zero, 0
	sd t0, 96(s0)
	sd t0, 104(s0)
	addi a0, s1, 32
	addi a1, s0, 96
	addi a2, s6, 0
213:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 213b
	addi a0, s2, 240
	addi a1, s1, 16
	addi a2, s0, 96
	addi a3, zero, 1
	addi a4, s0, 512
	call {vg_ghash}
	j 212f
211:
212:
	addi s4, s10, 0
	addi s6, s11, 0
	slli a0, s4, 3
	slli a1, s6, 3
	srli t0, a0, 56
	sb t0, 96(s0)
	srli t0, a0, 48
	sb t0, 97(s0)
	srli t0, a0, 40
	sb t0, 98(s0)
	srli t0, a0, 32
	sb t0, 99(s0)
	srli t0, a0, 24
	sb t0, 100(s0)
	srli t0, a0, 16
	sb t0, 101(s0)
	srli t0, a0, 8
	sb t0, 102(s0)
	srli t0, a0, 0
	sb t0, 103(s0)
	srli t0, a1, 56
	sb t0, 104(s0)
	srli t0, a1, 48
	sb t0, 105(s0)
	srli t0, a1, 40
	sb t0, 106(s0)
	srli t0, a1, 32
	sb t0, 107(s0)
	srli t0, a1, 24
	sb t0, 108(s0)
	srli t0, a1, 16
	sb t0, 109(s0)
	srli t0, a1, 8
	sb t0, 110(s0)
	srli t0, a1, 0
	sb t0, 111(s0)
	addi a0, s2, 240
	addi a1, s1, 16
	addi a2, s0, 96
	addi a3, zero, 1
	addi a4, s0, 512
	call {vg_ghash}
	ld t0, 16(s1)
	sd t0, 0(s0)
	ld t0, 24(s1)
	sd t0, 8(s0)
	addi a0, s2, 0
	addi a1, s1, 0
	addi a2, s0, 0
	addi a3, zero, 1
	call {vg_sm4_ctr32}
	addi t0, zero, 0
	sd t0, 272(s0)
	sd t0, 280(s0)
	addi a0, s0, 0
	addi a1, s0, 272
	addi a2, s8, 0
214:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 214b
	ld a0, 272(s0)
	ld a1, 256(s0)
	xor a0, a0, a1
	ld a1, 280(s0)
	ld a2, 264(s0)
	xor a1, a1, a2
	or a0, a0, a1
	addi a1, zero, 0
	sub a1, a1, a0
	or a0, a0, a1
	srli a0, a0, 63
	addi a1, zero, 1
	sub a0, a1, a0
	j 27f
26:
	addi a0, zero, 0
27:
	addi t1, s0, 0
	ld s0, 128(t1)
	ld s1, 136(t1)
	ld s2, 144(t1)
	ld s3, 152(t1)
	ld s4, 160(t1)
	ld s5, 168(t1)
	ld s6, 176(t1)
	ld s7, 184(t1)
	ld s8, 192(t1)
	ld s9, 200(t1)
	ld s10, 208(t1)
	ld s11, 216(t1)
	ld ra, 224(t1)
	addi sp, sp, 528
	addi sp, sp, 2032
	ret
	.option pop
