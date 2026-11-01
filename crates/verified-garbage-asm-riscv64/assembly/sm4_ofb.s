// The functions of `src/sm4_ofb.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sm4_ofb:
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
	lbu t0, 824(s4)
	lbu t2, 825(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 826(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 827(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 32(s4)
	srli t2, t0, 8
	sb t2, 33(s4)
	srli t2, t0, 16
	sb t2, 34(s4)
	srli t2, t0, 24
	sb t2, 35(s4)
	lbu t0, 828(s4)
	lbu t2, 829(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 830(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 831(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 36(s4)
	srli t2, t0, 8
	sb t2, 37(s4)
	srli t2, t0, 16
	sb t2, 38(s4)
	srli t2, t0, 24
	sb t2, 39(s4)
	lbu t0, 832(s4)
	lbu t2, 833(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 834(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 835(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 40(s4)
	srli t2, t0, 8
	sb t2, 41(s4)
	srli t2, t0, 16
	sb t2, 42(s4)
	srli t2, t0, 24
	sb t2, 43(s4)
	lbu t0, 836(s4)
	lbu t2, 837(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 838(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 839(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 44(s4)
	srli t2, t0, 8
	sb t2, 45(s4)
	srli t2, t0, 16
	sb t2, 46(s4)
	srli t2, t0, 24
	sb t2, 47(s4)
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
