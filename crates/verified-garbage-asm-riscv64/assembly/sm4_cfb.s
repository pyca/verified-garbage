// The functions of `src/sm4_cfb.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sm4_cfb128_encrypt:
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
	sw t0, 32(s4)
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
	sw t0, 36(s4)
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
	sw t0, 40(s4)
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
	sw t0, 44(s4)
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
	andi t0, s2, 3
	beqz t0, 24f
	beqz s3, 26f
28:
	lwu t0, 32(s4)
	sw t0, 824(s4)
	lwu t0, 36(s4)
	sw t0, 828(s4)
	lwu t0, 40(s4)
	sw t0, 832(s4)
	lwu t0, 44(s4)
	sw t0, 836(s4)
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
29:
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
	bnez t0, 29b
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
	lwu t1, 824(s4)
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
	lwu t1, 828(s4)
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
	lwu t1, 832(s4)
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
	lwu t1, 836(s4)
	xor t0, t0, t1
	sb t0, 12(s2)
	srli t2, t0, 8
	sb t2, 13(s2)
	srli t2, t0, 16
	sb t2, 14(s2)
	srli t2, t0, 24
	sb t2, 15(s2)
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
	sw t0, 32(s4)
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
	sw t0, 36(s4)
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
	sw t0, 40(s4)
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
	sw t0, 44(s4)
	addi s2, s2, 16
	addi s3, s3, -1
	bnez s3, 28b
	j 27f
26:
27:
	j 25f
24:
	beqz s3, 210f
212:
	lwu t0, 32(s4)
	sw t0, 824(s4)
	lwu t0, 36(s4)
	sw t0, 828(s4)
	lwu t0, 40(s4)
	sw t0, 832(s4)
	lwu t0, 44(s4)
	sw t0, 836(s4)
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
213:
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
	bnez t0, 213b
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
	lwu t0, 0(s2)
	lwu t1, 824(s4)
	xor t0, t0, t1
	sw t0, 0(s2)
	lwu t0, 4(s2)
	lwu t1, 828(s4)
	xor t0, t0, t1
	sw t0, 4(s2)
	lwu t0, 8(s2)
	lwu t1, 832(s4)
	xor t0, t0, t1
	sw t0, 8(s2)
	lwu t0, 12(s2)
	lwu t1, 836(s4)
	xor t0, t0, t1
	sw t0, 12(s2)
	lwu t0, 0(s2)
	sw t0, 32(s4)
	lwu t0, 4(s2)
	sw t0, 36(s4)
	lwu t0, 8(s2)
	sw t0, 40(s4)
	lwu t0, 12(s2)
	sw t0, 44(s4)
	addi s2, s2, 16
	addi s3, s3, -1
	bnez s3, 212b
	j 211f
210:
211:
25:
	addi s2, s1, 0
	lwu t0, 32(s4)
	sb t0, 0(s2)
	srli t2, t0, 8
	sb t2, 1(s2)
	srli t2, t0, 16
	sb t2, 2(s2)
	srli t2, t0, 24
	sb t2, 3(s2)
	lwu t0, 36(s4)
	sb t0, 4(s2)
	srli t2, t0, 8
	sb t2, 5(s2)
	srli t2, t0, 16
	sb t2, 6(s2)
	srli t2, t0, 24
	sb t2, 7(s2)
	lwu t0, 40(s4)
	sb t0, 8(s2)
	srli t2, t0, 8
	sb t2, 9(s2)
	srli t2, t0, 16
	sb t2, 10(s2)
	srli t2, t0, 24
	sb t2, 11(s2)
	lwu t0, 44(s4)
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
214:
	sd t0, 0(t1)
	addi t1, t1, 8
	addi t2, t2, -1
	bnez t2, 214b
	addi sp, sp, 1200
	addi sp, sp, 2032
	ret
	.option pop

vg_sm4_cfb128_decrypt:
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
	sw t0, 32(s4)
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
	sw t0, 36(s4)
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
	sw t0, 40(s4)
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
	sw t0, 44(s4)
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
	andi t0, s2, 3
	beqz t0, 24f
	srli t0, s3, 4
	beqz t0, 26f
28:
	lwu t0, 32(s4)
	sw t0, 824(s4)
	lwu t0, 36(s4)
	sw t0, 828(s4)
	lwu t0, 40(s4)
	sw t0, 832(s4)
	lwu t0, 44(s4)
	sw t0, 836(s4)
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
	sw t0, 32(s4)
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
	sw t0, 36(s4)
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
	sw t0, 40(s4)
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
	sw t0, 44(s4)
	lwu t0, 32(s4)
	sw t0, 840(s4)
	lwu t0, 36(s4)
	sw t0, 844(s4)
	lwu t0, 40(s4)
	sw t0, 848(s4)
	lwu t0, 44(s4)
	sw t0, 852(s4)
	lbu t0, 16(s2)
	lbu t2, 17(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 18(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 19(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 20(s2)
	lbu t2, 21(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 22(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 23(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lbu t0, 24(s2)
	lbu t2, 25(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 26(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 27(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 40(s4)
	lbu t0, 28(s2)
	lbu t2, 29(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 30(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 31(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 44(s4)
	lwu t0, 32(s4)
	sw t0, 856(s4)
	lwu t0, 36(s4)
	sw t0, 860(s4)
	lwu t0, 40(s4)
	sw t0, 864(s4)
	lwu t0, 44(s4)
	sw t0, 868(s4)
	lbu t0, 32(s2)
	lbu t2, 33(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 34(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 35(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 36(s2)
	lbu t2, 37(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 38(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 39(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lbu t0, 40(s2)
	lbu t2, 41(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 42(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 43(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 40(s4)
	lbu t0, 44(s2)
	lbu t2, 45(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 46(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 47(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 44(s4)
	lwu t0, 32(s4)
	sw t0, 872(s4)
	lwu t0, 36(s4)
	sw t0, 876(s4)
	lwu t0, 40(s4)
	sw t0, 880(s4)
	lwu t0, 44(s4)
	sw t0, 884(s4)
	lbu t0, 48(s2)
	lbu t2, 49(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 50(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 51(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 52(s2)
	lbu t2, 53(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 54(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 55(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lbu t0, 56(s2)
	lbu t2, 57(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 58(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 59(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 40(s4)
	lbu t0, 60(s2)
	lbu t2, 61(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 62(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 63(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 44(s4)
	lwu t0, 32(s4)
	sw t0, 888(s4)
	lwu t0, 36(s4)
	sw t0, 892(s4)
	lwu t0, 40(s4)
	sw t0, 896(s4)
	lwu t0, 44(s4)
	sw t0, 900(s4)
	lbu t0, 64(s2)
	lbu t2, 65(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 66(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 67(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 68(s2)
	lbu t2, 69(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 70(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 71(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lbu t0, 72(s2)
	lbu t2, 73(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 74(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 75(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 40(s4)
	lbu t0, 76(s2)
	lbu t2, 77(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 78(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 79(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 44(s4)
	lwu t0, 32(s4)
	sw t0, 904(s4)
	lwu t0, 36(s4)
	sw t0, 908(s4)
	lwu t0, 40(s4)
	sw t0, 912(s4)
	lwu t0, 44(s4)
	sw t0, 916(s4)
	lbu t0, 80(s2)
	lbu t2, 81(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 82(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 83(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 84(s2)
	lbu t2, 85(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 86(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 87(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lbu t0, 88(s2)
	lbu t2, 89(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 90(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 91(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 40(s4)
	lbu t0, 92(s2)
	lbu t2, 93(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 94(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 95(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 44(s4)
	lwu t0, 32(s4)
	sw t0, 920(s4)
	lwu t0, 36(s4)
	sw t0, 924(s4)
	lwu t0, 40(s4)
	sw t0, 928(s4)
	lwu t0, 44(s4)
	sw t0, 932(s4)
	lbu t0, 96(s2)
	lbu t2, 97(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 98(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 99(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 100(s2)
	lbu t2, 101(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 102(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 103(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lbu t0, 104(s2)
	lbu t2, 105(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 106(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 107(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 40(s4)
	lbu t0, 108(s2)
	lbu t2, 109(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 110(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 111(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 44(s4)
	lwu t0, 32(s4)
	sw t0, 936(s4)
	lwu t0, 36(s4)
	sw t0, 940(s4)
	lwu t0, 40(s4)
	sw t0, 944(s4)
	lwu t0, 44(s4)
	sw t0, 948(s4)
	lbu t0, 112(s2)
	lbu t2, 113(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 114(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 115(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 116(s2)
	lbu t2, 117(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 118(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 119(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lbu t0, 120(s2)
	lbu t2, 121(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 122(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 123(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 40(s4)
	lbu t0, 124(s2)
	lbu t2, 125(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 126(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 127(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 44(s4)
	lwu t0, 32(s4)
	sw t0, 952(s4)
	lwu t0, 36(s4)
	sw t0, 956(s4)
	lwu t0, 40(s4)
	sw t0, 960(s4)
	lwu t0, 44(s4)
	sw t0, 964(s4)
	lbu t0, 128(s2)
	lbu t2, 129(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 130(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 131(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 132(s2)
	lbu t2, 133(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 134(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 135(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lbu t0, 136(s2)
	lbu t2, 137(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 138(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 139(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 40(s4)
	lbu t0, 140(s2)
	lbu t2, 141(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 142(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 143(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 44(s4)
	lwu t0, 32(s4)
	sw t0, 968(s4)
	lwu t0, 36(s4)
	sw t0, 972(s4)
	lwu t0, 40(s4)
	sw t0, 976(s4)
	lwu t0, 44(s4)
	sw t0, 980(s4)
	lbu t0, 144(s2)
	lbu t2, 145(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 146(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 147(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 148(s2)
	lbu t2, 149(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 150(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 151(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lbu t0, 152(s2)
	lbu t2, 153(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 154(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 155(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 40(s4)
	lbu t0, 156(s2)
	lbu t2, 157(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 158(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 159(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 44(s4)
	lwu t0, 32(s4)
	sw t0, 984(s4)
	lwu t0, 36(s4)
	sw t0, 988(s4)
	lwu t0, 40(s4)
	sw t0, 992(s4)
	lwu t0, 44(s4)
	sw t0, 996(s4)
	lbu t0, 160(s2)
	lbu t2, 161(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 162(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 163(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 164(s2)
	lbu t2, 165(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 166(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 167(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lbu t0, 168(s2)
	lbu t2, 169(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 170(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 171(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 40(s4)
	lbu t0, 172(s2)
	lbu t2, 173(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 174(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 175(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 44(s4)
	lwu t0, 32(s4)
	sw t0, 1000(s4)
	lwu t0, 36(s4)
	sw t0, 1004(s4)
	lwu t0, 40(s4)
	sw t0, 1008(s4)
	lwu t0, 44(s4)
	sw t0, 1012(s4)
	lbu t0, 176(s2)
	lbu t2, 177(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 178(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 179(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 180(s2)
	lbu t2, 181(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 182(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 183(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lbu t0, 184(s2)
	lbu t2, 185(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 186(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 187(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 40(s4)
	lbu t0, 188(s2)
	lbu t2, 189(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 190(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 191(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 44(s4)
	lwu t0, 32(s4)
	sw t0, 1016(s4)
	lwu t0, 36(s4)
	sw t0, 1020(s4)
	lwu t0, 40(s4)
	sw t0, 1024(s4)
	lwu t0, 44(s4)
	sw t0, 1028(s4)
	lbu t0, 192(s2)
	lbu t2, 193(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 194(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 195(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 196(s2)
	lbu t2, 197(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 198(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 199(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lbu t0, 200(s2)
	lbu t2, 201(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 202(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 203(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 40(s4)
	lbu t0, 204(s2)
	lbu t2, 205(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 206(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 207(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 44(s4)
	lwu t0, 32(s4)
	sw t0, 1032(s4)
	lwu t0, 36(s4)
	sw t0, 1036(s4)
	lwu t0, 40(s4)
	sw t0, 1040(s4)
	lwu t0, 44(s4)
	sw t0, 1044(s4)
	lbu t0, 208(s2)
	lbu t2, 209(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 210(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 211(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 212(s2)
	lbu t2, 213(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 214(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 215(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lbu t0, 216(s2)
	lbu t2, 217(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 218(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 219(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 40(s4)
	lbu t0, 220(s2)
	lbu t2, 221(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 222(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 223(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 44(s4)
	lwu t0, 32(s4)
	sw t0, 1048(s4)
	lwu t0, 36(s4)
	sw t0, 1052(s4)
	lwu t0, 40(s4)
	sw t0, 1056(s4)
	lwu t0, 44(s4)
	sw t0, 1060(s4)
	lbu t0, 224(s2)
	lbu t2, 225(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 226(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 227(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 228(s2)
	lbu t2, 229(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 230(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 231(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lbu t0, 232(s2)
	lbu t2, 233(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 234(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 235(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 40(s4)
	lbu t0, 236(s2)
	lbu t2, 237(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 238(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 239(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 44(s4)
	lwu t0, 32(s4)
	sw t0, 1064(s4)
	lwu t0, 36(s4)
	sw t0, 1068(s4)
	lwu t0, 40(s4)
	sw t0, 1072(s4)
	lwu t0, 44(s4)
	sw t0, 1076(s4)
	lbu t0, 240(s2)
	lbu t2, 241(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 242(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 243(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 244(s2)
	lbu t2, 245(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 246(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 247(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lbu t0, 248(s2)
	lbu t2, 249(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 250(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 251(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 40(s4)
	lbu t0, 252(s2)
	lbu t2, 253(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 254(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 255(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 44(s4)
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
29:
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
	bnez t0, 29b
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
	lwu t1, 824(s4)
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
	lwu t1, 828(s4)
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
	lwu t1, 832(s4)
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
	lwu t1, 836(s4)
	xor t0, t0, t1
	sb t0, 12(s2)
	srli t2, t0, 8
	sb t2, 13(s2)
	srli t2, t0, 16
	sb t2, 14(s2)
	srli t2, t0, 24
	sb t2, 15(s2)
	lbu t0, 16(s2)
	lbu t2, 17(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 18(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 19(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 840(s4)
	xor t0, t0, t1
	sb t0, 16(s2)
	srli t2, t0, 8
	sb t2, 17(s2)
	srli t2, t0, 16
	sb t2, 18(s2)
	srli t2, t0, 24
	sb t2, 19(s2)
	lbu t0, 20(s2)
	lbu t2, 21(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 22(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 23(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 844(s4)
	xor t0, t0, t1
	sb t0, 20(s2)
	srli t2, t0, 8
	sb t2, 21(s2)
	srli t2, t0, 16
	sb t2, 22(s2)
	srli t2, t0, 24
	sb t2, 23(s2)
	lbu t0, 24(s2)
	lbu t2, 25(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 26(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 27(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 848(s4)
	xor t0, t0, t1
	sb t0, 24(s2)
	srli t2, t0, 8
	sb t2, 25(s2)
	srli t2, t0, 16
	sb t2, 26(s2)
	srli t2, t0, 24
	sb t2, 27(s2)
	lbu t0, 28(s2)
	lbu t2, 29(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 30(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 31(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 852(s4)
	xor t0, t0, t1
	sb t0, 28(s2)
	srli t2, t0, 8
	sb t2, 29(s2)
	srli t2, t0, 16
	sb t2, 30(s2)
	srli t2, t0, 24
	sb t2, 31(s2)
	lbu t0, 32(s2)
	lbu t2, 33(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 34(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 35(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 856(s4)
	xor t0, t0, t1
	sb t0, 32(s2)
	srli t2, t0, 8
	sb t2, 33(s2)
	srli t2, t0, 16
	sb t2, 34(s2)
	srli t2, t0, 24
	sb t2, 35(s2)
	lbu t0, 36(s2)
	lbu t2, 37(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 38(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 39(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 860(s4)
	xor t0, t0, t1
	sb t0, 36(s2)
	srli t2, t0, 8
	sb t2, 37(s2)
	srli t2, t0, 16
	sb t2, 38(s2)
	srli t2, t0, 24
	sb t2, 39(s2)
	lbu t0, 40(s2)
	lbu t2, 41(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 42(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 43(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 864(s4)
	xor t0, t0, t1
	sb t0, 40(s2)
	srli t2, t0, 8
	sb t2, 41(s2)
	srli t2, t0, 16
	sb t2, 42(s2)
	srli t2, t0, 24
	sb t2, 43(s2)
	lbu t0, 44(s2)
	lbu t2, 45(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 46(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 47(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 868(s4)
	xor t0, t0, t1
	sb t0, 44(s2)
	srli t2, t0, 8
	sb t2, 45(s2)
	srli t2, t0, 16
	sb t2, 46(s2)
	srli t2, t0, 24
	sb t2, 47(s2)
	lbu t0, 48(s2)
	lbu t2, 49(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 50(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 51(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 872(s4)
	xor t0, t0, t1
	sb t0, 48(s2)
	srli t2, t0, 8
	sb t2, 49(s2)
	srli t2, t0, 16
	sb t2, 50(s2)
	srli t2, t0, 24
	sb t2, 51(s2)
	lbu t0, 52(s2)
	lbu t2, 53(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 54(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 55(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 876(s4)
	xor t0, t0, t1
	sb t0, 52(s2)
	srli t2, t0, 8
	sb t2, 53(s2)
	srli t2, t0, 16
	sb t2, 54(s2)
	srli t2, t0, 24
	sb t2, 55(s2)
	lbu t0, 56(s2)
	lbu t2, 57(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 58(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 59(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 880(s4)
	xor t0, t0, t1
	sb t0, 56(s2)
	srli t2, t0, 8
	sb t2, 57(s2)
	srli t2, t0, 16
	sb t2, 58(s2)
	srli t2, t0, 24
	sb t2, 59(s2)
	lbu t0, 60(s2)
	lbu t2, 61(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 62(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 63(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 884(s4)
	xor t0, t0, t1
	sb t0, 60(s2)
	srli t2, t0, 8
	sb t2, 61(s2)
	srli t2, t0, 16
	sb t2, 62(s2)
	srli t2, t0, 24
	sb t2, 63(s2)
	lbu t0, 64(s2)
	lbu t2, 65(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 66(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 67(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 888(s4)
	xor t0, t0, t1
	sb t0, 64(s2)
	srli t2, t0, 8
	sb t2, 65(s2)
	srli t2, t0, 16
	sb t2, 66(s2)
	srli t2, t0, 24
	sb t2, 67(s2)
	lbu t0, 68(s2)
	lbu t2, 69(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 70(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 71(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 892(s4)
	xor t0, t0, t1
	sb t0, 68(s2)
	srli t2, t0, 8
	sb t2, 69(s2)
	srli t2, t0, 16
	sb t2, 70(s2)
	srli t2, t0, 24
	sb t2, 71(s2)
	lbu t0, 72(s2)
	lbu t2, 73(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 74(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 75(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 896(s4)
	xor t0, t0, t1
	sb t0, 72(s2)
	srli t2, t0, 8
	sb t2, 73(s2)
	srli t2, t0, 16
	sb t2, 74(s2)
	srli t2, t0, 24
	sb t2, 75(s2)
	lbu t0, 76(s2)
	lbu t2, 77(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 78(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 79(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 900(s4)
	xor t0, t0, t1
	sb t0, 76(s2)
	srli t2, t0, 8
	sb t2, 77(s2)
	srli t2, t0, 16
	sb t2, 78(s2)
	srli t2, t0, 24
	sb t2, 79(s2)
	lbu t0, 80(s2)
	lbu t2, 81(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 82(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 83(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 904(s4)
	xor t0, t0, t1
	sb t0, 80(s2)
	srli t2, t0, 8
	sb t2, 81(s2)
	srli t2, t0, 16
	sb t2, 82(s2)
	srli t2, t0, 24
	sb t2, 83(s2)
	lbu t0, 84(s2)
	lbu t2, 85(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 86(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 87(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 908(s4)
	xor t0, t0, t1
	sb t0, 84(s2)
	srli t2, t0, 8
	sb t2, 85(s2)
	srli t2, t0, 16
	sb t2, 86(s2)
	srli t2, t0, 24
	sb t2, 87(s2)
	lbu t0, 88(s2)
	lbu t2, 89(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 90(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 91(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 912(s4)
	xor t0, t0, t1
	sb t0, 88(s2)
	srli t2, t0, 8
	sb t2, 89(s2)
	srli t2, t0, 16
	sb t2, 90(s2)
	srli t2, t0, 24
	sb t2, 91(s2)
	lbu t0, 92(s2)
	lbu t2, 93(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 94(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 95(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 916(s4)
	xor t0, t0, t1
	sb t0, 92(s2)
	srli t2, t0, 8
	sb t2, 93(s2)
	srli t2, t0, 16
	sb t2, 94(s2)
	srli t2, t0, 24
	sb t2, 95(s2)
	lbu t0, 96(s2)
	lbu t2, 97(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 98(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 99(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 920(s4)
	xor t0, t0, t1
	sb t0, 96(s2)
	srli t2, t0, 8
	sb t2, 97(s2)
	srli t2, t0, 16
	sb t2, 98(s2)
	srli t2, t0, 24
	sb t2, 99(s2)
	lbu t0, 100(s2)
	lbu t2, 101(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 102(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 103(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 924(s4)
	xor t0, t0, t1
	sb t0, 100(s2)
	srli t2, t0, 8
	sb t2, 101(s2)
	srli t2, t0, 16
	sb t2, 102(s2)
	srli t2, t0, 24
	sb t2, 103(s2)
	lbu t0, 104(s2)
	lbu t2, 105(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 106(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 107(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 928(s4)
	xor t0, t0, t1
	sb t0, 104(s2)
	srli t2, t0, 8
	sb t2, 105(s2)
	srli t2, t0, 16
	sb t2, 106(s2)
	srli t2, t0, 24
	sb t2, 107(s2)
	lbu t0, 108(s2)
	lbu t2, 109(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 110(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 111(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 932(s4)
	xor t0, t0, t1
	sb t0, 108(s2)
	srli t2, t0, 8
	sb t2, 109(s2)
	srli t2, t0, 16
	sb t2, 110(s2)
	srli t2, t0, 24
	sb t2, 111(s2)
	lbu t0, 112(s2)
	lbu t2, 113(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 114(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 115(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 936(s4)
	xor t0, t0, t1
	sb t0, 112(s2)
	srli t2, t0, 8
	sb t2, 113(s2)
	srli t2, t0, 16
	sb t2, 114(s2)
	srli t2, t0, 24
	sb t2, 115(s2)
	lbu t0, 116(s2)
	lbu t2, 117(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 118(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 119(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 940(s4)
	xor t0, t0, t1
	sb t0, 116(s2)
	srli t2, t0, 8
	sb t2, 117(s2)
	srli t2, t0, 16
	sb t2, 118(s2)
	srli t2, t0, 24
	sb t2, 119(s2)
	lbu t0, 120(s2)
	lbu t2, 121(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 122(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 123(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 944(s4)
	xor t0, t0, t1
	sb t0, 120(s2)
	srli t2, t0, 8
	sb t2, 121(s2)
	srli t2, t0, 16
	sb t2, 122(s2)
	srli t2, t0, 24
	sb t2, 123(s2)
	lbu t0, 124(s2)
	lbu t2, 125(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 126(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 127(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 948(s4)
	xor t0, t0, t1
	sb t0, 124(s2)
	srli t2, t0, 8
	sb t2, 125(s2)
	srli t2, t0, 16
	sb t2, 126(s2)
	srli t2, t0, 24
	sb t2, 127(s2)
	lbu t0, 128(s2)
	lbu t2, 129(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 130(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 131(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 952(s4)
	xor t0, t0, t1
	sb t0, 128(s2)
	srli t2, t0, 8
	sb t2, 129(s2)
	srli t2, t0, 16
	sb t2, 130(s2)
	srli t2, t0, 24
	sb t2, 131(s2)
	lbu t0, 132(s2)
	lbu t2, 133(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 134(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 135(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 956(s4)
	xor t0, t0, t1
	sb t0, 132(s2)
	srli t2, t0, 8
	sb t2, 133(s2)
	srli t2, t0, 16
	sb t2, 134(s2)
	srli t2, t0, 24
	sb t2, 135(s2)
	lbu t0, 136(s2)
	lbu t2, 137(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 138(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 139(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 960(s4)
	xor t0, t0, t1
	sb t0, 136(s2)
	srli t2, t0, 8
	sb t2, 137(s2)
	srli t2, t0, 16
	sb t2, 138(s2)
	srli t2, t0, 24
	sb t2, 139(s2)
	lbu t0, 140(s2)
	lbu t2, 141(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 142(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 143(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 964(s4)
	xor t0, t0, t1
	sb t0, 140(s2)
	srli t2, t0, 8
	sb t2, 141(s2)
	srli t2, t0, 16
	sb t2, 142(s2)
	srli t2, t0, 24
	sb t2, 143(s2)
	lbu t0, 144(s2)
	lbu t2, 145(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 146(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 147(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 968(s4)
	xor t0, t0, t1
	sb t0, 144(s2)
	srli t2, t0, 8
	sb t2, 145(s2)
	srli t2, t0, 16
	sb t2, 146(s2)
	srli t2, t0, 24
	sb t2, 147(s2)
	lbu t0, 148(s2)
	lbu t2, 149(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 150(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 151(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 972(s4)
	xor t0, t0, t1
	sb t0, 148(s2)
	srli t2, t0, 8
	sb t2, 149(s2)
	srli t2, t0, 16
	sb t2, 150(s2)
	srli t2, t0, 24
	sb t2, 151(s2)
	lbu t0, 152(s2)
	lbu t2, 153(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 154(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 155(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 976(s4)
	xor t0, t0, t1
	sb t0, 152(s2)
	srli t2, t0, 8
	sb t2, 153(s2)
	srli t2, t0, 16
	sb t2, 154(s2)
	srli t2, t0, 24
	sb t2, 155(s2)
	lbu t0, 156(s2)
	lbu t2, 157(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 158(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 159(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 980(s4)
	xor t0, t0, t1
	sb t0, 156(s2)
	srli t2, t0, 8
	sb t2, 157(s2)
	srli t2, t0, 16
	sb t2, 158(s2)
	srli t2, t0, 24
	sb t2, 159(s2)
	lbu t0, 160(s2)
	lbu t2, 161(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 162(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 163(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 984(s4)
	xor t0, t0, t1
	sb t0, 160(s2)
	srli t2, t0, 8
	sb t2, 161(s2)
	srli t2, t0, 16
	sb t2, 162(s2)
	srli t2, t0, 24
	sb t2, 163(s2)
	lbu t0, 164(s2)
	lbu t2, 165(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 166(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 167(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 988(s4)
	xor t0, t0, t1
	sb t0, 164(s2)
	srli t2, t0, 8
	sb t2, 165(s2)
	srli t2, t0, 16
	sb t2, 166(s2)
	srli t2, t0, 24
	sb t2, 167(s2)
	lbu t0, 168(s2)
	lbu t2, 169(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 170(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 171(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 992(s4)
	xor t0, t0, t1
	sb t0, 168(s2)
	srli t2, t0, 8
	sb t2, 169(s2)
	srli t2, t0, 16
	sb t2, 170(s2)
	srli t2, t0, 24
	sb t2, 171(s2)
	lbu t0, 172(s2)
	lbu t2, 173(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 174(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 175(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 996(s4)
	xor t0, t0, t1
	sb t0, 172(s2)
	srli t2, t0, 8
	sb t2, 173(s2)
	srli t2, t0, 16
	sb t2, 174(s2)
	srli t2, t0, 24
	sb t2, 175(s2)
	lbu t0, 176(s2)
	lbu t2, 177(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 178(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 179(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 1000(s4)
	xor t0, t0, t1
	sb t0, 176(s2)
	srli t2, t0, 8
	sb t2, 177(s2)
	srli t2, t0, 16
	sb t2, 178(s2)
	srli t2, t0, 24
	sb t2, 179(s2)
	lbu t0, 180(s2)
	lbu t2, 181(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 182(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 183(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 1004(s4)
	xor t0, t0, t1
	sb t0, 180(s2)
	srli t2, t0, 8
	sb t2, 181(s2)
	srli t2, t0, 16
	sb t2, 182(s2)
	srli t2, t0, 24
	sb t2, 183(s2)
	lbu t0, 184(s2)
	lbu t2, 185(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 186(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 187(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 1008(s4)
	xor t0, t0, t1
	sb t0, 184(s2)
	srli t2, t0, 8
	sb t2, 185(s2)
	srli t2, t0, 16
	sb t2, 186(s2)
	srli t2, t0, 24
	sb t2, 187(s2)
	lbu t0, 188(s2)
	lbu t2, 189(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 190(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 191(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 1012(s4)
	xor t0, t0, t1
	sb t0, 188(s2)
	srli t2, t0, 8
	sb t2, 189(s2)
	srli t2, t0, 16
	sb t2, 190(s2)
	srli t2, t0, 24
	sb t2, 191(s2)
	lbu t0, 192(s2)
	lbu t2, 193(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 194(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 195(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 1016(s4)
	xor t0, t0, t1
	sb t0, 192(s2)
	srli t2, t0, 8
	sb t2, 193(s2)
	srli t2, t0, 16
	sb t2, 194(s2)
	srli t2, t0, 24
	sb t2, 195(s2)
	lbu t0, 196(s2)
	lbu t2, 197(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 198(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 199(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 1020(s4)
	xor t0, t0, t1
	sb t0, 196(s2)
	srli t2, t0, 8
	sb t2, 197(s2)
	srli t2, t0, 16
	sb t2, 198(s2)
	srli t2, t0, 24
	sb t2, 199(s2)
	lbu t0, 200(s2)
	lbu t2, 201(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 202(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 203(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 1024(s4)
	xor t0, t0, t1
	sb t0, 200(s2)
	srli t2, t0, 8
	sb t2, 201(s2)
	srli t2, t0, 16
	sb t2, 202(s2)
	srli t2, t0, 24
	sb t2, 203(s2)
	lbu t0, 204(s2)
	lbu t2, 205(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 206(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 207(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 1028(s4)
	xor t0, t0, t1
	sb t0, 204(s2)
	srli t2, t0, 8
	sb t2, 205(s2)
	srli t2, t0, 16
	sb t2, 206(s2)
	srli t2, t0, 24
	sb t2, 207(s2)
	lbu t0, 208(s2)
	lbu t2, 209(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 210(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 211(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 1032(s4)
	xor t0, t0, t1
	sb t0, 208(s2)
	srli t2, t0, 8
	sb t2, 209(s2)
	srli t2, t0, 16
	sb t2, 210(s2)
	srli t2, t0, 24
	sb t2, 211(s2)
	lbu t0, 212(s2)
	lbu t2, 213(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 214(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 215(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 1036(s4)
	xor t0, t0, t1
	sb t0, 212(s2)
	srli t2, t0, 8
	sb t2, 213(s2)
	srli t2, t0, 16
	sb t2, 214(s2)
	srli t2, t0, 24
	sb t2, 215(s2)
	lbu t0, 216(s2)
	lbu t2, 217(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 218(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 219(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 1040(s4)
	xor t0, t0, t1
	sb t0, 216(s2)
	srli t2, t0, 8
	sb t2, 217(s2)
	srli t2, t0, 16
	sb t2, 218(s2)
	srli t2, t0, 24
	sb t2, 219(s2)
	lbu t0, 220(s2)
	lbu t2, 221(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 222(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 223(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 1044(s4)
	xor t0, t0, t1
	sb t0, 220(s2)
	srli t2, t0, 8
	sb t2, 221(s2)
	srli t2, t0, 16
	sb t2, 222(s2)
	srli t2, t0, 24
	sb t2, 223(s2)
	lbu t0, 224(s2)
	lbu t2, 225(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 226(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 227(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 1048(s4)
	xor t0, t0, t1
	sb t0, 224(s2)
	srli t2, t0, 8
	sb t2, 225(s2)
	srli t2, t0, 16
	sb t2, 226(s2)
	srli t2, t0, 24
	sb t2, 227(s2)
	lbu t0, 228(s2)
	lbu t2, 229(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 230(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 231(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 1052(s4)
	xor t0, t0, t1
	sb t0, 228(s2)
	srli t2, t0, 8
	sb t2, 229(s2)
	srli t2, t0, 16
	sb t2, 230(s2)
	srli t2, t0, 24
	sb t2, 231(s2)
	lbu t0, 232(s2)
	lbu t2, 233(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 234(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 235(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 1056(s4)
	xor t0, t0, t1
	sb t0, 232(s2)
	srli t2, t0, 8
	sb t2, 233(s2)
	srli t2, t0, 16
	sb t2, 234(s2)
	srli t2, t0, 24
	sb t2, 235(s2)
	lbu t0, 236(s2)
	lbu t2, 237(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 238(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 239(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 1060(s4)
	xor t0, t0, t1
	sb t0, 236(s2)
	srli t2, t0, 8
	sb t2, 237(s2)
	srli t2, t0, 16
	sb t2, 238(s2)
	srli t2, t0, 24
	sb t2, 239(s2)
	lbu t0, 240(s2)
	lbu t2, 241(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 242(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 243(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 1064(s4)
	xor t0, t0, t1
	sb t0, 240(s2)
	srli t2, t0, 8
	sb t2, 241(s2)
	srli t2, t0, 16
	sb t2, 242(s2)
	srli t2, t0, 24
	sb t2, 243(s2)
	lbu t0, 244(s2)
	lbu t2, 245(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 246(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 247(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 1068(s4)
	xor t0, t0, t1
	sb t0, 244(s2)
	srli t2, t0, 8
	sb t2, 245(s2)
	srli t2, t0, 16
	sb t2, 246(s2)
	srli t2, t0, 24
	sb t2, 247(s2)
	lbu t0, 248(s2)
	lbu t2, 249(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 250(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 251(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 1072(s4)
	xor t0, t0, t1
	sb t0, 248(s2)
	srli t2, t0, 8
	sb t2, 249(s2)
	srli t2, t0, 16
	sb t2, 250(s2)
	srli t2, t0, 24
	sb t2, 251(s2)
	lbu t0, 252(s2)
	lbu t2, 253(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 254(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 255(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 1076(s4)
	xor t0, t0, t1
	sb t0, 252(s2)
	srli t2, t0, 8
	sb t2, 253(s2)
	srli t2, t0, 16
	sb t2, 254(s2)
	srli t2, t0, 24
	sb t2, 255(s2)
	addi s2, s2, 256
	addi s3, s3, -16
	srli t0, s3, 4
	bnez t0, 28b
	j 27f
26:
27:
	beqz s3, 210f
212:
	lwu t0, 32(s4)
	sw t0, 824(s4)
	lwu t0, 36(s4)
	sw t0, 828(s4)
	lwu t0, 40(s4)
	sw t0, 832(s4)
	lwu t0, 44(s4)
	sw t0, 836(s4)
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
	sw t0, 32(s4)
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
	sw t0, 36(s4)
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
	sw t0, 40(s4)
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
	sw t0, 44(s4)
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
213:
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
	bnez t0, 213b
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
	lwu t1, 824(s4)
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
	lwu t1, 828(s4)
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
	lwu t1, 832(s4)
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
	lwu t1, 836(s4)
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
	bnez s3, 212b
	j 211f
210:
211:
	j 25f
24:
	srli t0, s3, 4
	beqz t0, 214f
216:
	lwu t0, 32(s4)
	sw t0, 824(s4)
	lwu t0, 36(s4)
	sw t0, 828(s4)
	lwu t0, 40(s4)
	sw t0, 832(s4)
	lwu t0, 44(s4)
	sw t0, 836(s4)
	lwu t0, 0(s2)
	sw t0, 32(s4)
	lwu t0, 4(s2)
	sw t0, 36(s4)
	lwu t0, 8(s2)
	sw t0, 40(s4)
	lwu t0, 12(s2)
	sw t0, 44(s4)
	lwu t0, 32(s4)
	sw t0, 840(s4)
	lwu t0, 36(s4)
	sw t0, 844(s4)
	lwu t0, 40(s4)
	sw t0, 848(s4)
	lwu t0, 44(s4)
	sw t0, 852(s4)
	lwu t0, 16(s2)
	sw t0, 32(s4)
	lwu t0, 20(s2)
	sw t0, 36(s4)
	lwu t0, 24(s2)
	sw t0, 40(s4)
	lwu t0, 28(s2)
	sw t0, 44(s4)
	lwu t0, 32(s4)
	sw t0, 856(s4)
	lwu t0, 36(s4)
	sw t0, 860(s4)
	lwu t0, 40(s4)
	sw t0, 864(s4)
	lwu t0, 44(s4)
	sw t0, 868(s4)
	lwu t0, 32(s2)
	sw t0, 32(s4)
	lwu t0, 36(s2)
	sw t0, 36(s4)
	lwu t0, 40(s2)
	sw t0, 40(s4)
	lwu t0, 44(s2)
	sw t0, 44(s4)
	lwu t0, 32(s4)
	sw t0, 872(s4)
	lwu t0, 36(s4)
	sw t0, 876(s4)
	lwu t0, 40(s4)
	sw t0, 880(s4)
	lwu t0, 44(s4)
	sw t0, 884(s4)
	lwu t0, 48(s2)
	sw t0, 32(s4)
	lwu t0, 52(s2)
	sw t0, 36(s4)
	lwu t0, 56(s2)
	sw t0, 40(s4)
	lwu t0, 60(s2)
	sw t0, 44(s4)
	lwu t0, 32(s4)
	sw t0, 888(s4)
	lwu t0, 36(s4)
	sw t0, 892(s4)
	lwu t0, 40(s4)
	sw t0, 896(s4)
	lwu t0, 44(s4)
	sw t0, 900(s4)
	lwu t0, 64(s2)
	sw t0, 32(s4)
	lwu t0, 68(s2)
	sw t0, 36(s4)
	lwu t0, 72(s2)
	sw t0, 40(s4)
	lwu t0, 76(s2)
	sw t0, 44(s4)
	lwu t0, 32(s4)
	sw t0, 904(s4)
	lwu t0, 36(s4)
	sw t0, 908(s4)
	lwu t0, 40(s4)
	sw t0, 912(s4)
	lwu t0, 44(s4)
	sw t0, 916(s4)
	lwu t0, 80(s2)
	sw t0, 32(s4)
	lwu t0, 84(s2)
	sw t0, 36(s4)
	lwu t0, 88(s2)
	sw t0, 40(s4)
	lwu t0, 92(s2)
	sw t0, 44(s4)
	lwu t0, 32(s4)
	sw t0, 920(s4)
	lwu t0, 36(s4)
	sw t0, 924(s4)
	lwu t0, 40(s4)
	sw t0, 928(s4)
	lwu t0, 44(s4)
	sw t0, 932(s4)
	lwu t0, 96(s2)
	sw t0, 32(s4)
	lwu t0, 100(s2)
	sw t0, 36(s4)
	lwu t0, 104(s2)
	sw t0, 40(s4)
	lwu t0, 108(s2)
	sw t0, 44(s4)
	lwu t0, 32(s4)
	sw t0, 936(s4)
	lwu t0, 36(s4)
	sw t0, 940(s4)
	lwu t0, 40(s4)
	sw t0, 944(s4)
	lwu t0, 44(s4)
	sw t0, 948(s4)
	lwu t0, 112(s2)
	sw t0, 32(s4)
	lwu t0, 116(s2)
	sw t0, 36(s4)
	lwu t0, 120(s2)
	sw t0, 40(s4)
	lwu t0, 124(s2)
	sw t0, 44(s4)
	lwu t0, 32(s4)
	sw t0, 952(s4)
	lwu t0, 36(s4)
	sw t0, 956(s4)
	lwu t0, 40(s4)
	sw t0, 960(s4)
	lwu t0, 44(s4)
	sw t0, 964(s4)
	lwu t0, 128(s2)
	sw t0, 32(s4)
	lwu t0, 132(s2)
	sw t0, 36(s4)
	lwu t0, 136(s2)
	sw t0, 40(s4)
	lwu t0, 140(s2)
	sw t0, 44(s4)
	lwu t0, 32(s4)
	sw t0, 968(s4)
	lwu t0, 36(s4)
	sw t0, 972(s4)
	lwu t0, 40(s4)
	sw t0, 976(s4)
	lwu t0, 44(s4)
	sw t0, 980(s4)
	lwu t0, 144(s2)
	sw t0, 32(s4)
	lwu t0, 148(s2)
	sw t0, 36(s4)
	lwu t0, 152(s2)
	sw t0, 40(s4)
	lwu t0, 156(s2)
	sw t0, 44(s4)
	lwu t0, 32(s4)
	sw t0, 984(s4)
	lwu t0, 36(s4)
	sw t0, 988(s4)
	lwu t0, 40(s4)
	sw t0, 992(s4)
	lwu t0, 44(s4)
	sw t0, 996(s4)
	lwu t0, 160(s2)
	sw t0, 32(s4)
	lwu t0, 164(s2)
	sw t0, 36(s4)
	lwu t0, 168(s2)
	sw t0, 40(s4)
	lwu t0, 172(s2)
	sw t0, 44(s4)
	lwu t0, 32(s4)
	sw t0, 1000(s4)
	lwu t0, 36(s4)
	sw t0, 1004(s4)
	lwu t0, 40(s4)
	sw t0, 1008(s4)
	lwu t0, 44(s4)
	sw t0, 1012(s4)
	lwu t0, 176(s2)
	sw t0, 32(s4)
	lwu t0, 180(s2)
	sw t0, 36(s4)
	lwu t0, 184(s2)
	sw t0, 40(s4)
	lwu t0, 188(s2)
	sw t0, 44(s4)
	lwu t0, 32(s4)
	sw t0, 1016(s4)
	lwu t0, 36(s4)
	sw t0, 1020(s4)
	lwu t0, 40(s4)
	sw t0, 1024(s4)
	lwu t0, 44(s4)
	sw t0, 1028(s4)
	lwu t0, 192(s2)
	sw t0, 32(s4)
	lwu t0, 196(s2)
	sw t0, 36(s4)
	lwu t0, 200(s2)
	sw t0, 40(s4)
	lwu t0, 204(s2)
	sw t0, 44(s4)
	lwu t0, 32(s4)
	sw t0, 1032(s4)
	lwu t0, 36(s4)
	sw t0, 1036(s4)
	lwu t0, 40(s4)
	sw t0, 1040(s4)
	lwu t0, 44(s4)
	sw t0, 1044(s4)
	lwu t0, 208(s2)
	sw t0, 32(s4)
	lwu t0, 212(s2)
	sw t0, 36(s4)
	lwu t0, 216(s2)
	sw t0, 40(s4)
	lwu t0, 220(s2)
	sw t0, 44(s4)
	lwu t0, 32(s4)
	sw t0, 1048(s4)
	lwu t0, 36(s4)
	sw t0, 1052(s4)
	lwu t0, 40(s4)
	sw t0, 1056(s4)
	lwu t0, 44(s4)
	sw t0, 1060(s4)
	lwu t0, 224(s2)
	sw t0, 32(s4)
	lwu t0, 228(s2)
	sw t0, 36(s4)
	lwu t0, 232(s2)
	sw t0, 40(s4)
	lwu t0, 236(s2)
	sw t0, 44(s4)
	lwu t0, 32(s4)
	sw t0, 1064(s4)
	lwu t0, 36(s4)
	sw t0, 1068(s4)
	lwu t0, 40(s4)
	sw t0, 1072(s4)
	lwu t0, 44(s4)
	sw t0, 1076(s4)
	lwu t0, 240(s2)
	sw t0, 32(s4)
	lwu t0, 244(s2)
	sw t0, 36(s4)
	lwu t0, 248(s2)
	sw t0, 40(s4)
	lwu t0, 252(s2)
	sw t0, 44(s4)
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
217:
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
	bnez t0, 217b
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
	lwu t0, 0(s2)
	lwu t1, 824(s4)
	xor t0, t0, t1
	sw t0, 0(s2)
	lwu t0, 4(s2)
	lwu t1, 828(s4)
	xor t0, t0, t1
	sw t0, 4(s2)
	lwu t0, 8(s2)
	lwu t1, 832(s4)
	xor t0, t0, t1
	sw t0, 8(s2)
	lwu t0, 12(s2)
	lwu t1, 836(s4)
	xor t0, t0, t1
	sw t0, 12(s2)
	lwu t0, 16(s2)
	lwu t1, 840(s4)
	xor t0, t0, t1
	sw t0, 16(s2)
	lwu t0, 20(s2)
	lwu t1, 844(s4)
	xor t0, t0, t1
	sw t0, 20(s2)
	lwu t0, 24(s2)
	lwu t1, 848(s4)
	xor t0, t0, t1
	sw t0, 24(s2)
	lwu t0, 28(s2)
	lwu t1, 852(s4)
	xor t0, t0, t1
	sw t0, 28(s2)
	lwu t0, 32(s2)
	lwu t1, 856(s4)
	xor t0, t0, t1
	sw t0, 32(s2)
	lwu t0, 36(s2)
	lwu t1, 860(s4)
	xor t0, t0, t1
	sw t0, 36(s2)
	lwu t0, 40(s2)
	lwu t1, 864(s4)
	xor t0, t0, t1
	sw t0, 40(s2)
	lwu t0, 44(s2)
	lwu t1, 868(s4)
	xor t0, t0, t1
	sw t0, 44(s2)
	lwu t0, 48(s2)
	lwu t1, 872(s4)
	xor t0, t0, t1
	sw t0, 48(s2)
	lwu t0, 52(s2)
	lwu t1, 876(s4)
	xor t0, t0, t1
	sw t0, 52(s2)
	lwu t0, 56(s2)
	lwu t1, 880(s4)
	xor t0, t0, t1
	sw t0, 56(s2)
	lwu t0, 60(s2)
	lwu t1, 884(s4)
	xor t0, t0, t1
	sw t0, 60(s2)
	lwu t0, 64(s2)
	lwu t1, 888(s4)
	xor t0, t0, t1
	sw t0, 64(s2)
	lwu t0, 68(s2)
	lwu t1, 892(s4)
	xor t0, t0, t1
	sw t0, 68(s2)
	lwu t0, 72(s2)
	lwu t1, 896(s4)
	xor t0, t0, t1
	sw t0, 72(s2)
	lwu t0, 76(s2)
	lwu t1, 900(s4)
	xor t0, t0, t1
	sw t0, 76(s2)
	lwu t0, 80(s2)
	lwu t1, 904(s4)
	xor t0, t0, t1
	sw t0, 80(s2)
	lwu t0, 84(s2)
	lwu t1, 908(s4)
	xor t0, t0, t1
	sw t0, 84(s2)
	lwu t0, 88(s2)
	lwu t1, 912(s4)
	xor t0, t0, t1
	sw t0, 88(s2)
	lwu t0, 92(s2)
	lwu t1, 916(s4)
	xor t0, t0, t1
	sw t0, 92(s2)
	lwu t0, 96(s2)
	lwu t1, 920(s4)
	xor t0, t0, t1
	sw t0, 96(s2)
	lwu t0, 100(s2)
	lwu t1, 924(s4)
	xor t0, t0, t1
	sw t0, 100(s2)
	lwu t0, 104(s2)
	lwu t1, 928(s4)
	xor t0, t0, t1
	sw t0, 104(s2)
	lwu t0, 108(s2)
	lwu t1, 932(s4)
	xor t0, t0, t1
	sw t0, 108(s2)
	lwu t0, 112(s2)
	lwu t1, 936(s4)
	xor t0, t0, t1
	sw t0, 112(s2)
	lwu t0, 116(s2)
	lwu t1, 940(s4)
	xor t0, t0, t1
	sw t0, 116(s2)
	lwu t0, 120(s2)
	lwu t1, 944(s4)
	xor t0, t0, t1
	sw t0, 120(s2)
	lwu t0, 124(s2)
	lwu t1, 948(s4)
	xor t0, t0, t1
	sw t0, 124(s2)
	lwu t0, 128(s2)
	lwu t1, 952(s4)
	xor t0, t0, t1
	sw t0, 128(s2)
	lwu t0, 132(s2)
	lwu t1, 956(s4)
	xor t0, t0, t1
	sw t0, 132(s2)
	lwu t0, 136(s2)
	lwu t1, 960(s4)
	xor t0, t0, t1
	sw t0, 136(s2)
	lwu t0, 140(s2)
	lwu t1, 964(s4)
	xor t0, t0, t1
	sw t0, 140(s2)
	lwu t0, 144(s2)
	lwu t1, 968(s4)
	xor t0, t0, t1
	sw t0, 144(s2)
	lwu t0, 148(s2)
	lwu t1, 972(s4)
	xor t0, t0, t1
	sw t0, 148(s2)
	lwu t0, 152(s2)
	lwu t1, 976(s4)
	xor t0, t0, t1
	sw t0, 152(s2)
	lwu t0, 156(s2)
	lwu t1, 980(s4)
	xor t0, t0, t1
	sw t0, 156(s2)
	lwu t0, 160(s2)
	lwu t1, 984(s4)
	xor t0, t0, t1
	sw t0, 160(s2)
	lwu t0, 164(s2)
	lwu t1, 988(s4)
	xor t0, t0, t1
	sw t0, 164(s2)
	lwu t0, 168(s2)
	lwu t1, 992(s4)
	xor t0, t0, t1
	sw t0, 168(s2)
	lwu t0, 172(s2)
	lwu t1, 996(s4)
	xor t0, t0, t1
	sw t0, 172(s2)
	lwu t0, 176(s2)
	lwu t1, 1000(s4)
	xor t0, t0, t1
	sw t0, 176(s2)
	lwu t0, 180(s2)
	lwu t1, 1004(s4)
	xor t0, t0, t1
	sw t0, 180(s2)
	lwu t0, 184(s2)
	lwu t1, 1008(s4)
	xor t0, t0, t1
	sw t0, 184(s2)
	lwu t0, 188(s2)
	lwu t1, 1012(s4)
	xor t0, t0, t1
	sw t0, 188(s2)
	lwu t0, 192(s2)
	lwu t1, 1016(s4)
	xor t0, t0, t1
	sw t0, 192(s2)
	lwu t0, 196(s2)
	lwu t1, 1020(s4)
	xor t0, t0, t1
	sw t0, 196(s2)
	lwu t0, 200(s2)
	lwu t1, 1024(s4)
	xor t0, t0, t1
	sw t0, 200(s2)
	lwu t0, 204(s2)
	lwu t1, 1028(s4)
	xor t0, t0, t1
	sw t0, 204(s2)
	lwu t0, 208(s2)
	lwu t1, 1032(s4)
	xor t0, t0, t1
	sw t0, 208(s2)
	lwu t0, 212(s2)
	lwu t1, 1036(s4)
	xor t0, t0, t1
	sw t0, 212(s2)
	lwu t0, 216(s2)
	lwu t1, 1040(s4)
	xor t0, t0, t1
	sw t0, 216(s2)
	lwu t0, 220(s2)
	lwu t1, 1044(s4)
	xor t0, t0, t1
	sw t0, 220(s2)
	lwu t0, 224(s2)
	lwu t1, 1048(s4)
	xor t0, t0, t1
	sw t0, 224(s2)
	lwu t0, 228(s2)
	lwu t1, 1052(s4)
	xor t0, t0, t1
	sw t0, 228(s2)
	lwu t0, 232(s2)
	lwu t1, 1056(s4)
	xor t0, t0, t1
	sw t0, 232(s2)
	lwu t0, 236(s2)
	lwu t1, 1060(s4)
	xor t0, t0, t1
	sw t0, 236(s2)
	lwu t0, 240(s2)
	lwu t1, 1064(s4)
	xor t0, t0, t1
	sw t0, 240(s2)
	lwu t0, 244(s2)
	lwu t1, 1068(s4)
	xor t0, t0, t1
	sw t0, 244(s2)
	lwu t0, 248(s2)
	lwu t1, 1072(s4)
	xor t0, t0, t1
	sw t0, 248(s2)
	lwu t0, 252(s2)
	lwu t1, 1076(s4)
	xor t0, t0, t1
	sw t0, 252(s2)
	addi s2, s2, 256
	addi s3, s3, -16
	srli t0, s3, 4
	bnez t0, 216b
	j 215f
214:
215:
	beqz s3, 218f
220:
	lwu t0, 32(s4)
	sw t0, 824(s4)
	lwu t0, 36(s4)
	sw t0, 828(s4)
	lwu t0, 40(s4)
	sw t0, 832(s4)
	lwu t0, 44(s4)
	sw t0, 836(s4)
	lwu t0, 0(s2)
	sw t0, 32(s4)
	lwu t0, 4(s2)
	sw t0, 36(s4)
	lwu t0, 8(s2)
	sw t0, 40(s4)
	lwu t0, 12(s2)
	sw t0, 44(s4)
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
221:
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
	bnez t0, 221b
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
	lwu t0, 0(s2)
	lwu t1, 824(s4)
	xor t0, t0, t1
	sw t0, 0(s2)
	lwu t0, 4(s2)
	lwu t1, 828(s4)
	xor t0, t0, t1
	sw t0, 4(s2)
	lwu t0, 8(s2)
	lwu t1, 832(s4)
	xor t0, t0, t1
	sw t0, 8(s2)
	lwu t0, 12(s2)
	lwu t1, 836(s4)
	xor t0, t0, t1
	sw t0, 12(s2)
	addi s2, s2, 16
	addi s3, s3, -1
	bnez s3, 220b
	j 219f
218:
219:
25:
	addi s2, s1, 0
	lwu t0, 32(s4)
	sb t0, 0(s2)
	srli t2, t0, 8
	sb t2, 1(s2)
	srli t2, t0, 16
	sb t2, 2(s2)
	srli t2, t0, 24
	sb t2, 3(s2)
	lwu t0, 36(s4)
	sb t0, 4(s2)
	srli t2, t0, 8
	sb t2, 5(s2)
	srli t2, t0, 16
	sb t2, 6(s2)
	srli t2, t0, 24
	sb t2, 7(s2)
	lwu t0, 40(s4)
	sb t0, 8(s2)
	srli t2, t0, 8
	sb t2, 9(s2)
	srli t2, t0, 16
	sb t2, 10(s2)
	srli t2, t0, 24
	sb t2, 11(s2)
	lwu t0, 44(s4)
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
222:
	sd t0, 0(t1)
	addi t1, t1, 8
	addi t2, t2, -1
	bnez t2, 222b
	addi sp, sp, 1200
	addi sp, sp, 2032
	ret
	.option pop

vg_sm4_cfb128_encrypt_final:
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
	sw t0, 32(s4)
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
	sw t0, 36(s4)
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
	sw t0, 40(s4)
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
	sw t0, 44(s4)
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
	andi t0, s2, 3
	beqz t0, 24f
	beqz s3, 26f
28:
	lwu t0, 32(s4)
	sw t0, 824(s4)
	lwu t0, 36(s4)
	sw t0, 828(s4)
	lwu t0, 40(s4)
	sw t0, 832(s4)
	lwu t0, 44(s4)
	sw t0, 836(s4)
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
29:
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
	bnez t0, 29b
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
	addi t0, zero, 16
	bltu s3, t0, 210f
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
	lwu t1, 824(s4)
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
	lwu t1, 828(s4)
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
	lwu t1, 832(s4)
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
	lwu t1, 836(s4)
	xor t0, t0, t1
	sb t0, 12(s2)
	srli t2, t0, 8
	sb t2, 13(s2)
	srli t2, t0, 16
	sb t2, 14(s2)
	srli t2, t0, 24
	sb t2, 15(s2)
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
	sw t0, 32(s4)
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
	sw t0, 36(s4)
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
	sw t0, 40(s4)
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
	sw t0, 44(s4)
	addi s2, s2, 16
	addi s3, s3, -16
	j 211f
210:
	lwu t0, 824(s4)
	sw t0, 32(s4)
	lwu t0, 828(s4)
	sw t0, 36(s4)
	lwu t0, 832(s4)
	sw t0, 40(s4)
	lwu t0, 836(s4)
	sw t0, 44(s4)
	addi t2, s4, 824
212:
	lbu t0, 0(s2)
	lbu t1, 0(t2)
	xor t0, t0, t1
	sb t0, 0(s2)
	addi s2, s2, 1
	addi t2, t2, 1
	addi s3, s3, -1
	bnez s3, 212b
211:
	bnez s3, 28b
	j 27f
26:
27:
	j 25f
24:
	beqz s3, 213f
215:
	lwu t0, 32(s4)
	sw t0, 824(s4)
	lwu t0, 36(s4)
	sw t0, 828(s4)
	lwu t0, 40(s4)
	sw t0, 832(s4)
	lwu t0, 44(s4)
	sw t0, 836(s4)
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
216:
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
	bnez t0, 216b
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
	addi t0, zero, 16
	bltu s3, t0, 217f
	lwu t0, 0(s2)
	lwu t1, 824(s4)
	xor t0, t0, t1
	sw t0, 0(s2)
	lwu t0, 4(s2)
	lwu t1, 828(s4)
	xor t0, t0, t1
	sw t0, 4(s2)
	lwu t0, 8(s2)
	lwu t1, 832(s4)
	xor t0, t0, t1
	sw t0, 8(s2)
	lwu t0, 12(s2)
	lwu t1, 836(s4)
	xor t0, t0, t1
	sw t0, 12(s2)
	lwu t0, 0(s2)
	sw t0, 32(s4)
	lwu t0, 4(s2)
	sw t0, 36(s4)
	lwu t0, 8(s2)
	sw t0, 40(s4)
	lwu t0, 12(s2)
	sw t0, 44(s4)
	addi s2, s2, 16
	addi s3, s3, -16
	j 218f
217:
	lwu t0, 824(s4)
	sw t0, 32(s4)
	lwu t0, 828(s4)
	sw t0, 36(s4)
	lwu t0, 832(s4)
	sw t0, 40(s4)
	lwu t0, 836(s4)
	sw t0, 44(s4)
	addi t2, s4, 824
219:
	lbu t0, 0(s2)
	lbu t1, 0(t2)
	xor t0, t0, t1
	sb t0, 0(s2)
	addi s2, s2, 1
	addi t2, t2, 1
	addi s3, s3, -1
	bnez s3, 219b
218:
	bnez s3, 215b
	j 214f
213:
214:
25:
	addi s2, s1, 0
	lwu t0, 32(s4)
	sb t0, 0(s2)
	srli t2, t0, 8
	sb t2, 1(s2)
	srli t2, t0, 16
	sb t2, 2(s2)
	srli t2, t0, 24
	sb t2, 3(s2)
	lwu t0, 36(s4)
	sb t0, 4(s2)
	srli t2, t0, 8
	sb t2, 5(s2)
	srli t2, t0, 16
	sb t2, 6(s2)
	srli t2, t0, 24
	sb t2, 7(s2)
	lwu t0, 40(s4)
	sb t0, 8(s2)
	srli t2, t0, 8
	sb t2, 9(s2)
	srli t2, t0, 16
	sb t2, 10(s2)
	srli t2, t0, 24
	sb t2, 11(s2)
	lwu t0, 44(s4)
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
220:
	sd t0, 0(t1)
	addi t1, t1, 8
	addi t2, t2, -1
	bnez t2, 220b
	addi sp, sp, 1200
	addi sp, sp, 2032
	ret
	.option pop

vg_sm4_cfb128_decrypt_final:
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
	sw t0, 32(s4)
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
	sw t0, 36(s4)
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
	sw t0, 40(s4)
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
	sw t0, 44(s4)
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
	andi t0, s2, 3
	beqz t0, 24f
	beqz s3, 26f
28:
	lwu t0, 32(s4)
	sw t0, 824(s4)
	lwu t0, 36(s4)
	sw t0, 828(s4)
	lwu t0, 40(s4)
	sw t0, 832(s4)
	lwu t0, 44(s4)
	sw t0, 836(s4)
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
29:
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
	bnez t0, 29b
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
	addi t0, zero, 16
	bltu s3, t0, 210f
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
	sw t0, 32(s4)
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
	sw t0, 36(s4)
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
	sw t0, 40(s4)
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
	sw t0, 44(s4)
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
	lwu t1, 824(s4)
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
	lwu t1, 828(s4)
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
	lwu t1, 832(s4)
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
	lwu t1, 836(s4)
	xor t0, t0, t1
	sb t0, 12(s2)
	srli t2, t0, 8
	sb t2, 13(s2)
	srli t2, t0, 16
	sb t2, 14(s2)
	srli t2, t0, 24
	sb t2, 15(s2)
	addi s2, s2, 16
	addi s3, s3, -16
	j 211f
210:
	lwu t0, 824(s4)
	sw t0, 32(s4)
	lwu t0, 828(s4)
	sw t0, 36(s4)
	lwu t0, 832(s4)
	sw t0, 40(s4)
	lwu t0, 836(s4)
	sw t0, 44(s4)
	addi t2, s4, 824
212:
	lbu t0, 0(s2)
	lbu t1, 0(t2)
	xor t0, t0, t1
	sb t0, 0(s2)
	addi s2, s2, 1
	addi t2, t2, 1
	addi s3, s3, -1
	bnez s3, 212b
211:
	bnez s3, 28b
	j 27f
26:
27:
	j 25f
24:
	beqz s3, 213f
215:
	lwu t0, 32(s4)
	sw t0, 824(s4)
	lwu t0, 36(s4)
	sw t0, 828(s4)
	lwu t0, 40(s4)
	sw t0, 832(s4)
	lwu t0, 44(s4)
	sw t0, 836(s4)
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
216:
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
	bnez t0, 216b
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
	addi t0, zero, 16
	bltu s3, t0, 217f
	lwu t0, 0(s2)
	sw t0, 32(s4)
	lwu t0, 4(s2)
	sw t0, 36(s4)
	lwu t0, 8(s2)
	sw t0, 40(s4)
	lwu t0, 12(s2)
	sw t0, 44(s4)
	lwu t0, 0(s2)
	lwu t1, 824(s4)
	xor t0, t0, t1
	sw t0, 0(s2)
	lwu t0, 4(s2)
	lwu t1, 828(s4)
	xor t0, t0, t1
	sw t0, 4(s2)
	lwu t0, 8(s2)
	lwu t1, 832(s4)
	xor t0, t0, t1
	sw t0, 8(s2)
	lwu t0, 12(s2)
	lwu t1, 836(s4)
	xor t0, t0, t1
	sw t0, 12(s2)
	addi s2, s2, 16
	addi s3, s3, -16
	j 218f
217:
	lwu t0, 824(s4)
	sw t0, 32(s4)
	lwu t0, 828(s4)
	sw t0, 36(s4)
	lwu t0, 832(s4)
	sw t0, 40(s4)
	lwu t0, 836(s4)
	sw t0, 44(s4)
	addi t2, s4, 824
219:
	lbu t0, 0(s2)
	lbu t1, 0(t2)
	xor t0, t0, t1
	sb t0, 0(s2)
	addi s2, s2, 1
	addi t2, t2, 1
	addi s3, s3, -1
	bnez s3, 219b
218:
	bnez s3, 215b
	j 214f
213:
214:
25:
	addi s2, s1, 0
	lwu t0, 32(s4)
	sb t0, 0(s2)
	srli t2, t0, 8
	sb t2, 1(s2)
	srli t2, t0, 16
	sb t2, 2(s2)
	srli t2, t0, 24
	sb t2, 3(s2)
	lwu t0, 36(s4)
	sb t0, 4(s2)
	srli t2, t0, 8
	sb t2, 5(s2)
	srli t2, t0, 16
	sb t2, 6(s2)
	srli t2, t0, 24
	sb t2, 7(s2)
	lwu t0, 40(s4)
	sb t0, 8(s2)
	srli t2, t0, 8
	sb t2, 9(s2)
	srli t2, t0, 16
	sb t2, 10(s2)
	srli t2, t0, 24
	sb t2, 11(s2)
	lwu t0, 44(s4)
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
220:
	sd t0, 0(t1)
	addi t1, t1, 8
	addi t2, t2, -1
	bnez t2, 220b
	addi sp, sp, 1200
	addi sp, sp, 2032
	ret
	.option pop
