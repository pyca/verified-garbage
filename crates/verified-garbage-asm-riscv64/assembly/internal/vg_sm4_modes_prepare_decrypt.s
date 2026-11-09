// The functions of `src/internal/vg_sm4_modes_prepare_decrypt.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sm4_modes_prepare_decrypt:
	.option push
	.option arch, +m, +c
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
	addi a3, a5, 2040
	addi a3, a3, 968
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
	addi a3, a3, -64
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
	addi a3, a3, -64
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
	addi a3, a3, -64
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
	addi a3, a3, -64
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
	addi a3, a3, -64
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
	addi a3, a3, -64
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
	addi a3, a3, -64
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
	addi a3, a3, -64
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
	addi a3, a3, -64
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
	addi a3, a3, -64
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
	addi a3, a3, -64
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
	addi a3, a3, -64
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
	addi a3, a3, -64
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
	addi a3, a3, -64
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
	addi a3, a3, -64
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
	addi a3, a3, -64
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
	addi a3, a3, -64
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
	addi a3, a3, -64
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
	addi a3, a3, -64
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
	addi a3, a3, -64
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
	addi a3, a3, -64
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
	addi a3, a3, -64
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
	addi a3, a3, -64
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
	addi a3, a3, -64
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
	addi a3, a3, -64
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
	addi a3, a3, -64
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
	addi a3, a3, -64
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
	addi a3, a3, -64
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
	addi a3, a3, -64
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
	addi a3, a3, -64
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
	addi a3, a3, -64
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
	addi a3, a3, -64
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
	ret
	.option pop
