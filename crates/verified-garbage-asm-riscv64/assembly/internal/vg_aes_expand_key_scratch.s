// The functions of `src/internal/vg_aes_expand_key_scratch.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_expand_key_scratch:
	.option push
	.option arch, +m, +c
	addi a5, a3, 0
	addi a5, a5, 7
	andi a5, a5, -8
	sd s0, 320(a5)
	sd s1, 328(a5)
	sd s2, 336(a5)
	sd s3, 344(a5)
	sd s4, 352(a5)
	sd s5, 360(a5)
	sd s6, 368(a5)
	sd s7, 376(a5)
	sd s8, 384(a5)
	sd s9, 392(a5)
	sd s10, 400(a5)
	sd s11, 408(a5)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 416(a5)
	lui t0, 16
	addiw t0, t0, -256
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, -256
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 424(a5)
	lui t0, 4080
	addiw t0, t0, 255
	slli t0, t0, 32
	lui t1, 4080
	addiw t1, t1, 255
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 432(a5)
	lui t0, 349525
	addiw t0, t0, 1365
	slli t0, t0, 32
	lui t1, 349525
	addiw t1, t1, 1365
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 440(a5)
	lui t0, 209715
	addiw t0, t0, 819
	slli t0, t0, 32
	lui t1, 209715
	addiw t1, t1, 819
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 448(a5)
	lui t0, 61681
	addiw t0, t0, -241
	slli t0, t0, 32
	lui t1, 61681
	addiw t1, t1, -241
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 456(a5)
	addi a4, a1, 0
20:
	lbu t0, 0(a0)
	sb t0, 0(a2)
	lbu t0, 1(a0)
	sb t0, 1(a2)
	lbu t0, 2(a0)
	sb t0, 2(a2)
	lbu t0, 3(a0)
	sb t0, 3(a2)
	lbu t0, 4(a0)
	sb t0, 4(a2)
	lbu t0, 5(a0)
	sb t0, 5(a2)
	lbu t0, 6(a0)
	sb t0, 6(a2)
	lbu t0, 7(a0)
	sb t0, 7(a2)
	addi a0, a0, 8
	addi a2, a2, 8
	addi a1, a1, -8
	bnez a1, 20b
	sub a0, a2, a4
	addi a2, a2, -4
	addi a3, zero, 0
	srli a1, a4, 2
	add t0, a1, a1
	add a1, a1, t0
	addi a1, a1, 28
	addi t0, zero, 1
	sd t0, 464(a5)
21:
	lbu s0, 0(a2)
	lbu t0, 1(a2)
	slli t0, t0, 8
	or s0, s0, t0
	lbu t0, 2(a2)
	slli t0, t0, 16
	or s0, s0, t0
	lbu t0, 3(a2)
	slli t0, t0, 24
	or s0, s0, t0
	beqz a3, 22f
	addi t0, a3, -16
	beqz t0, 24f
	j 25f
24:
	addi t0, a4, -32
	beqz t0, 26f
	j 27f
26:
	ld t3, 416(a5)
	ld t4, 424(a5)
	ld t5, 432(a5)
	ld t6, 440(a5)
	ld a6, 448(a5)
	ld a7, 456(a5)
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
	xor t0, s4, s2
	xor t1, s7, s1
	xor t2, s7, s4
	xor t3, s7, s2
	xor s5, s6, s5
	xor t4, s5, s0
	xor s4, t4, s4
	xor t5, t1, t0
	xor t6, t4, s7
	xor s1, t4, s1
	xor a6, s1, t3
	xor s3, s3, t5
	xor s2, s3, s2
	xor s3, s3, s6
	xor s6, s2, s0
	xor a7, s2, s5
	xor s8, s3, t2
	xor s9, s0, s8
	xor s10, a7, s8
	xor s11, a7, t3
	xor s5, s5, s8
	sd s11, 0(a5)
	xor s11, t1, s5
	xor s7, s7, s5
	sd s7, 8(a5)
	and s7, t5, s2
	sd t5, 16(a5)
	and t5, a6, s6
	xor t5, t5, s7
	sd a6, 24(a5)
	and a6, s4, s0
	xor a6, a6, s7
	and s7, t1, s5
	sd t1, 32(a5)
	and t1, s1, t4
	xor t1, t1, s7
	sd s1, 40(a5)
	and s1, t6, s9
	xor s1, s1, s7
	and s7, t2, s8
	sd t2, 48(a5)
	and t2, t0, s10
	xor t2, t2, s7
	sd t0, 56(a5)
	and t0, t3, a7
	xor t0, t0, s7
	xor t5, t5, t2
	xor a6, a6, t0
	xor t1, t1, t2
	xor s1, s1, t0
	xor t5, t5, s3
	ld s3, 0(a5)
	xor a6, a6, s3
	xor t1, t1, s11
	ld s11, 8(a5)
	xor s1, s1, s11
	xor s11, t5, a6
	and t5, t5, t1
	xor s3, s1, t5
	and t0, s11, s3
	xor t0, t0, a6
	xor t2, t1, s1
	xor a6, a6, t5
	and a6, a6, t2
	xor a6, a6, s1
	xor t1, t1, a6
	xor t2, s3, a6
	and s1, s1, t2
	xor t1, s1, t1
	xor s3, s3, s1
	and s3, t0, s3
	xor s11, s11, s3
	xor s3, s11, t1
	xor s1, t0, a6
	xor t2, t0, s11
	xor t5, a6, t1
	xor s7, s1, s3
	and s2, t5, s2
	and s6, t1, s6
	and s0, a6, s0
	and s5, t2, s5
	and t4, s11, t4
	and s9, t0, s9
	and s8, s1, s8
	and s10, s7, s10
	and a7, s3, a7
	sd s6, 8(a5)
	ld s6, 16(a5)
	and t5, t5, s6
	ld s6, 24(a5)
	and t1, t1, s6
	and a6, a6, s4
	ld s4, 32(a5)
	and t2, t2, s4
	ld s4, 40(a5)
	and s11, s11, s4
	and t0, t0, t6
	ld t6, 48(a5)
	and s1, s1, t6
	ld t6, 56(a5)
	and s7, s7, t6
	and s3, s3, t3
	xor s1, s1, s7
	xor a6, t1, a6
	xor s11, s9, s11
	xor t5, t5, t1
	xor t1, s0, t2
	xor s0, s0, s9
	xor a7, s10, a7
	xor s2, s2, s5
	xor s8, s8, s10
	xor s7, s7, s3
	xor t2, t2, s11
	xor t1, t1, s2
	xor s3, t4, s1
	xor s5, s5, s8
	xor s1, s1, t1
	xor t0, t0, t1
	xor a7, a7, s3
	xor t5, t5, s3
	xor t4, t4, s5
	xor t0, t0, a7
	ld s3, 8(a5)
	xor s3, s3, t5
	xor s5, s5, t5
	xor t2, t2, a7
	xori t2, t2, -1
	xor s11, s11, s1
	xori s11, s11, -1
	xor s1, t4, t0
	xor s4, s2, s3
	xor s3, s0, s3
	xor s2, a6, t0
	xor s6, t4, s4
	xori s6, s6, -1
	xor s7, s7, s1
	xori s7, s7, -1
	sd s7, 8(a5)
	addi s7, s5, 0
	ld s5, 8(a5)
	addi s1, t2, 0
	addi s0, s11, 0
	ld t3, 416(a5)
	ld t4, 424(a5)
	ld t5, 432(a5)
	ld t6, 440(a5)
	ld a6, 448(a5)
	ld a7, 456(a5)
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
27:
25:
	j 23f
22:
	ld t3, 416(a5)
	ld t4, 424(a5)
	ld t5, 432(a5)
	ld t6, 440(a5)
	ld a6, 448(a5)
	ld a7, 456(a5)
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
	xor t0, s4, s2
	xor t1, s7, s1
	xor t2, s7, s4
	xor t3, s7, s2
	xor s5, s6, s5
	xor t4, s5, s0
	xor s4, t4, s4
	xor t5, t1, t0
	xor t6, t4, s7
	xor s1, t4, s1
	xor a6, s1, t3
	xor s3, s3, t5
	xor s2, s3, s2
	xor s3, s3, s6
	xor s6, s2, s0
	xor a7, s2, s5
	xor s8, s3, t2
	xor s9, s0, s8
	xor s10, a7, s8
	xor s11, a7, t3
	xor s5, s5, s8
	sd s11, 0(a5)
	xor s11, t1, s5
	xor s7, s7, s5
	sd s7, 8(a5)
	and s7, t5, s2
	sd t5, 16(a5)
	and t5, a6, s6
	xor t5, t5, s7
	sd a6, 24(a5)
	and a6, s4, s0
	xor a6, a6, s7
	and s7, t1, s5
	sd t1, 32(a5)
	and t1, s1, t4
	xor t1, t1, s7
	sd s1, 40(a5)
	and s1, t6, s9
	xor s1, s1, s7
	and s7, t2, s8
	sd t2, 48(a5)
	and t2, t0, s10
	xor t2, t2, s7
	sd t0, 56(a5)
	and t0, t3, a7
	xor t0, t0, s7
	xor t5, t5, t2
	xor a6, a6, t0
	xor t1, t1, t2
	xor s1, s1, t0
	xor t5, t5, s3
	ld s3, 0(a5)
	xor a6, a6, s3
	xor t1, t1, s11
	ld s11, 8(a5)
	xor s1, s1, s11
	xor s11, t5, a6
	and t5, t5, t1
	xor s3, s1, t5
	and t0, s11, s3
	xor t0, t0, a6
	xor t2, t1, s1
	xor a6, a6, t5
	and a6, a6, t2
	xor a6, a6, s1
	xor t1, t1, a6
	xor t2, s3, a6
	and s1, s1, t2
	xor t1, s1, t1
	xor s3, s3, s1
	and s3, t0, s3
	xor s11, s11, s3
	xor s3, s11, t1
	xor s1, t0, a6
	xor t2, t0, s11
	xor t5, a6, t1
	xor s7, s1, s3
	and s2, t5, s2
	and s6, t1, s6
	and s0, a6, s0
	and s5, t2, s5
	and t4, s11, t4
	and s9, t0, s9
	and s8, s1, s8
	and s10, s7, s10
	and a7, s3, a7
	sd s6, 8(a5)
	ld s6, 16(a5)
	and t5, t5, s6
	ld s6, 24(a5)
	and t1, t1, s6
	and a6, a6, s4
	ld s4, 32(a5)
	and t2, t2, s4
	ld s4, 40(a5)
	and s11, s11, s4
	and t0, t0, t6
	ld t6, 48(a5)
	and s1, s1, t6
	ld t6, 56(a5)
	and s7, s7, t6
	and s3, s3, t3
	xor s1, s1, s7
	xor a6, t1, a6
	xor s11, s9, s11
	xor t5, t5, t1
	xor t1, s0, t2
	xor s0, s0, s9
	xor a7, s10, a7
	xor s2, s2, s5
	xor s8, s8, s10
	xor s7, s7, s3
	xor t2, t2, s11
	xor t1, t1, s2
	xor s3, t4, s1
	xor s5, s5, s8
	xor s1, s1, t1
	xor t0, t0, t1
	xor a7, a7, s3
	xor t5, t5, s3
	xor t4, t4, s5
	xor t0, t0, a7
	ld s3, 8(a5)
	xor s3, s3, t5
	xor s5, s5, t5
	xor t2, t2, a7
	xori t2, t2, -1
	xor s11, s11, s1
	xori s11, s11, -1
	xor s1, t4, t0
	xor s4, s2, s3
	xor s3, s0, s3
	xor s2, a6, t0
	xor s6, t4, s4
	xori s6, s6, -1
	xor s7, s7, s1
	xori s7, s7, -1
	sd s7, 8(a5)
	addi s7, s5, 0
	ld s5, 8(a5)
	addi s1, t2, 0
	addi s0, s11, 0
	ld t3, 416(a5)
	ld t4, 424(a5)
	ld t5, 432(a5)
	ld t6, 440(a5)
	ld a6, 448(a5)
	ld a7, 456(a5)
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
	srliw t0, s0, 8
	slliw s0, s0, 24
	xor s0, s0, t0
	ld s1, 464(a5)
	xor s0, s0, s1
	srli s2, s1, 7
	addi s3, zero, 0
	sub s3, s3, s2
	andi s3, s3, 27
	add s1, s1, s1
	xor s1, s1, s3
	andi s1, s1, 255
	sd s1, 464(a5)
23:
	lbu t0, 0(a0)
	lbu t1, 1(a0)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 2(a0)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 3(a0)
	slli t1, t1, 24
	or t0, t0, t1
	xor s0, s0, t0
	sb s0, 4(a2)
	srli t0, s0, 8
	sb t0, 5(a2)
	srli t0, s0, 16
	sb t0, 6(a2)
	srli t0, s0, 24
	sb t0, 7(a2)
	addi a2, a2, 4
	addi a0, a0, 4
	addi a3, a3, 4
	sub t0, a3, a4
	beqz t0, 28f
	j 29f
28:
	addi a3, zero, 0
29:
	addi a1, a1, -1
	bnez a1, 21b
	ld s0, 320(a5)
	ld s1, 328(a5)
	ld s2, 336(a5)
	ld s3, 344(a5)
	ld s4, 352(a5)
	ld s5, 360(a5)
	ld s6, 368(a5)
	ld s7, 376(a5)
	ld s8, 384(a5)
	ld s9, 392(a5)
	ld s10, 400(a5)
	ld s11, 408(a5)
	ret
	.option pop
