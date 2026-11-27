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
	lui t1, 4112
	addiw t1, t1, 257
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 416(a5)
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
	srli t0, a4, 2
	add a1, t0, t0
	add a1, t0, a1
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
	srli s1, s0, 1
	srli s2, s0, 2
	srli s3, s0, 3
	srli s4, s0, 4
	srli s5, s0, 5
	srli s6, s0, 6
	srli s7, s0, 7
	xor s11, s5, s2
	xor t0, s11, s1
	xor s8, t0, s6
	xor t5, s8, s3
	xor a6, t5, s7
	xor t4, t0, s0
	xor a7, a6, s11
	xor t1, a7, t4
	xor t6, t1, s5
	xor s5, t6, s7
	xor s9, t1, s8
	xor t2, t1, s4
	and s0, t2, t1
	xor t5, t2, s5
	xor s10, t2, a6
	xor t3, a6, s4
	and s3, s5, s8
	and a6, t5, s9
	xor s2, s5, s6
	xor s4, a7, s4
	sd t1, 0(a5)
	and t1, s4, s10
	xor a6, t1, a6
	sd t2, 8(a5)
	and t2, s7, t0
	xor t1, t1, s3
	xor t2, s0, t2
	xor t2, t2, t1
	xor s3, t4, s7
	xor s1, s4, s1
	xor s2, t2, s2
	and t2, t4, t3
	xor t1, t1, t2
	sd s10, 16(a5)
	and s10, s3, s1
	xor s10, a6, s10
	xor s10, s10, s0
	xor s10, s10, s11
	and s11, t6, s6
	xor s0, t6, t0
	xor t1, t1, s11
	xor s11, t1, s0
	xor t1, s4, t6
	xor s0, s9, s1
	sd s6, 24(a5)
	and s6, t1, s0
	xor a6, a6, s6
	xor t2, a6, t2
	and a6, s2, s10
	xor s6, t2, a7
	xor a7, s11, a6
	xor a6, s6, a6
	xor t2, s10, s6
	and a7, a7, t2
	xor t2, s2, s11
	xor a7, s6, a7
	xor s10, s10, a7
	xor s2, a6, a7
	and s2, s6, s2
	xor s6, s2, s10
	and t0, a7, t0
	xor s10, a6, s2
	and a6, t2, a6
	xor a6, s11, a6
	and s11, a6, s10
	xor s10, s11, t2
	and t5, s10, t5
	and s11, a7, s7
	xor t2, a6, s10
	and s0, t2, s0
	and s1, a6, s1
	and s2, a6, s3
	and s9, s10, s9
	xor s7, a6, a7
	xor a6, s0, s9
	and t1, t2, t1
	xor s9, s9, s1
	and t2, s7, t3
	xor s3, a7, s6
	xor s10, s10, s6
	and a7, s7, t4
	and t3, s6, s8
	xor s8, t3, t0
	xor t4, a7, t1
	xor t3, a6, t2
	xor t2, s7, s10
	and a7, s6, s5
	ld s6, 16(a5)
	and s6, t2, s6
	xor t1, s11, t1
	and s0, t2, s4
	xor t2, a6, s6
	ld s5, 8(a5)
	and a6, s10, s5
	xor s9, s9, s8
	xor s7, s0, t5
	xor a6, s7, a6
	xor t4, t4, s7
	xor s0, t4, s9
	xor t1, t1, a6
	xor s1, a6, s2
	xor a6, s0, s2
	xor t0, t2, t0
	and t6, s3, t6
	xor t4, s1, s6
	xor t2, a6, a7
	xor s5, s9, s1
	ld a7, 24(a5)
	and s9, s3, a7
	xor a7, t2, t5
	xor s8, t4, s8
	xor a6, t0, s9
	ld t2, 0(a5)
	and s9, s10, t2
	xor s7, s8, s9
	xor s4, a7, s11
	xor s2, t1, t6
	xor t1, t4, s2
	xor s3, a6, s9
	xor s6, t1, t3
	xori s0, s0, -1
	xori s1, s1, -1
	xori s5, s5, -1
	xori s6, s6, -1
	ld t0, 416(a5)
	and s0, s0, t0
	and s1, s1, t0
	slli s1, s1, 1
	xor s0, s0, s1
	and s2, s2, t0
	slli s2, s2, 2
	xor s0, s0, s2
	and s3, s3, t0
	slli s3, s3, 3
	xor s0, s0, s3
	and s4, s4, t0
	slli s4, s4, 4
	xor s0, s0, s4
	and s5, s5, t0
	slli s5, s5, 5
	xor s0, s0, s5
	and s6, s6, t0
	slli s6, s6, 6
	xor s0, s0, s6
	and s7, s7, t0
	slli s7, s7, 7
	xor s0, s0, s7
27:
25:
	j 23f
22:
	srli s1, s0, 1
	srli s2, s0, 2
	srli s3, s0, 3
	srli s4, s0, 4
	srli s5, s0, 5
	srli s6, s0, 6
	srli s7, s0, 7
	xor s11, s5, s2
	xor t0, s11, s1
	xor s8, t0, s6
	xor t5, s8, s3
	xor a6, t5, s7
	xor t4, t0, s0
	xor a7, a6, s11
	xor t1, a7, t4
	xor t6, t1, s5
	xor s5, t6, s7
	xor s9, t1, s8
	xor t2, t1, s4
	and s0, t2, t1
	xor t5, t2, s5
	xor s10, t2, a6
	xor t3, a6, s4
	and s3, s5, s8
	and a6, t5, s9
	xor s2, s5, s6
	xor s4, a7, s4
	sd t1, 0(a5)
	and t1, s4, s10
	xor a6, t1, a6
	sd t2, 8(a5)
	and t2, s7, t0
	xor t1, t1, s3
	xor t2, s0, t2
	xor t2, t2, t1
	xor s3, t4, s7
	xor s1, s4, s1
	xor s2, t2, s2
	and t2, t4, t3
	xor t1, t1, t2
	sd s10, 16(a5)
	and s10, s3, s1
	xor s10, a6, s10
	xor s10, s10, s0
	xor s10, s10, s11
	and s11, t6, s6
	xor s0, t6, t0
	xor t1, t1, s11
	xor s11, t1, s0
	xor t1, s4, t6
	xor s0, s9, s1
	sd s6, 24(a5)
	and s6, t1, s0
	xor a6, a6, s6
	xor t2, a6, t2
	and a6, s2, s10
	xor s6, t2, a7
	xor a7, s11, a6
	xor a6, s6, a6
	xor t2, s10, s6
	and a7, a7, t2
	xor t2, s2, s11
	xor a7, s6, a7
	xor s10, s10, a7
	xor s2, a6, a7
	and s2, s6, s2
	xor s6, s2, s10
	and t0, a7, t0
	xor s10, a6, s2
	and a6, t2, a6
	xor a6, s11, a6
	and s11, a6, s10
	xor s10, s11, t2
	and t5, s10, t5
	and s11, a7, s7
	xor t2, a6, s10
	and s0, t2, s0
	and s1, a6, s1
	and s2, a6, s3
	and s9, s10, s9
	xor s7, a6, a7
	xor a6, s0, s9
	and t1, t2, t1
	xor s9, s9, s1
	and t2, s7, t3
	xor s3, a7, s6
	xor s10, s10, s6
	and a7, s7, t4
	and t3, s6, s8
	xor s8, t3, t0
	xor t4, a7, t1
	xor t3, a6, t2
	xor t2, s7, s10
	and a7, s6, s5
	ld s6, 16(a5)
	and s6, t2, s6
	xor t1, s11, t1
	and s0, t2, s4
	xor t2, a6, s6
	ld s5, 8(a5)
	and a6, s10, s5
	xor s9, s9, s8
	xor s7, s0, t5
	xor a6, s7, a6
	xor t4, t4, s7
	xor s0, t4, s9
	xor t1, t1, a6
	xor s1, a6, s2
	xor a6, s0, s2
	xor t0, t2, t0
	and t6, s3, t6
	xor t4, s1, s6
	xor t2, a6, a7
	xor s5, s9, s1
	ld a7, 24(a5)
	and s9, s3, a7
	xor a7, t2, t5
	xor s8, t4, s8
	xor a6, t0, s9
	ld t2, 0(a5)
	and s9, s10, t2
	xor s7, s8, s9
	xor s4, a7, s11
	xor s2, t1, t6
	xor t1, t4, s2
	xor s3, a6, s9
	xor s6, t1, t3
	xori s0, s0, -1
	xori s1, s1, -1
	xori s5, s5, -1
	xori s6, s6, -1
	ld t0, 416(a5)
	and s0, s0, t0
	and s1, s1, t0
	slli s1, s1, 1
	xor s0, s0, s1
	and s2, s2, t0
	slli s2, s2, 2
	xor s0, s0, s2
	and s3, s3, t0
	slli s3, s3, 3
	xor s0, s0, s3
	and s4, s4, t0
	slli s4, s4, 4
	xor s0, s0, s4
	and s5, s5, t0
	slli s5, s5, 5
	xor s0, s0, s5
	and s6, s6, t0
	slli s6, s6, 6
	xor s0, s0, s6
	and s7, s7, t0
	slli s7, s7, 7
	xor s0, s0, s7
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
