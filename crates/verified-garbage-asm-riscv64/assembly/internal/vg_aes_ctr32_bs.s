// The functions of `src/internal/vg_aes_ctr32_bs.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_ctr32_bs:
	.option push
	.option arch, +m, +c
	addi a5, a5, 7
	andi a5, a5, -8
	sd ra, 496(a5)
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
	lui t0, 349525
	addiw t0, t0, 1365
	slli t0, t0, 32
	lui t1, 349525
	addiw t1, t1, 1365
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 416(a5)
	lui t0, 209715
	addiw t0, t0, 819
	slli t0, t0, 32
	lui t1, 209715
	addiw t1, t1, 819
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 424(a5)
	lui t0, 61681
	addiw t0, t0, -241
	slli t0, t0, 32
	lui t1, 61681
	addiw t1, t1, -241
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 432(a5)
	lui t0, 4080
	addiw t0, t0, 255
	slli t0, t0, 32
	lui t1, 4080
	addiw t1, t1, 255
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 440(a5)
	lui t0, 16
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, -1
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 448(a5)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 456(a5)
	lui t0, 4080
	addiw t0, t0, 255
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 512(a5)
	lui t0, 1048560
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 520(a5)
	lui t0, 65521
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 65521
	addiw t1, t1, -1
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 528(a5)
	lui t0, 4080
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 4080
	addiw t1, t1, 0
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 536(a5)
	lbu t0, 0(a2)
	lbu t1, 1(a2)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 2(a2)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 3(a2)
	slli t1, t1, 24
	or t0, t0, t1
	lbu t2, 4(a2)
	lbu t1, 5(a2)
	slli t1, t1, 8
	or t2, t2, t1
	lbu t1, 6(a2)
	slli t1, t1, 16
	or t2, t2, t1
	lbu t1, 7(a2)
	slli t1, t1, 24
	or t2, t2, t1
	slli t2, t2, 32
	or t0, t0, t2
	sd t0, 472(a5)
	lbu t0, 8(a2)
	lbu t1, 9(a2)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 10(a2)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 11(a2)
	slli t1, t1, 24
	or t0, t0, t1
	sd t0, 480(a5)
	lbu t0, 12(a2)
	slli t0, t0, 24
	lbu t1, 13(a2)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 14(a2)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 15(a2)
	or t0, t0, t1
	sd t0, 488(a5)
	add t0, t0, a4
	srli t1, t0, 24
	sb t1, 12(a2)
	srli t1, t0, 16
	sb t1, 13(a2)
	srli t1, t0, 8
	sb t1, 14(a2)
	srli t1, t0, 0
	sb t1, 15(a2)
	slli t0, a1, 6
	add ra, a0, t0
	addi ra, ra, -1920
	beqz a4, 20f
	andi t0, a3, 7
	beqz t0, 22f
24:
	ld s0, 472(a5)
	ld t0, 488(a5)
	addi t0, t0, 0
	srli t1, t0, 24
	sb t1, 484(a5)
	srli t1, t0, 16
	sb t1, 485(a5)
	srli t1, t0, 8
	sb t1, 486(a5)
	srli t1, t0, 0
	sb t1, 487(a5)
	ld s4, 480(a5)
	ld s1, 472(a5)
	ld t0, 488(a5)
	addi t0, t0, 1
	srli t1, t0, 24
	sb t1, 484(a5)
	srli t1, t0, 16
	sb t1, 485(a5)
	srli t1, t0, 8
	sb t1, 486(a5)
	srli t1, t0, 0
	sb t1, 487(a5)
	ld s5, 480(a5)
	ld s2, 472(a5)
	ld t0, 488(a5)
	addi t0, t0, 2
	srli t1, t0, 24
	sb t1, 484(a5)
	srli t1, t0, 16
	sb t1, 485(a5)
	srli t1, t0, 8
	sb t1, 486(a5)
	srli t1, t0, 0
	sb t1, 487(a5)
	ld s6, 480(a5)
	ld s3, 472(a5)
	ld t0, 488(a5)
	addi t0, t0, 3
	srli t1, t0, 24
	sb t1, 484(a5)
	srli t1, t0, 16
	sb t1, 485(a5)
	srli t1, t0, 8
	sb t1, 486(a5)
	srli t1, t0, 0
	sb t1, 487(a5)
	ld s7, 480(a5)
	ld t0, 488(a5)
	addi t0, t0, 4
	sd t0, 488(a5)
	ld t1, 440(a5)
	srli t0, s0, 8
	xor t0, t0, s4
	and t0, t0, t1
	xor s4, s4, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s5
	and t0, t0, t1
	xor s5, s5, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s6
	and t0, t0, t1
	xor s6, s6, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s7
	and t0, t0, t1
	xor s7, s7, t0
	slli t0, t0, 8
	xor s3, s3, t0
	ld t1, 448(a5)
	srli t0, s0, 16
	xor t0, t0, s4
	and t0, t0, t1
	xor s4, s4, t0
	slli t0, t0, 16
	xor s0, s0, t0
	srli t0, s1, 16
	xor t0, t0, s5
	and t0, t0, t1
	xor s5, s5, t0
	slli t0, t0, 16
	xor s1, s1, t0
	srli t0, s2, 16
	xor t0, t0, s6
	and t0, t0, t1
	xor s6, s6, t0
	slli t0, t0, 16
	xor s2, s2, t0
	srli t0, s3, 16
	xor t0, t0, s7
	and t0, t0, t1
	xor s7, s7, t0
	slli t0, t0, 16
	xor s3, s3, t0
	ld t1, 456(a5)
	srli t0, s0, 32
	xor t0, t0, s4
	and t0, t0, t1
	xor s4, s4, t0
	slli t0, t0, 32
	xor s0, s0, t0
	srli t0, s1, 32
	xor t0, t0, s5
	and t0, t0, t1
	xor s5, s5, t0
	slli t0, t0, 32
	xor s1, s1, t0
	srli t0, s2, 32
	xor t0, t0, s6
	and t0, t0, t1
	xor s6, s6, t0
	slli t0, t0, 32
	xor s2, s2, t0
	srli t0, s3, 32
	xor t0, t0, s7
	and t0, t0, t1
	xor s7, s7, t0
	slli t0, t0, 32
	xor s3, s3, t0
	ld t1, 432(a5)
	srli t0, s0, 4
	xor t0, t0, s4
	and t0, t0, t1
	xor s4, s4, t0
	slli t0, t0, 4
	xor s0, s0, t0
	srli t0, s1, 4
	xor t0, t0, s5
	and t0, t0, t1
	xor s5, s5, t0
	slli t0, t0, 4
	xor s1, s1, t0
	srli t0, s2, 4
	xor t0, t0, s6
	and t0, t0, t1
	xor s6, s6, t0
	slli t0, t0, 4
	xor s2, s2, t0
	srli t0, s3, 4
	xor t0, t0, s7
	and t0, t0, t1
	xor s7, s7, t0
	slli t0, t0, 4
	xor s3, s3, t0
	ld t1, 424(a5)
	srli t0, s0, 2
	xor t0, t0, s2
	and t0, t0, t1
	xor s2, s2, t0
	slli t0, t0, 2
	xor s0, s0, t0
	srli t0, s1, 2
	xor t0, t0, s3
	and t0, t0, t1
	xor s3, s3, t0
	slli t0, t0, 2
	xor s1, s1, t0
	srli t0, s4, 2
	xor t0, t0, s6
	and t0, t0, t1
	xor s6, s6, t0
	slli t0, t0, 2
	xor s4, s4, t0
	srli t0, s5, 2
	xor t0, t0, s7
	and t0, t0, t1
	xor s7, s7, t0
	slli t0, t0, 2
	xor s5, s5, t0
	ld t1, 416(a5)
	srli t0, s0, 1
	xor t0, t0, s1
	and t0, t0, t1
	xor s1, s1, t0
	slli t0, t0, 1
	xor s0, s0, t0
	srli t0, s2, 1
	xor t0, t0, s3
	and t0, t0, t1
	xor s3, s3, t0
	slli t0, t0, 1
	xor s2, s2, t0
	srli t0, s4, 1
	xor t0, t0, s5
	and t0, t0, t1
	xor s5, s5, t0
	slli t0, t0, 1
	xor s4, s4, t0
	srli t0, s6, 1
	xor t0, t0, s7
	and t0, t0, t1
	xor s7, s7, t0
	slli t0, t0, 1
	xor s6, s6, t0
	addi a1, a0, 0
	ld t0, 0(a1)
	xor s0, s0, t0
	ld t0, 8(a1)
	xor s1, s1, t0
	ld t0, 16(a1)
	xor s2, s2, t0
	ld t0, 24(a1)
	xor s3, s3, t0
	ld t0, 32(a1)
	xor s4, s4, t0
	ld t0, 40(a1)
	xor s5, s5, t0
	ld t0, 48(a1)
	xor s6, s6, t0
	ld t0, 56(a1)
	xor s7, s7, t0
25:
	addi a1, a1, 64
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
	ld t3, 512(a5)
	ld t4, 520(a5)
	srli t0, s0, 8
	xor t0, t0, s0
	and t0, t0, t3
	xor s0, s0, t0
	slli t0, t0, 8
	xor s0, s0, t0
	and t0, s0, t4
	xor s0, s0, t0
	srli t1, t0, 4
	slli t0, t0, 12
	xor t0, t0, t1
	and t0, t0, t4
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s1
	and t0, t0, t3
	xor s1, s1, t0
	slli t0, t0, 8
	xor s1, s1, t0
	and t0, s1, t4
	xor s1, s1, t0
	srli t1, t0, 4
	slli t0, t0, 12
	xor t0, t0, t1
	and t0, t0, t4
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s2
	and t0, t0, t3
	xor s2, s2, t0
	slli t0, t0, 8
	xor s2, s2, t0
	and t0, s2, t4
	xor s2, s2, t0
	srli t1, t0, 4
	slli t0, t0, 12
	xor t0, t0, t1
	and t0, t0, t4
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s3
	and t0, t0, t3
	xor s3, s3, t0
	slli t0, t0, 8
	xor s3, s3, t0
	and t0, s3, t4
	xor s3, s3, t0
	srli t1, t0, 4
	slli t0, t0, 12
	xor t0, t0, t1
	and t0, t0, t4
	xor s3, s3, t0
	srli t0, s4, 8
	xor t0, t0, s4
	and t0, t0, t3
	xor s4, s4, t0
	slli t0, t0, 8
	xor s4, s4, t0
	and t0, s4, t4
	xor s4, s4, t0
	srli t1, t0, 4
	slli t0, t0, 12
	xor t0, t0, t1
	and t0, t0, t4
	xor s4, s4, t0
	srli t0, s5, 8
	xor t0, t0, s5
	and t0, t0, t3
	xor s5, s5, t0
	slli t0, t0, 8
	xor s5, s5, t0
	and t0, s5, t4
	xor s5, s5, t0
	srli t1, t0, 4
	slli t0, t0, 12
	xor t0, t0, t1
	and t0, t0, t4
	xor s5, s5, t0
	srli t0, s6, 8
	xor t0, t0, s6
	and t0, t0, t3
	xor s6, s6, t0
	slli t0, t0, 8
	xor s6, s6, t0
	and t0, s6, t4
	xor s6, s6, t0
	srli t1, t0, 4
	slli t0, t0, 12
	xor t0, t0, t1
	and t0, t0, t4
	xor s6, s6, t0
	srli t0, s7, 8
	xor t0, t0, s7
	and t0, t0, t3
	xor s7, s7, t0
	slli t0, t0, 8
	xor s7, s7, t0
	and t0, s7, t4
	xor s7, s7, t0
	srli t1, t0, 4
	slli t0, t0, 12
	xor t0, t0, t1
	and t0, t0, t4
	xor s7, s7, t0
	srli t0, s7, 16
	slli t1, s7, 48
	xor t6, t0, t1
	xor t2, s7, t6
	srli t0, s6, 16
	slli t1, s6, 48
	xor t5, t0, t1
	xor t3, s6, t5
	srli t0, t2, 32
	slli t1, t2, 32
	xor t0, t0, t1
	xor s7, t0, t6
	xor s7, s7, t3
	srli t0, s5, 16
	slli t1, s5, 48
	xor t6, t0, t1
	xor t4, s5, t6
	srli t0, t3, 32
	slli t1, t3, 32
	xor t0, t0, t1
	xor s6, t0, t5
	xor s6, s6, t4
	srli t0, s4, 16
	slli t1, s4, 48
	xor t5, t0, t1
	xor t3, s4, t5
	srli t0, t4, 32
	slli t1, t4, 32
	xor t0, t0, t1
	xor s5, t0, t6
	xor s5, s5, t3
	srli t0, s3, 16
	slli t1, s3, 48
	xor t6, t0, t1
	xor t4, s3, t6
	srli t0, t3, 32
	slli t1, t3, 32
	xor t0, t0, t1
	xor s4, t0, t5
	xor s4, s4, t4
	xor s4, s4, t2
	srli t0, s2, 16
	slli t1, s2, 48
	xor t5, t0, t1
	xor t3, s2, t5
	srli t0, t4, 32
	slli t1, t4, 32
	xor t0, t0, t1
	xor s3, t0, t6
	xor s3, s3, t3
	xor s3, s3, t2
	srli t0, s1, 16
	slli t1, s1, 48
	xor t6, t0, t1
	xor t4, s1, t6
	srli t0, t3, 32
	slli t1, t3, 32
	xor t0, t0, t1
	xor s2, t0, t5
	xor s2, s2, t4
	srli t0, s0, 16
	slli t1, s0, 48
	xor t5, t0, t1
	xor t3, s0, t5
	srli t0, t4, 32
	slli t1, t4, 32
	xor t0, t0, t1
	xor s1, t0, t6
	xor s1, s1, t3
	xor s1, s1, t2
	srli t0, t3, 32
	slli t1, t3, 32
	xor t0, t0, t1
	xor s0, t0, t5
	xor s0, s0, t2
	ld t0, 0(a1)
	xor s0, s0, t0
	ld t0, 8(a1)
	xor s1, s1, t0
	ld t0, 16(a1)
	xor s2, s2, t0
	ld t0, 24(a1)
	xor s3, s3, t0
	ld t0, 32(a1)
	xor s4, s4, t0
	ld t0, 40(a1)
	xor s5, s5, t0
	ld t0, 48(a1)
	xor s6, s6, t0
	ld t0, 56(a1)
	xor s7, s7, t0
	sub t0, a1, ra
	addi t0, t0, -1856
	bnez t0, 25b
	addi a1, a1, 64
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
	ld t3, 512(a5)
	ld t4, 520(a5)
	srli t0, s0, 8
	xor t0, t0, s0
	and t0, t0, t3
	xor s0, s0, t0
	slli t0, t0, 8
	xor s0, s0, t0
	and t0, s0, t4
	xor s0, s0, t0
	srli t1, t0, 4
	slli t0, t0, 12
	xor t0, t0, t1
	and t0, t0, t4
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s1
	and t0, t0, t3
	xor s1, s1, t0
	slli t0, t0, 8
	xor s1, s1, t0
	and t0, s1, t4
	xor s1, s1, t0
	srli t1, t0, 4
	slli t0, t0, 12
	xor t0, t0, t1
	and t0, t0, t4
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s2
	and t0, t0, t3
	xor s2, s2, t0
	slli t0, t0, 8
	xor s2, s2, t0
	and t0, s2, t4
	xor s2, s2, t0
	srli t1, t0, 4
	slli t0, t0, 12
	xor t0, t0, t1
	and t0, t0, t4
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s3
	and t0, t0, t3
	xor s3, s3, t0
	slli t0, t0, 8
	xor s3, s3, t0
	and t0, s3, t4
	xor s3, s3, t0
	srli t1, t0, 4
	slli t0, t0, 12
	xor t0, t0, t1
	and t0, t0, t4
	xor s3, s3, t0
	srli t0, s4, 8
	xor t0, t0, s4
	and t0, t0, t3
	xor s4, s4, t0
	slli t0, t0, 8
	xor s4, s4, t0
	and t0, s4, t4
	xor s4, s4, t0
	srli t1, t0, 4
	slli t0, t0, 12
	xor t0, t0, t1
	and t0, t0, t4
	xor s4, s4, t0
	srli t0, s5, 8
	xor t0, t0, s5
	and t0, t0, t3
	xor s5, s5, t0
	slli t0, t0, 8
	xor s5, s5, t0
	and t0, s5, t4
	xor s5, s5, t0
	srli t1, t0, 4
	slli t0, t0, 12
	xor t0, t0, t1
	and t0, t0, t4
	xor s5, s5, t0
	srli t0, s6, 8
	xor t0, t0, s6
	and t0, t0, t3
	xor s6, s6, t0
	slli t0, t0, 8
	xor s6, s6, t0
	and t0, s6, t4
	xor s6, s6, t0
	srli t1, t0, 4
	slli t0, t0, 12
	xor t0, t0, t1
	and t0, t0, t4
	xor s6, s6, t0
	srli t0, s7, 8
	xor t0, t0, s7
	and t0, t0, t3
	xor s7, s7, t0
	slli t0, t0, 8
	xor s7, s7, t0
	and t0, s7, t4
	xor s7, s7, t0
	srli t1, t0, 4
	slli t0, t0, 12
	xor t0, t0, t1
	and t0, t0, t4
	xor s7, s7, t0
	ld t0, 0(a1)
	xor s0, s0, t0
	ld t0, 8(a1)
	xor s1, s1, t0
	ld t0, 16(a1)
	xor s2, s2, t0
	ld t0, 24(a1)
	xor s3, s3, t0
	ld t0, 32(a1)
	xor s4, s4, t0
	ld t0, 40(a1)
	xor s5, s5, t0
	ld t0, 48(a1)
	xor s6, s6, t0
	ld t0, 56(a1)
	xor s7, s7, t0
	ld t1, 416(a5)
	srli t0, s0, 1
	xor t0, t0, s1
	and t0, t0, t1
	xor s1, s1, t0
	slli t0, t0, 1
	xor s0, s0, t0
	srli t0, s2, 1
	xor t0, t0, s3
	and t0, t0, t1
	xor s3, s3, t0
	slli t0, t0, 1
	xor s2, s2, t0
	srli t0, s4, 1
	xor t0, t0, s5
	and t0, t0, t1
	xor s5, s5, t0
	slli t0, t0, 1
	xor s4, s4, t0
	srli t0, s6, 1
	xor t0, t0, s7
	and t0, t0, t1
	xor s7, s7, t0
	slli t0, t0, 1
	xor s6, s6, t0
	ld t1, 424(a5)
	srli t0, s0, 2
	xor t0, t0, s2
	and t0, t0, t1
	xor s2, s2, t0
	slli t0, t0, 2
	xor s0, s0, t0
	srli t0, s1, 2
	xor t0, t0, s3
	and t0, t0, t1
	xor s3, s3, t0
	slli t0, t0, 2
	xor s1, s1, t0
	srli t0, s4, 2
	xor t0, t0, s6
	and t0, t0, t1
	xor s6, s6, t0
	slli t0, t0, 2
	xor s4, s4, t0
	srli t0, s5, 2
	xor t0, t0, s7
	and t0, t0, t1
	xor s7, s7, t0
	slli t0, t0, 2
	xor s5, s5, t0
	ld t1, 432(a5)
	srli t0, s0, 4
	xor t0, t0, s4
	and t0, t0, t1
	xor s4, s4, t0
	slli t0, t0, 4
	xor s0, s0, t0
	srli t0, s1, 4
	xor t0, t0, s5
	and t0, t0, t1
	xor s5, s5, t0
	slli t0, t0, 4
	xor s1, s1, t0
	srli t0, s2, 4
	xor t0, t0, s6
	and t0, t0, t1
	xor s6, s6, t0
	slli t0, t0, 4
	xor s2, s2, t0
	srli t0, s3, 4
	xor t0, t0, s7
	and t0, t0, t1
	xor s7, s7, t0
	slli t0, t0, 4
	xor s3, s3, t0
	ld t1, 456(a5)
	srli t0, s0, 32
	xor t0, t0, s4
	and t0, t0, t1
	xor s4, s4, t0
	slli t0, t0, 32
	xor s0, s0, t0
	srli t0, s1, 32
	xor t0, t0, s5
	and t0, t0, t1
	xor s5, s5, t0
	slli t0, t0, 32
	xor s1, s1, t0
	srli t0, s2, 32
	xor t0, t0, s6
	and t0, t0, t1
	xor s6, s6, t0
	slli t0, t0, 32
	xor s2, s2, t0
	srli t0, s3, 32
	xor t0, t0, s7
	and t0, t0, t1
	xor s7, s7, t0
	slli t0, t0, 32
	xor s3, s3, t0
	ld t1, 448(a5)
	srli t0, s0, 16
	xor t0, t0, s4
	and t0, t0, t1
	xor s4, s4, t0
	slli t0, t0, 16
	xor s0, s0, t0
	srli t0, s1, 16
	xor t0, t0, s5
	and t0, t0, t1
	xor s5, s5, t0
	slli t0, t0, 16
	xor s1, s1, t0
	srli t0, s2, 16
	xor t0, t0, s6
	and t0, t0, t1
	xor s6, s6, t0
	slli t0, t0, 16
	xor s2, s2, t0
	srli t0, s3, 16
	xor t0, t0, s7
	and t0, t0, t1
	xor s7, s7, t0
	slli t0, t0, 16
	xor s3, s3, t0
	ld t1, 440(a5)
	srli t0, s0, 8
	xor t0, t0, s4
	and t0, t0, t1
	xor s4, s4, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s5
	and t0, t0, t1
	xor s5, s5, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s6
	and t0, t0, t1
	xor s6, s6, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s7
	and t0, t0, t1
	xor s7, s7, t0
	slli t0, t0, 8
	xor s3, s3, t0
	srli t0, a4, 2
	bnez t0, 26f
	lbu t0, 0(a3)
	lbu t1, 1(a3)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 2(a3)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 3(a3)
	slli t1, t1, 24
	or t0, t0, t1
	lbu t2, 4(a3)
	lbu t1, 5(a3)
	slli t1, t1, 8
	or t2, t2, t1
	lbu t1, 6(a3)
	slli t1, t1, 16
	or t2, t2, t1
	lbu t1, 7(a3)
	slli t1, t1, 24
	or t2, t2, t1
	slli t2, t2, 32
	or t0, t0, t2
	xor t0, t0, s0
	sb t0, 0(a3)
	srli t1, t0, 8
	sb t1, 1(a3)
	srli t1, t0, 16
	sb t1, 2(a3)
	srli t1, t0, 24
	sb t1, 3(a3)
	srli t2, t0, 32
	sb t2, 4(a3)
	srli t1, t2, 8
	sb t1, 5(a3)
	srli t1, t2, 16
	sb t1, 6(a3)
	srli t1, t2, 24
	sb t1, 7(a3)
	lbu t0, 8(a3)
	lbu t1, 9(a3)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 10(a3)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 11(a3)
	slli t1, t1, 24
	or t0, t0, t1
	lbu t2, 12(a3)
	lbu t1, 13(a3)
	slli t1, t1, 8
	or t2, t2, t1
	lbu t1, 14(a3)
	slli t1, t1, 16
	or t2, t2, t1
	lbu t1, 15(a3)
	slli t1, t1, 24
	or t2, t2, t1
	slli t2, t2, 32
	or t0, t0, t2
	xor t0, t0, s4
	sb t0, 8(a3)
	srli t1, t0, 8
	sb t1, 9(a3)
	srli t1, t0, 16
	sb t1, 10(a3)
	srli t1, t0, 24
	sb t1, 11(a3)
	srli t2, t0, 32
	sb t2, 12(a3)
	srli t1, t2, 8
	sb t1, 13(a3)
	srli t1, t2, 16
	sb t1, 14(a3)
	srli t1, t2, 24
	sb t1, 15(a3)
	addi t0, a4, -1
	bnez t0, 28f
	j 29f
28:
	lbu t0, 16(a3)
	lbu t1, 17(a3)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 18(a3)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 19(a3)
	slli t1, t1, 24
	or t0, t0, t1
	lbu t2, 20(a3)
	lbu t1, 21(a3)
	slli t1, t1, 8
	or t2, t2, t1
	lbu t1, 22(a3)
	slli t1, t1, 16
	or t2, t2, t1
	lbu t1, 23(a3)
	slli t1, t1, 24
	or t2, t2, t1
	slli t2, t2, 32
	or t0, t0, t2
	xor t0, t0, s1
	sb t0, 16(a3)
	srli t1, t0, 8
	sb t1, 17(a3)
	srli t1, t0, 16
	sb t1, 18(a3)
	srli t1, t0, 24
	sb t1, 19(a3)
	srli t2, t0, 32
	sb t2, 20(a3)
	srli t1, t2, 8
	sb t1, 21(a3)
	srli t1, t2, 16
	sb t1, 22(a3)
	srli t1, t2, 24
	sb t1, 23(a3)
	lbu t0, 24(a3)
	lbu t1, 25(a3)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 26(a3)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 27(a3)
	slli t1, t1, 24
	or t0, t0, t1
	lbu t2, 28(a3)
	lbu t1, 29(a3)
	slli t1, t1, 8
	or t2, t2, t1
	lbu t1, 30(a3)
	slli t1, t1, 16
	or t2, t2, t1
	lbu t1, 31(a3)
	slli t1, t1, 24
	or t2, t2, t1
	slli t2, t2, 32
	or t0, t0, t2
	xor t0, t0, s5
	sb t0, 24(a3)
	srli t1, t0, 8
	sb t1, 25(a3)
	srli t1, t0, 16
	sb t1, 26(a3)
	srli t1, t0, 24
	sb t1, 27(a3)
	srli t2, t0, 32
	sb t2, 28(a3)
	srli t1, t2, 8
	sb t1, 29(a3)
	srli t1, t2, 16
	sb t1, 30(a3)
	srli t1, t2, 24
	sb t1, 31(a3)
	addi t0, a4, -3
	beqz t0, 210f
	j 211f
210:
	lbu t0, 32(a3)
	lbu t1, 33(a3)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 34(a3)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 35(a3)
	slli t1, t1, 24
	or t0, t0, t1
	lbu t2, 36(a3)
	lbu t1, 37(a3)
	slli t1, t1, 8
	or t2, t2, t1
	lbu t1, 38(a3)
	slli t1, t1, 16
	or t2, t2, t1
	lbu t1, 39(a3)
	slli t1, t1, 24
	or t2, t2, t1
	slli t2, t2, 32
	or t0, t0, t2
	xor t0, t0, s2
	sb t0, 32(a3)
	srli t1, t0, 8
	sb t1, 33(a3)
	srli t1, t0, 16
	sb t1, 34(a3)
	srli t1, t0, 24
	sb t1, 35(a3)
	srli t2, t0, 32
	sb t2, 36(a3)
	srli t1, t2, 8
	sb t1, 37(a3)
	srli t1, t2, 16
	sb t1, 38(a3)
	srli t1, t2, 24
	sb t1, 39(a3)
	lbu t0, 40(a3)
	lbu t1, 41(a3)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 42(a3)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 43(a3)
	slli t1, t1, 24
	or t0, t0, t1
	lbu t2, 44(a3)
	lbu t1, 45(a3)
	slli t1, t1, 8
	or t2, t2, t1
	lbu t1, 46(a3)
	slli t1, t1, 16
	or t2, t2, t1
	lbu t1, 47(a3)
	slli t1, t1, 24
	or t2, t2, t1
	slli t2, t2, 32
	or t0, t0, t2
	xor t0, t0, s6
	sb t0, 40(a3)
	srli t1, t0, 8
	sb t1, 41(a3)
	srli t1, t0, 16
	sb t1, 42(a3)
	srli t1, t0, 24
	sb t1, 43(a3)
	srli t2, t0, 32
	sb t2, 44(a3)
	srli t1, t2, 8
	sb t1, 45(a3)
	srli t1, t2, 16
	sb t1, 46(a3)
	srli t1, t2, 24
	sb t1, 47(a3)
211:
29:
	addi a4, zero, 0
	j 27f
26:
	lbu t0, 0(a3)
	lbu t1, 1(a3)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 2(a3)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 3(a3)
	slli t1, t1, 24
	or t0, t0, t1
	lbu t2, 4(a3)
	lbu t1, 5(a3)
	slli t1, t1, 8
	or t2, t2, t1
	lbu t1, 6(a3)
	slli t1, t1, 16
	or t2, t2, t1
	lbu t1, 7(a3)
	slli t1, t1, 24
	or t2, t2, t1
	slli t2, t2, 32
	or t0, t0, t2
	xor t0, t0, s0
	sb t0, 0(a3)
	srli t1, t0, 8
	sb t1, 1(a3)
	srli t1, t0, 16
	sb t1, 2(a3)
	srli t1, t0, 24
	sb t1, 3(a3)
	srli t2, t0, 32
	sb t2, 4(a3)
	srli t1, t2, 8
	sb t1, 5(a3)
	srli t1, t2, 16
	sb t1, 6(a3)
	srli t1, t2, 24
	sb t1, 7(a3)
	lbu t0, 8(a3)
	lbu t1, 9(a3)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 10(a3)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 11(a3)
	slli t1, t1, 24
	or t0, t0, t1
	lbu t2, 12(a3)
	lbu t1, 13(a3)
	slli t1, t1, 8
	or t2, t2, t1
	lbu t1, 14(a3)
	slli t1, t1, 16
	or t2, t2, t1
	lbu t1, 15(a3)
	slli t1, t1, 24
	or t2, t2, t1
	slli t2, t2, 32
	or t0, t0, t2
	xor t0, t0, s4
	sb t0, 8(a3)
	srli t1, t0, 8
	sb t1, 9(a3)
	srli t1, t0, 16
	sb t1, 10(a3)
	srli t1, t0, 24
	sb t1, 11(a3)
	srli t2, t0, 32
	sb t2, 12(a3)
	srli t1, t2, 8
	sb t1, 13(a3)
	srli t1, t2, 16
	sb t1, 14(a3)
	srli t1, t2, 24
	sb t1, 15(a3)
	lbu t0, 16(a3)
	lbu t1, 17(a3)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 18(a3)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 19(a3)
	slli t1, t1, 24
	or t0, t0, t1
	lbu t2, 20(a3)
	lbu t1, 21(a3)
	slli t1, t1, 8
	or t2, t2, t1
	lbu t1, 22(a3)
	slli t1, t1, 16
	or t2, t2, t1
	lbu t1, 23(a3)
	slli t1, t1, 24
	or t2, t2, t1
	slli t2, t2, 32
	or t0, t0, t2
	xor t0, t0, s1
	sb t0, 16(a3)
	srli t1, t0, 8
	sb t1, 17(a3)
	srli t1, t0, 16
	sb t1, 18(a3)
	srli t1, t0, 24
	sb t1, 19(a3)
	srli t2, t0, 32
	sb t2, 20(a3)
	srli t1, t2, 8
	sb t1, 21(a3)
	srli t1, t2, 16
	sb t1, 22(a3)
	srli t1, t2, 24
	sb t1, 23(a3)
	lbu t0, 24(a3)
	lbu t1, 25(a3)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 26(a3)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 27(a3)
	slli t1, t1, 24
	or t0, t0, t1
	lbu t2, 28(a3)
	lbu t1, 29(a3)
	slli t1, t1, 8
	or t2, t2, t1
	lbu t1, 30(a3)
	slli t1, t1, 16
	or t2, t2, t1
	lbu t1, 31(a3)
	slli t1, t1, 24
	or t2, t2, t1
	slli t2, t2, 32
	or t0, t0, t2
	xor t0, t0, s5
	sb t0, 24(a3)
	srli t1, t0, 8
	sb t1, 25(a3)
	srli t1, t0, 16
	sb t1, 26(a3)
	srli t1, t0, 24
	sb t1, 27(a3)
	srli t2, t0, 32
	sb t2, 28(a3)
	srli t1, t2, 8
	sb t1, 29(a3)
	srli t1, t2, 16
	sb t1, 30(a3)
	srli t1, t2, 24
	sb t1, 31(a3)
	lbu t0, 32(a3)
	lbu t1, 33(a3)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 34(a3)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 35(a3)
	slli t1, t1, 24
	or t0, t0, t1
	lbu t2, 36(a3)
	lbu t1, 37(a3)
	slli t1, t1, 8
	or t2, t2, t1
	lbu t1, 38(a3)
	slli t1, t1, 16
	or t2, t2, t1
	lbu t1, 39(a3)
	slli t1, t1, 24
	or t2, t2, t1
	slli t2, t2, 32
	or t0, t0, t2
	xor t0, t0, s2
	sb t0, 32(a3)
	srli t1, t0, 8
	sb t1, 33(a3)
	srli t1, t0, 16
	sb t1, 34(a3)
	srli t1, t0, 24
	sb t1, 35(a3)
	srli t2, t0, 32
	sb t2, 36(a3)
	srli t1, t2, 8
	sb t1, 37(a3)
	srli t1, t2, 16
	sb t1, 38(a3)
	srli t1, t2, 24
	sb t1, 39(a3)
	lbu t0, 40(a3)
	lbu t1, 41(a3)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 42(a3)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 43(a3)
	slli t1, t1, 24
	or t0, t0, t1
	lbu t2, 44(a3)
	lbu t1, 45(a3)
	slli t1, t1, 8
	or t2, t2, t1
	lbu t1, 46(a3)
	slli t1, t1, 16
	or t2, t2, t1
	lbu t1, 47(a3)
	slli t1, t1, 24
	or t2, t2, t1
	slli t2, t2, 32
	or t0, t0, t2
	xor t0, t0, s6
	sb t0, 40(a3)
	srli t1, t0, 8
	sb t1, 41(a3)
	srli t1, t0, 16
	sb t1, 42(a3)
	srli t1, t0, 24
	sb t1, 43(a3)
	srli t2, t0, 32
	sb t2, 44(a3)
	srli t1, t2, 8
	sb t1, 45(a3)
	srli t1, t2, 16
	sb t1, 46(a3)
	srli t1, t2, 24
	sb t1, 47(a3)
	lbu t0, 48(a3)
	lbu t1, 49(a3)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 50(a3)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 51(a3)
	slli t1, t1, 24
	or t0, t0, t1
	lbu t2, 52(a3)
	lbu t1, 53(a3)
	slli t1, t1, 8
	or t2, t2, t1
	lbu t1, 54(a3)
	slli t1, t1, 16
	or t2, t2, t1
	lbu t1, 55(a3)
	slli t1, t1, 24
	or t2, t2, t1
	slli t2, t2, 32
	or t0, t0, t2
	xor t0, t0, s3
	sb t0, 48(a3)
	srli t1, t0, 8
	sb t1, 49(a3)
	srli t1, t0, 16
	sb t1, 50(a3)
	srli t1, t0, 24
	sb t1, 51(a3)
	srli t2, t0, 32
	sb t2, 52(a3)
	srli t1, t2, 8
	sb t1, 53(a3)
	srli t1, t2, 16
	sb t1, 54(a3)
	srli t1, t2, 24
	sb t1, 55(a3)
	lbu t0, 56(a3)
	lbu t1, 57(a3)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 58(a3)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 59(a3)
	slli t1, t1, 24
	or t0, t0, t1
	lbu t2, 60(a3)
	lbu t1, 61(a3)
	slli t1, t1, 8
	or t2, t2, t1
	lbu t1, 62(a3)
	slli t1, t1, 16
	or t2, t2, t1
	lbu t1, 63(a3)
	slli t1, t1, 24
	or t2, t2, t1
	slli t2, t2, 32
	or t0, t0, t2
	xor t0, t0, s7
	sb t0, 56(a3)
	srli t1, t0, 8
	sb t1, 57(a3)
	srli t1, t0, 16
	sb t1, 58(a3)
	srli t1, t0, 24
	sb t1, 59(a3)
	srli t2, t0, 32
	sb t2, 60(a3)
	srli t1, t2, 8
	sb t1, 61(a3)
	srli t1, t2, 16
	sb t1, 62(a3)
	srli t1, t2, 24
	sb t1, 63(a3)
	addi a3, a3, 64
	addi a4, a4, -4
27:
	bnez a4, 24b
	j 23f
22:
212:
	ld s0, 472(a5)
	ld t0, 488(a5)
	addi t0, t0, 0
	srli t1, t0, 24
	sb t1, 484(a5)
	srli t1, t0, 16
	sb t1, 485(a5)
	srli t1, t0, 8
	sb t1, 486(a5)
	srli t1, t0, 0
	sb t1, 487(a5)
	ld s4, 480(a5)
	ld s1, 472(a5)
	ld t0, 488(a5)
	addi t0, t0, 1
	srli t1, t0, 24
	sb t1, 484(a5)
	srli t1, t0, 16
	sb t1, 485(a5)
	srli t1, t0, 8
	sb t1, 486(a5)
	srli t1, t0, 0
	sb t1, 487(a5)
	ld s5, 480(a5)
	ld s2, 472(a5)
	ld t0, 488(a5)
	addi t0, t0, 2
	srli t1, t0, 24
	sb t1, 484(a5)
	srli t1, t0, 16
	sb t1, 485(a5)
	srli t1, t0, 8
	sb t1, 486(a5)
	srli t1, t0, 0
	sb t1, 487(a5)
	ld s6, 480(a5)
	ld s3, 472(a5)
	ld t0, 488(a5)
	addi t0, t0, 3
	srli t1, t0, 24
	sb t1, 484(a5)
	srli t1, t0, 16
	sb t1, 485(a5)
	srli t1, t0, 8
	sb t1, 486(a5)
	srli t1, t0, 0
	sb t1, 487(a5)
	ld s7, 480(a5)
	ld t0, 488(a5)
	addi t0, t0, 4
	sd t0, 488(a5)
	ld t1, 440(a5)
	srli t0, s0, 8
	xor t0, t0, s4
	and t0, t0, t1
	xor s4, s4, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s5
	and t0, t0, t1
	xor s5, s5, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s6
	and t0, t0, t1
	xor s6, s6, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s7
	and t0, t0, t1
	xor s7, s7, t0
	slli t0, t0, 8
	xor s3, s3, t0
	ld t1, 448(a5)
	srli t0, s0, 16
	xor t0, t0, s4
	and t0, t0, t1
	xor s4, s4, t0
	slli t0, t0, 16
	xor s0, s0, t0
	srli t0, s1, 16
	xor t0, t0, s5
	and t0, t0, t1
	xor s5, s5, t0
	slli t0, t0, 16
	xor s1, s1, t0
	srli t0, s2, 16
	xor t0, t0, s6
	and t0, t0, t1
	xor s6, s6, t0
	slli t0, t0, 16
	xor s2, s2, t0
	srli t0, s3, 16
	xor t0, t0, s7
	and t0, t0, t1
	xor s7, s7, t0
	slli t0, t0, 16
	xor s3, s3, t0
	ld t1, 456(a5)
	srli t0, s0, 32
	xor t0, t0, s4
	and t0, t0, t1
	xor s4, s4, t0
	slli t0, t0, 32
	xor s0, s0, t0
	srli t0, s1, 32
	xor t0, t0, s5
	and t0, t0, t1
	xor s5, s5, t0
	slli t0, t0, 32
	xor s1, s1, t0
	srli t0, s2, 32
	xor t0, t0, s6
	and t0, t0, t1
	xor s6, s6, t0
	slli t0, t0, 32
	xor s2, s2, t0
	srli t0, s3, 32
	xor t0, t0, s7
	and t0, t0, t1
	xor s7, s7, t0
	slli t0, t0, 32
	xor s3, s3, t0
	ld t1, 432(a5)
	srli t0, s0, 4
	xor t0, t0, s4
	and t0, t0, t1
	xor s4, s4, t0
	slli t0, t0, 4
	xor s0, s0, t0
	srli t0, s1, 4
	xor t0, t0, s5
	and t0, t0, t1
	xor s5, s5, t0
	slli t0, t0, 4
	xor s1, s1, t0
	srli t0, s2, 4
	xor t0, t0, s6
	and t0, t0, t1
	xor s6, s6, t0
	slli t0, t0, 4
	xor s2, s2, t0
	srli t0, s3, 4
	xor t0, t0, s7
	and t0, t0, t1
	xor s7, s7, t0
	slli t0, t0, 4
	xor s3, s3, t0
	ld t1, 424(a5)
	srli t0, s0, 2
	xor t0, t0, s2
	and t0, t0, t1
	xor s2, s2, t0
	slli t0, t0, 2
	xor s0, s0, t0
	srli t0, s1, 2
	xor t0, t0, s3
	and t0, t0, t1
	xor s3, s3, t0
	slli t0, t0, 2
	xor s1, s1, t0
	srli t0, s4, 2
	xor t0, t0, s6
	and t0, t0, t1
	xor s6, s6, t0
	slli t0, t0, 2
	xor s4, s4, t0
	srli t0, s5, 2
	xor t0, t0, s7
	and t0, t0, t1
	xor s7, s7, t0
	slli t0, t0, 2
	xor s5, s5, t0
	ld t1, 416(a5)
	srli t0, s0, 1
	xor t0, t0, s1
	and t0, t0, t1
	xor s1, s1, t0
	slli t0, t0, 1
	xor s0, s0, t0
	srli t0, s2, 1
	xor t0, t0, s3
	and t0, t0, t1
	xor s3, s3, t0
	slli t0, t0, 1
	xor s2, s2, t0
	srli t0, s4, 1
	xor t0, t0, s5
	and t0, t0, t1
	xor s5, s5, t0
	slli t0, t0, 1
	xor s4, s4, t0
	srli t0, s6, 1
	xor t0, t0, s7
	and t0, t0, t1
	xor s7, s7, t0
	slli t0, t0, 1
	xor s6, s6, t0
	addi a1, a0, 0
	ld t0, 0(a1)
	xor s0, s0, t0
	ld t0, 8(a1)
	xor s1, s1, t0
	ld t0, 16(a1)
	xor s2, s2, t0
	ld t0, 24(a1)
	xor s3, s3, t0
	ld t0, 32(a1)
	xor s4, s4, t0
	ld t0, 40(a1)
	xor s5, s5, t0
	ld t0, 48(a1)
	xor s6, s6, t0
	ld t0, 56(a1)
	xor s7, s7, t0
213:
	addi a1, a1, 64
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
	ld t3, 512(a5)
	ld t4, 520(a5)
	srli t0, s0, 8
	xor t0, t0, s0
	and t0, t0, t3
	xor s0, s0, t0
	slli t0, t0, 8
	xor s0, s0, t0
	and t0, s0, t4
	xor s0, s0, t0
	srli t1, t0, 4
	slli t0, t0, 12
	xor t0, t0, t1
	and t0, t0, t4
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s1
	and t0, t0, t3
	xor s1, s1, t0
	slli t0, t0, 8
	xor s1, s1, t0
	and t0, s1, t4
	xor s1, s1, t0
	srli t1, t0, 4
	slli t0, t0, 12
	xor t0, t0, t1
	and t0, t0, t4
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s2
	and t0, t0, t3
	xor s2, s2, t0
	slli t0, t0, 8
	xor s2, s2, t0
	and t0, s2, t4
	xor s2, s2, t0
	srli t1, t0, 4
	slli t0, t0, 12
	xor t0, t0, t1
	and t0, t0, t4
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s3
	and t0, t0, t3
	xor s3, s3, t0
	slli t0, t0, 8
	xor s3, s3, t0
	and t0, s3, t4
	xor s3, s3, t0
	srli t1, t0, 4
	slli t0, t0, 12
	xor t0, t0, t1
	and t0, t0, t4
	xor s3, s3, t0
	srli t0, s4, 8
	xor t0, t0, s4
	and t0, t0, t3
	xor s4, s4, t0
	slli t0, t0, 8
	xor s4, s4, t0
	and t0, s4, t4
	xor s4, s4, t0
	srli t1, t0, 4
	slli t0, t0, 12
	xor t0, t0, t1
	and t0, t0, t4
	xor s4, s4, t0
	srli t0, s5, 8
	xor t0, t0, s5
	and t0, t0, t3
	xor s5, s5, t0
	slli t0, t0, 8
	xor s5, s5, t0
	and t0, s5, t4
	xor s5, s5, t0
	srli t1, t0, 4
	slli t0, t0, 12
	xor t0, t0, t1
	and t0, t0, t4
	xor s5, s5, t0
	srli t0, s6, 8
	xor t0, t0, s6
	and t0, t0, t3
	xor s6, s6, t0
	slli t0, t0, 8
	xor s6, s6, t0
	and t0, s6, t4
	xor s6, s6, t0
	srli t1, t0, 4
	slli t0, t0, 12
	xor t0, t0, t1
	and t0, t0, t4
	xor s6, s6, t0
	srli t0, s7, 8
	xor t0, t0, s7
	and t0, t0, t3
	xor s7, s7, t0
	slli t0, t0, 8
	xor s7, s7, t0
	and t0, s7, t4
	xor s7, s7, t0
	srli t1, t0, 4
	slli t0, t0, 12
	xor t0, t0, t1
	and t0, t0, t4
	xor s7, s7, t0
	srli t0, s7, 16
	slli t1, s7, 48
	xor t6, t0, t1
	xor t2, s7, t6
	srli t0, s6, 16
	slli t1, s6, 48
	xor t5, t0, t1
	xor t3, s6, t5
	srli t0, t2, 32
	slli t1, t2, 32
	xor t0, t0, t1
	xor s7, t0, t6
	xor s7, s7, t3
	srli t0, s5, 16
	slli t1, s5, 48
	xor t6, t0, t1
	xor t4, s5, t6
	srli t0, t3, 32
	slli t1, t3, 32
	xor t0, t0, t1
	xor s6, t0, t5
	xor s6, s6, t4
	srli t0, s4, 16
	slli t1, s4, 48
	xor t5, t0, t1
	xor t3, s4, t5
	srli t0, t4, 32
	slli t1, t4, 32
	xor t0, t0, t1
	xor s5, t0, t6
	xor s5, s5, t3
	srli t0, s3, 16
	slli t1, s3, 48
	xor t6, t0, t1
	xor t4, s3, t6
	srli t0, t3, 32
	slli t1, t3, 32
	xor t0, t0, t1
	xor s4, t0, t5
	xor s4, s4, t4
	xor s4, s4, t2
	srli t0, s2, 16
	slli t1, s2, 48
	xor t5, t0, t1
	xor t3, s2, t5
	srli t0, t4, 32
	slli t1, t4, 32
	xor t0, t0, t1
	xor s3, t0, t6
	xor s3, s3, t3
	xor s3, s3, t2
	srli t0, s1, 16
	slli t1, s1, 48
	xor t6, t0, t1
	xor t4, s1, t6
	srli t0, t3, 32
	slli t1, t3, 32
	xor t0, t0, t1
	xor s2, t0, t5
	xor s2, s2, t4
	srli t0, s0, 16
	slli t1, s0, 48
	xor t5, t0, t1
	xor t3, s0, t5
	srli t0, t4, 32
	slli t1, t4, 32
	xor t0, t0, t1
	xor s1, t0, t6
	xor s1, s1, t3
	xor s1, s1, t2
	srli t0, t3, 32
	slli t1, t3, 32
	xor t0, t0, t1
	xor s0, t0, t5
	xor s0, s0, t2
	ld t0, 0(a1)
	xor s0, s0, t0
	ld t0, 8(a1)
	xor s1, s1, t0
	ld t0, 16(a1)
	xor s2, s2, t0
	ld t0, 24(a1)
	xor s3, s3, t0
	ld t0, 32(a1)
	xor s4, s4, t0
	ld t0, 40(a1)
	xor s5, s5, t0
	ld t0, 48(a1)
	xor s6, s6, t0
	ld t0, 56(a1)
	xor s7, s7, t0
	sub t0, a1, ra
	addi t0, t0, -1856
	bnez t0, 213b
	addi a1, a1, 64
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
	ld t3, 512(a5)
	ld t4, 520(a5)
	srli t0, s0, 8
	xor t0, t0, s0
	and t0, t0, t3
	xor s0, s0, t0
	slli t0, t0, 8
	xor s0, s0, t0
	and t0, s0, t4
	xor s0, s0, t0
	srli t1, t0, 4
	slli t0, t0, 12
	xor t0, t0, t1
	and t0, t0, t4
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s1
	and t0, t0, t3
	xor s1, s1, t0
	slli t0, t0, 8
	xor s1, s1, t0
	and t0, s1, t4
	xor s1, s1, t0
	srli t1, t0, 4
	slli t0, t0, 12
	xor t0, t0, t1
	and t0, t0, t4
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s2
	and t0, t0, t3
	xor s2, s2, t0
	slli t0, t0, 8
	xor s2, s2, t0
	and t0, s2, t4
	xor s2, s2, t0
	srli t1, t0, 4
	slli t0, t0, 12
	xor t0, t0, t1
	and t0, t0, t4
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s3
	and t0, t0, t3
	xor s3, s3, t0
	slli t0, t0, 8
	xor s3, s3, t0
	and t0, s3, t4
	xor s3, s3, t0
	srli t1, t0, 4
	slli t0, t0, 12
	xor t0, t0, t1
	and t0, t0, t4
	xor s3, s3, t0
	srli t0, s4, 8
	xor t0, t0, s4
	and t0, t0, t3
	xor s4, s4, t0
	slli t0, t0, 8
	xor s4, s4, t0
	and t0, s4, t4
	xor s4, s4, t0
	srli t1, t0, 4
	slli t0, t0, 12
	xor t0, t0, t1
	and t0, t0, t4
	xor s4, s4, t0
	srli t0, s5, 8
	xor t0, t0, s5
	and t0, t0, t3
	xor s5, s5, t0
	slli t0, t0, 8
	xor s5, s5, t0
	and t0, s5, t4
	xor s5, s5, t0
	srli t1, t0, 4
	slli t0, t0, 12
	xor t0, t0, t1
	and t0, t0, t4
	xor s5, s5, t0
	srli t0, s6, 8
	xor t0, t0, s6
	and t0, t0, t3
	xor s6, s6, t0
	slli t0, t0, 8
	xor s6, s6, t0
	and t0, s6, t4
	xor s6, s6, t0
	srli t1, t0, 4
	slli t0, t0, 12
	xor t0, t0, t1
	and t0, t0, t4
	xor s6, s6, t0
	srli t0, s7, 8
	xor t0, t0, s7
	and t0, t0, t3
	xor s7, s7, t0
	slli t0, t0, 8
	xor s7, s7, t0
	and t0, s7, t4
	xor s7, s7, t0
	srli t1, t0, 4
	slli t0, t0, 12
	xor t0, t0, t1
	and t0, t0, t4
	xor s7, s7, t0
	ld t0, 0(a1)
	xor s0, s0, t0
	ld t0, 8(a1)
	xor s1, s1, t0
	ld t0, 16(a1)
	xor s2, s2, t0
	ld t0, 24(a1)
	xor s3, s3, t0
	ld t0, 32(a1)
	xor s4, s4, t0
	ld t0, 40(a1)
	xor s5, s5, t0
	ld t0, 48(a1)
	xor s6, s6, t0
	ld t0, 56(a1)
	xor s7, s7, t0
	ld t1, 416(a5)
	srli t0, s0, 1
	xor t0, t0, s1
	and t0, t0, t1
	xor s1, s1, t0
	slli t0, t0, 1
	xor s0, s0, t0
	srli t0, s2, 1
	xor t0, t0, s3
	and t0, t0, t1
	xor s3, s3, t0
	slli t0, t0, 1
	xor s2, s2, t0
	srli t0, s4, 1
	xor t0, t0, s5
	and t0, t0, t1
	xor s5, s5, t0
	slli t0, t0, 1
	xor s4, s4, t0
	srli t0, s6, 1
	xor t0, t0, s7
	and t0, t0, t1
	xor s7, s7, t0
	slli t0, t0, 1
	xor s6, s6, t0
	ld t1, 424(a5)
	srli t0, s0, 2
	xor t0, t0, s2
	and t0, t0, t1
	xor s2, s2, t0
	slli t0, t0, 2
	xor s0, s0, t0
	srli t0, s1, 2
	xor t0, t0, s3
	and t0, t0, t1
	xor s3, s3, t0
	slli t0, t0, 2
	xor s1, s1, t0
	srli t0, s4, 2
	xor t0, t0, s6
	and t0, t0, t1
	xor s6, s6, t0
	slli t0, t0, 2
	xor s4, s4, t0
	srli t0, s5, 2
	xor t0, t0, s7
	and t0, t0, t1
	xor s7, s7, t0
	slli t0, t0, 2
	xor s5, s5, t0
	ld t1, 432(a5)
	srli t0, s0, 4
	xor t0, t0, s4
	and t0, t0, t1
	xor s4, s4, t0
	slli t0, t0, 4
	xor s0, s0, t0
	srli t0, s1, 4
	xor t0, t0, s5
	and t0, t0, t1
	xor s5, s5, t0
	slli t0, t0, 4
	xor s1, s1, t0
	srli t0, s2, 4
	xor t0, t0, s6
	and t0, t0, t1
	xor s6, s6, t0
	slli t0, t0, 4
	xor s2, s2, t0
	srli t0, s3, 4
	xor t0, t0, s7
	and t0, t0, t1
	xor s7, s7, t0
	slli t0, t0, 4
	xor s3, s3, t0
	ld t1, 456(a5)
	srli t0, s0, 32
	xor t0, t0, s4
	and t0, t0, t1
	xor s4, s4, t0
	slli t0, t0, 32
	xor s0, s0, t0
	srli t0, s1, 32
	xor t0, t0, s5
	and t0, t0, t1
	xor s5, s5, t0
	slli t0, t0, 32
	xor s1, s1, t0
	srli t0, s2, 32
	xor t0, t0, s6
	and t0, t0, t1
	xor s6, s6, t0
	slli t0, t0, 32
	xor s2, s2, t0
	srli t0, s3, 32
	xor t0, t0, s7
	and t0, t0, t1
	xor s7, s7, t0
	slli t0, t0, 32
	xor s3, s3, t0
	ld t1, 448(a5)
	srli t0, s0, 16
	xor t0, t0, s4
	and t0, t0, t1
	xor s4, s4, t0
	slli t0, t0, 16
	xor s0, s0, t0
	srli t0, s1, 16
	xor t0, t0, s5
	and t0, t0, t1
	xor s5, s5, t0
	slli t0, t0, 16
	xor s1, s1, t0
	srli t0, s2, 16
	xor t0, t0, s6
	and t0, t0, t1
	xor s6, s6, t0
	slli t0, t0, 16
	xor s2, s2, t0
	srli t0, s3, 16
	xor t0, t0, s7
	and t0, t0, t1
	xor s7, s7, t0
	slli t0, t0, 16
	xor s3, s3, t0
	ld t1, 440(a5)
	srli t0, s0, 8
	xor t0, t0, s4
	and t0, t0, t1
	xor s4, s4, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s5
	and t0, t0, t1
	xor s5, s5, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s6
	and t0, t0, t1
	xor s6, s6, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s7
	and t0, t0, t1
	xor s7, s7, t0
	slli t0, t0, 8
	xor s3, s3, t0
	srli t0, a4, 2
	bnez t0, 214f
	ld t0, 0(a3)
	xor t0, t0, s0
	sd t0, 0(a3)
	ld t0, 8(a3)
	xor t0, t0, s4
	sd t0, 8(a3)
	addi t0, a4, -1
	bnez t0, 216f
	j 217f
216:
	ld t0, 16(a3)
	xor t0, t0, s1
	sd t0, 16(a3)
	ld t0, 24(a3)
	xor t0, t0, s5
	sd t0, 24(a3)
	addi t0, a4, -3
	beqz t0, 218f
	j 219f
218:
	ld t0, 32(a3)
	xor t0, t0, s2
	sd t0, 32(a3)
	ld t0, 40(a3)
	xor t0, t0, s6
	sd t0, 40(a3)
219:
217:
	addi a4, zero, 0
	j 215f
214:
	ld t0, 0(a3)
	xor t0, t0, s0
	sd t0, 0(a3)
	ld t0, 8(a3)
	xor t0, t0, s4
	sd t0, 8(a3)
	ld t0, 16(a3)
	xor t0, t0, s1
	sd t0, 16(a3)
	ld t0, 24(a3)
	xor t0, t0, s5
	sd t0, 24(a3)
	ld t0, 32(a3)
	xor t0, t0, s2
	sd t0, 32(a3)
	ld t0, 40(a3)
	xor t0, t0, s6
	sd t0, 40(a3)
	ld t0, 48(a3)
	xor t0, t0, s3
	sd t0, 48(a3)
	ld t0, 56(a3)
	xor t0, t0, s7
	sd t0, 56(a3)
	addi a3, a3, 64
	addi a4, a4, -4
215:
	bnez a4, 212b
23:
	j 21f
20:
21:
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
	ld ra, 496(a5)
	ret
	.option pop
