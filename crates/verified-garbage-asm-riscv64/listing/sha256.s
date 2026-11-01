// The functions of `src/sha256.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha224_init:
	.option push
	.option arch, +m, +c
	lui t0, 790618
	addiw t0, t0, -296
	sb t0, 0(a0)
	srli t1, t0, 8
	sb t1, 1(a0)
	srli t1, t0, 16
	sb t1, 2(a0)
	srli t1, t0, 24
	sb t1, 3(a0)
	lui t0, 223181
	addiw t0, t0, 1287
	sb t0, 4(a0)
	srli t1, t0, 8
	sb t1, 5(a0)
	srli t1, t0, 16
	sb t1, 6(a0)
	srli t1, t0, 24
	sb t1, 7(a0)
	lui t0, 198414
	addiw t0, t0, -745
	sb t0, 8(a0)
	srli t1, t0, 8
	sb t1, 9(a0)
	srli t1, t0, 16
	sb t1, 10(a0)
	srli t1, t0, 24
	sb t1, 11(a0)
	lui t0, 1011942
	addiw t0, t0, -1735
	sb t0, 12(a0)
	srli t1, t0, 8
	sb t1, 13(a0)
	srli t1, t0, 16
	sb t1, 14(a0)
	srli t1, t0, 24
	sb t1, 15(a0)
	lui t0, 1047553
	addiw t0, t0, -1231
	sb t0, 16(a0)
	srli t1, t0, 8
	sb t1, 17(a0)
	srli t1, t0, 16
	sb t1, 18(a0)
	srli t1, t0, 24
	sb t1, 19(a0)
	lui t0, 427393
	addiw t0, t0, 1297
	sb t0, 20(a0)
	srli t1, t0, 8
	sb t1, 21(a0)
	srli t1, t0, 16
	sb t1, 22(a0)
	srli t1, t0, 24
	sb t1, 23(a0)
	lui t0, 413593
	addiw t0, t0, -89
	sb t0, 24(a0)
	srli t1, t0, 8
	sb t1, 25(a0)
	srli t1, t0, 16
	sb t1, 26(a0)
	srli t1, t0, 24
	sb t1, 27(a0)
	lui t0, 782245
	addiw t0, t0, -92
	sb t0, 28(a0)
	srli t1, t0, 8
	sb t1, 29(a0)
	srli t1, t0, 16
	sb t1, 30(a0)
	srli t1, t0, 24
	sb t1, 31(a0)
	ret
	.option pop

vg_sha224_finalize:
	.option push
	.option arch, +m, +c
	addi sp, sp, -144
	addi t0, sp, 0
	sd ra, 80(t0)
	sd s1, 88(t0)
	sd s2, 96(t0)
	sd s3, 104(t0)
	sd s4, 112(t0)
	sd s5, 120(t0)
	sd s6, 128(t0)
	addi s1, a0, 0
	addi s2, t0, 0
	addi s3, a2, 0
	addi s4, a1, 0
	andi s5, s4, 63
	addi t1, zero, 128
	add t3, s1, s5
	sb t1, 32(t3)
	addi s5, s5, 1
	addi s6, s5, 7
	srli s6, s6, 6
20:
	addi t2, zero, 64
	beqz s6, 21f
	j 22f
21:
	addi t2, zero, 56
22:
	addi t1, zero, 0
	sub t2, t2, s5
	beqz t2, 23f
25:
	add t3, s1, s5
	sb t1, 32(t3)
	addi s5, s5, 1
	addi t2, t2, -1
	bnez t2, 25b
	j 24f
23:
24:
	beqz s6, 26f
	j 27f
26:
	slli t1, s4, 3
	srli t3, t1, 56
	sb t3, 88(s1)
	srli t3, t1, 48
	sb t3, 89(s1)
	srli t3, t1, 40
	sb t3, 90(s1)
	srli t3, t1, 32
	sb t3, 91(s1)
	srli t3, t1, 24
	sb t3, 92(s1)
	srli t3, t1, 16
	sb t3, 93(s1)
	srli t3, t1, 8
	sb t3, 94(s1)
	srli t3, t1, 0
	sb t3, 95(s1)
27:
	addi a1, s1, 32
	addi a0, s1, 0
	addi a2, zero, 1
	addi a3, s2, 0
	call {vg_sha256_compress}
	addi s5, zero, 0
	addi s6, s6, -1
	beqz s6, 20b
	lbu t1, 0(s1)
	lbu t2, 1(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 2(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 3(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 0(s3)
	srli t2, t1, 16
	sb t2, 1(s3)
	srli t2, t1, 8
	sb t2, 2(s3)
	srli t2, t1, 0
	sb t2, 3(s3)
	lbu t1, 4(s1)
	lbu t2, 5(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 6(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 7(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 4(s3)
	srli t2, t1, 16
	sb t2, 5(s3)
	srli t2, t1, 8
	sb t2, 6(s3)
	srli t2, t1, 0
	sb t2, 7(s3)
	lbu t1, 8(s1)
	lbu t2, 9(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 10(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 11(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 8(s3)
	srli t2, t1, 16
	sb t2, 9(s3)
	srli t2, t1, 8
	sb t2, 10(s3)
	srli t2, t1, 0
	sb t2, 11(s3)
	lbu t1, 12(s1)
	lbu t2, 13(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 14(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 15(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 12(s3)
	srli t2, t1, 16
	sb t2, 13(s3)
	srli t2, t1, 8
	sb t2, 14(s3)
	srli t2, t1, 0
	sb t2, 15(s3)
	lbu t1, 16(s1)
	lbu t2, 17(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 18(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 19(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 16(s3)
	srli t2, t1, 16
	sb t2, 17(s3)
	srli t2, t1, 8
	sb t2, 18(s3)
	srli t2, t1, 0
	sb t2, 19(s3)
	lbu t1, 20(s1)
	lbu t2, 21(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 22(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 23(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 20(s3)
	srli t2, t1, 16
	sb t2, 21(s3)
	srli t2, t1, 8
	sb t2, 22(s3)
	srli t2, t1, 0
	sb t2, 23(s3)
	lbu t1, 24(s1)
	lbu t2, 25(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 26(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 27(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 24(s3)
	srli t2, t1, 16
	sb t2, 25(s3)
	srli t2, t1, 8
	sb t2, 26(s3)
	srli t2, t1, 0
	sb t2, 27(s3)
	ld ra, 80(s2)
	ld s1, 88(s2)
	ld s3, 104(s2)
	ld s4, 112(s2)
	ld s5, 120(s2)
	ld s6, 128(s2)
	ld s2, 96(s2)
	addi sp, sp, 144
	ret
	.option pop

vg_sha256_compress:
	.option push
	.option arch, +m, +c
	addi a3, a3, 7
	andi a3, a3, -8
	sd s0, 64(a3)
	beqz a2, 20f
22:
	lbu t0, 0(a0)
	lbu a5, 1(a0)
	slli a5, a5, 8
	or t0, t0, a5
	lbu a5, 2(a0)
	slli a5, a5, 16
	or t0, t0, a5
	lbu a5, 3(a0)
	slli a5, a5, 24
	or t0, t0, a5
	lbu t1, 4(a0)
	lbu a5, 5(a0)
	slli a5, a5, 8
	or t1, t1, a5
	lbu a5, 6(a0)
	slli a5, a5, 16
	or t1, t1, a5
	lbu a5, 7(a0)
	slli a5, a5, 24
	or t1, t1, a5
	lbu t2, 8(a0)
	lbu a5, 9(a0)
	slli a5, a5, 8
	or t2, t2, a5
	lbu a5, 10(a0)
	slli a5, a5, 16
	or t2, t2, a5
	lbu a5, 11(a0)
	slli a5, a5, 24
	or t2, t2, a5
	lbu t3, 12(a0)
	lbu a5, 13(a0)
	slli a5, a5, 8
	or t3, t3, a5
	lbu a5, 14(a0)
	slli a5, a5, 16
	or t3, t3, a5
	lbu a5, 15(a0)
	slli a5, a5, 24
	or t3, t3, a5
	lbu t4, 16(a0)
	lbu a5, 17(a0)
	slli a5, a5, 8
	or t4, t4, a5
	lbu a5, 18(a0)
	slli a5, a5, 16
	or t4, t4, a5
	lbu a5, 19(a0)
	slli a5, a5, 24
	or t4, t4, a5
	lbu t5, 20(a0)
	lbu a5, 21(a0)
	slli a5, a5, 8
	or t5, t5, a5
	lbu a5, 22(a0)
	slli a5, a5, 16
	or t5, t5, a5
	lbu a5, 23(a0)
	slli a5, a5, 24
	or t5, t5, a5
	lbu t6, 24(a0)
	lbu a5, 25(a0)
	slli a5, a5, 8
	or t6, t6, a5
	lbu a5, 26(a0)
	slli a5, a5, 16
	or t6, t6, a5
	lbu a5, 27(a0)
	slli a5, a5, 24
	or t6, t6, a5
	lbu a4, 28(a0)
	lbu a5, 29(a0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 30(a0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 31(a0)
	slli a5, a5, 24
	or a4, a4, a5
	lbu a5, 0(a1)
	slli a5, a5, 24
	lbu a6, 1(a1)
	slli a6, a6, 16
	or a5, a5, a6
	lbu a6, 2(a1)
	slli a6, a6, 8
	or a5, a5, a6
	lbu a6, 3(a1)
	or a5, a5, a6
	sw a5, 0(a3)
	srliw a6, t4, 6
	slliw a7, t4, 26
	xor a6, a6, a7
	srliw a7, t4, 11
	xor a6, a6, a7
	slliw a7, t4, 21
	xor a6, a6, a7
	srliw a7, t4, 25
	xor a6, a6, a7
	slliw a7, t4, 7
	xor a6, a6, a7
	add a4, a4, a6
	xor a6, t5, t6
	and a6, a6, t4
	xor a6, a6, t6
	add a4, a4, a6
	lui a6, 272547
	addiw a6, a6, -104
	add a4, a4, a6
	add a4, a4, a5
	add t3, t3, a4
	srliw a6, t0, 2
	slliw a7, t0, 30
	xor a6, a6, a7
	srliw a7, t0, 13
	xor a6, a6, a7
	slliw a7, t0, 19
	xor a6, a6, a7
	srliw a7, t0, 22
	xor a6, a6, a7
	slliw a7, t0, 10
	xor a6, a6, a7
	add a4, a4, a6
	or a6, t0, t1
	and a6, a6, t2
	and a7, t0, t1
	or a6, a6, a7
	add a4, a4, a6
	lbu a5, 4(a1)
	slli a5, a5, 24
	lbu a6, 5(a1)
	slli a6, a6, 16
	or a5, a5, a6
	lbu a6, 6(a1)
	slli a6, a6, 8
	or a5, a5, a6
	lbu a6, 7(a1)
	or a5, a5, a6
	sw a5, 4(a3)
	srliw a6, t3, 6
	slliw a7, t3, 26
	xor a6, a6, a7
	srliw a7, t3, 11
	xor a6, a6, a7
	slliw a7, t3, 21
	xor a6, a6, a7
	srliw a7, t3, 25
	xor a6, a6, a7
	slliw a7, t3, 7
	xor a6, a6, a7
	add t6, t6, a6
	xor a6, t4, t5
	and a6, a6, t3
	xor a6, a6, t5
	add t6, t6, a6
	lui a6, 463732
	addiw a6, a6, 1169
	add t6, t6, a6
	add t6, t6, a5
	add t2, t2, t6
	srliw a6, a4, 2
	slliw a7, a4, 30
	xor a6, a6, a7
	srliw a7, a4, 13
	xor a6, a6, a7
	slliw a7, a4, 19
	xor a6, a6, a7
	srliw a7, a4, 22
	xor a6, a6, a7
	slliw a7, a4, 10
	xor a6, a6, a7
	add t6, t6, a6
	or a6, a4, t0
	and a6, a6, t1
	and a7, a4, t0
	or a6, a6, a7
	add t6, t6, a6
	lbu a5, 8(a1)
	slli a5, a5, 24
	lbu a6, 9(a1)
	slli a6, a6, 16
	or a5, a5, a6
	lbu a6, 10(a1)
	slli a6, a6, 8
	or a5, a5, a6
	lbu a6, 11(a1)
	or a5, a5, a6
	sw a5, 8(a3)
	srliw a6, t2, 6
	slliw a7, t2, 26
	xor a6, a6, a7
	srliw a7, t2, 11
	xor a6, a6, a7
	slliw a7, t2, 21
	xor a6, a6, a7
	srliw a7, t2, 25
	xor a6, a6, a7
	slliw a7, t2, 7
	xor a6, a6, a7
	add t5, t5, a6
	xor a6, t3, t4
	and a6, a6, t2
	xor a6, a6, t4
	add t5, t5, a6
	lui a6, 744464
	addiw a6, a6, -1073
	add t5, t5, a6
	add t5, t5, a5
	add t1, t1, t5
	srliw a6, t6, 2
	slliw a7, t6, 30
	xor a6, a6, a7
	srliw a7, t6, 13
	xor a6, a6, a7
	slliw a7, t6, 19
	xor a6, a6, a7
	srliw a7, t6, 22
	xor a6, a6, a7
	slliw a7, t6, 10
	xor a6, a6, a7
	add t5, t5, a6
	or a6, t6, a4
	and a6, a6, t0
	and a7, t6, a4
	or a6, a6, a7
	add t5, t5, a6
	lbu a5, 12(a1)
	slli a5, a5, 24
	lbu a6, 13(a1)
	slli a6, a6, 16
	or a5, a5, a6
	lbu a6, 14(a1)
	slli a6, a6, 8
	or a5, a5, a6
	lbu a6, 15(a1)
	or a5, a5, a6
	sw a5, 12(a3)
	srliw a6, t1, 6
	slliw a7, t1, 26
	xor a6, a6, a7
	srliw a7, t1, 11
	xor a6, a6, a7
	slliw a7, t1, 21
	xor a6, a6, a7
	srliw a7, t1, 25
	xor a6, a6, a7
	slliw a7, t1, 7
	xor a6, a6, a7
	add t4, t4, a6
	xor a6, t2, t3
	and a6, a6, t1
	xor a6, a6, t3
	add t4, t4, a6
	lui a6, 957278
	addiw a6, a6, -1115
	add t4, t4, a6
	add t4, t4, a5
	add t0, t0, t4
	srliw a6, t5, 2
	slliw a7, t5, 30
	xor a6, a6, a7
	srliw a7, t5, 13
	xor a6, a6, a7
	slliw a7, t5, 19
	xor a6, a6, a7
	srliw a7, t5, 22
	xor a6, a6, a7
	slliw a7, t5, 10
	xor a6, a6, a7
	add t4, t4, a6
	or a6, t5, t6
	and a6, a6, a4
	and a7, t5, t6
	or a6, a6, a7
	add t4, t4, a6
	lbu a5, 16(a1)
	slli a5, a5, 24
	lbu a6, 17(a1)
	slli a6, a6, 16
	or a5, a5, a6
	lbu a6, 18(a1)
	slli a6, a6, 8
	or a5, a5, a6
	lbu a6, 19(a1)
	or a5, a5, a6
	sw a5, 16(a3)
	srliw a6, t0, 6
	slliw a7, t0, 26
	xor a6, a6, a7
	srliw a7, t0, 11
	xor a6, a6, a7
	slliw a7, t0, 21
	xor a6, a6, a7
	srliw a7, t0, 25
	xor a6, a6, a7
	slliw a7, t0, 7
	xor a6, a6, a7
	add t3, t3, a6
	xor a6, t1, t2
	and a6, a6, t0
	xor a6, a6, t2
	add t3, t3, a6
	lui a6, 234860
	addiw a6, a6, 603
	add t3, t3, a6
	add t3, t3, a5
	add a4, a4, t3
	srliw a6, t4, 2
	slliw a7, t4, 30
	xor a6, a6, a7
	srliw a7, t4, 13
	xor a6, a6, a7
	slliw a7, t4, 19
	xor a6, a6, a7
	srliw a7, t4, 22
	xor a6, a6, a7
	slliw a7, t4, 10
	xor a6, a6, a7
	add t3, t3, a6
	or a6, t4, t5
	and a6, a6, t6
	and a7, t4, t5
	or a6, a6, a7
	add t3, t3, a6
	lbu a5, 20(a1)
	slli a5, a5, 24
	lbu a6, 21(a1)
	slli a6, a6, 16
	or a5, a5, a6
	lbu a6, 22(a1)
	slli a6, a6, 8
	or a5, a5, a6
	lbu a6, 23(a1)
	or a5, a5, a6
	sw a5, 20(a3)
	srliw a6, a4, 6
	slliw a7, a4, 26
	xor a6, a6, a7
	srliw a7, a4, 11
	xor a6, a6, a7
	slliw a7, a4, 21
	xor a6, a6, a7
	srliw a7, a4, 25
	xor a6, a6, a7
	slliw a7, a4, 7
	xor a6, a6, a7
	add t2, t2, a6
	xor a6, t0, t1
	and a6, a6, a4
	xor a6, a6, t1
	add t2, t2, a6
	lui a6, 368401
	addiw a6, a6, 497
	add t2, t2, a6
	add t2, t2, a5
	add t6, t6, t2
	srliw a6, t3, 2
	slliw a7, t3, 30
	xor a6, a6, a7
	srliw a7, t3, 13
	xor a6, a6, a7
	slliw a7, t3, 19
	xor a6, a6, a7
	srliw a7, t3, 22
	xor a6, a6, a7
	slliw a7, t3, 10
	xor a6, a6, a7
	add t2, t2, a6
	or a6, t3, t4
	and a6, a6, t5
	and a7, t3, t4
	or a6, a6, a7
	add t2, t2, a6
	lbu a5, 24(a1)
	slli a5, a5, 24
	lbu a6, 25(a1)
	slli a6, a6, 16
	or a5, a5, a6
	lbu a6, 26(a1)
	slli a6, a6, 8
	or a5, a5, a6
	lbu a6, 27(a1)
	or a5, a5, a6
	sw a5, 24(a3)
	srliw a6, t6, 6
	slliw a7, t6, 26
	xor a6, a6, a7
	srliw a7, t6, 11
	xor a6, a6, a7
	slliw a7, t6, 21
	xor a6, a6, a7
	srliw a7, t6, 25
	xor a6, a6, a7
	slliw a7, t6, 7
	xor a6, a6, a7
	add t1, t1, a6
	xor a6, a4, t0
	and a6, a6, t6
	xor a6, a6, t0
	add t1, t1, a6
	lui a6, 599032
	addiw a6, a6, 676
	add t1, t1, a6
	add t1, t1, a5
	add t5, t5, t1
	srliw a6, t2, 2
	slliw a7, t2, 30
	xor a6, a6, a7
	srliw a7, t2, 13
	xor a6, a6, a7
	slliw a7, t2, 19
	xor a6, a6, a7
	srliw a7, t2, 22
	xor a6, a6, a7
	slliw a7, t2, 10
	xor a6, a6, a7
	add t1, t1, a6
	or a6, t2, t3
	and a6, a6, t4
	and a7, t2, t3
	or a6, a6, a7
	add t1, t1, a6
	lbu a5, 28(a1)
	slli a5, a5, 24
	lbu a6, 29(a1)
	slli a6, a6, 16
	or a5, a5, a6
	lbu a6, 30(a1)
	slli a6, a6, 8
	or a5, a5, a6
	lbu a6, 31(a1)
	or a5, a5, a6
	sw a5, 28(a3)
	srliw a6, t5, 6
	slliw a7, t5, 26
	xor a6, a6, a7
	srliw a7, t5, 11
	xor a6, a6, a7
	slliw a7, t5, 21
	xor a6, a6, a7
	srliw a7, t5, 25
	xor a6, a6, a7
	slliw a7, t5, 7
	xor a6, a6, a7
	add t0, t0, a6
	xor a6, t6, a4
	and a6, a6, t5
	xor a6, a6, a4
	add t0, t0, a6
	lui a6, 700870
	addiw a6, a6, -299
	add t0, t0, a6
	add t0, t0, a5
	add t4, t4, t0
	srliw a6, t1, 2
	slliw a7, t1, 30
	xor a6, a6, a7
	srliw a7, t1, 13
	xor a6, a6, a7
	slliw a7, t1, 19
	xor a6, a6, a7
	srliw a7, t1, 22
	xor a6, a6, a7
	slliw a7, t1, 10
	xor a6, a6, a7
	add t0, t0, a6
	or a6, t1, t2
	and a6, a6, t3
	and a7, t1, t2
	or a6, a6, a7
	add t0, t0, a6
	lbu a5, 32(a1)
	slli a5, a5, 24
	lbu a6, 33(a1)
	slli a6, a6, 16
	or a5, a5, a6
	lbu a6, 34(a1)
	slli a6, a6, 8
	or a5, a5, a6
	lbu a6, 35(a1)
	or a5, a5, a6
	sw a5, 32(a3)
	srliw a6, t4, 6
	slliw a7, t4, 26
	xor a6, a6, a7
	srliw a7, t4, 11
	xor a6, a6, a7
	slliw a7, t4, 21
	xor a6, a6, a7
	srliw a7, t4, 25
	xor a6, a6, a7
	slliw a7, t4, 7
	xor a6, a6, a7
	add a4, a4, a6
	xor a6, t5, t6
	and a6, a6, t4
	xor a6, a6, t6
	add a4, a4, a6
	lui a6, 884859
	addiw a6, a6, -1384
	add a4, a4, a6
	add a4, a4, a5
	add t3, t3, a4
	srliw a6, t0, 2
	slliw a7, t0, 30
	xor a6, a6, a7
	srliw a7, t0, 13
	xor a6, a6, a7
	slliw a7, t0, 19
	xor a6, a6, a7
	srliw a7, t0, 22
	xor a6, a6, a7
	slliw a7, t0, 10
	xor a6, a6, a7
	add a4, a4, a6
	or a6, t0, t1
	and a6, a6, t2
	and a7, t0, t1
	or a6, a6, a7
	add a4, a4, a6
	lbu a5, 36(a1)
	slli a5, a5, 24
	lbu a6, 37(a1)
	slli a6, a6, 16
	or a5, a5, a6
	lbu a6, 38(a1)
	slli a6, a6, 8
	or a5, a5, a6
	lbu a6, 39(a1)
	or a5, a5, a6
	sw a5, 36(a3)
	srliw a6, t3, 6
	slliw a7, t3, 26
	xor a6, a6, a7
	srliw a7, t3, 11
	xor a6, a6, a7
	slliw a7, t3, 21
	xor a6, a6, a7
	srliw a7, t3, 25
	xor a6, a6, a7
	slliw a7, t3, 7
	xor a6, a6, a7
	add t6, t6, a6
	xor a6, t4, t5
	and a6, a6, t3
	xor a6, a6, t5
	add t6, t6, a6
	lui a6, 75830
	addiw a6, a6, -1279
	add t6, t6, a6
	add t6, t6, a5
	add t2, t2, t6
	srliw a6, a4, 2
	slliw a7, a4, 30
	xor a6, a6, a7
	srliw a7, a4, 13
	xor a6, a6, a7
	slliw a7, a4, 19
	xor a6, a6, a7
	srliw a7, a4, 22
	xor a6, a6, a7
	slliw a7, a4, 10
	xor a6, a6, a7
	add t6, t6, a6
	or a6, a4, t0
	and a6, a6, t1
	and a7, a4, t0
	or a6, a6, a7
	add t6, t6, a6
	lbu a5, 40(a1)
	slli a5, a5, 24
	lbu a6, 41(a1)
	slli a6, a6, 16
	or a5, a5, a6
	lbu a6, 42(a1)
	slli a6, a6, 8
	or a5, a5, a6
	lbu a6, 43(a1)
	or a5, a5, a6
	sw a5, 40(a3)
	srliw a6, t2, 6
	slliw a7, t2, 26
	xor a6, a6, a7
	srliw a7, t2, 11
	xor a6, a6, a7
	slliw a7, t2, 21
	xor a6, a6, a7
	srliw a7, t2, 25
	xor a6, a6, a7
	slliw a7, t2, 7
	xor a6, a6, a7
	add t5, t5, a6
	xor a6, t3, t4
	and a6, a6, t2
	xor a6, a6, t4
	add t5, t5, a6
	lui a6, 148248
	addiw a6, a6, 1470
	add t5, t5, a6
	add t5, t5, a5
	add t1, t1, t5
	srliw a6, t6, 2
	slliw a7, t6, 30
	xor a6, a6, a7
	srliw a7, t6, 13
	xor a6, a6, a7
	slliw a7, t6, 19
	xor a6, a6, a7
	srliw a7, t6, 22
	xor a6, a6, a7
	slliw a7, t6, 10
	xor a6, a6, a7
	add t5, t5, a6
	or a6, t6, a4
	and a6, a6, t0
	and a7, t6, a4
	or a6, a6, a7
	add t5, t5, a6
	lbu a5, 44(a1)
	slli a5, a5, 24
	lbu a6, 45(a1)
	slli a6, a6, 16
	or a5, a5, a6
	lbu a6, 46(a1)
	slli a6, a6, 8
	or a5, a5, a6
	lbu a6, 47(a1)
	or a5, a5, a6
	sw a5, 44(a3)
	srliw a6, t1, 6
	slliw a7, t1, 26
	xor a6, a6, a7
	srliw a7, t1, 11
	xor a6, a6, a7
	slliw a7, t1, 21
	xor a6, a6, a7
	srliw a7, t1, 25
	xor a6, a6, a7
	slliw a7, t1, 7
	xor a6, a6, a7
	add t4, t4, a6
	xor a6, t2, t3
	and a6, a6, t1
	xor a6, a6, t3
	add t4, t4, a6
	lui a6, 348360
	addiw a6, a6, -573
	add t4, t4, a6
	add t4, t4, a5
	add t0, t0, t4
	srliw a6, t5, 2
	slliw a7, t5, 30
	xor a6, a6, a7
	srliw a7, t5, 13
	xor a6, a6, a7
	slliw a7, t5, 19
	xor a6, a6, a7
	srliw a7, t5, 22
	xor a6, a6, a7
	slliw a7, t5, 10
	xor a6, a6, a7
	add t4, t4, a6
	or a6, t5, t6
	and a6, a6, a4
	and a7, t5, t6
	or a6, a6, a7
	add t4, t4, a6
	lbu a5, 48(a1)
	slli a5, a5, 24
	lbu a6, 49(a1)
	slli a6, a6, 16
	or a5, a5, a6
	lbu a6, 50(a1)
	slli a6, a6, 8
	or a5, a5, a6
	lbu a6, 51(a1)
	or a5, a5, a6
	sw a5, 48(a3)
	srliw a6, t0, 6
	slliw a7, t0, 26
	xor a6, a6, a7
	srliw a7, t0, 11
	xor a6, a6, a7
	slliw a7, t0, 21
	xor a6, a6, a7
	srliw a7, t0, 25
	xor a6, a6, a7
	slliw a7, t0, 7
	xor a6, a6, a7
	add t3, t3, a6
	xor a6, t1, t2
	and a6, a6, t0
	xor a6, a6, t2
	add t3, t3, a6
	lui a6, 469990
	addiw a6, a6, -652
	add t3, t3, a6
	add t3, t3, a5
	add a4, a4, t3
	srliw a6, t4, 2
	slliw a7, t4, 30
	xor a6, a6, a7
	srliw a7, t4, 13
	xor a6, a6, a7
	slliw a7, t4, 19
	xor a6, a6, a7
	srliw a7, t4, 22
	xor a6, a6, a7
	slliw a7, t4, 10
	xor a6, a6, a7
	add t3, t3, a6
	or a6, t4, t5
	and a6, a6, t6
	and a7, t4, t5
	or a6, a6, a7
	add t3, t3, a6
	lbu a5, 52(a1)
	slli a5, a5, 24
	lbu a6, 53(a1)
	slli a6, a6, 16
	or a5, a5, a6
	lbu a6, 54(a1)
	slli a6, a6, 8
	or a5, a5, a6
	lbu a6, 55(a1)
	or a5, a5, a6
	sw a5, 52(a3)
	srliw a6, a4, 6
	slliw a7, a4, 26
	xor a6, a6, a7
	srliw a7, a4, 11
	xor a6, a6, a7
	slliw a7, a4, 21
	xor a6, a6, a7
	srliw a7, a4, 25
	xor a6, a6, a7
	slliw a7, a4, 7
	xor a6, a6, a7
	add t2, t2, a6
	xor a6, t0, t1
	and a6, a6, a4
	xor a6, a6, t1
	add t2, t2, a6
	lui a6, 527851
	addiw a6, a6, 510
	add t2, t2, a6
	add t2, t2, a5
	add t6, t6, t2
	srliw a6, t3, 2
	slliw a7, t3, 30
	xor a6, a6, a7
	srliw a7, t3, 13
	xor a6, a6, a7
	slliw a7, t3, 19
	xor a6, a6, a7
	srliw a7, t3, 22
	xor a6, a6, a7
	slliw a7, t3, 10
	xor a6, a6, a7
	add t2, t2, a6
	or a6, t3, t4
	and a6, a6, t5
	and a7, t3, t4
	or a6, a6, a7
	add t2, t2, a6
	lbu a5, 56(a1)
	slli a5, a5, 24
	lbu a6, 57(a1)
	slli a6, a6, 16
	or a5, a5, a6
	lbu a6, 58(a1)
	slli a6, a6, 8
	or a5, a5, a6
	lbu a6, 59(a1)
	or a5, a5, a6
	sw a5, 56(a3)
	srliw a6, t6, 6
	slliw a7, t6, 26
	xor a6, a6, a7
	srliw a7, t6, 11
	xor a6, a6, a7
	slliw a7, t6, 21
	xor a6, a6, a7
	srliw a7, t6, 25
	xor a6, a6, a7
	slliw a7, t6, 7
	xor a6, a6, a7
	add t1, t1, a6
	xor a6, a4, t0
	and a6, a6, t6
	xor a6, a6, t0
	add t1, t1, a6
	lui a6, 638400
	addiw a6, a6, 1703
	add t1, t1, a6
	add t1, t1, a5
	add t5, t5, t1
	srliw a6, t2, 2
	slliw a7, t2, 30
	xor a6, a6, a7
	srliw a7, t2, 13
	xor a6, a6, a7
	slliw a7, t2, 19
	xor a6, a6, a7
	srliw a7, t2, 22
	xor a6, a6, a7
	slliw a7, t2, 10
	xor a6, a6, a7
	add t1, t1, a6
	or a6, t2, t3
	and a6, a6, t4
	and a7, t2, t3
	or a6, a6, a7
	add t1, t1, a6
	lbu a5, 60(a1)
	slli a5, a5, 24
	lbu a6, 61(a1)
	slli a6, a6, 16
	or a5, a5, a6
	lbu a6, 62(a1)
	slli a6, a6, 8
	or a5, a5, a6
	lbu a6, 63(a1)
	or a5, a5, a6
	sw a5, 60(a3)
	srliw a6, t5, 6
	slliw a7, t5, 26
	xor a6, a6, a7
	srliw a7, t5, 11
	xor a6, a6, a7
	slliw a7, t5, 21
	xor a6, a6, a7
	srliw a7, t5, 25
	xor a6, a6, a7
	slliw a7, t5, 7
	xor a6, a6, a7
	add t0, t0, a6
	xor a6, t6, a4
	and a6, a6, t5
	xor a6, a6, a4
	add t0, t0, a6
	lui a6, 793023
	addiw a6, a6, 372
	add t0, t0, a6
	add t0, t0, a5
	add t4, t4, t0
	srliw a6, t1, 2
	slliw a7, t1, 30
	xor a6, a6, a7
	srliw a7, t1, 13
	xor a6, a6, a7
	slliw a7, t1, 19
	xor a6, a6, a7
	srliw a7, t1, 22
	xor a6, a6, a7
	slliw a7, t1, 10
	xor a6, a6, a7
	add t0, t0, a6
	or a6, t1, t2
	and a6, a6, t3
	and a7, t1, t2
	or a6, a6, a7
	add t0, t0, a6
	lwu a6, 56(a3)
	srliw a5, a6, 17
	slliw a7, a6, 15
	xor a5, a5, a7
	srliw a7, a6, 19
	xor a5, a5, a7
	slliw a7, a6, 13
	xor a5, a5, a7
	srliw a7, a6, 10
	xor a5, a5, a7
	lwu a7, 36(a3)
	add a5, a5, a7
	lwu a6, 4(a3)
	srliw a7, a6, 7
	slliw s0, a6, 25
	xor a7, a7, s0
	srliw s0, a6, 18
	xor a7, a7, s0
	slliw s0, a6, 14
	xor a7, a7, s0
	srliw s0, a6, 3
	xor a7, a7, s0
	add a5, a5, a7
	lwu a7, 0(a3)
	add a5, a5, a7
	sw a5, 0(a3)
	srliw a6, t4, 6
	slliw a7, t4, 26
	xor a6, a6, a7
	srliw a7, t4, 11
	xor a6, a6, a7
	slliw a7, t4, 21
	xor a6, a6, a7
	srliw a7, t4, 25
	xor a6, a6, a7
	slliw a7, t4, 7
	xor a6, a6, a7
	add a4, a4, a6
	xor a6, t5, t6
	and a6, a6, t4
	xor a6, a6, t6
	add a4, a4, a6
	lui a6, 936375
	addiw a6, a6, -1599
	add a4, a4, a6
	add a4, a4, a5
	add t3, t3, a4
	srliw a6, t0, 2
	slliw a7, t0, 30
	xor a6, a6, a7
	srliw a7, t0, 13
	xor a6, a6, a7
	slliw a7, t0, 19
	xor a6, a6, a7
	srliw a7, t0, 22
	xor a6, a6, a7
	slliw a7, t0, 10
	xor a6, a6, a7
	add a4, a4, a6
	or a6, t0, t1
	and a6, a6, t2
	and a7, t0, t1
	or a6, a6, a7
	add a4, a4, a6
	lwu a6, 60(a3)
	srliw a5, a6, 17
	slliw a7, a6, 15
	xor a5, a5, a7
	srliw a7, a6, 19
	xor a5, a5, a7
	slliw a7, a6, 13
	xor a5, a5, a7
	srliw a7, a6, 10
	xor a5, a5, a7
	lwu a7, 40(a3)
	add a5, a5, a7
	lwu a6, 8(a3)
	srliw a7, a6, 7
	slliw s0, a6, 25
	xor a7, a7, s0
	srliw s0, a6, 18
	xor a7, a7, s0
	slliw s0, a6, 14
	xor a7, a7, s0
	srliw s0, a6, 3
	xor a7, a7, s0
	add a5, a5, a7
	lwu a7, 4(a3)
	add a5, a5, a7
	sw a5, 4(a3)
	srliw a6, t3, 6
	slliw a7, t3, 26
	xor a6, a6, a7
	srliw a7, t3, 11
	xor a6, a6, a7
	slliw a7, t3, 21
	xor a6, a6, a7
	srliw a7, t3, 25
	xor a6, a6, a7
	slliw a7, t3, 7
	xor a6, a6, a7
	add t6, t6, a6
	xor a6, t4, t5
	and a6, a6, t3
	xor a6, a6, t5
	add t6, t6, a6
	lui a6, 981988
	addiw a6, a6, 1926
	add t6, t6, a6
	add t6, t6, a5
	add t2, t2, t6
	srliw a6, a4, 2
	slliw a7, a4, 30
	xor a6, a6, a7
	srliw a7, a4, 13
	xor a6, a6, a7
	slliw a7, a4, 19
	xor a6, a6, a7
	srliw a7, a4, 22
	xor a6, a6, a7
	slliw a7, a4, 10
	xor a6, a6, a7
	add t6, t6, a6
	or a6, a4, t0
	and a6, a6, t1
	and a7, a4, t0
	or a6, a6, a7
	add t6, t6, a6
	lwu a6, 0(a3)
	srliw a5, a6, 17
	slliw a7, a6, 15
	xor a5, a5, a7
	srliw a7, a6, 19
	xor a5, a5, a7
	slliw a7, a6, 13
	xor a5, a5, a7
	srliw a7, a6, 10
	xor a5, a5, a7
	lwu a7, 44(a3)
	add a5, a5, a7
	lwu a6, 12(a3)
	srliw a7, a6, 7
	slliw s0, a6, 25
	xor a7, a7, s0
	srliw s0, a6, 18
	xor a7, a7, s0
	slliw s0, a6, 14
	xor a7, a7, s0
	srliw s0, a6, 3
	xor a7, a7, s0
	add a5, a5, a7
	lwu a7, 8(a3)
	add a5, a5, a7
	sw a5, 8(a3)
	srliw a6, t2, 6
	slliw a7, t2, 26
	xor a6, a6, a7
	srliw a7, t2, 11
	xor a6, a6, a7
	slliw a7, t2, 21
	xor a6, a6, a7
	srliw a7, t2, 25
	xor a6, a6, a7
	slliw a7, t2, 7
	xor a6, a6, a7
	add t5, t5, a6
	xor a6, t3, t4
	and a6, a6, t2
	xor a6, a6, t4
	add t5, t5, a6
	lui a6, 64538
	addiw a6, a6, -570
	add t5, t5, a6
	add t5, t5, a5
	add t1, t1, t5
	srliw a6, t6, 2
	slliw a7, t6, 30
	xor a6, a6, a7
	srliw a7, t6, 13
	xor a6, a6, a7
	slliw a7, t6, 19
	xor a6, a6, a7
	srliw a7, t6, 22
	xor a6, a6, a7
	slliw a7, t6, 10
	xor a6, a6, a7
	add t5, t5, a6
	or a6, t6, a4
	and a6, a6, t0
	and a7, t6, a4
	or a6, a6, a7
	add t5, t5, a6
	lwu a6, 4(a3)
	srliw a5, a6, 17
	slliw a7, a6, 15
	xor a5, a5, a7
	srliw a7, a6, 19
	xor a5, a5, a7
	slliw a7, a6, 13
	xor a5, a5, a7
	srliw a7, a6, 10
	xor a5, a5, a7
	lwu a7, 48(a3)
	add a5, a5, a7
	lwu a6, 16(a3)
	srliw a7, a6, 7
	slliw s0, a6, 25
	xor a7, a7, s0
	srliw s0, a6, 18
	xor a7, a7, s0
	slliw s0, a6, 14
	xor a7, a7, s0
	srliw s0, a6, 3
	xor a7, a7, s0
	add a5, a5, a7
	lwu a7, 12(a3)
	add a5, a5, a7
	sw a5, 12(a3)
	srliw a6, t1, 6
	slliw a7, t1, 26
	xor a6, a6, a7
	srliw a7, t1, 11
	xor a6, a6, a7
	slliw a7, t1, 21
	xor a6, a6, a7
	srliw a7, t1, 25
	xor a6, a6, a7
	slliw a7, t1, 7
	xor a6, a6, a7
	add t4, t4, a6
	xor a6, t2, t3
	and a6, a6, t1
	xor a6, a6, t3
	add t4, t4, a6
	lui a6, 147658
	addiw a6, a6, 460
	add t4, t4, a6
	add t4, t4, a5
	add t0, t0, t4
	srliw a6, t5, 2
	slliw a7, t5, 30
	xor a6, a6, a7
	srliw a7, t5, 13
	xor a6, a6, a7
	slliw a7, t5, 19
	xor a6, a6, a7
	srliw a7, t5, 22
	xor a6, a6, a7
	slliw a7, t5, 10
	xor a6, a6, a7
	add t4, t4, a6
	or a6, t5, t6
	and a6, a6, a4
	and a7, t5, t6
	or a6, a6, a7
	add t4, t4, a6
	lwu a6, 8(a3)
	srliw a5, a6, 17
	slliw a7, a6, 15
	xor a5, a5, a7
	srliw a7, a6, 19
	xor a5, a5, a7
	slliw a7, a6, 13
	xor a5, a5, a7
	srliw a7, a6, 10
	xor a5, a5, a7
	lwu a7, 52(a3)
	add a5, a5, a7
	lwu a6, 20(a3)
	srliw a7, a6, 7
	slliw s0, a6, 25
	xor a7, a7, s0
	srliw s0, a6, 18
	xor a7, a7, s0
	slliw s0, a6, 14
	xor a7, a7, s0
	srliw s0, a6, 3
	xor a7, a7, s0
	add a5, a5, a7
	lwu a7, 16(a3)
	add a5, a5, a7
	sw a5, 16(a3)
	srliw a6, t0, 6
	slliw a7, t0, 26
	xor a6, a6, a7
	srliw a7, t0, 11
	xor a6, a6, a7
	slliw a7, t0, 21
	xor a6, a6, a7
	srliw a7, t0, 25
	xor a6, a6, a7
	slliw a7, t0, 7
	xor a6, a6, a7
	add t3, t3, a6
	xor a6, t1, t2
	and a6, a6, t0
	xor a6, a6, t2
	add t3, t3, a6
	lui a6, 188051
	addiw a6, a6, -913
	add t3, t3, a6
	add t3, t3, a5
	add a4, a4, t3
	srliw a6, t4, 2
	slliw a7, t4, 30
	xor a6, a6, a7
	srliw a7, t4, 13
	xor a6, a6, a7
	slliw a7, t4, 19
	xor a6, a6, a7
	srliw a7, t4, 22
	xor a6, a6, a7
	slliw a7, t4, 10
	xor a6, a6, a7
	add t3, t3, a6
	or a6, t4, t5
	and a6, a6, t6
	and a7, t4, t5
	or a6, a6, a7
	add t3, t3, a6
	lwu a6, 12(a3)
	srliw a5, a6, 17
	slliw a7, a6, 15
	xor a5, a5, a7
	srliw a7, a6, 19
	xor a5, a5, a7
	slliw a7, a6, 13
	xor a5, a5, a7
	srliw a7, a6, 10
	xor a5, a5, a7
	lwu a7, 56(a3)
	add a5, a5, a7
	lwu a6, 24(a3)
	srliw a7, a6, 7
	slliw s0, a6, 25
	xor a7, a7, s0
	srliw s0, a6, 18
	xor a7, a7, s0
	slliw s0, a6, 14
	xor a7, a7, s0
	srliw s0, a6, 3
	xor a7, a7, s0
	add a5, a5, a7
	lwu a7, 20(a3)
	add a5, a5, a7
	sw a5, 20(a3)
	srliw a6, a4, 6
	slliw a7, a4, 26
	xor a6, a6, a7
	srliw a7, a4, 11
	xor a6, a6, a7
	slliw a7, a4, 21
	xor a6, a6, a7
	srliw a7, a4, 25
	xor a6, a6, a7
	slliw a7, a4, 7
	xor a6, a6, a7
	add t2, t2, a6
	xor a6, t0, t1
	and a6, a6, a4
	xor a6, a6, t1
	add t2, t2, a6
	lui a6, 304968
	addiw a6, a6, 1194
	add t2, t2, a6
	add t2, t2, a5
	add t6, t6, t2
	srliw a6, t3, 2
	slliw a7, t3, 30
	xor a6, a6, a7
	srliw a7, t3, 13
	xor a6, a6, a7
	slliw a7, t3, 19
	xor a6, a6, a7
	srliw a7, t3, 22
	xor a6, a6, a7
	slliw a7, t3, 10
	xor a6, a6, a7
	add t2, t2, a6
	or a6, t3, t4
	and a6, a6, t5
	and a7, t3, t4
	or a6, a6, a7
	add t2, t2, a6
	lwu a6, 16(a3)
	srliw a5, a6, 17
	slliw a7, a6, 15
	xor a5, a5, a7
	srliw a7, a6, 19
	xor a5, a5, a7
	slliw a7, a6, 13
	xor a5, a5, a7
	srliw a7, a6, 10
	xor a5, a5, a7
	lwu a7, 60(a3)
	add a5, a5, a7
	lwu a6, 28(a3)
	srliw a7, a6, 7
	slliw s0, a6, 25
	xor a7, a7, s0
	srliw s0, a6, 18
	xor a7, a7, s0
	slliw s0, a6, 14
	xor a7, a7, s0
	srliw s0, a6, 3
	xor a7, a7, s0
	add a5, a5, a7
	lwu a7, 24(a3)
	add a5, a5, a7
	sw a5, 24(a3)
	srliw a6, t6, 6
	slliw a7, t6, 26
	xor a6, a6, a7
	srliw a7, t6, 11
	xor a6, a6, a7
	slliw a7, t6, 21
	xor a6, a6, a7
	srliw a7, t6, 25
	xor a6, a6, a7
	slliw a7, t6, 7
	xor a6, a6, a7
	add t1, t1, a6
	xor a6, a4, t0
	and a6, a6, t6
	xor a6, a6, t0
	add t1, t1, a6
	lui a6, 379659
	addiw a6, a6, -1572
	add t1, t1, a6
	add t1, t1, a5
	add t5, t5, t1
	srliw a6, t2, 2
	slliw a7, t2, 30
	xor a6, a6, a7
	srliw a7, t2, 13
	xor a6, a6, a7
	slliw a7, t2, 19
	xor a6, a6, a7
	srliw a7, t2, 22
	xor a6, a6, a7
	slliw a7, t2, 10
	xor a6, a6, a7
	add t1, t1, a6
	or a6, t2, t3
	and a6, a6, t4
	and a7, t2, t3
	or a6, a6, a7
	add t1, t1, a6
	lwu a6, 20(a3)
	srliw a5, a6, 17
	slliw a7, a6, 15
	xor a5, a5, a7
	srliw a7, a6, 19
	xor a5, a5, a7
	slliw a7, a6, 13
	xor a5, a5, a7
	srliw a7, a6, 10
	xor a5, a5, a7
	lwu a7, 0(a3)
	add a5, a5, a7
	lwu a6, 32(a3)
	srliw a7, a6, 7
	slliw s0, a6, 25
	xor a7, a7, s0
	srliw s0, a6, 18
	xor a7, a7, s0
	slliw s0, a6, 14
	xor a7, a7, s0
	srliw s0, a6, 3
	xor a7, a7, s0
	add a5, a5, a7
	lwu a7, 28(a3)
	add a5, a5, a7
	sw a5, 28(a3)
	srliw a6, t5, 6
	slliw a7, t5, 26
	xor a6, a6, a7
	srliw a7, t5, 11
	xor a6, a6, a7
	slliw a7, t5, 21
	xor a6, a6, a7
	srliw a7, t5, 25
	xor a6, a6, a7
	slliw a7, t5, 7
	xor a6, a6, a7
	add t0, t0, a6
	xor a6, t6, a4
	and a6, a6, t5
	xor a6, a6, a4
	add t0, t0, a6
	lui a6, 487321
	addiw a6, a6, -1830
	add t0, t0, a6
	add t0, t0, a5
	add t4, t4, t0
	srliw a6, t1, 2
	slliw a7, t1, 30
	xor a6, a6, a7
	srliw a7, t1, 13
	xor a6, a6, a7
	slliw a7, t1, 19
	xor a6, a6, a7
	srliw a7, t1, 22
	xor a6, a6, a7
	slliw a7, t1, 10
	xor a6, a6, a7
	add t0, t0, a6
	or a6, t1, t2
	and a6, a6, t3
	and a7, t1, t2
	or a6, a6, a7
	add t0, t0, a6
	lwu a6, 24(a3)
	srliw a5, a6, 17
	slliw a7, a6, 15
	xor a5, a5, a7
	srliw a7, a6, 19
	xor a5, a5, a7
	slliw a7, a6, 13
	xor a5, a5, a7
	srliw a7, a6, 10
	xor a5, a5, a7
	lwu a7, 4(a3)
	add a5, a5, a7
	lwu a6, 36(a3)
	srliw a7, a6, 7
	slliw s0, a6, 25
	xor a7, a7, s0
	srliw s0, a6, 18
	xor a7, a7, s0
	slliw s0, a6, 14
	xor a7, a7, s0
	srliw s0, a6, 3
	xor a7, a7, s0
	add a5, a5, a7
	lwu a7, 32(a3)
	add a5, a5, a7
	sw a5, 32(a3)
	srliw a6, t4, 6
	slliw a7, t4, 26
	xor a6, a6, a7
	srliw a7, t4, 11
	xor a6, a6, a7
	slliw a7, t4, 21
	xor a6, a6, a7
	srliw a7, t4, 25
	xor a6, a6, a7
	slliw a7, t4, 7
	xor a6, a6, a7
	add a4, a4, a6
	xor a6, t5, t6
	and a6, a6, t4
	xor a6, a6, t6
	add a4, a4, a6
	lui a6, 623589
	addiw a6, a6, 338
	add a4, a4, a6
	add a4, a4, a5
	add t3, t3, a4
	srliw a6, t0, 2
	slliw a7, t0, 30
	xor a6, a6, a7
	srliw a7, t0, 13
	xor a6, a6, a7
	slliw a7, t0, 19
	xor a6, a6, a7
	srliw a7, t0, 22
	xor a6, a6, a7
	slliw a7, t0, 10
	xor a6, a6, a7
	add a4, a4, a6
	or a6, t0, t1
	and a6, a6, t2
	and a7, t0, t1
	or a6, a6, a7
	add a4, a4, a6
	lwu a6, 28(a3)
	srliw a5, a6, 17
	slliw a7, a6, 15
	xor a5, a5, a7
	srliw a7, a6, 19
	xor a5, a5, a7
	slliw a7, a6, 13
	xor a5, a5, a7
	srliw a7, a6, 10
	xor a5, a5, a7
	lwu a7, 8(a3)
	add a5, a5, a7
	lwu a6, 40(a3)
	srliw a7, a6, 7
	slliw s0, a6, 25
	xor a7, a7, s0
	srliw s0, a6, 18
	xor a7, a7, s0
	slliw s0, a6, 14
	xor a7, a7, s0
	srliw s0, a6, 3
	xor a7, a7, s0
	add a5, a5, a7
	lwu a7, 36(a3)
	add a5, a5, a7
	sw a5, 36(a3)
	srliw a6, t3, 6
	slliw a7, t3, 26
	xor a6, a6, a7
	srliw a7, t3, 11
	xor a6, a6, a7
	slliw a7, t3, 21
	xor a6, a6, a7
	srliw a7, t3, 25
	xor a6, a6, a7
	slliw a7, t3, 7
	xor a6, a6, a7
	add t6, t6, a6
	xor a6, t4, t5
	and a6, a6, t3
	xor a6, a6, t5
	add t6, t6, a6
	lui a6, 688924
	addiw a6, a6, 1645
	add t6, t6, a6
	add t6, t6, a5
	add t2, t2, t6
	srliw a6, a4, 2
	slliw a7, a4, 30
	xor a6, a6, a7
	srliw a7, a4, 13
	xor a6, a6, a7
	slliw a7, a4, 19
	xor a6, a6, a7
	srliw a7, a4, 22
	xor a6, a6, a7
	slliw a7, a4, 10
	xor a6, a6, a7
	add t6, t6, a6
	or a6, a4, t0
	and a6, a6, t1
	and a7, a4, t0
	or a6, a6, a7
	add t6, t6, a6
	lwu a6, 32(a3)
	srliw a5, a6, 17
	slliw a7, a6, 15
	xor a5, a5, a7
	srliw a7, a6, 19
	xor a5, a5, a7
	slliw a7, a6, 13
	xor a5, a5, a7
	srliw a7, a6, 10
	xor a5, a5, a7
	lwu a7, 12(a3)
	add a5, a5, a7
	lwu a6, 44(a3)
	srliw a7, a6, 7
	slliw s0, a6, 25
	xor a7, a7, s0
	srliw s0, a6, 18
	xor a7, a7, s0
	slliw s0, a6, 14
	xor a7, a7, s0
	srliw s0, a6, 3
	xor a7, a7, s0
	add a5, a5, a7
	lwu a7, 40(a3)
	add a5, a5, a7
	sw a5, 40(a3)
	srliw a6, t2, 6
	slliw a7, t2, 26
	xor a6, a6, a7
	srliw a7, t2, 11
	xor a6, a6, a7
	slliw a7, t2, 21
	xor a6, a6, a7
	srliw a7, t2, 25
	xor a6, a6, a7
	slliw a7, t2, 7
	xor a6, a6, a7
	add t5, t5, a6
	xor a6, t3, t4
	and a6, a6, t2
	xor a6, a6, t4
	add t5, t5, a6
	lui a6, 720946
	addiw a6, a6, 1992
	add t5, t5, a6
	add t5, t5, a5
	add t1, t1, t5
	srliw a6, t6, 2
	slliw a7, t6, 30
	xor a6, a6, a7
	srliw a7, t6, 13
	xor a6, a6, a7
	slliw a7, t6, 19
	xor a6, a6, a7
	srliw a7, t6, 22
	xor a6, a6, a7
	slliw a7, t6, 10
	xor a6, a6, a7
	add t5, t5, a6
	or a6, t6, a4
	and a6, a6, t0
	and a7, t6, a4
	or a6, a6, a7
	add t5, t5, a6
	lwu a6, 36(a3)
	srliw a5, a6, 17
	slliw a7, a6, 15
	xor a5, a5, a7
	srliw a7, a6, 19
	xor a5, a5, a7
	slliw a7, a6, 13
	xor a5, a5, a7
	srliw a7, a6, 10
	xor a5, a5, a7
	lwu a7, 16(a3)
	add a5, a5, a7
	lwu a6, 48(a3)
	srliw a7, a6, 7
	slliw s0, a6, 25
	xor a7, a7, s0
	srliw s0, a6, 18
	xor a7, a7, s0
	slliw s0, a6, 14
	xor a7, a7, s0
	srliw s0, a6, 3
	xor a7, a7, s0
	add a5, a5, a7
	lwu a7, 44(a3)
	add a5, a5, a7
	sw a5, 44(a3)
	srliw a6, t1, 6
	slliw a7, t1, 26
	xor a6, a6, a7
	srliw a7, t1, 11
	xor a6, a6, a7
	slliw a7, t1, 21
	xor a6, a6, a7
	srliw a7, t1, 25
	xor a6, a6, a7
	slliw a7, t1, 7
	xor a6, a6, a7
	add t4, t4, a6
	xor a6, t2, t3
	and a6, a6, t1
	xor a6, a6, t3
	add t4, t4, a6
	lui a6, 783768
	addiw a6, a6, -57
	add t4, t4, a6
	add t4, t4, a5
	add t0, t0, t4
	srliw a6, t5, 2
	slliw a7, t5, 30
	xor a6, a6, a7
	srliw a7, t5, 13
	xor a6, a6, a7
	slliw a7, t5, 19
	xor a6, a6, a7
	srliw a7, t5, 22
	xor a6, a6, a7
	slliw a7, t5, 10
	xor a6, a6, a7
	add t4, t4, a6
	or a6, t5, t6
	and a6, a6, a4
	and a7, t5, t6
	or a6, a6, a7
	add t4, t4, a6
	lwu a6, 40(a3)
	srliw a5, a6, 17
	slliw a7, a6, 15
	xor a5, a5, a7
	srliw a7, a6, 19
	xor a5, a5, a7
	slliw a7, a6, 13
	xor a5, a5, a7
	srliw a7, a6, 10
	xor a5, a5, a7
	lwu a7, 20(a3)
	add a5, a5, a7
	lwu a6, 52(a3)
	srliw a7, a6, 7
	slliw s0, a6, 25
	xor a7, a7, s0
	srliw s0, a6, 18
	xor a7, a7, s0
	slliw s0, a6, 14
	xor a7, a7, s0
	srliw s0, a6, 3
	xor a7, a7, s0
	add a5, a5, a7
	lwu a7, 48(a3)
	add a5, a5, a7
	sw a5, 48(a3)
	srliw a6, t0, 6
	slliw a7, t0, 26
	xor a6, a6, a7
	srliw a7, t0, 11
	xor a6, a6, a7
	slliw a7, t0, 21
	xor a6, a6, a7
	srliw a7, t0, 25
	xor a6, a6, a7
	slliw a7, t0, 7
	xor a6, a6, a7
	add t3, t3, a6
	xor a6, t1, t2
	and a6, a6, t0
	xor a6, a6, t2
	add t3, t3, a6
	lui a6, 814593
	addiw a6, a6, -1037
	add t3, t3, a6
	add t3, t3, a5
	add a4, a4, t3
	srliw a6, t4, 2
	slliw a7, t4, 30
	xor a6, a6, a7
	srliw a7, t4, 13
	xor a6, a6, a7
	slliw a7, t4, 19
	xor a6, a6, a7
	srliw a7, t4, 22
	xor a6, a6, a7
	slliw a7, t4, 10
	xor a6, a6, a7
	add t3, t3, a6
	or a6, t4, t5
	and a6, a6, t6
	and a7, t4, t5
	or a6, a6, a7
	add t3, t3, a6
	lwu a6, 44(a3)
	srliw a5, a6, 17
	slliw a7, a6, 15
	xor a5, a5, a7
	srliw a7, a6, 19
	xor a5, a5, a7
	slliw a7, a6, 13
	xor a5, a5, a7
	srliw a7, a6, 10
	xor a5, a5, a7
	lwu a7, 24(a3)
	add a5, a5, a7
	lwu a6, 56(a3)
	srliw a7, a6, 7
	slliw s0, a6, 25
	xor a7, a7, s0
	srliw s0, a6, 18
	xor a7, a7, s0
	slliw s0, a6, 14
	xor a7, a7, s0
	srliw s0, a6, 3
	xor a7, a7, s0
	add a5, a5, a7
	lwu a7, 52(a3)
	add a5, a5, a7
	sw a5, 52(a3)
	srliw a6, a4, 6
	slliw a7, a4, 26
	xor a6, a6, a7
	srliw a7, a4, 11
	xor a6, a6, a7
	slliw a7, a4, 21
	xor a6, a6, a7
	srliw a7, a4, 25
	xor a6, a6, a7
	slliw a7, a4, 7
	xor a6, a6, a7
	add t2, t2, a6
	xor a6, t0, t1
	and a6, a6, a4
	xor a6, a6, t1
	add t2, t2, a6
	lui a6, 875129
	addiw a6, a6, 327
	add t2, t2, a6
	add t2, t2, a5
	add t6, t6, t2
	srliw a6, t3, 2
	slliw a7, t3, 30
	xor a6, a6, a7
	srliw a7, t3, 13
	xor a6, a6, a7
	slliw a7, t3, 19
	xor a6, a6, a7
	srliw a7, t3, 22
	xor a6, a6, a7
	slliw a7, t3, 10
	xor a6, a6, a7
	add t2, t2, a6
	or a6, t3, t4
	and a6, a6, t5
	and a7, t3, t4
	or a6, a6, a7
	add t2, t2, a6
	lwu a6, 48(a3)
	srliw a5, a6, 17
	slliw a7, a6, 15
	xor a5, a5, a7
	srliw a7, a6, 19
	xor a5, a5, a7
	slliw a7, a6, 13
	xor a5, a5, a7
	srliw a7, a6, 10
	xor a5, a5, a7
	lwu a7, 28(a3)
	add a5, a5, a7
	lwu a6, 60(a3)
	srliw a7, a6, 7
	slliw s0, a6, 25
	xor a7, a7, s0
	srliw s0, a6, 18
	xor a7, a7, s0
	slliw s0, a6, 14
	xor a7, a7, s0
	srliw s0, a6, 3
	xor a7, a7, s0
	add a5, a5, a7
	lwu a7, 56(a3)
	add a5, a5, a7
	sw a5, 56(a3)
	srliw a6, t6, 6
	slliw a7, t6, 26
	xor a6, a6, a7
	srliw a7, t6, 11
	xor a6, a6, a7
	slliw a7, t6, 21
	xor a6, a6, a7
	srliw a7, t6, 25
	xor a6, a6, a7
	slliw a7, t6, 7
	xor a6, a6, a7
	add t1, t1, a6
	xor a6, a4, t0
	and a6, a6, t6
	xor a6, a6, t0
	add t1, t1, a6
	lui a6, 27814
	addiw a6, a6, 849
	add t1, t1, a6
	add t1, t1, a5
	add t5, t5, t1
	srliw a6, t2, 2
	slliw a7, t2, 30
	xor a6, a6, a7
	srliw a7, t2, 13
	xor a6, a6, a7
	slliw a7, t2, 19
	xor a6, a6, a7
	srliw a7, t2, 22
	xor a6, a6, a7
	slliw a7, t2, 10
	xor a6, a6, a7
	add t1, t1, a6
	or a6, t2, t3
	and a6, a6, t4
	and a7, t2, t3
	or a6, a6, a7
	add t1, t1, a6
	lwu a6, 52(a3)
	srliw a5, a6, 17
	slliw a7, a6, 15
	xor a5, a5, a7
	srliw a7, a6, 19
	xor a5, a5, a7
	slliw a7, a6, 13
	xor a5, a5, a7
	srliw a7, a6, 10
	xor a5, a5, a7
	lwu a7, 32(a3)
	add a5, a5, a7
	lwu a6, 0(a3)
	srliw a7, a6, 7
	slliw s0, a6, 25
	xor a7, a7, s0
	srliw s0, a6, 18
	xor a7, a7, s0
	slliw s0, a6, 14
	xor a7, a7, s0
	srliw s0, a6, 3
	xor a7, a7, s0
	add a5, a5, a7
	lwu a7, 60(a3)
	add a5, a5, a7
	sw a5, 60(a3)
	srliw a6, t5, 6
	slliw a7, t5, 26
	xor a6, a6, a7
	srliw a7, t5, 11
	xor a6, a6, a7
	slliw a7, t5, 21
	xor a6, a6, a7
	srliw a7, t5, 25
	xor a6, a6, a7
	slliw a7, t5, 7
	xor a6, a6, a7
	add t0, t0, a6
	xor a6, t6, a4
	and a6, a6, t5
	xor a6, a6, a4
	add t0, t0, a6
	lui a6, 82579
	addiw a6, a6, -1689
	add t0, t0, a6
	add t0, t0, a5
	add t4, t4, t0
	srliw a6, t1, 2
	slliw a7, t1, 30
	xor a6, a6, a7
	srliw a7, t1, 13
	xor a6, a6, a7
	slliw a7, t1, 19
	xor a6, a6, a7
	srliw a7, t1, 22
	xor a6, a6, a7
	slliw a7, t1, 10
	xor a6, a6, a7
	add t0, t0, a6
	or a6, t1, t2
	and a6, a6, t3
	and a7, t1, t2
	or a6, a6, a7
	add t0, t0, a6
	lwu a6, 56(a3)
	srliw a5, a6, 17
	slliw a7, a6, 15
	xor a5, a5, a7
	srliw a7, a6, 19
	xor a5, a5, a7
	slliw a7, a6, 13
	xor a5, a5, a7
	srliw a7, a6, 10
	xor a5, a5, a7
	lwu a7, 36(a3)
	add a5, a5, a7
	lwu a6, 4(a3)
	srliw a7, a6, 7
	slliw s0, a6, 25
	xor a7, a7, s0
	srliw s0, a6, 18
	xor a7, a7, s0
	slliw s0, a6, 14
	xor a7, a7, s0
	srliw s0, a6, 3
	xor a7, a7, s0
	add a5, a5, a7
	lwu a7, 0(a3)
	add a5, a5, a7
	sw a5, 0(a3)
	srliw a6, t4, 6
	slliw a7, t4, 26
	xor a6, a6, a7
	srliw a7, t4, 11
	xor a6, a6, a7
	slliw a7, t4, 21
	xor a6, a6, a7
	srliw a7, t4, 25
	xor a6, a6, a7
	slliw a7, t4, 7
	xor a6, a6, a7
	add a4, a4, a6
	xor a6, t5, t6
	and a6, a6, t4
	xor a6, a6, t6
	add a4, a4, a6
	lui a6, 162673
	addiw a6, a6, -1403
	add a4, a4, a6
	add a4, a4, a5
	add t3, t3, a4
	srliw a6, t0, 2
	slliw a7, t0, 30
	xor a6, a6, a7
	srliw a7, t0, 13
	xor a6, a6, a7
	slliw a7, t0, 19
	xor a6, a6, a7
	srliw a7, t0, 22
	xor a6, a6, a7
	slliw a7, t0, 10
	xor a6, a6, a7
	add a4, a4, a6
	or a6, t0, t1
	and a6, a6, t2
	and a7, t0, t1
	or a6, a6, a7
	add a4, a4, a6
	lwu a6, 60(a3)
	srliw a5, a6, 17
	slliw a7, a6, 15
	xor a5, a5, a7
	srliw a7, a6, 19
	xor a5, a5, a7
	slliw a7, a6, 13
	xor a5, a5, a7
	srliw a7, a6, 10
	xor a5, a5, a7
	lwu a7, 40(a3)
	add a5, a5, a7
	lwu a6, 8(a3)
	srliw a7, a6, 7
	slliw s0, a6, 25
	xor a7, a7, s0
	srliw s0, a6, 18
	xor a7, a7, s0
	slliw s0, a6, 14
	xor a7, a7, s0
	srliw s0, a6, 3
	xor a7, a7, s0
	add a5, a5, a7
	lwu a7, 4(a3)
	add a5, a5, a7
	sw a5, 4(a3)
	srliw a6, t3, 6
	slliw a7, t3, 26
	xor a6, a6, a7
	srliw a7, t3, 11
	xor a6, a6, a7
	slliw a7, t3, 21
	xor a6, a6, a7
	srliw a7, t3, 25
	xor a6, a6, a7
	slliw a7, t3, 7
	xor a6, a6, a7
	add t6, t6, a6
	xor a6, t4, t5
	and a6, a6, t3
	xor a6, a6, t5
	add t6, t6, a6
	lui a6, 188850
	addiw a6, a6, 312
	add t6, t6, a6
	add t6, t6, a5
	add t2, t2, t6
	srliw a6, a4, 2
	slliw a7, a4, 30
	xor a6, a6, a7
	srliw a7, a4, 13
	xor a6, a6, a7
	slliw a7, a4, 19
	xor a6, a6, a7
	srliw a7, a4, 22
	xor a6, a6, a7
	slliw a7, a4, 10
	xor a6, a6, a7
	add t6, t6, a6
	or a6, a4, t0
	and a6, a6, t1
	and a7, a4, t0
	or a6, a6, a7
	add t6, t6, a6
	lwu a6, 0(a3)
	srliw a5, a6, 17
	slliw a7, a6, 15
	xor a5, a5, a7
	srliw a7, a6, 19
	xor a5, a5, a7
	slliw a7, a6, 13
	xor a5, a5, a7
	srliw a7, a6, 10
	xor a5, a5, a7
	lwu a7, 44(a3)
	add a5, a5, a7
	lwu a6, 12(a3)
	srliw a7, a6, 7
	slliw s0, a6, 25
	xor a7, a7, s0
	srliw s0, a6, 18
	xor a7, a7, s0
	slliw s0, a6, 14
	xor a7, a7, s0
	srliw s0, a6, 3
	xor a7, a7, s0
	add a5, a5, a7
	lwu a7, 8(a3)
	add a5, a5, a7
	sw a5, 8(a3)
	srliw a6, t2, 6
	slliw a7, t2, 26
	xor a6, a6, a7
	srliw a7, t2, 11
	xor a6, a6, a7
	slliw a7, t2, 21
	xor a6, a6, a7
	srliw a7, t2, 25
	xor a6, a6, a7
	slliw a7, t2, 7
	xor a6, a6, a7
	add t5, t5, a6
	xor a6, t3, t4
	and a6, a6, t2
	xor a6, a6, t4
	add t5, t5, a6
	lui a6, 316103
	addiw a6, a6, -516
	add t5, t5, a6
	add t5, t5, a5
	add t1, t1, t5
	srliw a6, t6, 2
	slliw a7, t6, 30
	xor a6, a6, a7
	srliw a7, t6, 13
	xor a6, a6, a7
	slliw a7, t6, 19
	xor a6, a6, a7
	srliw a7, t6, 22
	xor a6, a6, a7
	slliw a7, t6, 10
	xor a6, a6, a7
	add t5, t5, a6
	or a6, t6, a4
	and a6, a6, t0
	and a7, t6, a4
	or a6, a6, a7
	add t5, t5, a6
	lwu a6, 4(a3)
	srliw a5, a6, 17
	slliw a7, a6, 15
	xor a5, a5, a7
	srliw a7, a6, 19
	xor a5, a5, a7
	slliw a7, a6, 13
	xor a5, a5, a7
	srliw a7, a6, 10
	xor a5, a5, a7
	lwu a7, 48(a3)
	add a5, a5, a7
	lwu a6, 16(a3)
	srliw a7, a6, 7
	slliw s0, a6, 25
	xor a7, a7, s0
	srliw s0, a6, 18
	xor a7, a7, s0
	slliw s0, a6, 14
	xor a7, a7, s0
	srliw s0, a6, 3
	xor a7, a7, s0
	add a5, a5, a7
	lwu a7, 12(a3)
	add a5, a5, a7
	sw a5, 12(a3)
	srliw a6, t1, 6
	slliw a7, t1, 26
	xor a6, a6, a7
	srliw a7, t1, 11
	xor a6, a6, a7
	slliw a7, t1, 21
	xor a6, a6, a7
	srliw a7, t1, 25
	xor a6, a6, a7
	slliw a7, t1, 7
	xor a6, a6, a7
	add t4, t4, a6
	xor a6, t2, t3
	and a6, a6, t1
	xor a6, a6, t3
	add t4, t4, a6
	lui a6, 340865
	addiw a6, a6, -749
	add t4, t4, a6
	add t4, t4, a5
	add t0, t0, t4
	srliw a6, t5, 2
	slliw a7, t5, 30
	xor a6, a6, a7
	srliw a7, t5, 13
	xor a6, a6, a7
	slliw a7, t5, 19
	xor a6, a6, a7
	srliw a7, t5, 22
	xor a6, a6, a7
	slliw a7, t5, 10
	xor a6, a6, a7
	add t4, t4, a6
	or a6, t5, t6
	and a6, a6, a4
	and a7, t5, t6
	or a6, a6, a7
	add t4, t4, a6
	lwu a6, 8(a3)
	srliw a5, a6, 17
	slliw a7, a6, 15
	xor a5, a5, a7
	srliw a7, a6, 19
	xor a5, a5, a7
	slliw a7, a6, 13
	xor a5, a5, a7
	srliw a7, a6, 10
	xor a5, a5, a7
	lwu a7, 52(a3)
	add a5, a5, a7
	lwu a6, 20(a3)
	srliw a7, a6, 7
	slliw s0, a6, 25
	xor a7, a7, s0
	srliw s0, a6, 18
	xor a7, a7, s0
	slliw s0, a6, 14
	xor a7, a7, s0
	srliw s0, a6, 3
	xor a7, a7, s0
	add a5, a5, a7
	lwu a7, 16(a3)
	add a5, a5, a7
	sw a5, 16(a3)
	srliw a6, t0, 6
	slliw a7, t0, 26
	xor a6, a6, a7
	srliw a7, t0, 11
	xor a6, a6, a7
	slliw a7, t0, 21
	xor a6, a6, a7
	srliw a7, t0, 25
	xor a6, a6, a7
	slliw a7, t0, 7
	xor a6, a6, a7
	add t3, t3, a6
	xor a6, t1, t2
	and a6, a6, t0
	xor a6, a6, t2
	add t3, t3, a6
	lui a6, 413863
	addiw a6, a6, 852
	add t3, t3, a6
	add t3, t3, a5
	add a4, a4, t3
	srliw a6, t4, 2
	slliw a7, t4, 30
	xor a6, a6, a7
	srliw a7, t4, 13
	xor a6, a6, a7
	slliw a7, t4, 19
	xor a6, a6, a7
	srliw a7, t4, 22
	xor a6, a6, a7
	slliw a7, t4, 10
	xor a6, a6, a7
	add t3, t3, a6
	or a6, t4, t5
	and a6, a6, t6
	and a7, t4, t5
	or a6, a6, a7
	add t3, t3, a6
	lwu a6, 12(a3)
	srliw a5, a6, 17
	slliw a7, a6, 15
	xor a5, a5, a7
	srliw a7, a6, 19
	xor a5, a5, a7
	slliw a7, a6, 13
	xor a5, a5, a7
	srliw a7, a6, 10
	xor a5, a5, a7
	lwu a7, 56(a3)
	add a5, a5, a7
	lwu a6, 24(a3)
	srliw a7, a6, 7
	slliw s0, a6, 25
	xor a7, a7, s0
	srliw s0, a6, 18
	xor a7, a7, s0
	slliw s0, a6, 14
	xor a7, a7, s0
	srliw s0, a6, 3
	xor a7, a7, s0
	add a5, a5, a7
	lwu a7, 20(a3)
	add a5, a5, a7
	sw a5, 20(a3)
	srliw a6, a4, 6
	slliw a7, a4, 26
	xor a6, a6, a7
	srliw a7, a4, 11
	xor a6, a6, a7
	slliw a7, a4, 21
	xor a6, a6, a7
	srliw a7, a4, 25
	xor a6, a6, a7
	slliw a7, a4, 7
	xor a6, a6, a7
	add t2, t2, a6
	xor a6, t0, t1
	and a6, a6, a4
	xor a6, a6, t1
	add t2, t2, a6
	lui a6, 485025
	addiw a6, a6, -1349
	add t2, t2, a6
	add t2, t2, a5
	add t6, t6, t2
	srliw a6, t3, 2
	slliw a7, t3, 30
	xor a6, a6, a7
	srliw a7, t3, 13
	xor a6, a6, a7
	slliw a7, t3, 19
	xor a6, a6, a7
	srliw a7, t3, 22
	xor a6, a6, a7
	slliw a7, t3, 10
	xor a6, a6, a7
	add t2, t2, a6
	or a6, t3, t4
	and a6, a6, t5
	and a7, t3, t4
	or a6, a6, a7
	add t2, t2, a6
	lwu a6, 16(a3)
	srliw a5, a6, 17
	slliw a7, a6, 15
	xor a5, a5, a7
	srliw a7, a6, 19
	xor a5, a5, a7
	slliw a7, a6, 13
	xor a5, a5, a7
	srliw a7, a6, 10
	xor a5, a5, a7
	lwu a7, 60(a3)
	add a5, a5, a7
	lwu a6, 28(a3)
	srliw a7, a6, 7
	slliw s0, a6, 25
	xor a7, a7, s0
	srliw s0, a6, 18
	xor a7, a7, s0
	slliw s0, a6, 14
	xor a7, a7, s0
	srliw s0, a6, 3
	xor a7, a7, s0
	add a5, a5, a7
	lwu a7, 24(a3)
	add a5, a5, a7
	sw a5, 24(a3)
	srliw a6, t6, 6
	slliw a7, t6, 26
	xor a6, a6, a7
	srliw a7, t6, 11
	xor a6, a6, a7
	slliw a7, t6, 21
	xor a6, a6, a7
	srliw a7, t6, 25
	xor a6, a6, a7
	slliw a7, t6, 7
	xor a6, a6, a7
	add t1, t1, a6
	xor a6, a4, t0
	and a6, a6, t6
	xor a6, a6, t0
	add t1, t1, a6
	lui a6, 531501
	addiw a6, a6, -1746
	add t1, t1, a6
	add t1, t1, a5
	add t5, t5, t1
	srliw a6, t2, 2
	slliw a7, t2, 30
	xor a6, a6, a7
	srliw a7, t2, 13
	xor a6, a6, a7
	slliw a7, t2, 19
	xor a6, a6, a7
	srliw a7, t2, 22
	xor a6, a6, a7
	slliw a7, t2, 10
	xor a6, a6, a7
	add t1, t1, a6
	or a6, t2, t3
	and a6, a6, t4
	and a7, t2, t3
	or a6, a6, a7
	add t1, t1, a6
	lwu a6, 20(a3)
	srliw a5, a6, 17
	slliw a7, a6, 15
	xor a5, a5, a7
	srliw a7, a6, 19
	xor a5, a5, a7
	slliw a7, a6, 13
	xor a5, a5, a7
	srliw a7, a6, 10
	xor a5, a5, a7
	lwu a7, 0(a3)
	add a5, a5, a7
	lwu a6, 32(a3)
	srliw a7, a6, 7
	slliw s0, a6, 25
	xor a7, a7, s0
	srliw s0, a6, 18
	xor a7, a7, s0
	slliw s0, a6, 14
	xor a7, a7, s0
	srliw s0, a6, 3
	xor a7, a7, s0
	add a5, a5, a7
	lwu a7, 28(a3)
	add a5, a5, a7
	sw a5, 28(a3)
	srliw a6, t5, 6
	slliw a7, t5, 26
	xor a6, a6, a7
	srliw a7, t5, 11
	xor a6, a6, a7
	slliw a7, t5, 21
	xor a6, a6, a7
	srliw a7, t5, 25
	xor a6, a6, a7
	slliw a7, t5, 7
	xor a6, a6, a7
	add t0, t0, a6
	xor a6, t6, a4
	and a6, a6, t5
	xor a6, a6, a4
	add t0, t0, a6
	lui a6, 599843
	addiw a6, a6, -891
	add t0, t0, a6
	add t0, t0, a5
	add t4, t4, t0
	srliw a6, t1, 2
	slliw a7, t1, 30
	xor a6, a6, a7
	srliw a7, t1, 13
	xor a6, a6, a7
	slliw a7, t1, 19
	xor a6, a6, a7
	srliw a7, t1, 22
	xor a6, a6, a7
	slliw a7, t1, 10
	xor a6, a6, a7
	add t0, t0, a6
	or a6, t1, t2
	and a6, a6, t3
	and a7, t1, t2
	or a6, a6, a7
	add t0, t0, a6
	lwu a6, 24(a3)
	srliw a5, a6, 17
	slliw a7, a6, 15
	xor a5, a5, a7
	srliw a7, a6, 19
	xor a5, a5, a7
	slliw a7, a6, 13
	xor a5, a5, a7
	srliw a7, a6, 10
	xor a5, a5, a7
	lwu a7, 4(a3)
	add a5, a5, a7
	lwu a6, 36(a3)
	srliw a7, a6, 7
	slliw s0, a6, 25
	xor a7, a7, s0
	srliw s0, a6, 18
	xor a7, a7, s0
	slliw s0, a6, 14
	xor a7, a7, s0
	srliw s0, a6, 3
	xor a7, a7, s0
	add a5, a5, a7
	lwu a7, 32(a3)
	add a5, a5, a7
	sw a5, 32(a3)
	srliw a6, t4, 6
	slliw a7, t4, 26
	xor a6, a6, a7
	srliw a7, t4, 11
	xor a6, a6, a7
	slliw a7, t4, 21
	xor a6, a6, a7
	srliw a7, t4, 25
	xor a6, a6, a7
	slliw a7, t4, 7
	xor a6, a6, a7
	add a4, a4, a6
	xor a6, t5, t6
	and a6, a6, t4
	xor a6, a6, t6
	add a4, a4, a6
	lui a6, 666623
	addiw a6, a6, -1887
	add a4, a4, a6
	add a4, a4, a5
	add t3, t3, a4
	srliw a6, t0, 2
	slliw a7, t0, 30
	xor a6, a6, a7
	srliw a7, t0, 13
	xor a6, a6, a7
	slliw a7, t0, 19
	xor a6, a6, a7
	srliw a7, t0, 22
	xor a6, a6, a7
	slliw a7, t0, 10
	xor a6, a6, a7
	add a4, a4, a6
	or a6, t0, t1
	and a6, a6, t2
	and a7, t0, t1
	or a6, a6, a7
	add a4, a4, a6
	lwu a6, 28(a3)
	srliw a5, a6, 17
	slliw a7, a6, 15
	xor a5, a5, a7
	srliw a7, a6, 19
	xor a5, a5, a7
	slliw a7, a6, 13
	xor a5, a5, a7
	srliw a7, a6, 10
	xor a5, a5, a7
	lwu a7, 8(a3)
	add a5, a5, a7
	lwu a6, 40(a3)
	srliw a7, a6, 7
	slliw s0, a6, 25
	xor a7, a7, s0
	srliw s0, a6, 18
	xor a7, a7, s0
	slliw s0, a6, 14
	xor a7, a7, s0
	srliw s0, a6, 3
	xor a7, a7, s0
	add a5, a5, a7
	lwu a7, 36(a3)
	add a5, a5, a7
	sw a5, 36(a3)
	srliw a6, t3, 6
	slliw a7, t3, 26
	xor a6, a6, a7
	srliw a7, t3, 11
	xor a6, a6, a7
	slliw a7, t3, 21
	xor a6, a6, a7
	srliw a7, t3, 25
	xor a6, a6, a7
	slliw a7, t3, 7
	xor a6, a6, a7
	add t6, t6, a6
	xor a6, t4, t5
	and a6, a6, t3
	xor a6, a6, t5
	add t6, t6, a6
	lui a6, 688550
	addiw a6, a6, 1611
	add t6, t6, a6
	add t6, t6, a5
	add t2, t2, t6
	srliw a6, a4, 2
	slliw a7, a4, 30
	xor a6, a6, a7
	srliw a7, a4, 13
	xor a6, a6, a7
	slliw a7, a4, 19
	xor a6, a6, a7
	srliw a7, a4, 22
	xor a6, a6, a7
	slliw a7, a4, 10
	xor a6, a6, a7
	add t6, t6, a6
	or a6, a4, t0
	and a6, a6, t1
	and a7, a4, t0
	or a6, a6, a7
	add t6, t6, a6
	lwu a6, 32(a3)
	srliw a5, a6, 17
	slliw a7, a6, 15
	xor a5, a5, a7
	srliw a7, a6, 19
	xor a5, a5, a7
	slliw a7, a6, 13
	xor a5, a5, a7
	srliw a7, a6, 10
	xor a5, a5, a7
	lwu a7, 12(a3)
	add a5, a5, a7
	lwu a6, 44(a3)
	srliw a7, a6, 7
	slliw s0, a6, 25
	xor a7, a7, s0
	srliw s0, a6, 18
	xor a7, a7, s0
	slliw s0, a6, 14
	xor a7, a7, s0
	srliw s0, a6, 3
	xor a7, a7, s0
	add a5, a5, a7
	lwu a7, 40(a3)
	add a5, a5, a7
	sw a5, 40(a3)
	srliw a6, t2, 6
	slliw a7, t2, 26
	xor a6, a6, a7
	srliw a7, t2, 11
	xor a6, a6, a7
	slliw a7, t2, 21
	xor a6, a6, a7
	srliw a7, t2, 25
	xor a6, a6, a7
	slliw a7, t2, 7
	xor a6, a6, a7
	add t5, t5, a6
	xor a6, t3, t4
	and a6, a6, t2
	xor a6, a6, t4
	add t5, t5, a6
	lui a6, 795833
	addiw a6, a6, -1168
	add t5, t5, a6
	add t5, t5, a5
	add t1, t1, t5
	srliw a6, t6, 2
	slliw a7, t6, 30
	xor a6, a6, a7
	srliw a7, t6, 13
	xor a6, a6, a7
	slliw a7, t6, 19
	xor a6, a6, a7
	srliw a7, t6, 22
	xor a6, a6, a7
	slliw a7, t6, 10
	xor a6, a6, a7
	add t5, t5, a6
	or a6, t6, a4
	and a6, a6, t0
	and a7, t6, a4
	or a6, a6, a7
	add t5, t5, a6
	lwu a6, 36(a3)
	srliw a5, a6, 17
	slliw a7, a6, 15
	xor a5, a5, a7
	srliw a7, a6, 19
	xor a5, a5, a7
	slliw a7, a6, 13
	xor a5, a5, a7
	srliw a7, a6, 10
	xor a5, a5, a7
	lwu a7, 16(a3)
	add a5, a5, a7
	lwu a6, 48(a3)
	srliw a7, a6, 7
	slliw s0, a6, 25
	xor a7, a7, s0
	srliw s0, a6, 18
	xor a7, a7, s0
	slliw s0, a6, 14
	xor a7, a7, s0
	srliw s0, a6, 3
	xor a7, a7, s0
	add a5, a5, a7
	lwu a7, 44(a3)
	add a5, a5, a7
	sw a5, 44(a3)
	srliw a6, t1, 6
	slliw a7, t1, 26
	xor a6, a6, a7
	srliw a7, t1, 11
	xor a6, a6, a7
	slliw a7, t1, 21
	xor a6, a6, a7
	srliw a7, t1, 25
	xor a6, a6, a7
	slliw a7, t1, 7
	xor a6, a6, a7
	add t4, t4, a6
	xor a6, t2, t3
	and a6, a6, t1
	xor a6, a6, t3
	add t4, t4, a6
	lui a6, 816837
	addiw a6, a6, 419
	add t4, t4, a6
	add t4, t4, a5
	add t0, t0, t4
	srliw a6, t5, 2
	slliw a7, t5, 30
	xor a6, a6, a7
	srliw a7, t5, 13
	xor a6, a6, a7
	slliw a7, t5, 19
	xor a6, a6, a7
	srliw a7, t5, 22
	xor a6, a6, a7
	slliw a7, t5, 10
	xor a6, a6, a7
	add t4, t4, a6
	or a6, t5, t6
	and a6, a6, a4
	and a7, t5, t6
	or a6, a6, a7
	add t4, t4, a6
	lwu a6, 40(a3)
	srliw a5, a6, 17
	slliw a7, a6, 15
	xor a5, a5, a7
	srliw a7, a6, 19
	xor a5, a5, a7
	slliw a7, a6, 13
	xor a5, a5, a7
	srliw a7, a6, 10
	xor a5, a5, a7
	lwu a7, 20(a3)
	add a5, a5, a7
	lwu a6, 52(a3)
	srliw a7, a6, 7
	slliw s0, a6, 25
	xor a7, a7, s0
	srliw s0, a6, 18
	xor a7, a7, s0
	slliw s0, a6, 14
	xor a7, a7, s0
	srliw s0, a6, 3
	xor a7, a7, s0
	add a5, a5, a7
	lwu a7, 48(a3)
	add a5, a5, a7
	sw a5, 48(a3)
	srliw a6, t0, 6
	slliw a7, t0, 26
	xor a6, a6, a7
	srliw a7, t0, 11
	xor a6, a6, a7
	slliw a7, t0, 21
	xor a6, a6, a7
	srliw a7, t0, 25
	xor a6, a6, a7
	slliw a7, t0, 7
	xor a6, a6, a7
	add t3, t3, a6
	xor a6, t1, t2
	and a6, a6, t0
	xor a6, a6, t2
	add t3, t3, a6
	lui a6, 858415
	addiw a6, a6, -2023
	add t3, t3, a6
	add t3, t3, a5
	add a4, a4, t3
	srliw a6, t4, 2
	slliw a7, t4, 30
	xor a6, a6, a7
	srliw a7, t4, 13
	xor a6, a6, a7
	slliw a7, t4, 19
	xor a6, a6, a7
	srliw a7, t4, 22
	xor a6, a6, a7
	slliw a7, t4, 10
	xor a6, a6, a7
	add t3, t3, a6
	or a6, t4, t5
	and a6, a6, t6
	and a7, t4, t5
	or a6, a6, a7
	add t3, t3, a6
	lwu a6, 44(a3)
	srliw a5, a6, 17
	slliw a7, a6, 15
	xor a5, a5, a7
	srliw a7, a6, 19
	xor a5, a5, a7
	slliw a7, a6, 13
	xor a5, a5, a7
	srliw a7, a6, 10
	xor a5, a5, a7
	lwu a7, 24(a3)
	add a5, a5, a7
	lwu a6, 56(a3)
	srliw a7, a6, 7
	slliw s0, a6, 25
	xor a7, a7, s0
	srliw s0, a6, 18
	xor a7, a7, s0
	slliw s0, a6, 14
	xor a7, a7, s0
	srliw s0, a6, 3
	xor a7, a7, s0
	add a5, a5, a7
	lwu a7, 52(a3)
	add a5, a5, a7
	sw a5, 52(a3)
	srliw a6, a4, 6
	slliw a7, a4, 26
	xor a6, a6, a7
	srliw a7, a4, 11
	xor a6, a6, a7
	slliw a7, a4, 21
	xor a6, a6, a7
	srliw a7, a4, 25
	xor a6, a6, a7
	slliw a7, a4, 7
	xor a6, a6, a7
	add t2, t2, a6
	xor a6, t0, t1
	and a6, a6, a4
	xor a6, a6, t1
	add t2, t2, a6
	lui a6, 878992
	addiw a6, a6, 1572
	add t2, t2, a6
	add t2, t2, a5
	add t6, t6, t2
	srliw a6, t3, 2
	slliw a7, t3, 30
	xor a6, a6, a7
	srliw a7, t3, 13
	xor a6, a6, a7
	slliw a7, t3, 19
	xor a6, a6, a7
	srliw a7, t3, 22
	xor a6, a6, a7
	slliw a7, t3, 10
	xor a6, a6, a7
	add t2, t2, a6
	or a6, t3, t4
	and a6, a6, t5
	and a7, t3, t4
	or a6, a6, a7
	add t2, t2, a6
	lwu a6, 48(a3)
	srliw a5, a6, 17
	slliw a7, a6, 15
	xor a5, a5, a7
	srliw a7, a6, 19
	xor a5, a5, a7
	slliw a7, a6, 13
	xor a5, a5, a7
	srliw a7, a6, 10
	xor a5, a5, a7
	lwu a7, 28(a3)
	add a5, a5, a7
	lwu a6, 60(a3)
	srliw a7, a6, 7
	slliw s0, a6, 25
	xor a7, a7, s0
	srliw s0, a6, 18
	xor a7, a7, s0
	slliw s0, a6, 14
	xor a7, a7, s0
	srliw s0, a6, 3
	xor a7, a7, s0
	add a5, a5, a7
	lwu a7, 56(a3)
	add a5, a5, a7
	sw a5, 56(a3)
	srliw a6, t6, 6
	slliw a7, t6, 26
	xor a6, a6, a7
	srliw a7, t6, 11
	xor a6, a6, a7
	slliw a7, t6, 21
	xor a6, a6, a7
	srliw a7, t6, 25
	xor a6, a6, a7
	slliw a7, t6, 7
	xor a6, a6, a7
	add t1, t1, a6
	xor a6, a4, t0
	and a6, a6, t6
	xor a6, a6, t0
	add t1, t1, a6
	lui a6, 999651
	addiw a6, a6, 1413
	add t1, t1, a6
	add t1, t1, a5
	add t5, t5, t1
	srliw a6, t2, 2
	slliw a7, t2, 30
	xor a6, a6, a7
	srliw a7, t2, 13
	xor a6, a6, a7
	slliw a7, t2, 19
	xor a6, a6, a7
	srliw a7, t2, 22
	xor a6, a6, a7
	slliw a7, t2, 10
	xor a6, a6, a7
	add t1, t1, a6
	or a6, t2, t3
	and a6, a6, t4
	and a7, t2, t3
	or a6, a6, a7
	add t1, t1, a6
	lwu a6, 52(a3)
	srliw a5, a6, 17
	slliw a7, a6, 15
	xor a5, a5, a7
	srliw a7, a6, 19
	xor a5, a5, a7
	slliw a7, a6, 13
	xor a5, a5, a7
	srliw a7, a6, 10
	xor a5, a5, a7
	lwu a7, 32(a3)
	add a5, a5, a7
	lwu a6, 0(a3)
	srliw a7, a6, 7
	slliw s0, a6, 25
	xor a7, a7, s0
	srliw s0, a6, 18
	xor a7, a7, s0
	slliw s0, a6, 14
	xor a7, a7, s0
	srliw s0, a6, 3
	xor a7, a7, s0
	add a5, a5, a7
	lwu a7, 60(a3)
	add a5, a5, a7
	sw a5, 60(a3)
	srliw a6, t5, 6
	slliw a7, t5, 26
	xor a6, a6, a7
	srliw a7, t5, 11
	xor a6, a6, a7
	slliw a7, t5, 21
	xor a6, a6, a7
	srliw a7, t5, 25
	xor a6, a6, a7
	slliw a7, t5, 7
	xor a6, a6, a7
	add t0, t0, a6
	xor a6, t6, a4
	and a6, a6, t5
	xor a6, a6, a4
	add t0, t0, a6
	lui a6, 67242
	addiw a6, a6, 112
	add t0, t0, a6
	add t0, t0, a5
	add t4, t4, t0
	srliw a6, t1, 2
	slliw a7, t1, 30
	xor a6, a6, a7
	srliw a7, t1, 13
	xor a6, a6, a7
	slliw a7, t1, 19
	xor a6, a6, a7
	srliw a7, t1, 22
	xor a6, a6, a7
	slliw a7, t1, 10
	xor a6, a6, a7
	add t0, t0, a6
	or a6, t1, t2
	and a6, a6, t3
	and a7, t1, t2
	or a6, a6, a7
	add t0, t0, a6
	lwu a6, 56(a3)
	srliw a5, a6, 17
	slliw a7, a6, 15
	xor a5, a5, a7
	srliw a7, a6, 19
	xor a5, a5, a7
	slliw a7, a6, 13
	xor a5, a5, a7
	srliw a7, a6, 10
	xor a5, a5, a7
	lwu a7, 36(a3)
	add a5, a5, a7
	lwu a6, 4(a3)
	srliw a7, a6, 7
	slliw s0, a6, 25
	xor a7, a7, s0
	srliw s0, a6, 18
	xor a7, a7, s0
	slliw s0, a6, 14
	xor a7, a7, s0
	srliw s0, a6, 3
	xor a7, a7, s0
	add a5, a5, a7
	lwu a7, 0(a3)
	add a5, a5, a7
	sw a5, 0(a3)
	srliw a6, t4, 6
	slliw a7, t4, 26
	xor a6, a6, a7
	srliw a7, t4, 11
	xor a6, a6, a7
	slliw a7, t4, 21
	xor a6, a6, a7
	srliw a7, t4, 25
	xor a6, a6, a7
	slliw a7, t4, 7
	xor a6, a6, a7
	add a4, a4, a6
	xor a6, t5, t6
	and a6, a6, t4
	xor a6, a6, t6
	add a4, a4, a6
	lui a6, 105036
	addiw a6, a6, 278
	add a4, a4, a6
	add a4, a4, a5
	add t3, t3, a4
	srliw a6, t0, 2
	slliw a7, t0, 30
	xor a6, a6, a7
	srliw a7, t0, 13
	xor a6, a6, a7
	slliw a7, t0, 19
	xor a6, a6, a7
	srliw a7, t0, 22
	xor a6, a6, a7
	slliw a7, t0, 10
	xor a6, a6, a7
	add a4, a4, a6
	or a6, t0, t1
	and a6, a6, t2
	and a7, t0, t1
	or a6, a6, a7
	add a4, a4, a6
	lwu a6, 60(a3)
	srliw a5, a6, 17
	slliw a7, a6, 15
	xor a5, a5, a7
	srliw a7, a6, 19
	xor a5, a5, a7
	slliw a7, a6, 13
	xor a5, a5, a7
	srliw a7, a6, 10
	xor a5, a5, a7
	lwu a7, 40(a3)
	add a5, a5, a7
	lwu a6, 8(a3)
	srliw a7, a6, 7
	slliw s0, a6, 25
	xor a7, a7, s0
	srliw s0, a6, 18
	xor a7, a7, s0
	slliw s0, a6, 14
	xor a7, a7, s0
	srliw s0, a6, 3
	xor a7, a7, s0
	add a5, a5, a7
	lwu a7, 4(a3)
	add a5, a5, a7
	sw a5, 4(a3)
	srliw a6, t3, 6
	slliw a7, t3, 26
	xor a6, a6, a7
	srliw a7, t3, 11
	xor a6, a6, a7
	slliw a7, t3, 21
	xor a6, a6, a7
	srliw a7, t3, 25
	xor a6, a6, a7
	slliw a7, t3, 7
	xor a6, a6, a7
	add t6, t6, a6
	xor a6, t4, t5
	and a6, a6, t3
	xor a6, a6, t5
	add t6, t6, a6
	lui a6, 123767
	addiw a6, a6, -1016
	add t6, t6, a6
	add t6, t6, a5
	add t2, t2, t6
	srliw a6, a4, 2
	slliw a7, a4, 30
	xor a6, a6, a7
	srliw a7, a4, 13
	xor a6, a6, a7
	slliw a7, a4, 19
	xor a6, a6, a7
	srliw a7, a4, 22
	xor a6, a6, a7
	slliw a7, a4, 10
	xor a6, a6, a7
	add t6, t6, a6
	or a6, a4, t0
	and a6, a6, t1
	and a7, a4, t0
	or a6, a6, a7
	add t6, t6, a6
	lwu a6, 0(a3)
	srliw a5, a6, 17
	slliw a7, a6, 15
	xor a5, a5, a7
	srliw a7, a6, 19
	xor a5, a5, a7
	slliw a7, a6, 13
	xor a5, a5, a7
	srliw a7, a6, 10
	xor a5, a5, a7
	lwu a7, 44(a3)
	add a5, a5, a7
	lwu a6, 12(a3)
	srliw a7, a6, 7
	slliw s0, a6, 25
	xor a7, a7, s0
	srliw s0, a6, 18
	xor a7, a7, s0
	slliw s0, a6, 14
	xor a7, a7, s0
	srliw s0, a6, 3
	xor a7, a7, s0
	add a5, a5, a7
	lwu a7, 8(a3)
	add a5, a5, a7
	sw a5, 8(a3)
	srliw a6, t2, 6
	slliw a7, t2, 26
	xor a6, a6, a7
	srliw a7, t2, 11
	xor a6, a6, a7
	slliw a7, t2, 21
	xor a6, a6, a7
	srliw a7, t2, 25
	xor a6, a6, a7
	slliw a7, t2, 7
	xor a6, a6, a7
	add t5, t5, a6
	xor a6, t3, t4
	and a6, a6, t2
	xor a6, a6, t4
	add t5, t5, a6
	lui a6, 160903
	addiw a6, a6, 1868
	add t5, t5, a6
	add t5, t5, a5
	add t1, t1, t5
	srliw a6, t6, 2
	slliw a7, t6, 30
	xor a6, a6, a7
	srliw a7, t6, 13
	xor a6, a6, a7
	slliw a7, t6, 19
	xor a6, a6, a7
	srliw a7, t6, 22
	xor a6, a6, a7
	slliw a7, t6, 10
	xor a6, a6, a7
	add t5, t5, a6
	or a6, t6, a4
	and a6, a6, t0
	and a7, t6, a4
	or a6, a6, a7
	add t5, t5, a6
	lwu a6, 4(a3)
	srliw a5, a6, 17
	slliw a7, a6, 15
	xor a5, a5, a7
	srliw a7, a6, 19
	xor a5, a5, a7
	slliw a7, a6, 13
	xor a5, a5, a7
	srliw a7, a6, 10
	xor a5, a5, a7
	lwu a7, 48(a3)
	add a5, a5, a7
	lwu a6, 16(a3)
	srliw a7, a6, 7
	slliw s0, a6, 25
	xor a7, a7, s0
	srliw s0, a6, 18
	xor a7, a7, s0
	slliw s0, a6, 14
	xor a7, a7, s0
	srliw s0, a6, 3
	xor a7, a7, s0
	add a5, a5, a7
	lwu a7, 12(a3)
	add a5, a5, a7
	sw a5, 12(a3)
	srliw a6, t1, 6
	slliw a7, t1, 26
	xor a6, a6, a7
	srliw a7, t1, 11
	xor a6, a6, a7
	slliw a7, t1, 21
	xor a6, a6, a7
	srliw a7, t1, 25
	xor a6, a6, a7
	slliw a7, t1, 7
	xor a6, a6, a7
	add t4, t4, a6
	xor a6, t2, t3
	and a6, a6, t1
	xor a6, a6, t3
	add t4, t4, a6
	lui a6, 215820
	addiw a6, a6, -843
	add t4, t4, a6
	add t4, t4, a5
	add t0, t0, t4
	srliw a6, t5, 2
	slliw a7, t5, 30
	xor a6, a6, a7
	srliw a7, t5, 13
	xor a6, a6, a7
	slliw a7, t5, 19
	xor a6, a6, a7
	srliw a7, t5, 22
	xor a6, a6, a7
	slliw a7, t5, 10
	xor a6, a6, a7
	add t4, t4, a6
	or a6, t5, t6
	and a6, a6, a4
	and a7, t5, t6
	or a6, a6, a7
	add t4, t4, a6
	lwu a6, 8(a3)
	srliw a5, a6, 17
	slliw a7, a6, 15
	xor a5, a5, a7
	srliw a7, a6, 19
	xor a5, a5, a7
	slliw a7, a6, 13
	xor a5, a5, a7
	srliw a7, a6, 10
	xor a5, a5, a7
	lwu a7, 52(a3)
	add a5, a5, a7
	lwu a6, 20(a3)
	srliw a7, a6, 7
	slliw s0, a6, 25
	xor a7, a7, s0
	srliw s0, a6, 18
	xor a7, a7, s0
	slliw s0, a6, 14
	xor a7, a7, s0
	srliw s0, a6, 3
	xor a7, a7, s0
	add a5, a5, a7
	lwu a7, 16(a3)
	add a5, a5, a7
	sw a5, 16(a3)
	srliw a6, t0, 6
	slliw a7, t0, 26
	xor a6, a6, a7
	srliw a7, t0, 11
	xor a6, a6, a7
	slliw a7, t0, 21
	xor a6, a6, a7
	srliw a7, t0, 25
	xor a6, a6, a7
	slliw a7, t0, 7
	xor a6, a6, a7
	add t3, t3, a6
	xor a6, t1, t2
	and a6, a6, t0
	xor a6, a6, t2
	add t3, t3, a6
	lui a6, 233921
	addiw a6, a6, -845
	add t3, t3, a6
	add t3, t3, a5
	add a4, a4, t3
	srliw a6, t4, 2
	slliw a7, t4, 30
	xor a6, a6, a7
	srliw a7, t4, 13
	xor a6, a6, a7
	slliw a7, t4, 19
	xor a6, a6, a7
	srliw a7, t4, 22
	xor a6, a6, a7
	slliw a7, t4, 10
	xor a6, a6, a7
	add t3, t3, a6
	or a6, t4, t5
	and a6, a6, t6
	and a7, t4, t5
	or a6, a6, a7
	add t3, t3, a6
	lwu a6, 12(a3)
	srliw a5, a6, 17
	slliw a7, a6, 15
	xor a5, a5, a7
	srliw a7, a6, 19
	xor a5, a5, a7
	slliw a7, a6, 13
	xor a5, a5, a7
	srliw a7, a6, 10
	xor a5, a5, a7
	lwu a7, 56(a3)
	add a5, a5, a7
	lwu a6, 24(a3)
	srliw a7, a6, 7
	slliw s0, a6, 25
	xor a7, a7, s0
	srliw s0, a6, 18
	xor a7, a7, s0
	slliw s0, a6, 14
	xor a7, a7, s0
	srliw s0, a6, 3
	xor a7, a7, s0
	add a5, a5, a7
	lwu a7, 20(a3)
	add a5, a5, a7
	sw a5, 20(a3)
	srliw a6, a4, 6
	slliw a7, a4, 26
	xor a6, a6, a7
	srliw a7, a4, 11
	xor a6, a6, a7
	slliw a7, a4, 21
	xor a6, a6, a7
	srliw a7, a4, 25
	xor a6, a6, a7
	slliw a7, a4, 7
	xor a6, a6, a7
	add t2, t2, a6
	xor a6, t0, t1
	and a6, a6, a4
	xor a6, a6, t1
	add t2, t2, a6
	lui a6, 322955
	addiw a6, a6, -1462
	add t2, t2, a6
	add t2, t2, a5
	add t6, t6, t2
	srliw a6, t3, 2
	slliw a7, t3, 30
	xor a6, a6, a7
	srliw a7, t3, 13
	xor a6, a6, a7
	slliw a7, t3, 19
	xor a6, a6, a7
	srliw a7, t3, 22
	xor a6, a6, a7
	slliw a7, t3, 10
	xor a6, a6, a7
	add t2, t2, a6
	or a6, t3, t4
	and a6, a6, t5
	and a7, t3, t4
	or a6, a6, a7
	add t2, t2, a6
	lwu a6, 16(a3)
	srliw a5, a6, 17
	slliw a7, a6, 15
	xor a5, a5, a7
	srliw a7, a6, 19
	xor a5, a5, a7
	slliw a7, a6, 13
	xor a5, a5, a7
	srliw a7, a6, 10
	xor a5, a5, a7
	lwu a7, 60(a3)
	add a5, a5, a7
	lwu a6, 28(a3)
	srliw a7, a6, 7
	slliw s0, a6, 25
	xor a7, a7, s0
	srliw s0, a6, 18
	xor a7, a7, s0
	slliw s0, a6, 14
	xor a7, a7, s0
	srliw s0, a6, 3
	xor a7, a7, s0
	add a5, a5, a7
	lwu a7, 24(a3)
	add a5, a5, a7
	sw a5, 24(a3)
	srliw a6, t6, 6
	slliw a7, t6, 26
	xor a6, a6, a7
	srliw a7, t6, 11
	xor a6, a6, a7
	slliw a7, t6, 21
	xor a6, a6, a7
	srliw a7, t6, 25
	xor a6, a6, a7
	slliw a7, t6, 7
	xor a6, a6, a7
	add t1, t1, a6
	xor a6, a4, t0
	and a6, a6, t6
	xor a6, a6, t0
	add t1, t1, a6
	lui a6, 375245
	addiw a6, a6, -1457
	add t1, t1, a6
	add t1, t1, a5
	add t5, t5, t1
	srliw a6, t2, 2
	slliw a7, t2, 30
	xor a6, a6, a7
	srliw a7, t2, 13
	xor a6, a6, a7
	slliw a7, t2, 19
	xor a6, a6, a7
	srliw a7, t2, 22
	xor a6, a6, a7
	slliw a7, t2, 10
	xor a6, a6, a7
	add t1, t1, a6
	or a6, t2, t3
	and a6, a6, t4
	and a7, t2, t3
	or a6, a6, a7
	add t1, t1, a6
	lwu a6, 20(a3)
	srliw a5, a6, 17
	slliw a7, a6, 15
	xor a5, a5, a7
	srliw a7, a6, 19
	xor a5, a5, a7
	slliw a7, a6, 13
	xor a5, a5, a7
	srliw a7, a6, 10
	xor a5, a5, a7
	lwu a7, 0(a3)
	add a5, a5, a7
	lwu a6, 32(a3)
	srliw a7, a6, 7
	slliw s0, a6, 25
	xor a7, a7, s0
	srliw s0, a6, 18
	xor a7, a7, s0
	slliw s0, a6, 14
	xor a7, a7, s0
	srliw s0, a6, 3
	xor a7, a7, s0
	add a5, a5, a7
	lwu a7, 28(a3)
	add a5, a5, a7
	sw a5, 28(a3)
	srliw a6, t5, 6
	slliw a7, t5, 26
	xor a6, a6, a7
	srliw a7, t5, 11
	xor a6, a6, a7
	slliw a7, t5, 21
	xor a6, a6, a7
	srliw a7, t5, 25
	xor a6, a6, a7
	slliw a7, t5, 7
	xor a6, a6, a7
	add t0, t0, a6
	xor a6, t6, a4
	and a6, a6, t5
	xor a6, a6, a4
	add t0, t0, a6
	lui a6, 426727
	addiw a6, a6, -13
	add t0, t0, a6
	add t0, t0, a5
	add t4, t4, t0
	srliw a6, t1, 2
	slliw a7, t1, 30
	xor a6, a6, a7
	srliw a7, t1, 13
	xor a6, a6, a7
	slliw a7, t1, 19
	xor a6, a6, a7
	srliw a7, t1, 22
	xor a6, a6, a7
	slliw a7, t1, 10
	xor a6, a6, a7
	add t0, t0, a6
	or a6, t1, t2
	and a6, a6, t3
	and a7, t1, t2
	or a6, a6, a7
	add t0, t0, a6
	lwu a6, 24(a3)
	srliw a5, a6, 17
	slliw a7, a6, 15
	xor a5, a5, a7
	srliw a7, a6, 19
	xor a5, a5, a7
	slliw a7, a6, 13
	xor a5, a5, a7
	srliw a7, a6, 10
	xor a5, a5, a7
	lwu a7, 4(a3)
	add a5, a5, a7
	lwu a6, 36(a3)
	srliw a7, a6, 7
	slliw s0, a6, 25
	xor a7, a7, s0
	srliw s0, a6, 18
	xor a7, a7, s0
	slliw s0, a6, 14
	xor a7, a7, s0
	srliw s0, a6, 3
	xor a7, a7, s0
	add a5, a5, a7
	lwu a7, 32(a3)
	add a5, a5, a7
	sw a5, 32(a3)
	srliw a6, t4, 6
	slliw a7, t4, 26
	xor a6, a6, a7
	srliw a7, t4, 11
	xor a6, a6, a7
	slliw a7, t4, 21
	xor a6, a6, a7
	srliw a7, t4, 25
	xor a6, a6, a7
	slliw a7, t4, 7
	xor a6, a6, a7
	add a4, a4, a6
	xor a6, t5, t6
	and a6, a6, t4
	xor a6, a6, t6
	add a4, a4, a6
	lui a6, 477432
	addiw a6, a6, 750
	add a4, a4, a6
	add a4, a4, a5
	add t3, t3, a4
	srliw a6, t0, 2
	slliw a7, t0, 30
	xor a6, a6, a7
	srliw a7, t0, 13
	xor a6, a6, a7
	slliw a7, t0, 19
	xor a6, a6, a7
	srliw a7, t0, 22
	xor a6, a6, a7
	slliw a7, t0, 10
	xor a6, a6, a7
	add a4, a4, a6
	or a6, t0, t1
	and a6, a6, t2
	and a7, t0, t1
	or a6, a6, a7
	add a4, a4, a6
	lwu a6, 28(a3)
	srliw a5, a6, 17
	slliw a7, a6, 15
	xor a5, a5, a7
	srliw a7, a6, 19
	xor a5, a5, a7
	slliw a7, a6, 13
	xor a5, a5, a7
	srliw a7, a6, 10
	xor a5, a5, a7
	lwu a7, 8(a3)
	add a5, a5, a7
	lwu a6, 40(a3)
	srliw a7, a6, 7
	slliw s0, a6, 25
	xor a7, a7, s0
	srliw s0, a6, 18
	xor a7, a7, s0
	slliw s0, a6, 14
	xor a7, a7, s0
	srliw s0, a6, 3
	xor a7, a7, s0
	add a5, a5, a7
	lwu a7, 36(a3)
	add a5, a5, a7
	sw a5, 36(a3)
	srliw a6, t3, 6
	slliw a7, t3, 26
	xor a6, a6, a7
	srliw a7, t3, 11
	xor a6, a6, a7
	slliw a7, t3, 21
	xor a6, a6, a7
	srliw a7, t3, 25
	xor a6, a6, a7
	slliw a7, t3, 7
	xor a6, a6, a7
	add t6, t6, a6
	xor a6, t4, t5
	and a6, a6, t3
	xor a6, a6, t5
	add t6, t6, a6
	lui a6, 494166
	addiw a6, a6, 879
	add t6, t6, a6
	add t6, t6, a5
	add t2, t2, t6
	srliw a6, a4, 2
	slliw a7, a4, 30
	xor a6, a6, a7
	srliw a7, a4, 13
	xor a6, a6, a7
	slliw a7, a4, 19
	xor a6, a6, a7
	srliw a7, a4, 22
	xor a6, a6, a7
	slliw a7, a4, 10
	xor a6, a6, a7
	add t6, t6, a6
	or a6, a4, t0
	and a6, a6, t1
	and a7, a4, t0
	or a6, a6, a7
	add t6, t6, a6
	lwu a6, 32(a3)
	srliw a5, a6, 17
	slliw a7, a6, 15
	xor a5, a5, a7
	srliw a7, a6, 19
	xor a5, a5, a7
	slliw a7, a6, 13
	xor a5, a5, a7
	srliw a7, a6, 10
	xor a5, a5, a7
	lwu a7, 12(a3)
	add a5, a5, a7
	lwu a6, 44(a3)
	srliw a7, a6, 7
	slliw s0, a6, 25
	xor a7, a7, s0
	srliw s0, a6, 18
	xor a7, a7, s0
	slliw s0, a6, 14
	xor a7, a7, s0
	srliw s0, a6, 3
	xor a7, a7, s0
	add a5, a5, a7
	lwu a7, 40(a3)
	add a5, a5, a7
	sw a5, 40(a3)
	srliw a6, t2, 6
	slliw a7, t2, 26
	xor a6, a6, a7
	srliw a7, t2, 11
	xor a6, a6, a7
	slliw a7, t2, 21
	xor a6, a6, a7
	srliw a7, t2, 25
	xor a6, a6, a7
	slliw a7, t2, 7
	xor a6, a6, a7
	add t5, t5, a6
	xor a6, t3, t4
	and a6, a6, t2
	xor a6, a6, t4
	add t5, t5, a6
	lui a6, 543880
	addiw a6, a6, -2028
	add t5, t5, a6
	add t5, t5, a5
	add t1, t1, t5
	srliw a6, t6, 2
	slliw a7, t6, 30
	xor a6, a6, a7
	srliw a7, t6, 13
	xor a6, a6, a7
	slliw a7, t6, 19
	xor a6, a6, a7
	srliw a7, t6, 22
	xor a6, a6, a7
	slliw a7, t6, 10
	xor a6, a6, a7
	add t5, t5, a6
	or a6, t6, a4
	and a6, a6, t0
	and a7, t6, a4
	or a6, a6, a7
	add t5, t5, a6
	lwu a6, 36(a3)
	srliw a5, a6, 17
	slliw a7, a6, 15
	xor a5, a5, a7
	srliw a7, a6, 19
	xor a5, a5, a7
	slliw a7, a6, 13
	xor a5, a5, a7
	srliw a7, a6, 10
	xor a5, a5, a7
	lwu a7, 16(a3)
	add a5, a5, a7
	lwu a6, 48(a3)
	srliw a7, a6, 7
	slliw s0, a6, 25
	xor a7, a7, s0
	srliw s0, a6, 18
	xor a7, a7, s0
	slliw s0, a6, 14
	xor a7, a7, s0
	srliw s0, a6, 3
	xor a7, a7, s0
	add a5, a5, a7
	lwu a7, 44(a3)
	add a5, a5, a7
	sw a5, 44(a3)
	srliw a6, t1, 6
	slliw a7, t1, 26
	xor a6, a6, a7
	srliw a7, t1, 11
	xor a6, a6, a7
	slliw a7, t1, 21
	xor a6, a6, a7
	srliw a7, t1, 25
	xor a6, a6, a7
	slliw a7, t1, 7
	xor a6, a6, a7
	add t4, t4, a6
	xor a6, t2, t3
	and a6, a6, t1
	xor a6, a6, t3
	add t4, t4, a6
	lui a6, 576624
	addiw a6, a6, 520
	add t4, t4, a6
	add t4, t4, a5
	add t0, t0, t4
	srliw a6, t5, 2
	slliw a7, t5, 30
	xor a6, a6, a7
	srliw a7, t5, 13
	xor a6, a6, a7
	slliw a7, t5, 19
	xor a6, a6, a7
	srliw a7, t5, 22
	xor a6, a6, a7
	slliw a7, t5, 10
	xor a6, a6, a7
	add t4, t4, a6
	or a6, t5, t6
	and a6, a6, a4
	and a7, t5, t6
	or a6, a6, a7
	add t4, t4, a6
	lwu a6, 40(a3)
	srliw a5, a6, 17
	slliw a7, a6, 15
	xor a5, a5, a7
	srliw a7, a6, 19
	xor a5, a5, a7
	slliw a7, a6, 13
	xor a5, a5, a7
	srliw a7, a6, 10
	xor a5, a5, a7
	lwu a7, 20(a3)
	add a5, a5, a7
	lwu a6, 52(a3)
	srliw a7, a6, 7
	slliw s0, a6, 25
	xor a7, a7, s0
	srliw s0, a6, 18
	xor a7, a7, s0
	slliw s0, a6, 14
	xor a7, a7, s0
	srliw s0, a6, 3
	xor a7, a7, s0
	add a5, a5, a7
	lwu a7, 48(a3)
	add a5, a5, a7
	sw a5, 48(a3)
	srliw a6, t0, 6
	slliw a7, t0, 26
	xor a6, a6, a7
	srliw a7, t0, 11
	xor a6, a6, a7
	slliw a7, t0, 21
	xor a6, a6, a7
	srliw a7, t0, 25
	xor a6, a6, a7
	slliw a7, t0, 7
	xor a6, a6, a7
	add t3, t3, a6
	xor a6, t1, t2
	and a6, a6, t0
	xor a6, a6, t2
	add t3, t3, a6
	lui a6, 592880
	addiw a6, a6, -6
	add t3, t3, a6
	add t3, t3, a5
	add a4, a4, t3
	srliw a6, t4, 2
	slliw a7, t4, 30
	xor a6, a6, a7
	srliw a7, t4, 13
	xor a6, a6, a7
	slliw a7, t4, 19
	xor a6, a6, a7
	srliw a7, t4, 22
	xor a6, a6, a7
	slliw a7, t4, 10
	xor a6, a6, a7
	add t3, t3, a6
	or a6, t4, t5
	and a6, a6, t6
	and a7, t4, t5
	or a6, a6, a7
	add t3, t3, a6
	lwu a6, 44(a3)
	srliw a5, a6, 17
	slliw a7, a6, 15
	xor a5, a5, a7
	srliw a7, a6, 19
	xor a5, a5, a7
	slliw a7, a6, 13
	xor a5, a5, a7
	srliw a7, a6, 10
	xor a5, a5, a7
	lwu a7, 24(a3)
	add a5, a5, a7
	lwu a6, 56(a3)
	srliw a7, a6, 7
	slliw s0, a6, 25
	xor a7, a7, s0
	srliw s0, a6, 18
	xor a7, a7, s0
	slliw s0, a6, 14
	xor a7, a7, s0
	srliw s0, a6, 3
	xor a7, a7, s0
	add a5, a5, a7
	lwu a7, 52(a3)
	add a5, a5, a7
	sw a5, 52(a3)
	srliw a6, a4, 6
	slliw a7, a4, 26
	xor a6, a6, a7
	srliw a7, a4, 11
	xor a6, a6, a7
	slliw a7, a4, 21
	xor a6, a6, a7
	srliw a7, a4, 25
	xor a6, a6, a7
	slliw a7, a4, 7
	xor a6, a6, a7
	add t2, t2, a6
	xor a6, t0, t1
	and a6, a6, a4
	xor a6, a6, t1
	add t2, t2, a6
	lui a6, 673031
	addiw a6, a6, -789
	add t2, t2, a6
	add t2, t2, a5
	add t6, t6, t2
	srliw a6, t3, 2
	slliw a7, t3, 30
	xor a6, a6, a7
	srliw a7, t3, 13
	xor a6, a6, a7
	slliw a7, t3, 19
	xor a6, a6, a7
	srliw a7, t3, 22
	xor a6, a6, a7
	slliw a7, t3, 10
	xor a6, a6, a7
	add t2, t2, a6
	or a6, t3, t4
	and a6, a6, t5
	and a7, t3, t4
	or a6, a6, a7
	add t2, t2, a6
	lwu a6, 48(a3)
	srliw a5, a6, 17
	slliw a7, a6, 15
	xor a5, a5, a7
	srliw a7, a6, 19
	xor a5, a5, a7
	slliw a7, a6, 13
	xor a5, a5, a7
	srliw a7, a6, 10
	xor a5, a5, a7
	lwu a7, 28(a3)
	add a5, a5, a7
	lwu a6, 60(a3)
	srliw a7, a6, 7
	slliw s0, a6, 25
	xor a7, a7, s0
	srliw s0, a6, 18
	xor a7, a7, s0
	slliw s0, a6, 14
	xor a7, a7, s0
	srliw s0, a6, 3
	xor a7, a7, s0
	add a5, a5, a7
	lwu a7, 56(a3)
	add a5, a5, a7
	sw a5, 56(a3)
	srliw a6, t6, 6
	slliw a7, t6, 26
	xor a6, a6, a7
	srliw a7, t6, 11
	xor a6, a6, a7
	slliw a7, t6, 21
	xor a6, a6, a7
	srliw a7, t6, 25
	xor a6, a6, a7
	slliw a7, t6, 7
	xor a6, a6, a7
	add t1, t1, a6
	xor a6, a4, t0
	and a6, a6, t6
	xor a6, a6, t0
	add t1, t1, a6
	lui a6, 782234
	addiw a6, a6, 1015
	add t1, t1, a6
	add t1, t1, a5
	add t5, t5, t1
	srliw a6, t2, 2
	slliw a7, t2, 30
	xor a6, a6, a7
	srliw a7, t2, 13
	xor a6, a6, a7
	slliw a7, t2, 19
	xor a6, a6, a7
	srliw a7, t2, 22
	xor a6, a6, a7
	slliw a7, t2, 10
	xor a6, a6, a7
	add t1, t1, a6
	or a6, t2, t3
	and a6, a6, t4
	and a7, t2, t3
	or a6, a6, a7
	add t1, t1, a6
	lwu a6, 52(a3)
	srliw a5, a6, 17
	slliw a7, a6, 15
	xor a5, a5, a7
	srliw a7, a6, 19
	xor a5, a5, a7
	slliw a7, a6, 13
	xor a5, a5, a7
	srliw a7, a6, 10
	xor a5, a5, a7
	lwu a7, 32(a3)
	add a5, a5, a7
	lwu a6, 0(a3)
	srliw a7, a6, 7
	slliw s0, a6, 25
	xor a7, a7, s0
	srliw s0, a6, 18
	xor a7, a7, s0
	slliw s0, a6, 14
	xor a7, a7, s0
	srliw s0, a6, 3
	xor a7, a7, s0
	add a5, a5, a7
	lwu a7, 60(a3)
	add a5, a5, a7
	sw a5, 60(a3)
	srliw a6, t5, 6
	slliw a7, t5, 26
	xor a6, a6, a7
	srliw a7, t5, 11
	xor a6, a6, a7
	slliw a7, t5, 21
	xor a6, a6, a7
	srliw a7, t5, 25
	xor a6, a6, a7
	slliw a7, t5, 7
	xor a6, a6, a7
	add t0, t0, a6
	xor a6, t6, a4
	and a6, a6, t5
	xor a6, a6, a4
	add t0, t0, a6
	lui a6, 812824
	addiw a6, a6, -1806
	add t0, t0, a6
	add t0, t0, a5
	add t4, t4, t0
	srliw a6, t1, 2
	slliw a7, t1, 30
	xor a6, a6, a7
	srliw a7, t1, 13
	xor a6, a6, a7
	slliw a7, t1, 19
	xor a6, a6, a7
	srliw a7, t1, 22
	xor a6, a6, a7
	slliw a7, t1, 10
	xor a6, a6, a7
	add t0, t0, a6
	or a6, t1, t2
	and a6, a6, t3
	and a7, t1, t2
	or a6, a6, a7
	add t0, t0, a6
	lbu a5, 0(a0)
	lbu a6, 1(a0)
	slli a6, a6, 8
	or a5, a5, a6
	lbu a6, 2(a0)
	slli a6, a6, 16
	or a5, a5, a6
	lbu a6, 3(a0)
	slli a6, a6, 24
	or a5, a5, a6
	add t0, t0, a5
	sb t0, 0(a0)
	srli a5, t0, 8
	sb a5, 1(a0)
	srli a5, t0, 16
	sb a5, 2(a0)
	srli a5, t0, 24
	sb a5, 3(a0)
	lbu a5, 4(a0)
	lbu a6, 5(a0)
	slli a6, a6, 8
	or a5, a5, a6
	lbu a6, 6(a0)
	slli a6, a6, 16
	or a5, a5, a6
	lbu a6, 7(a0)
	slli a6, a6, 24
	or a5, a5, a6
	add t1, t1, a5
	sb t1, 4(a0)
	srli a5, t1, 8
	sb a5, 5(a0)
	srli a5, t1, 16
	sb a5, 6(a0)
	srli a5, t1, 24
	sb a5, 7(a0)
	lbu a5, 8(a0)
	lbu a6, 9(a0)
	slli a6, a6, 8
	or a5, a5, a6
	lbu a6, 10(a0)
	slli a6, a6, 16
	or a5, a5, a6
	lbu a6, 11(a0)
	slli a6, a6, 24
	or a5, a5, a6
	add t2, t2, a5
	sb t2, 8(a0)
	srli a5, t2, 8
	sb a5, 9(a0)
	srli a5, t2, 16
	sb a5, 10(a0)
	srli a5, t2, 24
	sb a5, 11(a0)
	lbu a5, 12(a0)
	lbu a6, 13(a0)
	slli a6, a6, 8
	or a5, a5, a6
	lbu a6, 14(a0)
	slli a6, a6, 16
	or a5, a5, a6
	lbu a6, 15(a0)
	slli a6, a6, 24
	or a5, a5, a6
	add t3, t3, a5
	sb t3, 12(a0)
	srli a5, t3, 8
	sb a5, 13(a0)
	srli a5, t3, 16
	sb a5, 14(a0)
	srli a5, t3, 24
	sb a5, 15(a0)
	lbu a5, 16(a0)
	lbu a6, 17(a0)
	slli a6, a6, 8
	or a5, a5, a6
	lbu a6, 18(a0)
	slli a6, a6, 16
	or a5, a5, a6
	lbu a6, 19(a0)
	slli a6, a6, 24
	or a5, a5, a6
	add t4, t4, a5
	sb t4, 16(a0)
	srli a5, t4, 8
	sb a5, 17(a0)
	srli a5, t4, 16
	sb a5, 18(a0)
	srli a5, t4, 24
	sb a5, 19(a0)
	lbu a5, 20(a0)
	lbu a6, 21(a0)
	slli a6, a6, 8
	or a5, a5, a6
	lbu a6, 22(a0)
	slli a6, a6, 16
	or a5, a5, a6
	lbu a6, 23(a0)
	slli a6, a6, 24
	or a5, a5, a6
	add t5, t5, a5
	sb t5, 20(a0)
	srli a5, t5, 8
	sb a5, 21(a0)
	srli a5, t5, 16
	sb a5, 22(a0)
	srli a5, t5, 24
	sb a5, 23(a0)
	lbu a5, 24(a0)
	lbu a6, 25(a0)
	slli a6, a6, 8
	or a5, a5, a6
	lbu a6, 26(a0)
	slli a6, a6, 16
	or a5, a5, a6
	lbu a6, 27(a0)
	slli a6, a6, 24
	or a5, a5, a6
	add t6, t6, a5
	sb t6, 24(a0)
	srli a5, t6, 8
	sb a5, 25(a0)
	srli a5, t6, 16
	sb a5, 26(a0)
	srli a5, t6, 24
	sb a5, 27(a0)
	lbu a5, 28(a0)
	lbu a6, 29(a0)
	slli a6, a6, 8
	or a5, a5, a6
	lbu a6, 30(a0)
	slli a6, a6, 16
	or a5, a5, a6
	lbu a6, 31(a0)
	slli a6, a6, 24
	or a5, a5, a6
	add a4, a4, a5
	sb a4, 28(a0)
	srli a5, a4, 8
	sb a5, 29(a0)
	srli a5, a4, 16
	sb a5, 30(a0)
	srli a5, a4, 24
	sb a5, 31(a0)
	addi a1, a1, 64
	addi a2, a2, -1
	bnez a2, 22b
	j 21f
20:
21:
	ld s0, 64(a3)
	ret
	.option pop

vg_sha256_init:
	.option push
	.option arch, +m, +c
	lui t0, 434334
	addiw t0, t0, 1639
	sb t0, 0(a0)
	srli t1, t0, 8
	sb t1, 1(a0)
	srli t1, t0, 16
	sb t1, 2(a0)
	srli t1, t0, 24
	sb t1, 3(a0)
	lui t0, 767611
	addiw t0, t0, -379
	sb t0, 4(a0)
	srli t1, t0, 8
	sb t1, 5(a0)
	srli t1, t0, 16
	sb t1, 6(a0)
	srli t1, t0, 24
	sb t1, 7(a0)
	lui t0, 247535
	addiw t0, t0, 882
	sb t0, 8(a0)
	srli t1, t0, 8
	sb t1, 9(a0)
	srli t1, t0, 16
	sb t1, 10(a0)
	srli t1, t0, 24
	sb t1, 11(a0)
	lui t0, 677119
	addiw t0, t0, 1338
	sb t0, 12(a0)
	srli t1, t0, 8
	sb t1, 13(a0)
	srli t1, t0, 16
	sb t1, 14(a0)
	srli t1, t0, 24
	sb t1, 15(a0)
	lui t0, 332005
	addiw t0, t0, 639
	sb t0, 16(a0)
	srli t1, t0, 8
	sb t1, 17(a0)
	srli t1, t0, 16
	sb t1, 18(a0)
	srli t1, t0, 24
	sb t1, 19(a0)
	lui t0, 634967
	addiw t0, t0, -1908
	sb t0, 20(a0)
	srli t1, t0, 8
	sb t1, 21(a0)
	srli t1, t0, 16
	sb t1, 22(a0)
	srli t1, t0, 24
	sb t1, 23(a0)
	lui t0, 129086
	addiw t0, t0, -1621
	sb t0, 24(a0)
	srli t1, t0, 8
	sb t1, 25(a0)
	srli t1, t0, 16
	sb t1, 26(a0)
	srli t1, t0, 24
	sb t1, 27(a0)
	lui t0, 376333
	addiw t0, t0, -743
	sb t0, 28(a0)
	srli t1, t0, 8
	sb t1, 29(a0)
	srli t1, t0, 16
	sb t1, 30(a0)
	srli t1, t0, 24
	sb t1, 31(a0)
	ret
	.option pop

vg_sha256_update:
	.option push
	.option arch, +m, +c
	addi sp, sp, -144
	addi t0, sp, 0
	sd ra, 80(t0)
	sd s1, 88(t0)
	sd s2, 96(t0)
	sd s3, 104(t0)
	sd s4, 112(t0)
	sd s5, 120(t0)
	sd s6, 128(t0)
	addi s1, a0, 0
	addi s2, t0, 0
	addi s3, a2, 0
	addi s4, a3, 0
	andi s5, a1, 63
	beqz s4, 20f
22:
	addi t0, zero, 0
	beqz s5, 23f
	addi t2, zero, 64
	sub t2, t2, s5
	srli t1, s4, 6
	beqz t1, 25f
	j 26f
25:
	add t1, s4, s5
	srli t1, t1, 6
	beqz t1, 27f
	j 28f
27:
	addi t2, s4, 0
28:
26:
	sub s4, s4, t2
29:
	lbu t1, 0(s3)
	add t3, s1, s5
	sb t1, 32(t3)
	addi s3, s3, 1
	addi s5, s5, 1
	addi t2, t2, -1
	bnez t2, 29b
	addi t1, s5, -64
	beqz t1, 210f
	j 211f
210:
	addi a1, s1, 32
	addi s5, zero, 0
	addi t0, zero, 1
211:
	j 24f
23:
	srli t1, s4, 6
	beqz t1, 212f
	addi a1, s3, 0
	addi s3, s3, 64
	addi s4, s4, -64
	addi t0, zero, 1
	j 213f
212:
	addi t2, zero, 64
	sub t2, t2, s5
	srli t1, s4, 6
	beqz t1, 214f
	j 215f
214:
	add t1, s4, s5
	srli t1, t1, 6
	beqz t1, 216f
	j 217f
216:
	addi t2, s4, 0
217:
215:
	sub s4, s4, t2
218:
	lbu t1, 0(s3)
	add t3, s1, s5
	sb t1, 32(t3)
	addi s3, s3, 1
	addi s5, s5, 1
	addi t2, t2, -1
	bnez t2, 218b
	addi t1, s5, -64
	beqz t1, 219f
	j 220f
219:
	addi a1, s1, 32
	addi s5, zero, 0
	addi t0, zero, 1
220:
213:
24:
	beqz t0, 221f
	addi a0, s1, 0
	addi a2, zero, 1
	addi a3, s2, 0
	call {vg_sha256_compress}
	j 222f
221:
222:
	bnez s4, 22b
	j 21f
20:
21:
	ld ra, 80(s2)
	ld s1, 88(s2)
	ld s3, 104(s2)
	ld s4, 112(s2)
	ld s5, 120(s2)
	ld s6, 128(s2)
	ld s2, 96(s2)
	addi sp, sp, 144
	ret
	.option pop

vg_sha256_finalize:
	.option push
	.option arch, +m, +c
	addi sp, sp, -144
	addi t0, sp, 0
	sd ra, 80(t0)
	sd s1, 88(t0)
	sd s2, 96(t0)
	sd s3, 104(t0)
	sd s4, 112(t0)
	sd s5, 120(t0)
	sd s6, 128(t0)
	addi s1, a0, 0
	addi s2, t0, 0
	addi s3, a2, 0
	addi s4, a1, 0
	andi s5, s4, 63
	addi t1, zero, 128
	add t3, s1, s5
	sb t1, 32(t3)
	addi s5, s5, 1
	addi s6, s5, 7
	srli s6, s6, 6
20:
	addi t2, zero, 64
	beqz s6, 21f
	j 22f
21:
	addi t2, zero, 56
22:
	addi t1, zero, 0
	sub t2, t2, s5
	beqz t2, 23f
25:
	add t3, s1, s5
	sb t1, 32(t3)
	addi s5, s5, 1
	addi t2, t2, -1
	bnez t2, 25b
	j 24f
23:
24:
	beqz s6, 26f
	j 27f
26:
	slli t1, s4, 3
	srli t3, t1, 56
	sb t3, 88(s1)
	srli t3, t1, 48
	sb t3, 89(s1)
	srli t3, t1, 40
	sb t3, 90(s1)
	srli t3, t1, 32
	sb t3, 91(s1)
	srli t3, t1, 24
	sb t3, 92(s1)
	srli t3, t1, 16
	sb t3, 93(s1)
	srli t3, t1, 8
	sb t3, 94(s1)
	srli t3, t1, 0
	sb t3, 95(s1)
27:
	addi a1, s1, 32
	addi a0, s1, 0
	addi a2, zero, 1
	addi a3, s2, 0
	call {vg_sha256_compress}
	addi s5, zero, 0
	addi s6, s6, -1
	beqz s6, 20b
	lbu t1, 0(s1)
	lbu t2, 1(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 2(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 3(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 0(s3)
	srli t2, t1, 16
	sb t2, 1(s3)
	srli t2, t1, 8
	sb t2, 2(s3)
	srli t2, t1, 0
	sb t2, 3(s3)
	lbu t1, 4(s1)
	lbu t2, 5(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 6(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 7(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 4(s3)
	srli t2, t1, 16
	sb t2, 5(s3)
	srli t2, t1, 8
	sb t2, 6(s3)
	srli t2, t1, 0
	sb t2, 7(s3)
	lbu t1, 8(s1)
	lbu t2, 9(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 10(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 11(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 8(s3)
	srli t2, t1, 16
	sb t2, 9(s3)
	srli t2, t1, 8
	sb t2, 10(s3)
	srli t2, t1, 0
	sb t2, 11(s3)
	lbu t1, 12(s1)
	lbu t2, 13(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 14(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 15(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 12(s3)
	srli t2, t1, 16
	sb t2, 13(s3)
	srli t2, t1, 8
	sb t2, 14(s3)
	srli t2, t1, 0
	sb t2, 15(s3)
	lbu t1, 16(s1)
	lbu t2, 17(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 18(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 19(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 16(s3)
	srli t2, t1, 16
	sb t2, 17(s3)
	srli t2, t1, 8
	sb t2, 18(s3)
	srli t2, t1, 0
	sb t2, 19(s3)
	lbu t1, 20(s1)
	lbu t2, 21(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 22(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 23(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 20(s3)
	srli t2, t1, 16
	sb t2, 21(s3)
	srli t2, t1, 8
	sb t2, 22(s3)
	srli t2, t1, 0
	sb t2, 23(s3)
	lbu t1, 24(s1)
	lbu t2, 25(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 26(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 27(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 24(s3)
	srli t2, t1, 16
	sb t2, 25(s3)
	srli t2, t1, 8
	sb t2, 26(s3)
	srli t2, t1, 0
	sb t2, 27(s3)
	lbu t1, 28(s1)
	lbu t2, 29(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 30(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 31(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 28(s3)
	srli t2, t1, 16
	sb t2, 29(s3)
	srli t2, t1, 8
	sb t2, 30(s3)
	srli t2, t1, 0
	sb t2, 31(s3)
	ld ra, 80(s2)
	ld s1, 88(s2)
	ld s3, 104(s2)
	ld s4, 112(s2)
	ld s5, 120(s2)
	ld s6, 128(s2)
	ld s2, 96(s2)
	addi sp, sp, 144
	ret
	.option pop
