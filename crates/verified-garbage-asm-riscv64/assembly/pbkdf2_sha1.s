// The functions of `src/pbkdf2_sha1.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_pbkdf2_hmac_sha1_iterate:
	.option push
	.option arch, +m, +c
	slli a2, a2, 32
	srli a2, a2, 32
	addi a4, a4, 7
	andi a4, a4, -8
	sd ra, 0(a4)
	sd s0, 8(a4)
	sd s1, 16(a4)
	sd s2, 24(a4)
	sd s3, 32(a4)
	sd s4, 40(a4)
	sd s5, 48(a4)
	sd s6, 56(a4)
	sd s7, 64(a4)
	sd s8, 72(a4)
	sd s9, 80(a4)
	sd s10, 88(a4)
	sd s11, 96(a4)
	lbu a6, 0(a0)
	lbu a5, 1(a0)
	slli a5, a5, 8
	or a6, a6, a5
	lbu a5, 2(a0)
	slli a5, a5, 16
	or a6, a6, a5
	lbu a5, 3(a0)
	slli a5, a5, 24
	or a6, a6, a5
	sw a6, 104(a4)
	lbu a6, 4(a0)
	lbu a5, 5(a0)
	slli a5, a5, 8
	or a6, a6, a5
	lbu a5, 6(a0)
	slli a5, a5, 16
	or a6, a6, a5
	lbu a5, 7(a0)
	slli a5, a5, 24
	or a6, a6, a5
	sw a6, 108(a4)
	lbu a6, 8(a0)
	lbu a5, 9(a0)
	slli a5, a5, 8
	or a6, a6, a5
	lbu a5, 10(a0)
	slli a5, a5, 16
	or a6, a6, a5
	lbu a5, 11(a0)
	slli a5, a5, 24
	or a6, a6, a5
	sw a6, 112(a4)
	lbu a6, 12(a0)
	lbu a5, 13(a0)
	slli a5, a5, 8
	or a6, a6, a5
	lbu a5, 14(a0)
	slli a5, a5, 16
	or a6, a6, a5
	lbu a5, 15(a0)
	slli a5, a5, 24
	or a6, a6, a5
	sw a6, 116(a4)
	lbu a6, 16(a0)
	lbu a5, 17(a0)
	slli a5, a5, 8
	or a6, a6, a5
	lbu a5, 18(a0)
	slli a5, a5, 16
	or a6, a6, a5
	lbu a5, 19(a0)
	slli a5, a5, 24
	or a6, a6, a5
	sw a6, 120(a4)
	lbu a6, 84(a0)
	lbu a5, 85(a0)
	slli a5, a5, 8
	or a6, a6, a5
	lbu a5, 86(a0)
	slli a5, a5, 16
	or a6, a6, a5
	lbu a5, 87(a0)
	slli a5, a5, 24
	or a6, a6, a5
	sw a6, 124(a4)
	lbu a6, 88(a0)
	lbu a5, 89(a0)
	slli a5, a5, 8
	or a6, a6, a5
	lbu a5, 90(a0)
	slli a5, a5, 16
	or a6, a6, a5
	lbu a5, 91(a0)
	slli a5, a5, 24
	or a6, a6, a5
	sw a6, 128(a4)
	lbu a6, 92(a0)
	lbu a5, 93(a0)
	slli a5, a5, 8
	or a6, a6, a5
	lbu a5, 94(a0)
	slli a5, a5, 16
	or a6, a6, a5
	lbu a5, 95(a0)
	slli a5, a5, 24
	or a6, a6, a5
	sw a6, 132(a4)
	lbu a6, 96(a0)
	lbu a5, 97(a0)
	slli a5, a5, 8
	or a6, a6, a5
	lbu a5, 98(a0)
	slli a5, a5, 16
	or a6, a6, a5
	lbu a5, 99(a0)
	slli a5, a5, 24
	or a6, a6, a5
	sw a6, 136(a4)
	lbu a6, 100(a0)
	lbu a5, 101(a0)
	slli a5, a5, 8
	or a6, a6, a5
	lbu a5, 102(a0)
	slli a5, a5, 16
	or a6, a6, a5
	lbu a5, 103(a0)
	slli a5, a5, 24
	or a6, a6, a5
	sw a6, 140(a4)
	lbu a6, 0(a3)
	slli a6, a6, 24
	lbu a5, 1(a3)
	slli a5, a5, 16
	or a6, a6, a5
	lbu a5, 2(a3)
	slli a5, a5, 8
	or a6, a6, a5
	lbu a5, 3(a3)
	or a6, a6, a5
	sw a6, 144(a4)
	lbu a6, 4(a3)
	slli a6, a6, 24
	lbu a5, 5(a3)
	slli a5, a5, 16
	or a6, a6, a5
	lbu a5, 6(a3)
	slli a5, a5, 8
	or a6, a6, a5
	lbu a5, 7(a3)
	or a6, a6, a5
	sw a6, 148(a4)
	lbu a6, 8(a3)
	slli a6, a6, 24
	lbu a5, 9(a3)
	slli a5, a5, 16
	or a6, a6, a5
	lbu a5, 10(a3)
	slli a5, a5, 8
	or a6, a6, a5
	lbu a5, 11(a3)
	or a6, a6, a5
	sw a6, 152(a4)
	lbu a6, 12(a3)
	slli a6, a6, 24
	lbu a5, 13(a3)
	slli a5, a5, 16
	or a6, a6, a5
	lbu a5, 14(a3)
	slli a5, a5, 8
	or a6, a6, a5
	lbu a5, 15(a3)
	or a6, a6, a5
	sw a6, 156(a4)
	lbu a6, 16(a3)
	slli a6, a6, 24
	lbu a5, 17(a3)
	slli a5, a5, 16
	or a6, a6, a5
	lbu a5, 18(a3)
	slli a5, a5, 8
	or a6, a6, a5
	lbu a5, 19(a3)
	or a6, a6, a5
	sw a6, 160(a4)
	lbu s1, 0(a1)
	slli s1, s1, 24
	lbu a5, 1(a1)
	slli a5, a5, 16
	or s1, s1, a5
	lbu a5, 2(a1)
	slli a5, a5, 8
	or s1, s1, a5
	lbu a5, 3(a1)
	or s1, s1, a5
	lbu s2, 4(a1)
	slli s2, s2, 24
	lbu a5, 5(a1)
	slli a5, a5, 16
	or s2, s2, a5
	lbu a5, 6(a1)
	slli a5, a5, 8
	or s2, s2, a5
	lbu a5, 7(a1)
	or s2, s2, a5
	lbu s3, 8(a1)
	slli s3, s3, 24
	lbu a5, 9(a1)
	slli a5, a5, 16
	or s3, s3, a5
	lbu a5, 10(a1)
	slli a5, a5, 8
	or s3, s3, a5
	lbu a5, 11(a1)
	or s3, s3, a5
	lbu s4, 12(a1)
	slli s4, s4, 24
	lbu a5, 13(a1)
	slli a5, a5, 16
	or s4, s4, a5
	lbu a5, 14(a1)
	slli a5, a5, 8
	or s4, s4, a5
	lbu a5, 15(a1)
	or s4, s4, a5
	lbu s5, 16(a1)
	slli s5, s5, 24
	lbu a5, 17(a1)
	slli a5, a5, 16
	or s5, s5, a5
	lbu a5, 18(a1)
	slli a5, a5, 8
	or s5, s5, a5
	lbu a5, 19(a1)
	or s5, s5, a5
	beqz a2, 20f
22:
	lwu s6, 104(a4)
	lwu s7, 108(a4)
	lwu s8, 112(a4)
	lwu s9, 116(a4)
	lwu s10, 120(a4)
	slli a6, s6, 32
	or s6, s6, a6
	slli a6, s7, 32
	or s7, s7, a6
	lui a5, 370728
	addiw a5, a5, -1639
	add s10, s10, s1
	add s10, s10, a5
	xor a6, s8, s9
	and a6, a6, s7
	xor a6, a6, s9
	add s10, s10, a6
	srli a6, s6, 27
	add s10, s10, a6
	srli s7, s7, 2
	slli s10, s10, 32
	srli a6, s10, 32
	or s10, s10, a6
	add s9, s9, s2
	add s9, s9, a5
	xor a6, s7, s8
	and a6, a6, s6
	xor a6, a6, s8
	add s9, s9, a6
	srli a6, s10, 27
	add s9, s9, a6
	srli s6, s6, 2
	slli s9, s9, 32
	srli a6, s9, 32
	or s9, s9, a6
	add s8, s8, s3
	add s8, s8, a5
	xor a6, s6, s7
	and a6, a6, s10
	xor a6, a6, s7
	add s8, s8, a6
	srli a6, s9, 27
	add s8, s8, a6
	srli s10, s10, 2
	slli s8, s8, 32
	srli a6, s8, 32
	or s8, s8, a6
	add s7, s7, s4
	add s7, s7, a5
	xor a6, s10, s6
	and a6, a6, s9
	xor a6, a6, s6
	add s7, s7, a6
	srli a6, s8, 27
	add s7, s7, a6
	srli s9, s9, 2
	slli s7, s7, 32
	srli a6, s7, 32
	or s7, s7, a6
	add s6, s6, s5
	add s6, s6, a5
	xor a6, s9, s10
	and a6, a6, s8
	xor a6, a6, s10
	add s6, s6, a6
	srli a6, s7, 27
	add s6, s6, a6
	srli s8, s8, 2
	slli s6, s6, 32
	srli a6, s6, 32
	or s6, s6, a6
	lui a6, 895016
	addiw a6, a6, -1639
	add s10, s10, a6
	xor a6, s8, s9
	and a6, a6, s7
	xor a6, a6, s9
	add s10, s10, a6
	srli a6, s6, 27
	add s10, s10, a6
	srli s7, s7, 2
	slli s10, s10, 32
	srli a6, s10, 32
	or s10, s10, a6
	add s9, s9, a5
	xor a6, s7, s8
	and a6, a6, s6
	xor a6, a6, s8
	add s9, s9, a6
	srli a6, s10, 27
	add s9, s9, a6
	srli s6, s6, 2
	slli s9, s9, 32
	srli a6, s9, 32
	or s9, s9, a6
	add s8, s8, a5
	xor a6, s6, s7
	and a6, a6, s10
	xor a6, a6, s7
	add s8, s8, a6
	srli a6, s9, 27
	add s8, s8, a6
	srli s10, s10, 2
	slli s8, s8, 32
	srli a6, s8, 32
	or s8, s8, a6
	add s7, s7, a5
	xor a6, s10, s6
	and a6, a6, s9
	xor a6, a6, s6
	add s7, s7, a6
	srli a6, s8, 27
	add s7, s7, a6
	srli s9, s9, 2
	slli s7, s7, 32
	srli a6, s7, 32
	or s7, s7, a6
	add s6, s6, a5
	xor a6, s9, s10
	and a6, a6, s8
	xor a6, a6, s10
	add s6, s6, a6
	srli a6, s7, 27
	add s6, s6, a6
	srli s8, s8, 2
	slli s6, s6, 32
	srli a6, s6, 32
	or s6, s6, a6
	add s10, s10, a5
	xor a6, s8, s9
	and a6, a6, s7
	xor a6, a6, s9
	add s10, s10, a6
	srli a6, s6, 27
	add s10, s10, a6
	srli s7, s7, 2
	slli s10, s10, 32
	srli a6, s10, 32
	or s10, s10, a6
	add s9, s9, a5
	xor a6, s7, s8
	and a6, a6, s6
	xor a6, a6, s8
	add s9, s9, a6
	srli a6, s10, 27
	add s9, s9, a6
	srli s6, s6, 2
	slli s9, s9, 32
	srli a6, s9, 32
	or s9, s9, a6
	add s8, s8, a5
	xor a6, s6, s7
	and a6, a6, s10
	xor a6, a6, s7
	add s8, s8, a6
	srli a6, s9, 27
	add s8, s8, a6
	srli s10, s10, 2
	slli s8, s8, 32
	srli a6, s8, 32
	or s8, s8, a6
	add s7, s7, a5
	xor a6, s10, s6
	and a6, a6, s9
	xor a6, a6, s6
	add s7, s7, a6
	srli a6, s8, 27
	add s7, s7, a6
	srli s9, s9, 2
	slli s7, s7, 32
	srli a6, s7, 32
	or s7, s7, a6
	add s6, s6, a5
	xor a6, s9, s10
	and a6, a6, s8
	xor a6, a6, s10
	add s6, s6, a6
	srli a6, s7, 27
	add s6, s6, a6
	srli s8, s8, 2
	slli s6, s6, 32
	srli a6, s6, 32
	or s6, s6, a6
	addi s10, s10, 672
	add s10, s10, a5
	xor a6, s8, s9
	and a6, a6, s7
	xor a6, a6, s9
	add s10, s10, a6
	srli a6, s6, 27
	add s10, s10, a6
	srli s7, s7, 2
	slli s10, s10, 32
	srli a6, s10, 32
	or s10, s10, a6
	xor s1, s1, s3
	slliw a6, s1, 1
	srliw s1, s1, 31
	or s1, s1, a6
	add s9, s9, s1
	add s9, s9, a5
	xor a6, s7, s8
	and a6, a6, s6
	xor a6, a6, s8
	add s9, s9, a6
	srli a6, s10, 27
	add s9, s9, a6
	srli s6, s6, 2
	slli s9, s9, 32
	srli a6, s9, 32
	or s9, s9, a6
	xor s2, s2, s4
	slliw a6, s2, 1
	srliw s2, s2, 31
	or s2, s2, a6
	add s8, s8, s2
	add s8, s8, a5
	xor a6, s6, s7
	and a6, a6, s10
	xor a6, a6, s7
	add s8, s8, a6
	srli a6, s9, 27
	add s8, s8, a6
	srli s10, s10, 2
	slli s8, s8, 32
	srli a6, s8, 32
	or s8, s8, a6
	xor s3, s3, s5
	slliw a6, s3, 1
	srliw s3, s3, 31
	or s3, s3, a6
	xori s3, s3, 1344
	add s7, s7, s3
	add s7, s7, a5
	xor a6, s10, s6
	and a6, a6, s9
	xor a6, a6, s6
	add s7, s7, a6
	srli a6, s8, 27
	add s7, s7, a6
	srli s9, s9, 2
	slli s7, s7, 32
	srli a6, s7, 32
	or s7, s7, a6
	xor s4, s4, s1
	slliw a6, s4, 1
	srliw s4, s4, 31
	or s4, s4, a6
	xori s4, s4, 1
	add s6, s6, s4
	add s6, s6, a5
	xor a6, s9, s10
	and a6, a6, s8
	xor a6, a6, s10
	add s6, s6, a6
	srli a6, s7, 27
	add s6, s6, a6
	srli s8, s8, 2
	slli s6, s6, 32
	srli a6, s6, 32
	or s6, s6, a6
	xor s5, s5, s2
	slliw a6, s5, 1
	srliw s5, s5, 31
	or s5, s5, a6
	lui a5, 454047
	addiw a5, a5, -1119
	add s10, s10, s5
	add s10, s10, a5
	xor a6, s7, s8
	xor a6, a6, s9
	add s10, s10, a6
	srli a6, s6, 27
	add s10, s10, a6
	srli s7, s7, 2
	slli s10, s10, 32
	srli a6, s10, 32
	or s10, s10, a6
	slliw a6, s3, 1
	srliw s11, s3, 31
	or s11, s11, a6
	xori s11, s11, 1
	add s9, s9, s11
	add s9, s9, a5
	xor a6, s6, s7
	xor a6, a6, s8
	add s9, s9, a6
	srli a6, s10, 27
	add s9, s9, a6
	srli s6, s6, 2
	slli s9, s9, 32
	srli a6, s9, 32
	or s9, s9, a6
	slliw a6, s4, 1
	srliw s0, s4, 31
	or s0, s0, a6
	add s8, s8, s0
	add s8, s8, a5
	xor a6, s10, s6
	xor a6, a6, s7
	add s8, s8, a6
	srli a6, s9, 27
	add s8, s8, a6
	srli s10, s10, 2
	slli s8, s8, 32
	srli a6, s8, 32
	or s8, s8, a6
	slliw a6, s5, 1
	srliw ra, s5, 31
	or ra, ra, a6
	xori ra, ra, 1344
	add s7, s7, ra
	add s7, s7, a5
	xor a6, s9, s10
	xor a6, a6, s6
	add s7, s7, a6
	srli a6, s8, 27
	add s7, s7, a6
	srli s9, s9, 2
	slli s7, s7, 32
	srli a6, s7, 32
	or s7, s7, a6
	xor t0, s1, s11
	slliw a6, t0, 1
	srliw t0, t0, 31
	or t0, t0, a6
	add s6, s6, t0
	add s6, s6, a5
	xor a6, s8, s9
	xor a6, a6, s10
	add s6, s6, a6
	srli a6, s7, 27
	add s6, s6, a6
	srli s8, s8, 2
	slli s6, s6, 32
	srli a6, s6, 32
	or s6, s6, a6
	xor t1, s2, s0
	slliw a6, t1, 1
	srliw t1, t1, 31
	or t1, t1, a6
	add s10, s10, t1
	add s10, s10, a5
	xor a6, s7, s8
	xor a6, a6, s9
	add s10, s10, a6
	srli a6, s6, 27
	add s10, s10, a6
	srli s7, s7, 2
	slli s10, s10, 32
	srli a6, s10, 32
	or s10, s10, a6
	xor t2, s3, ra
	slliw a6, t2, 1
	srliw t2, t2, 31
	or t2, t2, a6
	add s9, s9, t2
	add s9, s9, a5
	xor a6, s6, s7
	xor a6, a6, s8
	add s9, s9, a6
	srli a6, s10, 27
	add s9, s9, a6
	srli s6, s6, 2
	slli s9, s9, 32
	srli a6, s9, 32
	or s9, s9, a6
	xor t3, s4, t0
	slliw a6, t3, 1
	srliw t3, t3, 31
	or t3, t3, a6
	add s8, s8, t3
	add s8, s8, a5
	xor a6, s10, s6
	xor a6, a6, s7
	add s8, s8, a6
	srli a6, s9, 27
	add s8, s8, a6
	srli s10, s10, 2
	slli s8, s8, 32
	srli a6, s8, 32
	or s8, s8, a6
	xor t4, s5, t1
	slliw a6, t4, 1
	srliw t4, t4, 31
	or t4, t4, a6
	add s7, s7, t4
	add s7, s7, a5
	xor a6, s9, s10
	xor a6, a6, s6
	add s7, s7, a6
	srli a6, s8, 27
	add s7, s7, a6
	srli s9, s9, 2
	slli s7, s7, 32
	srli a6, s7, 32
	or s7, s7, a6
	xor t5, s11, t2
	slliw a6, t5, 1
	srliw t5, t5, 31
	or t5, t5, a6
	xori t5, t5, 1344
	add s6, s6, t5
	add s6, s6, a5
	xor a6, s8, s9
	xor a6, a6, s10
	add s6, s6, a6
	srli a6, s7, 27
	add s6, s6, a6
	srli s8, s8, 2
	slli s6, s6, 32
	srli a6, s6, 32
	or s6, s6, a6
	xor t6, s1, s0
	xor t6, t6, t3
	slliw a6, t6, 1
	srliw t6, t6, 31
	or t6, t6, a6
	add s10, s10, t6
	add s10, s10, a5
	xor a6, s7, s8
	xor a6, a6, s9
	add s10, s10, a6
	srli a6, s6, 27
	add s10, s10, a6
	srli s7, s7, 2
	slli s10, s10, 32
	srli a6, s10, 32
	or s10, s10, a6
	xor a7, s2, ra
	xor a7, a7, t4
	slliw a6, a7, 1
	srliw a7, a7, 31
	or a7, a7, a6
	xori a7, a7, 1344
	add s9, s9, a7
	add s9, s9, a5
	xor a6, s6, s7
	xor a6, a6, s8
	add s9, s9, a6
	srli a6, s10, 27
	add s9, s9, a6
	srli s6, s6, 2
	slli s9, s9, 32
	srli a6, s9, 32
	or s9, s9, a6
	xor s1, s1, s3
	xor s1, s1, t0
	xor s1, s1, t5
	slliw a6, s1, 1
	srliw s1, s1, 31
	or s1, s1, a6
	add s8, s8, s1
	add s8, s8, a5
	xor a6, s10, s6
	xor a6, a6, s7
	add s8, s8, a6
	srli a6, s9, 27
	add s8, s8, a6
	srli s10, s10, 2
	slli s8, s8, 32
	srli a6, s8, 32
	or s8, s8, a6
	xor s2, s2, s4
	xor s2, s2, t1
	xor s2, s2, t6
	slliw a6, s2, 1
	srliw s2, s2, 31
	or s2, s2, a6
	add s7, s7, s2
	add s7, s7, a5
	xor a6, s9, s10
	xor a6, a6, s6
	add s7, s7, a6
	srli a6, s8, 27
	add s7, s7, a6
	srli s9, s9, 2
	slli s7, s7, 32
	srli a6, s7, 32
	or s7, s7, a6
	xor s3, s3, s5
	xor s3, s3, t2
	xor s3, s3, a7
	slliw a6, s3, 1
	srliw s3, s3, 31
	or s3, s3, a6
	add s6, s6, s3
	add s6, s6, a5
	xor a6, s8, s9
	xor a6, a6, s10
	add s6, s6, a6
	srli a6, s7, 27
	add s6, s6, a6
	srli s8, s8, 2
	slli s6, s6, 32
	srli a6, s6, 32
	or s6, s6, a6
	xor s4, s4, s11
	xor s4, s4, t3
	xor s4, s4, s1
	slliw a6, s4, 1
	srliw s4, s4, 31
	or s4, s4, a6
	add s10, s10, s4
	add s10, s10, a5
	xor a6, s7, s8
	xor a6, a6, s9
	add s10, s10, a6
	srli a6, s6, 27
	add s10, s10, a6
	srli s7, s7, 2
	slli s10, s10, 32
	srli a6, s10, 32
	or s10, s10, a6
	xor s5, s5, s0
	xor s5, s5, t4
	xor s5, s5, s2
	slliw a6, s5, 1
	srliw s5, s5, 31
	or s5, s5, a6
	add s9, s9, s5
	add s9, s9, a5
	xor a6, s6, s7
	xor a6, a6, s8
	add s9, s9, a6
	srli a6, s10, 27
	add s9, s9, a6
	srli s6, s6, 2
	slli s9, s9, 32
	srli a6, s9, 32
	or s9, s9, a6
	xor s11, s11, ra
	xor s11, s11, t5
	xor s11, s11, s3
	slliw a6, s11, 1
	srliw s11, s11, 31
	or s11, s11, a6
	add s8, s8, s11
	add s8, s8, a5
	xor a6, s10, s6
	xor a6, a6, s7
	add s8, s8, a6
	srli a6, s9, 27
	add s8, s8, a6
	srli s10, s10, 2
	slli s8, s8, 32
	srli a6, s8, 32
	or s8, s8, a6
	xor s0, s0, t0
	xor s0, s0, t6
	xor s0, s0, s4
	slliw a6, s0, 1
	srliw s0, s0, 31
	or s0, s0, a6
	add s7, s7, s0
	add s7, s7, a5
	xor a6, s9, s10
	xor a6, a6, s6
	add s7, s7, a6
	srli a6, s8, 27
	add s7, s7, a6
	srli s9, s9, 2
	slli s7, s7, 32
	srli a6, s7, 32
	or s7, s7, a6
	xor ra, ra, t1
	xor ra, ra, a7
	xor ra, ra, s5
	slliw a6, ra, 1
	srliw ra, ra, 31
	or ra, ra, a6
	add s6, s6, ra
	add s6, s6, a5
	xor a6, s8, s9
	xor a6, a6, s10
	add s6, s6, a6
	srli a6, s7, 27
	add s6, s6, a6
	srli s8, s8, 2
	slli s6, s6, 32
	srli a6, s6, 32
	or s6, s6, a6
	xor t0, t0, t2
	xor t0, t0, s1
	xor t0, t0, s11
	slliw a6, t0, 1
	srliw t0, t0, 31
	or t0, t0, a6
	lui a5, 586172
	addiw a5, a5, -804
	add s10, s10, t0
	add s10, s10, a5
	and a6, s7, s8
	add s10, s10, a6
	xor a6, s7, s8
	and a6, a6, s9
	add s10, s10, a6
	srli a6, s6, 27
	add s10, s10, a6
	srli s7, s7, 2
	slli s10, s10, 32
	srli a6, s10, 32
	or s10, s10, a6
	xor t1, t1, t3
	xor t1, t1, s2
	xor t1, t1, s0
	slliw a6, t1, 1
	srliw t1, t1, 31
	or t1, t1, a6
	add s9, s9, t1
	add s9, s9, a5
	and a6, s6, s7
	add s9, s9, a6
	xor a6, s6, s7
	and a6, a6, s8
	add s9, s9, a6
	srli a6, s10, 27
	add s9, s9, a6
	srli s6, s6, 2
	slli s9, s9, 32
	srli a6, s9, 32
	or s9, s9, a6
	xor t2, t2, t4
	xor t2, t2, s3
	xor t2, t2, ra
	slliw a6, t2, 1
	srliw t2, t2, 31
	or t2, t2, a6
	add s8, s8, t2
	add s8, s8, a5
	and a6, s10, s6
	add s8, s8, a6
	xor a6, s10, s6
	and a6, a6, s7
	add s8, s8, a6
	srli a6, s9, 27
	add s8, s8, a6
	srli s10, s10, 2
	slli s8, s8, 32
	srli a6, s8, 32
	or s8, s8, a6
	xor t3, t3, t5
	xor t3, t3, s4
	xor t3, t3, t0
	slliw a6, t3, 1
	srliw t3, t3, 31
	or t3, t3, a6
	add s7, s7, t3
	add s7, s7, a5
	and a6, s9, s10
	add s7, s7, a6
	xor a6, s9, s10
	and a6, a6, s6
	add s7, s7, a6
	srli a6, s8, 27
	add s7, s7, a6
	srli s9, s9, 2
	slli s7, s7, 32
	srli a6, s7, 32
	or s7, s7, a6
	xor t4, t4, t6
	xor t4, t4, s5
	xor t4, t4, t1
	slliw a6, t4, 1
	srliw t4, t4, 31
	or t4, t4, a6
	add s6, s6, t4
	add s6, s6, a5
	and a6, s8, s9
	add s6, s6, a6
	xor a6, s8, s9
	and a6, a6, s10
	add s6, s6, a6
	srli a6, s7, 27
	add s6, s6, a6
	srli s8, s8, 2
	slli s6, s6, 32
	srli a6, s6, 32
	or s6, s6, a6
	xor t5, t5, a7
	xor t5, t5, s11
	xor t5, t5, t2
	slliw a6, t5, 1
	srliw t5, t5, 31
	or t5, t5, a6
	add s10, s10, t5
	add s10, s10, a5
	and a6, s7, s8
	add s10, s10, a6
	xor a6, s7, s8
	and a6, a6, s9
	add s10, s10, a6
	srli a6, s6, 27
	add s10, s10, a6
	srli s7, s7, 2
	slli s10, s10, 32
	srli a6, s10, 32
	or s10, s10, a6
	xor t6, t6, s1
	xor t6, t6, s0
	xor t6, t6, t3
	slliw a6, t6, 1
	srliw t6, t6, 31
	or t6, t6, a6
	add s9, s9, t6
	add s9, s9, a5
	and a6, s6, s7
	add s9, s9, a6
	xor a6, s6, s7
	and a6, a6, s8
	add s9, s9, a6
	srli a6, s10, 27
	add s9, s9, a6
	srli s6, s6, 2
	slli s9, s9, 32
	srli a6, s9, 32
	or s9, s9, a6
	xor a7, a7, s2
	xor a7, a7, ra
	xor a7, a7, t4
	slliw a6, a7, 1
	srliw a7, a7, 31
	or a7, a7, a6
	add s8, s8, a7
	add s8, s8, a5
	and a6, s10, s6
	add s8, s8, a6
	xor a6, s10, s6
	and a6, a6, s7
	add s8, s8, a6
	srli a6, s9, 27
	add s8, s8, a6
	srli s10, s10, 2
	slli s8, s8, 32
	srli a6, s8, 32
	or s8, s8, a6
	xor s1, s1, s3
	xor s1, s1, t0
	xor s1, s1, t5
	slliw a6, s1, 1
	srliw s1, s1, 31
	or s1, s1, a6
	add s7, s7, s1
	add s7, s7, a5
	and a6, s9, s10
	add s7, s7, a6
	xor a6, s9, s10
	and a6, a6, s6
	add s7, s7, a6
	srli a6, s8, 27
	add s7, s7, a6
	srli s9, s9, 2
	slli s7, s7, 32
	srli a6, s7, 32
	or s7, s7, a6
	xor s2, s2, s4
	xor s2, s2, t1
	xor s2, s2, t6
	slliw a6, s2, 1
	srliw s2, s2, 31
	or s2, s2, a6
	add s6, s6, s2
	add s6, s6, a5
	and a6, s8, s9
	add s6, s6, a6
	xor a6, s8, s9
	and a6, a6, s10
	add s6, s6, a6
	srli a6, s7, 27
	add s6, s6, a6
	srli s8, s8, 2
	slli s6, s6, 32
	srli a6, s6, 32
	or s6, s6, a6
	xor s3, s3, s5
	xor s3, s3, t2
	xor s3, s3, a7
	slliw a6, s3, 1
	srliw s3, s3, 31
	or s3, s3, a6
	add s10, s10, s3
	add s10, s10, a5
	and a6, s7, s8
	add s10, s10, a6
	xor a6, s7, s8
	and a6, a6, s9
	add s10, s10, a6
	srli a6, s6, 27
	add s10, s10, a6
	srli s7, s7, 2
	slli s10, s10, 32
	srli a6, s10, 32
	or s10, s10, a6
	xor s4, s4, s11
	xor s4, s4, t3
	xor s4, s4, s1
	slliw a6, s4, 1
	srliw s4, s4, 31
	or s4, s4, a6
	add s9, s9, s4
	add s9, s9, a5
	and a6, s6, s7
	add s9, s9, a6
	xor a6, s6, s7
	and a6, a6, s8
	add s9, s9, a6
	srli a6, s10, 27
	add s9, s9, a6
	srli s6, s6, 2
	slli s9, s9, 32
	srli a6, s9, 32
	or s9, s9, a6
	xor s5, s5, s0
	xor s5, s5, t4
	xor s5, s5, s2
	slliw a6, s5, 1
	srliw s5, s5, 31
	or s5, s5, a6
	add s8, s8, s5
	add s8, s8, a5
	and a6, s10, s6
	add s8, s8, a6
	xor a6, s10, s6
	and a6, a6, s7
	add s8, s8, a6
	srli a6, s9, 27
	add s8, s8, a6
	srli s10, s10, 2
	slli s8, s8, 32
	srli a6, s8, 32
	or s8, s8, a6
	xor s11, s11, ra
	xor s11, s11, t5
	xor s11, s11, s3
	slliw a6, s11, 1
	srliw s11, s11, 31
	or s11, s11, a6
	add s7, s7, s11
	add s7, s7, a5
	and a6, s9, s10
	add s7, s7, a6
	xor a6, s9, s10
	and a6, a6, s6
	add s7, s7, a6
	srli a6, s8, 27
	add s7, s7, a6
	srli s9, s9, 2
	slli s7, s7, 32
	srli a6, s7, 32
	or s7, s7, a6
	xor s0, s0, t0
	xor s0, s0, t6
	xor s0, s0, s4
	slliw a6, s0, 1
	srliw s0, s0, 31
	or s0, s0, a6
	add s6, s6, s0
	add s6, s6, a5
	and a6, s8, s9
	add s6, s6, a6
	xor a6, s8, s9
	and a6, a6, s10
	add s6, s6, a6
	srli a6, s7, 27
	add s6, s6, a6
	srli s8, s8, 2
	slli s6, s6, 32
	srli a6, s6, 32
	or s6, s6, a6
	xor ra, ra, t1
	xor ra, ra, a7
	xor ra, ra, s5
	slliw a6, ra, 1
	srliw ra, ra, 31
	or ra, ra, a6
	add s10, s10, ra
	add s10, s10, a5
	and a6, s7, s8
	add s10, s10, a6
	xor a6, s7, s8
	and a6, a6, s9
	add s10, s10, a6
	srli a6, s6, 27
	add s10, s10, a6
	srli s7, s7, 2
	slli s10, s10, 32
	srli a6, s10, 32
	or s10, s10, a6
	xor t0, t0, t2
	xor t0, t0, s1
	xor t0, t0, s11
	slliw a6, t0, 1
	srliw t0, t0, 31
	or t0, t0, a6
	add s9, s9, t0
	add s9, s9, a5
	and a6, s6, s7
	add s9, s9, a6
	xor a6, s6, s7
	and a6, a6, s8
	add s9, s9, a6
	srli a6, s10, 27
	add s9, s9, a6
	srli s6, s6, 2
	slli s9, s9, 32
	srli a6, s9, 32
	or s9, s9, a6
	xor t1, t1, t3
	xor t1, t1, s2
	xor t1, t1, s0
	slliw a6, t1, 1
	srliw t1, t1, 31
	or t1, t1, a6
	add s8, s8, t1
	add s8, s8, a5
	and a6, s10, s6
	add s8, s8, a6
	xor a6, s10, s6
	and a6, a6, s7
	add s8, s8, a6
	srli a6, s9, 27
	add s8, s8, a6
	srli s10, s10, 2
	slli s8, s8, 32
	srli a6, s8, 32
	or s8, s8, a6
	xor t2, t2, t4
	xor t2, t2, s3
	xor t2, t2, ra
	slliw a6, t2, 1
	srliw t2, t2, 31
	or t2, t2, a6
	add s7, s7, t2
	add s7, s7, a5
	and a6, s9, s10
	add s7, s7, a6
	xor a6, s9, s10
	and a6, a6, s6
	add s7, s7, a6
	srli a6, s8, 27
	add s7, s7, a6
	srli s9, s9, 2
	slli s7, s7, 32
	srli a6, s7, 32
	or s7, s7, a6
	xor t3, t3, t5
	xor t3, t3, s4
	xor t3, t3, t0
	slliw a6, t3, 1
	srliw t3, t3, 31
	or t3, t3, a6
	add s6, s6, t3
	add s6, s6, a5
	and a6, s8, s9
	add s6, s6, a6
	xor a6, s8, s9
	and a6, a6, s10
	add s6, s6, a6
	srli a6, s7, 27
	add s6, s6, a6
	srli s8, s8, 2
	slli s6, s6, 32
	srli a6, s6, 32
	or s6, s6, a6
	xor t4, t4, t6
	xor t4, t4, s5
	xor t4, t4, t1
	slliw a6, t4, 1
	srliw t4, t4, 31
	or t4, t4, a6
	lui a5, 828972
	addiw a5, a5, 470
	add s10, s10, t4
	add s10, s10, a5
	xor a6, s7, s8
	xor a6, a6, s9
	add s10, s10, a6
	srli a6, s6, 27
	add s10, s10, a6
	srli s7, s7, 2
	slli s10, s10, 32
	srli a6, s10, 32
	or s10, s10, a6
	xor t5, t5, a7
	xor t5, t5, s11
	xor t5, t5, t2
	slliw a6, t5, 1
	srliw t5, t5, 31
	or t5, t5, a6
	add s9, s9, t5
	add s9, s9, a5
	xor a6, s6, s7
	xor a6, a6, s8
	add s9, s9, a6
	srli a6, s10, 27
	add s9, s9, a6
	srli s6, s6, 2
	slli s9, s9, 32
	srli a6, s9, 32
	or s9, s9, a6
	xor t6, t6, s1
	xor t6, t6, s0
	xor t6, t6, t3
	slliw a6, t6, 1
	srliw t6, t6, 31
	or t6, t6, a6
	add s8, s8, t6
	add s8, s8, a5
	xor a6, s10, s6
	xor a6, a6, s7
	add s8, s8, a6
	srli a6, s9, 27
	add s8, s8, a6
	srli s10, s10, 2
	slli s8, s8, 32
	srli a6, s8, 32
	or s8, s8, a6
	xor a7, a7, s2
	xor a7, a7, ra
	xor a7, a7, t4
	slliw a6, a7, 1
	srliw a7, a7, 31
	or a7, a7, a6
	add s7, s7, a7
	add s7, s7, a5
	xor a6, s9, s10
	xor a6, a6, s6
	add s7, s7, a6
	srli a6, s8, 27
	add s7, s7, a6
	srli s9, s9, 2
	slli s7, s7, 32
	srli a6, s7, 32
	or s7, s7, a6
	xor s1, s1, s3
	xor s1, s1, t0
	xor s1, s1, t5
	slliw a6, s1, 1
	srliw s1, s1, 31
	or s1, s1, a6
	add s6, s6, s1
	add s6, s6, a5
	xor a6, s8, s9
	xor a6, a6, s10
	add s6, s6, a6
	srli a6, s7, 27
	add s6, s6, a6
	srli s8, s8, 2
	slli s6, s6, 32
	srli a6, s6, 32
	or s6, s6, a6
	xor s2, s2, s4
	xor s2, s2, t1
	xor s2, s2, t6
	slliw a6, s2, 1
	srliw s2, s2, 31
	or s2, s2, a6
	add s10, s10, s2
	add s10, s10, a5
	xor a6, s7, s8
	xor a6, a6, s9
	add s10, s10, a6
	srli a6, s6, 27
	add s10, s10, a6
	srli s7, s7, 2
	slli s10, s10, 32
	srli a6, s10, 32
	or s10, s10, a6
	xor s3, s3, s5
	xor s3, s3, t2
	xor s3, s3, a7
	slliw a6, s3, 1
	srliw s3, s3, 31
	or s3, s3, a6
	add s9, s9, s3
	add s9, s9, a5
	xor a6, s6, s7
	xor a6, a6, s8
	add s9, s9, a6
	srli a6, s10, 27
	add s9, s9, a6
	srli s6, s6, 2
	slli s9, s9, 32
	srli a6, s9, 32
	or s9, s9, a6
	xor s4, s4, s11
	xor s4, s4, t3
	xor s4, s4, s1
	slliw a6, s4, 1
	srliw s4, s4, 31
	or s4, s4, a6
	add s8, s8, s4
	add s8, s8, a5
	xor a6, s10, s6
	xor a6, a6, s7
	add s8, s8, a6
	srli a6, s9, 27
	add s8, s8, a6
	srli s10, s10, 2
	slli s8, s8, 32
	srli a6, s8, 32
	or s8, s8, a6
	xor s5, s5, s0
	xor s5, s5, t4
	xor s5, s5, s2
	slliw a6, s5, 1
	srliw s5, s5, 31
	or s5, s5, a6
	add s7, s7, s5
	add s7, s7, a5
	xor a6, s9, s10
	xor a6, a6, s6
	add s7, s7, a6
	srli a6, s8, 27
	add s7, s7, a6
	srli s9, s9, 2
	slli s7, s7, 32
	srli a6, s7, 32
	or s7, s7, a6
	xor s11, s11, ra
	xor s11, s11, t5
	xor s11, s11, s3
	slliw a6, s11, 1
	srliw s11, s11, 31
	or s11, s11, a6
	add s6, s6, s11
	add s6, s6, a5
	xor a6, s8, s9
	xor a6, a6, s10
	add s6, s6, a6
	srli a6, s7, 27
	add s6, s6, a6
	srli s8, s8, 2
	slli s6, s6, 32
	srli a6, s6, 32
	or s6, s6, a6
	xor s0, s0, t0
	xor s0, s0, t6
	xor s0, s0, s4
	slliw a6, s0, 1
	srliw s0, s0, 31
	or s0, s0, a6
	add s10, s10, s0
	add s10, s10, a5
	xor a6, s7, s8
	xor a6, a6, s9
	add s10, s10, a6
	srli a6, s6, 27
	add s10, s10, a6
	srli s7, s7, 2
	slli s10, s10, 32
	srli a6, s10, 32
	or s10, s10, a6
	xor ra, ra, t1
	xor ra, ra, a7
	xor ra, ra, s5
	slliw a6, ra, 1
	srliw ra, ra, 31
	or ra, ra, a6
	add s9, s9, ra
	add s9, s9, a5
	xor a6, s6, s7
	xor a6, a6, s8
	add s9, s9, a6
	srli a6, s10, 27
	add s9, s9, a6
	srli s6, s6, 2
	slli s9, s9, 32
	srli a6, s9, 32
	or s9, s9, a6
	xor t0, t0, t2
	xor t0, t0, s1
	xor t0, t0, s11
	slliw a6, t0, 1
	srliw t0, t0, 31
	or t0, t0, a6
	add s8, s8, t0
	add s8, s8, a5
	xor a6, s10, s6
	xor a6, a6, s7
	add s8, s8, a6
	srli a6, s9, 27
	add s8, s8, a6
	srli s10, s10, 2
	slli s8, s8, 32
	srli a6, s8, 32
	or s8, s8, a6
	xor t1, t1, t3
	xor t1, t1, s2
	xor t1, t1, s0
	slliw a6, t1, 1
	srliw t1, t1, 31
	or t1, t1, a6
	add s7, s7, t1
	add s7, s7, a5
	xor a6, s9, s10
	xor a6, a6, s6
	add s7, s7, a6
	srli a6, s8, 27
	add s7, s7, a6
	srli s9, s9, 2
	slli s7, s7, 32
	srli a6, s7, 32
	or s7, s7, a6
	xor t2, t2, t4
	xor t2, t2, s3
	xor t2, t2, ra
	slliw a6, t2, 1
	srliw t2, t2, 31
	or t2, t2, a6
	add s6, s6, t2
	add s6, s6, a5
	xor a6, s8, s9
	xor a6, a6, s10
	add s6, s6, a6
	srli a6, s7, 27
	add s6, s6, a6
	srli s8, s8, 2
	slli s6, s6, 32
	srli a6, s6, 32
	or s6, s6, a6
	xor t3, t3, t5
	xor t3, t3, s4
	xor t3, t3, t0
	slliw a6, t3, 1
	srliw t3, t3, 31
	or t3, t3, a6
	add s10, s10, t3
	add s10, s10, a5
	xor a6, s7, s8
	xor a6, a6, s9
	add s10, s10, a6
	srli a6, s6, 27
	add s10, s10, a6
	srli s7, s7, 2
	slli s10, s10, 32
	srli a6, s10, 32
	or s10, s10, a6
	xor t4, t4, t6
	xor t4, t4, s5
	xor t4, t4, t1
	slliw a6, t4, 1
	srliw t4, t4, 31
	or t4, t4, a6
	add s9, s9, t4
	add s9, s9, a5
	xor a6, s6, s7
	xor a6, a6, s8
	add s9, s9, a6
	srli a6, s10, 27
	add s9, s9, a6
	srli s6, s6, 2
	slli s9, s9, 32
	srli a6, s9, 32
	or s9, s9, a6
	xor t5, t5, a7
	xor t5, t5, s11
	xor t5, t5, t2
	slliw a6, t5, 1
	srliw t5, t5, 31
	or t5, t5, a6
	add s8, s8, t5
	add s8, s8, a5
	xor a6, s10, s6
	xor a6, a6, s7
	add s8, s8, a6
	srli a6, s9, 27
	add s8, s8, a6
	srli s10, s10, 2
	slli s8, s8, 32
	srli a6, s8, 32
	or s8, s8, a6
	xor t6, t6, s1
	xor t6, t6, s0
	xor t6, t6, t3
	slliw a6, t6, 1
	srliw t6, t6, 31
	or t6, t6, a6
	add s7, s7, t6
	add s7, s7, a5
	xor a6, s9, s10
	xor a6, a6, s6
	add s7, s7, a6
	srli a6, s8, 27
	add s7, s7, a6
	srli s9, s9, 2
	slli s7, s7, 32
	srli a6, s7, 32
	or s7, s7, a6
	xor a7, a7, s2
	xor a7, a7, ra
	xor a7, a7, t4
	slliw a6, a7, 1
	srliw a7, a7, 31
	or a7, a7, a6
	add s6, s6, a7
	add s6, s6, a5
	xor a6, s8, s9
	xor a6, a6, s10
	add s6, s6, a6
	srli a6, s7, 27
	add s6, s6, a6
	srli s8, s8, 2
	slli s6, s6, 32
	srli a6, s6, 32
	or s6, s6, a6
	lwu a6, 104(a4)
	add s6, s6, a6
	lwu a6, 108(a4)
	add s7, s7, a6
	lwu a6, 112(a4)
	add s8, s8, a6
	lwu a6, 116(a4)
	add s9, s9, a6
	lwu a6, 120(a4)
	add s10, s10, a6
	lwu s1, 124(a4)
	lwu s2, 128(a4)
	lwu s3, 132(a4)
	lwu s4, 136(a4)
	lwu s5, 140(a4)
	slli a6, s1, 32
	or s1, s1, a6
	slli a6, s2, 32
	or s2, s2, a6
	lui a5, 370728
	addiw a5, a5, -1639
	add s5, s5, s6
	add s5, s5, a5
	xor a6, s3, s4
	and a6, a6, s2
	xor a6, a6, s4
	add s5, s5, a6
	srli a6, s1, 27
	add s5, s5, a6
	srli s2, s2, 2
	slli s5, s5, 32
	srli a6, s5, 32
	or s5, s5, a6
	add s4, s4, s7
	add s4, s4, a5
	xor a6, s2, s3
	and a6, a6, s1
	xor a6, a6, s3
	add s4, s4, a6
	srli a6, s5, 27
	add s4, s4, a6
	srli s1, s1, 2
	slli s4, s4, 32
	srli a6, s4, 32
	or s4, s4, a6
	add s3, s3, s8
	add s3, s3, a5
	xor a6, s1, s2
	and a6, a6, s5
	xor a6, a6, s2
	add s3, s3, a6
	srli a6, s4, 27
	add s3, s3, a6
	srli s5, s5, 2
	slli s3, s3, 32
	srli a6, s3, 32
	or s3, s3, a6
	add s2, s2, s9
	add s2, s2, a5
	xor a6, s5, s1
	and a6, a6, s4
	xor a6, a6, s1
	add s2, s2, a6
	srli a6, s3, 27
	add s2, s2, a6
	srli s4, s4, 2
	slli s2, s2, 32
	srli a6, s2, 32
	or s2, s2, a6
	add s1, s1, s10
	add s1, s1, a5
	xor a6, s4, s5
	and a6, a6, s3
	xor a6, a6, s5
	add s1, s1, a6
	srli a6, s2, 27
	add s1, s1, a6
	srli s3, s3, 2
	slli s1, s1, 32
	srli a6, s1, 32
	or s1, s1, a6
	lui a6, 895016
	addiw a6, a6, -1639
	add s5, s5, a6
	xor a6, s3, s4
	and a6, a6, s2
	xor a6, a6, s4
	add s5, s5, a6
	srli a6, s1, 27
	add s5, s5, a6
	srli s2, s2, 2
	slli s5, s5, 32
	srli a6, s5, 32
	or s5, s5, a6
	add s4, s4, a5
	xor a6, s2, s3
	and a6, a6, s1
	xor a6, a6, s3
	add s4, s4, a6
	srli a6, s5, 27
	add s4, s4, a6
	srli s1, s1, 2
	slli s4, s4, 32
	srli a6, s4, 32
	or s4, s4, a6
	add s3, s3, a5
	xor a6, s1, s2
	and a6, a6, s5
	xor a6, a6, s2
	add s3, s3, a6
	srli a6, s4, 27
	add s3, s3, a6
	srli s5, s5, 2
	slli s3, s3, 32
	srli a6, s3, 32
	or s3, s3, a6
	add s2, s2, a5
	xor a6, s5, s1
	and a6, a6, s4
	xor a6, a6, s1
	add s2, s2, a6
	srli a6, s3, 27
	add s2, s2, a6
	srli s4, s4, 2
	slli s2, s2, 32
	srli a6, s2, 32
	or s2, s2, a6
	add s1, s1, a5
	xor a6, s4, s5
	and a6, a6, s3
	xor a6, a6, s5
	add s1, s1, a6
	srli a6, s2, 27
	add s1, s1, a6
	srli s3, s3, 2
	slli s1, s1, 32
	srli a6, s1, 32
	or s1, s1, a6
	add s5, s5, a5
	xor a6, s3, s4
	and a6, a6, s2
	xor a6, a6, s4
	add s5, s5, a6
	srli a6, s1, 27
	add s5, s5, a6
	srli s2, s2, 2
	slli s5, s5, 32
	srli a6, s5, 32
	or s5, s5, a6
	add s4, s4, a5
	xor a6, s2, s3
	and a6, a6, s1
	xor a6, a6, s3
	add s4, s4, a6
	srli a6, s5, 27
	add s4, s4, a6
	srli s1, s1, 2
	slli s4, s4, 32
	srli a6, s4, 32
	or s4, s4, a6
	add s3, s3, a5
	xor a6, s1, s2
	and a6, a6, s5
	xor a6, a6, s2
	add s3, s3, a6
	srli a6, s4, 27
	add s3, s3, a6
	srli s5, s5, 2
	slli s3, s3, 32
	srli a6, s3, 32
	or s3, s3, a6
	add s2, s2, a5
	xor a6, s5, s1
	and a6, a6, s4
	xor a6, a6, s1
	add s2, s2, a6
	srli a6, s3, 27
	add s2, s2, a6
	srli s4, s4, 2
	slli s2, s2, 32
	srli a6, s2, 32
	or s2, s2, a6
	add s1, s1, a5
	xor a6, s4, s5
	and a6, a6, s3
	xor a6, a6, s5
	add s1, s1, a6
	srli a6, s2, 27
	add s1, s1, a6
	srli s3, s3, 2
	slli s1, s1, 32
	srli a6, s1, 32
	or s1, s1, a6
	addi s5, s5, 672
	add s5, s5, a5
	xor a6, s3, s4
	and a6, a6, s2
	xor a6, a6, s4
	add s5, s5, a6
	srli a6, s1, 27
	add s5, s5, a6
	srli s2, s2, 2
	slli s5, s5, 32
	srli a6, s5, 32
	or s5, s5, a6
	xor s6, s6, s8
	slliw a6, s6, 1
	srliw s6, s6, 31
	or s6, s6, a6
	add s4, s4, s6
	add s4, s4, a5
	xor a6, s2, s3
	and a6, a6, s1
	xor a6, a6, s3
	add s4, s4, a6
	srli a6, s5, 27
	add s4, s4, a6
	srli s1, s1, 2
	slli s4, s4, 32
	srli a6, s4, 32
	or s4, s4, a6
	xor s7, s7, s9
	slliw a6, s7, 1
	srliw s7, s7, 31
	or s7, s7, a6
	add s3, s3, s7
	add s3, s3, a5
	xor a6, s1, s2
	and a6, a6, s5
	xor a6, a6, s2
	add s3, s3, a6
	srli a6, s4, 27
	add s3, s3, a6
	srli s5, s5, 2
	slli s3, s3, 32
	srli a6, s3, 32
	or s3, s3, a6
	xor s8, s8, s10
	slliw a6, s8, 1
	srliw s8, s8, 31
	or s8, s8, a6
	xori s8, s8, 1344
	add s2, s2, s8
	add s2, s2, a5
	xor a6, s5, s1
	and a6, a6, s4
	xor a6, a6, s1
	add s2, s2, a6
	srli a6, s3, 27
	add s2, s2, a6
	srli s4, s4, 2
	slli s2, s2, 32
	srli a6, s2, 32
	or s2, s2, a6
	xor s9, s9, s6
	slliw a6, s9, 1
	srliw s9, s9, 31
	or s9, s9, a6
	xori s9, s9, 1
	add s1, s1, s9
	add s1, s1, a5
	xor a6, s4, s5
	and a6, a6, s3
	xor a6, a6, s5
	add s1, s1, a6
	srli a6, s2, 27
	add s1, s1, a6
	srli s3, s3, 2
	slli s1, s1, 32
	srli a6, s1, 32
	or s1, s1, a6
	xor s10, s10, s7
	slliw a6, s10, 1
	srliw s10, s10, 31
	or s10, s10, a6
	lui a5, 454047
	addiw a5, a5, -1119
	add s5, s5, s10
	add s5, s5, a5
	xor a6, s2, s3
	xor a6, a6, s4
	add s5, s5, a6
	srli a6, s1, 27
	add s5, s5, a6
	srli s2, s2, 2
	slli s5, s5, 32
	srli a6, s5, 32
	or s5, s5, a6
	slliw a6, s8, 1
	srliw s11, s8, 31
	or s11, s11, a6
	xori s11, s11, 1
	add s4, s4, s11
	add s4, s4, a5
	xor a6, s1, s2
	xor a6, a6, s3
	add s4, s4, a6
	srli a6, s5, 27
	add s4, s4, a6
	srli s1, s1, 2
	slli s4, s4, 32
	srli a6, s4, 32
	or s4, s4, a6
	slliw a6, s9, 1
	srliw s0, s9, 31
	or s0, s0, a6
	add s3, s3, s0
	add s3, s3, a5
	xor a6, s5, s1
	xor a6, a6, s2
	add s3, s3, a6
	srli a6, s4, 27
	add s3, s3, a6
	srli s5, s5, 2
	slli s3, s3, 32
	srli a6, s3, 32
	or s3, s3, a6
	slliw a6, s10, 1
	srliw ra, s10, 31
	or ra, ra, a6
	xori ra, ra, 1344
	add s2, s2, ra
	add s2, s2, a5
	xor a6, s4, s5
	xor a6, a6, s1
	add s2, s2, a6
	srli a6, s3, 27
	add s2, s2, a6
	srli s4, s4, 2
	slli s2, s2, 32
	srli a6, s2, 32
	or s2, s2, a6
	xor t0, s6, s11
	slliw a6, t0, 1
	srliw t0, t0, 31
	or t0, t0, a6
	add s1, s1, t0
	add s1, s1, a5
	xor a6, s3, s4
	xor a6, a6, s5
	add s1, s1, a6
	srli a6, s2, 27
	add s1, s1, a6
	srli s3, s3, 2
	slli s1, s1, 32
	srli a6, s1, 32
	or s1, s1, a6
	xor t1, s7, s0
	slliw a6, t1, 1
	srliw t1, t1, 31
	or t1, t1, a6
	add s5, s5, t1
	add s5, s5, a5
	xor a6, s2, s3
	xor a6, a6, s4
	add s5, s5, a6
	srli a6, s1, 27
	add s5, s5, a6
	srli s2, s2, 2
	slli s5, s5, 32
	srli a6, s5, 32
	or s5, s5, a6
	xor t2, s8, ra
	slliw a6, t2, 1
	srliw t2, t2, 31
	or t2, t2, a6
	add s4, s4, t2
	add s4, s4, a5
	xor a6, s1, s2
	xor a6, a6, s3
	add s4, s4, a6
	srli a6, s5, 27
	add s4, s4, a6
	srli s1, s1, 2
	slli s4, s4, 32
	srli a6, s4, 32
	or s4, s4, a6
	xor t3, s9, t0
	slliw a6, t3, 1
	srliw t3, t3, 31
	or t3, t3, a6
	add s3, s3, t3
	add s3, s3, a5
	xor a6, s5, s1
	xor a6, a6, s2
	add s3, s3, a6
	srli a6, s4, 27
	add s3, s3, a6
	srli s5, s5, 2
	slli s3, s3, 32
	srli a6, s3, 32
	or s3, s3, a6
	xor t4, s10, t1
	slliw a6, t4, 1
	srliw t4, t4, 31
	or t4, t4, a6
	add s2, s2, t4
	add s2, s2, a5
	xor a6, s4, s5
	xor a6, a6, s1
	add s2, s2, a6
	srli a6, s3, 27
	add s2, s2, a6
	srli s4, s4, 2
	slli s2, s2, 32
	srli a6, s2, 32
	or s2, s2, a6
	xor t5, s11, t2
	slliw a6, t5, 1
	srliw t5, t5, 31
	or t5, t5, a6
	xori t5, t5, 1344
	add s1, s1, t5
	add s1, s1, a5
	xor a6, s3, s4
	xor a6, a6, s5
	add s1, s1, a6
	srli a6, s2, 27
	add s1, s1, a6
	srli s3, s3, 2
	slli s1, s1, 32
	srli a6, s1, 32
	or s1, s1, a6
	xor t6, s6, s0
	xor t6, t6, t3
	slliw a6, t6, 1
	srliw t6, t6, 31
	or t6, t6, a6
	add s5, s5, t6
	add s5, s5, a5
	xor a6, s2, s3
	xor a6, a6, s4
	add s5, s5, a6
	srli a6, s1, 27
	add s5, s5, a6
	srli s2, s2, 2
	slli s5, s5, 32
	srli a6, s5, 32
	or s5, s5, a6
	xor a7, s7, ra
	xor a7, a7, t4
	slliw a6, a7, 1
	srliw a7, a7, 31
	or a7, a7, a6
	xori a7, a7, 1344
	add s4, s4, a7
	add s4, s4, a5
	xor a6, s1, s2
	xor a6, a6, s3
	add s4, s4, a6
	srli a6, s5, 27
	add s4, s4, a6
	srli s1, s1, 2
	slli s4, s4, 32
	srli a6, s4, 32
	or s4, s4, a6
	xor s6, s6, s8
	xor s6, s6, t0
	xor s6, s6, t5
	slliw a6, s6, 1
	srliw s6, s6, 31
	or s6, s6, a6
	add s3, s3, s6
	add s3, s3, a5
	xor a6, s5, s1
	xor a6, a6, s2
	add s3, s3, a6
	srli a6, s4, 27
	add s3, s3, a6
	srli s5, s5, 2
	slli s3, s3, 32
	srli a6, s3, 32
	or s3, s3, a6
	xor s7, s7, s9
	xor s7, s7, t1
	xor s7, s7, t6
	slliw a6, s7, 1
	srliw s7, s7, 31
	or s7, s7, a6
	add s2, s2, s7
	add s2, s2, a5
	xor a6, s4, s5
	xor a6, a6, s1
	add s2, s2, a6
	srli a6, s3, 27
	add s2, s2, a6
	srli s4, s4, 2
	slli s2, s2, 32
	srli a6, s2, 32
	or s2, s2, a6
	xor s8, s8, s10
	xor s8, s8, t2
	xor s8, s8, a7
	slliw a6, s8, 1
	srliw s8, s8, 31
	or s8, s8, a6
	add s1, s1, s8
	add s1, s1, a5
	xor a6, s3, s4
	xor a6, a6, s5
	add s1, s1, a6
	srli a6, s2, 27
	add s1, s1, a6
	srli s3, s3, 2
	slli s1, s1, 32
	srli a6, s1, 32
	or s1, s1, a6
	xor s9, s9, s11
	xor s9, s9, t3
	xor s9, s9, s6
	slliw a6, s9, 1
	srliw s9, s9, 31
	or s9, s9, a6
	add s5, s5, s9
	add s5, s5, a5
	xor a6, s2, s3
	xor a6, a6, s4
	add s5, s5, a6
	srli a6, s1, 27
	add s5, s5, a6
	srli s2, s2, 2
	slli s5, s5, 32
	srli a6, s5, 32
	or s5, s5, a6
	xor s10, s10, s0
	xor s10, s10, t4
	xor s10, s10, s7
	slliw a6, s10, 1
	srliw s10, s10, 31
	or s10, s10, a6
	add s4, s4, s10
	add s4, s4, a5
	xor a6, s1, s2
	xor a6, a6, s3
	add s4, s4, a6
	srli a6, s5, 27
	add s4, s4, a6
	srli s1, s1, 2
	slli s4, s4, 32
	srli a6, s4, 32
	or s4, s4, a6
	xor s11, s11, ra
	xor s11, s11, t5
	xor s11, s11, s8
	slliw a6, s11, 1
	srliw s11, s11, 31
	or s11, s11, a6
	add s3, s3, s11
	add s3, s3, a5
	xor a6, s5, s1
	xor a6, a6, s2
	add s3, s3, a6
	srli a6, s4, 27
	add s3, s3, a6
	srli s5, s5, 2
	slli s3, s3, 32
	srli a6, s3, 32
	or s3, s3, a6
	xor s0, s0, t0
	xor s0, s0, t6
	xor s0, s0, s9
	slliw a6, s0, 1
	srliw s0, s0, 31
	or s0, s0, a6
	add s2, s2, s0
	add s2, s2, a5
	xor a6, s4, s5
	xor a6, a6, s1
	add s2, s2, a6
	srli a6, s3, 27
	add s2, s2, a6
	srli s4, s4, 2
	slli s2, s2, 32
	srli a6, s2, 32
	or s2, s2, a6
	xor ra, ra, t1
	xor ra, ra, a7
	xor ra, ra, s10
	slliw a6, ra, 1
	srliw ra, ra, 31
	or ra, ra, a6
	add s1, s1, ra
	add s1, s1, a5
	xor a6, s3, s4
	xor a6, a6, s5
	add s1, s1, a6
	srli a6, s2, 27
	add s1, s1, a6
	srli s3, s3, 2
	slli s1, s1, 32
	srli a6, s1, 32
	or s1, s1, a6
	xor t0, t0, t2
	xor t0, t0, s6
	xor t0, t0, s11
	slliw a6, t0, 1
	srliw t0, t0, 31
	or t0, t0, a6
	lui a5, 586172
	addiw a5, a5, -804
	add s5, s5, t0
	add s5, s5, a5
	and a6, s2, s3
	add s5, s5, a6
	xor a6, s2, s3
	and a6, a6, s4
	add s5, s5, a6
	srli a6, s1, 27
	add s5, s5, a6
	srli s2, s2, 2
	slli s5, s5, 32
	srli a6, s5, 32
	or s5, s5, a6
	xor t1, t1, t3
	xor t1, t1, s7
	xor t1, t1, s0
	slliw a6, t1, 1
	srliw t1, t1, 31
	or t1, t1, a6
	add s4, s4, t1
	add s4, s4, a5
	and a6, s1, s2
	add s4, s4, a6
	xor a6, s1, s2
	and a6, a6, s3
	add s4, s4, a6
	srli a6, s5, 27
	add s4, s4, a6
	srli s1, s1, 2
	slli s4, s4, 32
	srli a6, s4, 32
	or s4, s4, a6
	xor t2, t2, t4
	xor t2, t2, s8
	xor t2, t2, ra
	slliw a6, t2, 1
	srliw t2, t2, 31
	or t2, t2, a6
	add s3, s3, t2
	add s3, s3, a5
	and a6, s5, s1
	add s3, s3, a6
	xor a6, s5, s1
	and a6, a6, s2
	add s3, s3, a6
	srli a6, s4, 27
	add s3, s3, a6
	srli s5, s5, 2
	slli s3, s3, 32
	srli a6, s3, 32
	or s3, s3, a6
	xor t3, t3, t5
	xor t3, t3, s9
	xor t3, t3, t0
	slliw a6, t3, 1
	srliw t3, t3, 31
	or t3, t3, a6
	add s2, s2, t3
	add s2, s2, a5
	and a6, s4, s5
	add s2, s2, a6
	xor a6, s4, s5
	and a6, a6, s1
	add s2, s2, a6
	srli a6, s3, 27
	add s2, s2, a6
	srli s4, s4, 2
	slli s2, s2, 32
	srli a6, s2, 32
	or s2, s2, a6
	xor t4, t4, t6
	xor t4, t4, s10
	xor t4, t4, t1
	slliw a6, t4, 1
	srliw t4, t4, 31
	or t4, t4, a6
	add s1, s1, t4
	add s1, s1, a5
	and a6, s3, s4
	add s1, s1, a6
	xor a6, s3, s4
	and a6, a6, s5
	add s1, s1, a6
	srli a6, s2, 27
	add s1, s1, a6
	srli s3, s3, 2
	slli s1, s1, 32
	srli a6, s1, 32
	or s1, s1, a6
	xor t5, t5, a7
	xor t5, t5, s11
	xor t5, t5, t2
	slliw a6, t5, 1
	srliw t5, t5, 31
	or t5, t5, a6
	add s5, s5, t5
	add s5, s5, a5
	and a6, s2, s3
	add s5, s5, a6
	xor a6, s2, s3
	and a6, a6, s4
	add s5, s5, a6
	srli a6, s1, 27
	add s5, s5, a6
	srli s2, s2, 2
	slli s5, s5, 32
	srli a6, s5, 32
	or s5, s5, a6
	xor t6, t6, s6
	xor t6, t6, s0
	xor t6, t6, t3
	slliw a6, t6, 1
	srliw t6, t6, 31
	or t6, t6, a6
	add s4, s4, t6
	add s4, s4, a5
	and a6, s1, s2
	add s4, s4, a6
	xor a6, s1, s2
	and a6, a6, s3
	add s4, s4, a6
	srli a6, s5, 27
	add s4, s4, a6
	srli s1, s1, 2
	slli s4, s4, 32
	srli a6, s4, 32
	or s4, s4, a6
	xor a7, a7, s7
	xor a7, a7, ra
	xor a7, a7, t4
	slliw a6, a7, 1
	srliw a7, a7, 31
	or a7, a7, a6
	add s3, s3, a7
	add s3, s3, a5
	and a6, s5, s1
	add s3, s3, a6
	xor a6, s5, s1
	and a6, a6, s2
	add s3, s3, a6
	srli a6, s4, 27
	add s3, s3, a6
	srli s5, s5, 2
	slli s3, s3, 32
	srli a6, s3, 32
	or s3, s3, a6
	xor s6, s6, s8
	xor s6, s6, t0
	xor s6, s6, t5
	slliw a6, s6, 1
	srliw s6, s6, 31
	or s6, s6, a6
	add s2, s2, s6
	add s2, s2, a5
	and a6, s4, s5
	add s2, s2, a6
	xor a6, s4, s5
	and a6, a6, s1
	add s2, s2, a6
	srli a6, s3, 27
	add s2, s2, a6
	srli s4, s4, 2
	slli s2, s2, 32
	srli a6, s2, 32
	or s2, s2, a6
	xor s7, s7, s9
	xor s7, s7, t1
	xor s7, s7, t6
	slliw a6, s7, 1
	srliw s7, s7, 31
	or s7, s7, a6
	add s1, s1, s7
	add s1, s1, a5
	and a6, s3, s4
	add s1, s1, a6
	xor a6, s3, s4
	and a6, a6, s5
	add s1, s1, a6
	srli a6, s2, 27
	add s1, s1, a6
	srli s3, s3, 2
	slli s1, s1, 32
	srli a6, s1, 32
	or s1, s1, a6
	xor s8, s8, s10
	xor s8, s8, t2
	xor s8, s8, a7
	slliw a6, s8, 1
	srliw s8, s8, 31
	or s8, s8, a6
	add s5, s5, s8
	add s5, s5, a5
	and a6, s2, s3
	add s5, s5, a6
	xor a6, s2, s3
	and a6, a6, s4
	add s5, s5, a6
	srli a6, s1, 27
	add s5, s5, a6
	srli s2, s2, 2
	slli s5, s5, 32
	srli a6, s5, 32
	or s5, s5, a6
	xor s9, s9, s11
	xor s9, s9, t3
	xor s9, s9, s6
	slliw a6, s9, 1
	srliw s9, s9, 31
	or s9, s9, a6
	add s4, s4, s9
	add s4, s4, a5
	and a6, s1, s2
	add s4, s4, a6
	xor a6, s1, s2
	and a6, a6, s3
	add s4, s4, a6
	srli a6, s5, 27
	add s4, s4, a6
	srli s1, s1, 2
	slli s4, s4, 32
	srli a6, s4, 32
	or s4, s4, a6
	xor s10, s10, s0
	xor s10, s10, t4
	xor s10, s10, s7
	slliw a6, s10, 1
	srliw s10, s10, 31
	or s10, s10, a6
	add s3, s3, s10
	add s3, s3, a5
	and a6, s5, s1
	add s3, s3, a6
	xor a6, s5, s1
	and a6, a6, s2
	add s3, s3, a6
	srli a6, s4, 27
	add s3, s3, a6
	srli s5, s5, 2
	slli s3, s3, 32
	srli a6, s3, 32
	or s3, s3, a6
	xor s11, s11, ra
	xor s11, s11, t5
	xor s11, s11, s8
	slliw a6, s11, 1
	srliw s11, s11, 31
	or s11, s11, a6
	add s2, s2, s11
	add s2, s2, a5
	and a6, s4, s5
	add s2, s2, a6
	xor a6, s4, s5
	and a6, a6, s1
	add s2, s2, a6
	srli a6, s3, 27
	add s2, s2, a6
	srli s4, s4, 2
	slli s2, s2, 32
	srli a6, s2, 32
	or s2, s2, a6
	xor s0, s0, t0
	xor s0, s0, t6
	xor s0, s0, s9
	slliw a6, s0, 1
	srliw s0, s0, 31
	or s0, s0, a6
	add s1, s1, s0
	add s1, s1, a5
	and a6, s3, s4
	add s1, s1, a6
	xor a6, s3, s4
	and a6, a6, s5
	add s1, s1, a6
	srli a6, s2, 27
	add s1, s1, a6
	srli s3, s3, 2
	slli s1, s1, 32
	srli a6, s1, 32
	or s1, s1, a6
	xor ra, ra, t1
	xor ra, ra, a7
	xor ra, ra, s10
	slliw a6, ra, 1
	srliw ra, ra, 31
	or ra, ra, a6
	add s5, s5, ra
	add s5, s5, a5
	and a6, s2, s3
	add s5, s5, a6
	xor a6, s2, s3
	and a6, a6, s4
	add s5, s5, a6
	srli a6, s1, 27
	add s5, s5, a6
	srli s2, s2, 2
	slli s5, s5, 32
	srli a6, s5, 32
	or s5, s5, a6
	xor t0, t0, t2
	xor t0, t0, s6
	xor t0, t0, s11
	slliw a6, t0, 1
	srliw t0, t0, 31
	or t0, t0, a6
	add s4, s4, t0
	add s4, s4, a5
	and a6, s1, s2
	add s4, s4, a6
	xor a6, s1, s2
	and a6, a6, s3
	add s4, s4, a6
	srli a6, s5, 27
	add s4, s4, a6
	srli s1, s1, 2
	slli s4, s4, 32
	srli a6, s4, 32
	or s4, s4, a6
	xor t1, t1, t3
	xor t1, t1, s7
	xor t1, t1, s0
	slliw a6, t1, 1
	srliw t1, t1, 31
	or t1, t1, a6
	add s3, s3, t1
	add s3, s3, a5
	and a6, s5, s1
	add s3, s3, a6
	xor a6, s5, s1
	and a6, a6, s2
	add s3, s3, a6
	srli a6, s4, 27
	add s3, s3, a6
	srli s5, s5, 2
	slli s3, s3, 32
	srli a6, s3, 32
	or s3, s3, a6
	xor t2, t2, t4
	xor t2, t2, s8
	xor t2, t2, ra
	slliw a6, t2, 1
	srliw t2, t2, 31
	or t2, t2, a6
	add s2, s2, t2
	add s2, s2, a5
	and a6, s4, s5
	add s2, s2, a6
	xor a6, s4, s5
	and a6, a6, s1
	add s2, s2, a6
	srli a6, s3, 27
	add s2, s2, a6
	srli s4, s4, 2
	slli s2, s2, 32
	srli a6, s2, 32
	or s2, s2, a6
	xor t3, t3, t5
	xor t3, t3, s9
	xor t3, t3, t0
	slliw a6, t3, 1
	srliw t3, t3, 31
	or t3, t3, a6
	add s1, s1, t3
	add s1, s1, a5
	and a6, s3, s4
	add s1, s1, a6
	xor a6, s3, s4
	and a6, a6, s5
	add s1, s1, a6
	srli a6, s2, 27
	add s1, s1, a6
	srli s3, s3, 2
	slli s1, s1, 32
	srli a6, s1, 32
	or s1, s1, a6
	xor t4, t4, t6
	xor t4, t4, s10
	xor t4, t4, t1
	slliw a6, t4, 1
	srliw t4, t4, 31
	or t4, t4, a6
	lui a5, 828972
	addiw a5, a5, 470
	add s5, s5, t4
	add s5, s5, a5
	xor a6, s2, s3
	xor a6, a6, s4
	add s5, s5, a6
	srli a6, s1, 27
	add s5, s5, a6
	srli s2, s2, 2
	slli s5, s5, 32
	srli a6, s5, 32
	or s5, s5, a6
	xor t5, t5, a7
	xor t5, t5, s11
	xor t5, t5, t2
	slliw a6, t5, 1
	srliw t5, t5, 31
	or t5, t5, a6
	add s4, s4, t5
	add s4, s4, a5
	xor a6, s1, s2
	xor a6, a6, s3
	add s4, s4, a6
	srli a6, s5, 27
	add s4, s4, a6
	srli s1, s1, 2
	slli s4, s4, 32
	srli a6, s4, 32
	or s4, s4, a6
	xor t6, t6, s6
	xor t6, t6, s0
	xor t6, t6, t3
	slliw a6, t6, 1
	srliw t6, t6, 31
	or t6, t6, a6
	add s3, s3, t6
	add s3, s3, a5
	xor a6, s5, s1
	xor a6, a6, s2
	add s3, s3, a6
	srli a6, s4, 27
	add s3, s3, a6
	srli s5, s5, 2
	slli s3, s3, 32
	srli a6, s3, 32
	or s3, s3, a6
	xor a7, a7, s7
	xor a7, a7, ra
	xor a7, a7, t4
	slliw a6, a7, 1
	srliw a7, a7, 31
	or a7, a7, a6
	add s2, s2, a7
	add s2, s2, a5
	xor a6, s4, s5
	xor a6, a6, s1
	add s2, s2, a6
	srli a6, s3, 27
	add s2, s2, a6
	srli s4, s4, 2
	slli s2, s2, 32
	srli a6, s2, 32
	or s2, s2, a6
	xor s6, s6, s8
	xor s6, s6, t0
	xor s6, s6, t5
	slliw a6, s6, 1
	srliw s6, s6, 31
	or s6, s6, a6
	add s1, s1, s6
	add s1, s1, a5
	xor a6, s3, s4
	xor a6, a6, s5
	add s1, s1, a6
	srli a6, s2, 27
	add s1, s1, a6
	srli s3, s3, 2
	slli s1, s1, 32
	srli a6, s1, 32
	or s1, s1, a6
	xor s7, s7, s9
	xor s7, s7, t1
	xor s7, s7, t6
	slliw a6, s7, 1
	srliw s7, s7, 31
	or s7, s7, a6
	add s5, s5, s7
	add s5, s5, a5
	xor a6, s2, s3
	xor a6, a6, s4
	add s5, s5, a6
	srli a6, s1, 27
	add s5, s5, a6
	srli s2, s2, 2
	slli s5, s5, 32
	srli a6, s5, 32
	or s5, s5, a6
	xor s8, s8, s10
	xor s8, s8, t2
	xor s8, s8, a7
	slliw a6, s8, 1
	srliw s8, s8, 31
	or s8, s8, a6
	add s4, s4, s8
	add s4, s4, a5
	xor a6, s1, s2
	xor a6, a6, s3
	add s4, s4, a6
	srli a6, s5, 27
	add s4, s4, a6
	srli s1, s1, 2
	slli s4, s4, 32
	srli a6, s4, 32
	or s4, s4, a6
	xor s9, s9, s11
	xor s9, s9, t3
	xor s9, s9, s6
	slliw a6, s9, 1
	srliw s9, s9, 31
	or s9, s9, a6
	add s3, s3, s9
	add s3, s3, a5
	xor a6, s5, s1
	xor a6, a6, s2
	add s3, s3, a6
	srli a6, s4, 27
	add s3, s3, a6
	srli s5, s5, 2
	slli s3, s3, 32
	srli a6, s3, 32
	or s3, s3, a6
	xor s10, s10, s0
	xor s10, s10, t4
	xor s10, s10, s7
	slliw a6, s10, 1
	srliw s10, s10, 31
	or s10, s10, a6
	add s2, s2, s10
	add s2, s2, a5
	xor a6, s4, s5
	xor a6, a6, s1
	add s2, s2, a6
	srli a6, s3, 27
	add s2, s2, a6
	srli s4, s4, 2
	slli s2, s2, 32
	srli a6, s2, 32
	or s2, s2, a6
	xor s11, s11, ra
	xor s11, s11, t5
	xor s11, s11, s8
	slliw a6, s11, 1
	srliw s11, s11, 31
	or s11, s11, a6
	add s1, s1, s11
	add s1, s1, a5
	xor a6, s3, s4
	xor a6, a6, s5
	add s1, s1, a6
	srli a6, s2, 27
	add s1, s1, a6
	srli s3, s3, 2
	slli s1, s1, 32
	srli a6, s1, 32
	or s1, s1, a6
	xor s0, s0, t0
	xor s0, s0, t6
	xor s0, s0, s9
	slliw a6, s0, 1
	srliw s0, s0, 31
	or s0, s0, a6
	add s5, s5, s0
	add s5, s5, a5
	xor a6, s2, s3
	xor a6, a6, s4
	add s5, s5, a6
	srli a6, s1, 27
	add s5, s5, a6
	srli s2, s2, 2
	slli s5, s5, 32
	srli a6, s5, 32
	or s5, s5, a6
	xor ra, ra, t1
	xor ra, ra, a7
	xor ra, ra, s10
	slliw a6, ra, 1
	srliw ra, ra, 31
	or ra, ra, a6
	add s4, s4, ra
	add s4, s4, a5
	xor a6, s1, s2
	xor a6, a6, s3
	add s4, s4, a6
	srli a6, s5, 27
	add s4, s4, a6
	srli s1, s1, 2
	slli s4, s4, 32
	srli a6, s4, 32
	or s4, s4, a6
	xor t0, t0, t2
	xor t0, t0, s6
	xor t0, t0, s11
	slliw a6, t0, 1
	srliw t0, t0, 31
	or t0, t0, a6
	add s3, s3, t0
	add s3, s3, a5
	xor a6, s5, s1
	xor a6, a6, s2
	add s3, s3, a6
	srli a6, s4, 27
	add s3, s3, a6
	srli s5, s5, 2
	slli s3, s3, 32
	srli a6, s3, 32
	or s3, s3, a6
	xor t1, t1, t3
	xor t1, t1, s7
	xor t1, t1, s0
	slliw a6, t1, 1
	srliw t1, t1, 31
	or t1, t1, a6
	add s2, s2, t1
	add s2, s2, a5
	xor a6, s4, s5
	xor a6, a6, s1
	add s2, s2, a6
	srli a6, s3, 27
	add s2, s2, a6
	srli s4, s4, 2
	slli s2, s2, 32
	srli a6, s2, 32
	or s2, s2, a6
	xor t2, t2, t4
	xor t2, t2, s8
	xor t2, t2, ra
	slliw a6, t2, 1
	srliw t2, t2, 31
	or t2, t2, a6
	add s1, s1, t2
	add s1, s1, a5
	xor a6, s3, s4
	xor a6, a6, s5
	add s1, s1, a6
	srli a6, s2, 27
	add s1, s1, a6
	srli s3, s3, 2
	slli s1, s1, 32
	srli a6, s1, 32
	or s1, s1, a6
	xor t3, t3, t5
	xor t3, t3, s9
	xor t3, t3, t0
	slliw a6, t3, 1
	srliw t3, t3, 31
	or t3, t3, a6
	add s5, s5, t3
	add s5, s5, a5
	xor a6, s2, s3
	xor a6, a6, s4
	add s5, s5, a6
	srli a6, s1, 27
	add s5, s5, a6
	srli s2, s2, 2
	slli s5, s5, 32
	srli a6, s5, 32
	or s5, s5, a6
	xor t4, t4, t6
	xor t4, t4, s10
	xor t4, t4, t1
	slliw a6, t4, 1
	srliw t4, t4, 31
	or t4, t4, a6
	add s4, s4, t4
	add s4, s4, a5
	xor a6, s1, s2
	xor a6, a6, s3
	add s4, s4, a6
	srli a6, s5, 27
	add s4, s4, a6
	srli s1, s1, 2
	slli s4, s4, 32
	srli a6, s4, 32
	or s4, s4, a6
	xor t5, t5, a7
	xor t5, t5, s11
	xor t5, t5, t2
	slliw a6, t5, 1
	srliw t5, t5, 31
	or t5, t5, a6
	add s3, s3, t5
	add s3, s3, a5
	xor a6, s5, s1
	xor a6, a6, s2
	add s3, s3, a6
	srli a6, s4, 27
	add s3, s3, a6
	srli s5, s5, 2
	slli s3, s3, 32
	srli a6, s3, 32
	or s3, s3, a6
	xor t6, t6, s6
	xor t6, t6, s0
	xor t6, t6, t3
	slliw a6, t6, 1
	srliw t6, t6, 31
	or t6, t6, a6
	add s2, s2, t6
	add s2, s2, a5
	xor a6, s4, s5
	xor a6, a6, s1
	add s2, s2, a6
	srli a6, s3, 27
	add s2, s2, a6
	srli s4, s4, 2
	slli s2, s2, 32
	srli a6, s2, 32
	or s2, s2, a6
	xor a7, a7, s7
	xor a7, a7, ra
	xor a7, a7, t4
	slliw a6, a7, 1
	srliw a7, a7, 31
	or a7, a7, a6
	add s1, s1, a7
	add s1, s1, a5
	xor a6, s3, s4
	xor a6, a6, s5
	add s1, s1, a6
	srli a6, s2, 27
	add s1, s1, a6
	srli s3, s3, 2
	slli s1, s1, 32
	srli a6, s1, 32
	or s1, s1, a6
	lwu a6, 124(a4)
	add s1, s1, a6
	lwu a6, 128(a4)
	add s2, s2, a6
	lwu a6, 132(a4)
	add s3, s3, a6
	lwu a6, 136(a4)
	add s4, s4, a6
	lwu a6, 140(a4)
	add s5, s5, a6
	lwu a6, 144(a4)
	xor a6, a6, s1
	sw a6, 144(a4)
	lwu a6, 148(a4)
	xor a6, a6, s2
	sw a6, 148(a4)
	lwu a6, 152(a4)
	xor a6, a6, s3
	sw a6, 152(a4)
	lwu a6, 156(a4)
	xor a6, a6, s4
	sw a6, 156(a4)
	lwu a6, 160(a4)
	xor a6, a6, s5
	sw a6, 160(a4)
	addi a2, a2, -1
	bnez a2, 22b
	j 21f
20:
21:
	lwu a6, 144(a4)
	srli a5, a6, 24
	sb a5, 0(a3)
	srli a5, a6, 16
	sb a5, 1(a3)
	srli a5, a6, 8
	sb a5, 2(a3)
	srli a5, a6, 0
	sb a5, 3(a3)
	lwu a6, 148(a4)
	srli a5, a6, 24
	sb a5, 4(a3)
	srli a5, a6, 16
	sb a5, 5(a3)
	srli a5, a6, 8
	sb a5, 6(a3)
	srli a5, a6, 0
	sb a5, 7(a3)
	lwu a6, 152(a4)
	srli a5, a6, 24
	sb a5, 8(a3)
	srli a5, a6, 16
	sb a5, 9(a3)
	srli a5, a6, 8
	sb a5, 10(a3)
	srli a5, a6, 0
	sb a5, 11(a3)
	lwu a6, 156(a4)
	srli a5, a6, 24
	sb a5, 12(a3)
	srli a5, a6, 16
	sb a5, 13(a3)
	srli a5, a6, 8
	sb a5, 14(a3)
	srli a5, a6, 0
	sb a5, 15(a3)
	lwu a6, 160(a4)
	srli a5, a6, 24
	sb a5, 16(a3)
	srli a5, a6, 16
	sb a5, 17(a3)
	srli a5, a6, 8
	sb a5, 18(a3)
	srli a5, a6, 0
	sb a5, 19(a3)
	ld ra, 0(a4)
	ld s0, 8(a4)
	ld s1, 16(a4)
	ld s2, 24(a4)
	ld s3, 32(a4)
	ld s4, 40(a4)
	ld s5, 48(a4)
	ld s6, 56(a4)
	ld s7, 64(a4)
	ld s8, 72(a4)
	ld s9, 80(a4)
	ld s10, 88(a4)
	ld s11, 96(a4)
	ret
	.option pop

vg_pbkdf2_hmac_sha1:
	.option push
	.option arch, +m, +c
	addi sp, sp, -240
	addi sp, sp, -368
	addi t0, sp, 0
	sd ra, 0(t0)
	sd s1, 8(t0)
	sd s2, 16(t0)
	sd s3, 24(t0)
	sd s4, 32(t0)
	sd s5, 40(t0)
	sd s6, 48(t0)
	sd s7, 56(t0)
	addi s1, t0, 0
	addi s2, a3, 0
	addi s3, a4, 0
	addi s4, a5, 0
	addi s5, a6, 0
	addi s6, a2, 0
	addi a2, a0, 0
	addi a3, a1, 0
	addi a0, s1, 64
	addi a1, s1, 148
	call {vg_hmac_sha1_init}
	addi s7, zero, 1
	beqz s5, 20f
22:
	lbu t1, 64(s1)
	sb t1, 232(s1)
	lbu t1, 65(s1)
	sb t1, 233(s1)
	lbu t1, 66(s1)
	sb t1, 234(s1)
	lbu t1, 67(s1)
	sb t1, 235(s1)
	lbu t1, 68(s1)
	sb t1, 236(s1)
	lbu t1, 69(s1)
	sb t1, 237(s1)
	lbu t1, 70(s1)
	sb t1, 238(s1)
	lbu t1, 71(s1)
	sb t1, 239(s1)
	lbu t1, 72(s1)
	sb t1, 240(s1)
	lbu t1, 73(s1)
	sb t1, 241(s1)
	lbu t1, 74(s1)
	sb t1, 242(s1)
	lbu t1, 75(s1)
	sb t1, 243(s1)
	lbu t1, 76(s1)
	sb t1, 244(s1)
	lbu t1, 77(s1)
	sb t1, 245(s1)
	lbu t1, 78(s1)
	sb t1, 246(s1)
	lbu t1, 79(s1)
	sb t1, 247(s1)
	lbu t1, 80(s1)
	sb t1, 248(s1)
	lbu t1, 81(s1)
	sb t1, 249(s1)
	lbu t1, 82(s1)
	sb t1, 250(s1)
	lbu t1, 83(s1)
	sb t1, 251(s1)
	lbu t1, 84(s1)
	sb t1, 252(s1)
	lbu t1, 85(s1)
	sb t1, 253(s1)
	lbu t1, 86(s1)
	sb t1, 254(s1)
	lbu t1, 87(s1)
	sb t1, 255(s1)
	lbu t1, 88(s1)
	sb t1, 256(s1)
	lbu t1, 89(s1)
	sb t1, 257(s1)
	lbu t1, 90(s1)
	sb t1, 258(s1)
	lbu t1, 91(s1)
	sb t1, 259(s1)
	lbu t1, 92(s1)
	sb t1, 260(s1)
	lbu t1, 93(s1)
	sb t1, 261(s1)
	lbu t1, 94(s1)
	sb t1, 262(s1)
	lbu t1, 95(s1)
	sb t1, 263(s1)
	lbu t1, 96(s1)
	sb t1, 264(s1)
	lbu t1, 97(s1)
	sb t1, 265(s1)
	lbu t1, 98(s1)
	sb t1, 266(s1)
	lbu t1, 99(s1)
	sb t1, 267(s1)
	lbu t1, 100(s1)
	sb t1, 268(s1)
	lbu t1, 101(s1)
	sb t1, 269(s1)
	lbu t1, 102(s1)
	sb t1, 270(s1)
	lbu t1, 103(s1)
	sb t1, 271(s1)
	lbu t1, 104(s1)
	sb t1, 272(s1)
	lbu t1, 105(s1)
	sb t1, 273(s1)
	lbu t1, 106(s1)
	sb t1, 274(s1)
	lbu t1, 107(s1)
	sb t1, 275(s1)
	lbu t1, 108(s1)
	sb t1, 276(s1)
	lbu t1, 109(s1)
	sb t1, 277(s1)
	lbu t1, 110(s1)
	sb t1, 278(s1)
	lbu t1, 111(s1)
	sb t1, 279(s1)
	lbu t1, 112(s1)
	sb t1, 280(s1)
	lbu t1, 113(s1)
	sb t1, 281(s1)
	lbu t1, 114(s1)
	sb t1, 282(s1)
	lbu t1, 115(s1)
	sb t1, 283(s1)
	lbu t1, 116(s1)
	sb t1, 284(s1)
	lbu t1, 117(s1)
	sb t1, 285(s1)
	lbu t1, 118(s1)
	sb t1, 286(s1)
	lbu t1, 119(s1)
	sb t1, 287(s1)
	lbu t1, 120(s1)
	sb t1, 288(s1)
	lbu t1, 121(s1)
	sb t1, 289(s1)
	lbu t1, 122(s1)
	sb t1, 290(s1)
	lbu t1, 123(s1)
	sb t1, 291(s1)
	lbu t1, 124(s1)
	sb t1, 292(s1)
	lbu t1, 125(s1)
	sb t1, 293(s1)
	lbu t1, 126(s1)
	sb t1, 294(s1)
	lbu t1, 127(s1)
	sb t1, 295(s1)
	lbu t1, 128(s1)
	sb t1, 296(s1)
	lbu t1, 129(s1)
	sb t1, 297(s1)
	lbu t1, 130(s1)
	sb t1, 298(s1)
	lbu t1, 131(s1)
	sb t1, 299(s1)
	lbu t1, 132(s1)
	sb t1, 300(s1)
	lbu t1, 133(s1)
	sb t1, 301(s1)
	lbu t1, 134(s1)
	sb t1, 302(s1)
	lbu t1, 135(s1)
	sb t1, 303(s1)
	lbu t1, 136(s1)
	sb t1, 304(s1)
	lbu t1, 137(s1)
	sb t1, 305(s1)
	lbu t1, 138(s1)
	sb t1, 306(s1)
	lbu t1, 139(s1)
	sb t1, 307(s1)
	lbu t1, 140(s1)
	sb t1, 308(s1)
	lbu t1, 141(s1)
	sb t1, 309(s1)
	lbu t1, 142(s1)
	sb t1, 310(s1)
	lbu t1, 143(s1)
	sb t1, 311(s1)
	lbu t1, 144(s1)
	sb t1, 312(s1)
	lbu t1, 145(s1)
	sb t1, 313(s1)
	lbu t1, 146(s1)
	sb t1, 314(s1)
	lbu t1, 147(s1)
	sb t1, 315(s1)
	addi a0, s1, 232
	addi a1, zero, 64
	addi a2, s6, 0
	addi a3, s2, 0
	call {vg_sha1_update}
	srli t1, s7, 24
	sb t1, 356(s1)
	srli t1, s7, 16
	sb t1, 357(s1)
	srli t1, s7, 8
	sb t1, 358(s1)
	sb s7, 359(s1)
	addi a0, s1, 232
	addi a1, s2, 64
	addi a2, s1, 356
	addi a3, zero, 4
	call {vg_sha1_update}
	addi a0, s1, 232
	addi a1, s1, 148
	addi a2, s2, 68
	addi a3, s1, 316
	call {vg_hmac_sha1_finalize}
	lbu t1, 316(s1)
	sb t1, 336(s1)
	lbu t1, 317(s1)
	sb t1, 337(s1)
	lbu t1, 318(s1)
	sb t1, 338(s1)
	lbu t1, 319(s1)
	sb t1, 339(s1)
	lbu t1, 320(s1)
	sb t1, 340(s1)
	lbu t1, 321(s1)
	sb t1, 341(s1)
	lbu t1, 322(s1)
	sb t1, 342(s1)
	lbu t1, 323(s1)
	sb t1, 343(s1)
	lbu t1, 324(s1)
	sb t1, 344(s1)
	lbu t1, 325(s1)
	sb t1, 345(s1)
	lbu t1, 326(s1)
	sb t1, 346(s1)
	lbu t1, 327(s1)
	sb t1, 347(s1)
	lbu t1, 328(s1)
	sb t1, 348(s1)
	lbu t1, 329(s1)
	sb t1, 349(s1)
	lbu t1, 330(s1)
	sb t1, 350(s1)
	lbu t1, 331(s1)
	sb t1, 351(s1)
	lbu t1, 332(s1)
	sb t1, 352(s1)
	lbu t1, 333(s1)
	sb t1, 353(s1)
	lbu t1, 334(s1)
	sb t1, 354(s1)
	lbu t1, 335(s1)
	sb t1, 355(s1)
	addi a0, s1, 64
	addi a1, s1, 316
	addi a2, s3, -1
	addi a3, s1, 336
	addi a4, s1, 368
	call {vg_pbkdf2_hmac_sha1_iterate}
	addi t1, s5, -20
	srli t1, t1, 63
	addi t2, s5, 0
	bnez t1, 23f
	addi t2, zero, 20
	j 24f
23:
24:
	addi t3, zero, 0
25:
	add t4, s1, t3
	lbu t1, 336(t4)
	add t4, s4, t3
	sb t1, 0(t4)
	addi t3, t3, 1
	addi t2, t2, -1
	bnez t2, 25b
	add s4, s4, t3
	sub s5, s5, t3
	addi s7, s7, 1
	bnez s5, 22b
	j 21f
20:
21:
	ld ra, 0(s1)
	ld s2, 16(s1)
	ld s3, 24(s1)
	ld s4, 32(s1)
	ld s5, 40(s1)
	ld s6, 48(s1)
	ld s7, 56(s1)
	ld s1, 8(s1)
	addi sp, sp, 368
	addi sp, sp, 240
	ret
	.option pop
