// The functions of `src/internal/vg_scrypt_blockmix_bytes.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_scrypt_blockmix_bytes:
	.option push
	.option arch, +m, +c
	sd s0, 0(a3)
	sd s1, 8(a3)
	sd s2, 16(a3)
	sd s3, 24(a3)
	sd s4, 32(a3)
	sd s5, 40(a3)
	sd s6, 48(a3)
	sd s7, 56(a3)
	sd s8, 64(a3)
	sd s10, 72(a3)
	addi s8, a1, 0
	addi s5, a0, 0
	addi s6, a2, 0
	addi s10, a3, 0
	slli t1, a1, 6
	add s7, a2, t1
	slli t1, a1, 7
	add t0, a0, t1
	addi t0, t0, -64
	lbu a2, 0(t0)
	lbu t1, 1(t0)
	slli t1, t1, 8
	or a2, a2, t1
	lbu t1, 2(t0)
	slli t1, t1, 16
	or a2, a2, t1
	lbu t1, 3(t0)
	slli t1, t1, 24
	or a2, a2, t1
	lbu a3, 4(t0)
	lbu t1, 5(t0)
	slli t1, t1, 8
	or a3, a3, t1
	lbu t1, 6(t0)
	slli t1, t1, 16
	or a3, a3, t1
	lbu t1, 7(t0)
	slli t1, t1, 24
	or a3, a3, t1
	lbu a4, 8(t0)
	lbu t1, 9(t0)
	slli t1, t1, 8
	or a4, a4, t1
	lbu t1, 10(t0)
	slli t1, t1, 16
	or a4, a4, t1
	lbu t1, 11(t0)
	slli t1, t1, 24
	or a4, a4, t1
	lbu a5, 12(t0)
	lbu t1, 13(t0)
	slli t1, t1, 8
	or a5, a5, t1
	lbu t1, 14(t0)
	slli t1, t1, 16
	or a5, a5, t1
	lbu t1, 15(t0)
	slli t1, t1, 24
	or a5, a5, t1
	lbu a6, 16(t0)
	lbu t1, 17(t0)
	slli t1, t1, 8
	or a6, a6, t1
	lbu t1, 18(t0)
	slli t1, t1, 16
	or a6, a6, t1
	lbu t1, 19(t0)
	slli t1, t1, 24
	or a6, a6, t1
	lbu a7, 20(t0)
	lbu t1, 21(t0)
	slli t1, t1, 8
	or a7, a7, t1
	lbu t1, 22(t0)
	slli t1, t1, 16
	or a7, a7, t1
	lbu t1, 23(t0)
	slli t1, t1, 24
	or a7, a7, t1
	lbu t2, 24(t0)
	lbu t1, 25(t0)
	slli t1, t1, 8
	or t2, t2, t1
	lbu t1, 26(t0)
	slli t1, t1, 16
	or t2, t2, t1
	lbu t1, 27(t0)
	slli t1, t1, 24
	or t2, t2, t1
	lbu t3, 28(t0)
	lbu t1, 29(t0)
	slli t1, t1, 8
	or t3, t3, t1
	lbu t1, 30(t0)
	slli t1, t1, 16
	or t3, t3, t1
	lbu t1, 31(t0)
	slli t1, t1, 24
	or t3, t3, t1
	lbu t4, 32(t0)
	lbu t1, 33(t0)
	slli t1, t1, 8
	or t4, t4, t1
	lbu t1, 34(t0)
	slli t1, t1, 16
	or t4, t4, t1
	lbu t1, 35(t0)
	slli t1, t1, 24
	or t4, t4, t1
	lbu t5, 36(t0)
	lbu t1, 37(t0)
	slli t1, t1, 8
	or t5, t5, t1
	lbu t1, 38(t0)
	slli t1, t1, 16
	or t5, t5, t1
	lbu t1, 39(t0)
	slli t1, t1, 24
	or t5, t5, t1
	lbu t6, 40(t0)
	lbu t1, 41(t0)
	slli t1, t1, 8
	or t6, t6, t1
	lbu t1, 42(t0)
	slli t1, t1, 16
	or t6, t6, t1
	lbu t1, 43(t0)
	slli t1, t1, 24
	or t6, t6, t1
	lbu s0, 44(t0)
	lbu t1, 45(t0)
	slli t1, t1, 8
	or s0, s0, t1
	lbu t1, 46(t0)
	slli t1, t1, 16
	or s0, s0, t1
	lbu t1, 47(t0)
	slli t1, t1, 24
	or s0, s0, t1
	lbu s1, 48(t0)
	lbu t1, 49(t0)
	slli t1, t1, 8
	or s1, s1, t1
	lbu t1, 50(t0)
	slli t1, t1, 16
	or s1, s1, t1
	lbu t1, 51(t0)
	slli t1, t1, 24
	or s1, s1, t1
	lbu s2, 52(t0)
	lbu t1, 53(t0)
	slli t1, t1, 8
	or s2, s2, t1
	lbu t1, 54(t0)
	slli t1, t1, 16
	or s2, s2, t1
	lbu t1, 55(t0)
	slli t1, t1, 24
	or s2, s2, t1
	lbu s3, 56(t0)
	lbu t1, 57(t0)
	slli t1, t1, 8
	or s3, s3, t1
	lbu t1, 58(t0)
	slli t1, t1, 16
	or s3, s3, t1
	lbu t1, 59(t0)
	slli t1, t1, 24
	or s3, s3, t1
	lbu s4, 60(t0)
	lbu t1, 61(t0)
	slli t1, t1, 8
	or s4, s4, t1
	lbu t1, 62(t0)
	slli t1, t1, 16
	or s4, s4, t1
	lbu t1, 63(t0)
	slli t1, t1, 24
	or s4, s4, t1
20:
	lbu t0, 0(s5)
	lbu t1, 1(s5)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 2(s5)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 3(s5)
	slli t1, t1, 24
	or t0, t0, t1
	xor a2, a2, t0
	sb a2, 0(s6)
	srli t1, a2, 8
	sb t1, 1(s6)
	srli t1, a2, 16
	sb t1, 2(s6)
	srli t1, a2, 24
	sb t1, 3(s6)
	lbu t0, 4(s5)
	lbu t1, 5(s5)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 6(s5)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 7(s5)
	slli t1, t1, 24
	or t0, t0, t1
	xor a3, a3, t0
	sb a3, 4(s6)
	srli t1, a3, 8
	sb t1, 5(s6)
	srli t1, a3, 16
	sb t1, 6(s6)
	srli t1, a3, 24
	sb t1, 7(s6)
	lbu t0, 8(s5)
	lbu t1, 9(s5)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 10(s5)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 11(s5)
	slli t1, t1, 24
	or t0, t0, t1
	xor a4, a4, t0
	sb a4, 8(s6)
	srli t1, a4, 8
	sb t1, 9(s6)
	srli t1, a4, 16
	sb t1, 10(s6)
	srli t1, a4, 24
	sb t1, 11(s6)
	lbu t0, 12(s5)
	lbu t1, 13(s5)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 14(s5)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 15(s5)
	slli t1, t1, 24
	or t0, t0, t1
	xor a5, a5, t0
	sb a5, 12(s6)
	srli t1, a5, 8
	sb t1, 13(s6)
	srli t1, a5, 16
	sb t1, 14(s6)
	srli t1, a5, 24
	sb t1, 15(s6)
	lbu t0, 16(s5)
	lbu t1, 17(s5)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 18(s5)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 19(s5)
	slli t1, t1, 24
	or t0, t0, t1
	xor a6, a6, t0
	sb a6, 16(s6)
	srli t1, a6, 8
	sb t1, 17(s6)
	srli t1, a6, 16
	sb t1, 18(s6)
	srli t1, a6, 24
	sb t1, 19(s6)
	lbu t0, 20(s5)
	lbu t1, 21(s5)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 22(s5)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 23(s5)
	slli t1, t1, 24
	or t0, t0, t1
	xor a7, a7, t0
	sb a7, 20(s6)
	srli t1, a7, 8
	sb t1, 21(s6)
	srli t1, a7, 16
	sb t1, 22(s6)
	srli t1, a7, 24
	sb t1, 23(s6)
	lbu t0, 24(s5)
	lbu t1, 25(s5)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 26(s5)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 27(s5)
	slli t1, t1, 24
	or t0, t0, t1
	xor t2, t2, t0
	sb t2, 24(s6)
	srli t1, t2, 8
	sb t1, 25(s6)
	srli t1, t2, 16
	sb t1, 26(s6)
	srli t1, t2, 24
	sb t1, 27(s6)
	lbu t0, 28(s5)
	lbu t1, 29(s5)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 30(s5)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 31(s5)
	slli t1, t1, 24
	or t0, t0, t1
	xor t3, t3, t0
	sb t3, 28(s6)
	srli t1, t3, 8
	sb t1, 29(s6)
	srli t1, t3, 16
	sb t1, 30(s6)
	srli t1, t3, 24
	sb t1, 31(s6)
	lbu t0, 32(s5)
	lbu t1, 33(s5)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 34(s5)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 35(s5)
	slli t1, t1, 24
	or t0, t0, t1
	xor t4, t4, t0
	sb t4, 32(s6)
	srli t1, t4, 8
	sb t1, 33(s6)
	srli t1, t4, 16
	sb t1, 34(s6)
	srli t1, t4, 24
	sb t1, 35(s6)
	lbu t0, 36(s5)
	lbu t1, 37(s5)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 38(s5)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 39(s5)
	slli t1, t1, 24
	or t0, t0, t1
	xor t5, t5, t0
	sb t5, 36(s6)
	srli t1, t5, 8
	sb t1, 37(s6)
	srli t1, t5, 16
	sb t1, 38(s6)
	srli t1, t5, 24
	sb t1, 39(s6)
	lbu t0, 40(s5)
	lbu t1, 41(s5)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 42(s5)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 43(s5)
	slli t1, t1, 24
	or t0, t0, t1
	xor t6, t6, t0
	sb t6, 40(s6)
	srli t1, t6, 8
	sb t1, 41(s6)
	srli t1, t6, 16
	sb t1, 42(s6)
	srli t1, t6, 24
	sb t1, 43(s6)
	lbu t0, 44(s5)
	lbu t1, 45(s5)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 46(s5)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 47(s5)
	slli t1, t1, 24
	or t0, t0, t1
	xor s0, s0, t0
	sb s0, 44(s6)
	srli t1, s0, 8
	sb t1, 45(s6)
	srli t1, s0, 16
	sb t1, 46(s6)
	srli t1, s0, 24
	sb t1, 47(s6)
	lbu t0, 48(s5)
	lbu t1, 49(s5)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 50(s5)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 51(s5)
	slli t1, t1, 24
	or t0, t0, t1
	xor s1, s1, t0
	sb s1, 48(s6)
	srli t1, s1, 8
	sb t1, 49(s6)
	srli t1, s1, 16
	sb t1, 50(s6)
	srli t1, s1, 24
	sb t1, 51(s6)
	lbu t0, 52(s5)
	lbu t1, 53(s5)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 54(s5)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 55(s5)
	slli t1, t1, 24
	or t0, t0, t1
	xor s2, s2, t0
	sb s2, 52(s6)
	srli t1, s2, 8
	sb t1, 53(s6)
	srli t1, s2, 16
	sb t1, 54(s6)
	srli t1, s2, 24
	sb t1, 55(s6)
	lbu t0, 56(s5)
	lbu t1, 57(s5)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 58(s5)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 59(s5)
	slli t1, t1, 24
	or t0, t0, t1
	xor s3, s3, t0
	sb s3, 56(s6)
	srli t1, s3, 8
	sb t1, 57(s6)
	srli t1, s3, 16
	sb t1, 58(s6)
	srli t1, s3, 24
	sb t1, 59(s6)
	lbu t0, 60(s5)
	lbu t1, 61(s5)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 62(s5)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 63(s5)
	slli t1, t1, 24
	or t0, t0, t1
	xor s4, s4, t0
	sb s4, 60(s6)
	srli t1, s4, 8
	sb t1, 61(s6)
	srli t1, s4, 16
	sb t1, 62(s6)
	srli t1, s4, 24
	sb t1, 63(s6)
	addw t0, a2, s1
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor a6, a6, t1
	xor a6, a6, t0
	addw t0, a7, a3
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor t5, t5, t1
	xor t5, t5, t0
	addw t0, t6, t2
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor s3, s3, t1
	xor s3, s3, t0
	addw t0, s4, s0
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor a5, a5, t1
	xor a5, a5, t0
	addw t0, a6, a2
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t4, t4, t1
	xor t4, t4, t0
	addw t0, t5, a7
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor s2, s2, t1
	xor s2, s2, t0
	addw t0, s3, t6
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor a4, a4, t1
	xor a4, a4, t0
	addw t0, a5, s4
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t3, t3, t1
	xor t3, t3, t0
	addw t0, t4, a6
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor s1, s1, t1
	xor s1, s1, t0
	addw t0, s2, t5
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor a3, a3, t1
	xor a3, a3, t0
	addw t0, a4, s3
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor t2, t2, t1
	xor t2, t2, t0
	addw t0, t3, a5
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor s0, s0, t1
	xor s0, s0, t0
	addw t0, s1, t4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a2, a2, t1
	xor a2, a2, t0
	addw t0, a3, s2
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a7, a7, t1
	xor a7, a7, t0
	addw t0, t2, a4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor t6, t6, t1
	xor t6, t6, t0
	addw t0, s0, t3
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor s4, s4, t1
	xor s4, s4, t0
	addw t0, a2, a5
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor a3, a3, t1
	xor a3, a3, t0
	addw t0, a7, a6
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor t2, t2, t1
	xor t2, t2, t0
	addw t0, t6, t5
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor s0, s0, t1
	xor s0, s0, t0
	addw t0, s4, s3
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor s1, s1, t1
	xor s1, s1, t0
	addw t0, a3, a2
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor a4, a4, t1
	xor a4, a4, t0
	addw t0, t2, a7
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t3, t3, t1
	xor t3, t3, t0
	addw t0, s0, t6
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t4, t4, t1
	xor t4, t4, t0
	addw t0, s1, s4
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor s2, s2, t1
	xor s2, s2, t0
	addw t0, a4, a3
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor a5, a5, t1
	xor a5, a5, t0
	addw t0, t3, t2
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor a6, a6, t1
	xor a6, a6, t0
	addw t0, t4, s0
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor t5, t5, t1
	xor t5, t5, t0
	addw t0, s2, s1
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor s3, s3, t1
	xor s3, s3, t0
	addw t0, a5, a4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a2, a2, t1
	xor a2, a2, t0
	addw t0, a6, t3
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a7, a7, t1
	xor a7, a7, t0
	addw t0, t5, t4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor t6, t6, t1
	xor t6, t6, t0
	addw t0, s3, s2
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor s4, s4, t1
	xor s4, s4, t0
	addw t0, a2, s1
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor a6, a6, t1
	xor a6, a6, t0
	addw t0, a7, a3
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor t5, t5, t1
	xor t5, t5, t0
	addw t0, t6, t2
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor s3, s3, t1
	xor s3, s3, t0
	addw t0, s4, s0
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor a5, a5, t1
	xor a5, a5, t0
	addw t0, a6, a2
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t4, t4, t1
	xor t4, t4, t0
	addw t0, t5, a7
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor s2, s2, t1
	xor s2, s2, t0
	addw t0, s3, t6
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor a4, a4, t1
	xor a4, a4, t0
	addw t0, a5, s4
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t3, t3, t1
	xor t3, t3, t0
	addw t0, t4, a6
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor s1, s1, t1
	xor s1, s1, t0
	addw t0, s2, t5
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor a3, a3, t1
	xor a3, a3, t0
	addw t0, a4, s3
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor t2, t2, t1
	xor t2, t2, t0
	addw t0, t3, a5
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor s0, s0, t1
	xor s0, s0, t0
	addw t0, s1, t4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a2, a2, t1
	xor a2, a2, t0
	addw t0, a3, s2
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a7, a7, t1
	xor a7, a7, t0
	addw t0, t2, a4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor t6, t6, t1
	xor t6, t6, t0
	addw t0, s0, t3
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor s4, s4, t1
	xor s4, s4, t0
	addw t0, a2, a5
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor a3, a3, t1
	xor a3, a3, t0
	addw t0, a7, a6
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor t2, t2, t1
	xor t2, t2, t0
	addw t0, t6, t5
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor s0, s0, t1
	xor s0, s0, t0
	addw t0, s4, s3
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor s1, s1, t1
	xor s1, s1, t0
	addw t0, a3, a2
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor a4, a4, t1
	xor a4, a4, t0
	addw t0, t2, a7
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t3, t3, t1
	xor t3, t3, t0
	addw t0, s0, t6
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t4, t4, t1
	xor t4, t4, t0
	addw t0, s1, s4
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor s2, s2, t1
	xor s2, s2, t0
	addw t0, a4, a3
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor a5, a5, t1
	xor a5, a5, t0
	addw t0, t3, t2
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor a6, a6, t1
	xor a6, a6, t0
	addw t0, t4, s0
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor t5, t5, t1
	xor t5, t5, t0
	addw t0, s2, s1
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor s3, s3, t1
	xor s3, s3, t0
	addw t0, a5, a4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a2, a2, t1
	xor a2, a2, t0
	addw t0, a6, t3
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a7, a7, t1
	xor a7, a7, t0
	addw t0, t5, t4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor t6, t6, t1
	xor t6, t6, t0
	addw t0, s3, s2
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor s4, s4, t1
	xor s4, s4, t0
	addw t0, a2, s1
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor a6, a6, t1
	xor a6, a6, t0
	addw t0, a7, a3
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor t5, t5, t1
	xor t5, t5, t0
	addw t0, t6, t2
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor s3, s3, t1
	xor s3, s3, t0
	addw t0, s4, s0
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor a5, a5, t1
	xor a5, a5, t0
	addw t0, a6, a2
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t4, t4, t1
	xor t4, t4, t0
	addw t0, t5, a7
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor s2, s2, t1
	xor s2, s2, t0
	addw t0, s3, t6
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor a4, a4, t1
	xor a4, a4, t0
	addw t0, a5, s4
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t3, t3, t1
	xor t3, t3, t0
	addw t0, t4, a6
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor s1, s1, t1
	xor s1, s1, t0
	addw t0, s2, t5
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor a3, a3, t1
	xor a3, a3, t0
	addw t0, a4, s3
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor t2, t2, t1
	xor t2, t2, t0
	addw t0, t3, a5
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor s0, s0, t1
	xor s0, s0, t0
	addw t0, s1, t4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a2, a2, t1
	xor a2, a2, t0
	addw t0, a3, s2
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a7, a7, t1
	xor a7, a7, t0
	addw t0, t2, a4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor t6, t6, t1
	xor t6, t6, t0
	addw t0, s0, t3
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor s4, s4, t1
	xor s4, s4, t0
	addw t0, a2, a5
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor a3, a3, t1
	xor a3, a3, t0
	addw t0, a7, a6
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor t2, t2, t1
	xor t2, t2, t0
	addw t0, t6, t5
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor s0, s0, t1
	xor s0, s0, t0
	addw t0, s4, s3
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor s1, s1, t1
	xor s1, s1, t0
	addw t0, a3, a2
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor a4, a4, t1
	xor a4, a4, t0
	addw t0, t2, a7
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t3, t3, t1
	xor t3, t3, t0
	addw t0, s0, t6
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t4, t4, t1
	xor t4, t4, t0
	addw t0, s1, s4
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor s2, s2, t1
	xor s2, s2, t0
	addw t0, a4, a3
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor a5, a5, t1
	xor a5, a5, t0
	addw t0, t3, t2
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor a6, a6, t1
	xor a6, a6, t0
	addw t0, t4, s0
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor t5, t5, t1
	xor t5, t5, t0
	addw t0, s2, s1
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor s3, s3, t1
	xor s3, s3, t0
	addw t0, a5, a4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a2, a2, t1
	xor a2, a2, t0
	addw t0, a6, t3
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a7, a7, t1
	xor a7, a7, t0
	addw t0, t5, t4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor t6, t6, t1
	xor t6, t6, t0
	addw t0, s3, s2
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor s4, s4, t1
	xor s4, s4, t0
	addw t0, a2, s1
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor a6, a6, t1
	xor a6, a6, t0
	addw t0, a7, a3
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor t5, t5, t1
	xor t5, t5, t0
	addw t0, t6, t2
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor s3, s3, t1
	xor s3, s3, t0
	addw t0, s4, s0
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor a5, a5, t1
	xor a5, a5, t0
	addw t0, a6, a2
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t4, t4, t1
	xor t4, t4, t0
	addw t0, t5, a7
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor s2, s2, t1
	xor s2, s2, t0
	addw t0, s3, t6
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor a4, a4, t1
	xor a4, a4, t0
	addw t0, a5, s4
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t3, t3, t1
	xor t3, t3, t0
	addw t0, t4, a6
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor s1, s1, t1
	xor s1, s1, t0
	addw t0, s2, t5
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor a3, a3, t1
	xor a3, a3, t0
	addw t0, a4, s3
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor t2, t2, t1
	xor t2, t2, t0
	addw t0, t3, a5
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor s0, s0, t1
	xor s0, s0, t0
	addw t0, s1, t4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a2, a2, t1
	xor a2, a2, t0
	addw t0, a3, s2
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a7, a7, t1
	xor a7, a7, t0
	addw t0, t2, a4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor t6, t6, t1
	xor t6, t6, t0
	addw t0, s0, t3
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor s4, s4, t1
	xor s4, s4, t0
	addw t0, a2, a5
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor a3, a3, t1
	xor a3, a3, t0
	addw t0, a7, a6
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor t2, t2, t1
	xor t2, t2, t0
	addw t0, t6, t5
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor s0, s0, t1
	xor s0, s0, t0
	addw t0, s4, s3
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor s1, s1, t1
	xor s1, s1, t0
	addw t0, a3, a2
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor a4, a4, t1
	xor a4, a4, t0
	addw t0, t2, a7
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t3, t3, t1
	xor t3, t3, t0
	addw t0, s0, t6
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t4, t4, t1
	xor t4, t4, t0
	addw t0, s1, s4
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor s2, s2, t1
	xor s2, s2, t0
	addw t0, a4, a3
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor a5, a5, t1
	xor a5, a5, t0
	addw t0, t3, t2
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor a6, a6, t1
	xor a6, a6, t0
	addw t0, t4, s0
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor t5, t5, t1
	xor t5, t5, t0
	addw t0, s2, s1
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor s3, s3, t1
	xor s3, s3, t0
	addw t0, a5, a4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a2, a2, t1
	xor a2, a2, t0
	addw t0, a6, t3
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a7, a7, t1
	xor a7, a7, t0
	addw t0, t5, t4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor t6, t6, t1
	xor t6, t6, t0
	addw t0, s3, s2
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor s4, s4, t1
	xor s4, s4, t0
	lbu t0, 0(s6)
	lbu t1, 1(s6)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 2(s6)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 3(s6)
	slli t1, t1, 24
	or t0, t0, t1
	addw a2, a2, t0
	sb a2, 0(s6)
	srli t1, a2, 8
	sb t1, 1(s6)
	srli t1, a2, 16
	sb t1, 2(s6)
	srli t1, a2, 24
	sb t1, 3(s6)
	lbu t0, 4(s6)
	lbu t1, 5(s6)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 6(s6)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 7(s6)
	slli t1, t1, 24
	or t0, t0, t1
	addw a3, a3, t0
	sb a3, 4(s6)
	srli t1, a3, 8
	sb t1, 5(s6)
	srli t1, a3, 16
	sb t1, 6(s6)
	srli t1, a3, 24
	sb t1, 7(s6)
	lbu t0, 8(s6)
	lbu t1, 9(s6)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 10(s6)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 11(s6)
	slli t1, t1, 24
	or t0, t0, t1
	addw a4, a4, t0
	sb a4, 8(s6)
	srli t1, a4, 8
	sb t1, 9(s6)
	srli t1, a4, 16
	sb t1, 10(s6)
	srli t1, a4, 24
	sb t1, 11(s6)
	lbu t0, 12(s6)
	lbu t1, 13(s6)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 14(s6)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 15(s6)
	slli t1, t1, 24
	or t0, t0, t1
	addw a5, a5, t0
	sb a5, 12(s6)
	srli t1, a5, 8
	sb t1, 13(s6)
	srli t1, a5, 16
	sb t1, 14(s6)
	srli t1, a5, 24
	sb t1, 15(s6)
	lbu t0, 16(s6)
	lbu t1, 17(s6)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 18(s6)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 19(s6)
	slli t1, t1, 24
	or t0, t0, t1
	addw a6, a6, t0
	sb a6, 16(s6)
	srli t1, a6, 8
	sb t1, 17(s6)
	srli t1, a6, 16
	sb t1, 18(s6)
	srli t1, a6, 24
	sb t1, 19(s6)
	lbu t0, 20(s6)
	lbu t1, 21(s6)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 22(s6)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 23(s6)
	slli t1, t1, 24
	or t0, t0, t1
	addw a7, a7, t0
	sb a7, 20(s6)
	srli t1, a7, 8
	sb t1, 21(s6)
	srli t1, a7, 16
	sb t1, 22(s6)
	srli t1, a7, 24
	sb t1, 23(s6)
	lbu t0, 24(s6)
	lbu t1, 25(s6)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 26(s6)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 27(s6)
	slli t1, t1, 24
	or t0, t0, t1
	addw t2, t2, t0
	sb t2, 24(s6)
	srli t1, t2, 8
	sb t1, 25(s6)
	srli t1, t2, 16
	sb t1, 26(s6)
	srli t1, t2, 24
	sb t1, 27(s6)
	lbu t0, 28(s6)
	lbu t1, 29(s6)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 30(s6)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 31(s6)
	slli t1, t1, 24
	or t0, t0, t1
	addw t3, t3, t0
	sb t3, 28(s6)
	srli t1, t3, 8
	sb t1, 29(s6)
	srli t1, t3, 16
	sb t1, 30(s6)
	srli t1, t3, 24
	sb t1, 31(s6)
	lbu t0, 32(s6)
	lbu t1, 33(s6)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 34(s6)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 35(s6)
	slli t1, t1, 24
	or t0, t0, t1
	addw t4, t4, t0
	sb t4, 32(s6)
	srli t1, t4, 8
	sb t1, 33(s6)
	srli t1, t4, 16
	sb t1, 34(s6)
	srli t1, t4, 24
	sb t1, 35(s6)
	lbu t0, 36(s6)
	lbu t1, 37(s6)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 38(s6)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 39(s6)
	slli t1, t1, 24
	or t0, t0, t1
	addw t5, t5, t0
	sb t5, 36(s6)
	srli t1, t5, 8
	sb t1, 37(s6)
	srli t1, t5, 16
	sb t1, 38(s6)
	srli t1, t5, 24
	sb t1, 39(s6)
	lbu t0, 40(s6)
	lbu t1, 41(s6)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 42(s6)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 43(s6)
	slli t1, t1, 24
	or t0, t0, t1
	addw t6, t6, t0
	sb t6, 40(s6)
	srli t1, t6, 8
	sb t1, 41(s6)
	srli t1, t6, 16
	sb t1, 42(s6)
	srli t1, t6, 24
	sb t1, 43(s6)
	lbu t0, 44(s6)
	lbu t1, 45(s6)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 46(s6)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 47(s6)
	slli t1, t1, 24
	or t0, t0, t1
	addw s0, s0, t0
	sb s0, 44(s6)
	srli t1, s0, 8
	sb t1, 45(s6)
	srli t1, s0, 16
	sb t1, 46(s6)
	srli t1, s0, 24
	sb t1, 47(s6)
	lbu t0, 48(s6)
	lbu t1, 49(s6)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 50(s6)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 51(s6)
	slli t1, t1, 24
	or t0, t0, t1
	addw s1, s1, t0
	sb s1, 48(s6)
	srli t1, s1, 8
	sb t1, 49(s6)
	srli t1, s1, 16
	sb t1, 50(s6)
	srli t1, s1, 24
	sb t1, 51(s6)
	lbu t0, 52(s6)
	lbu t1, 53(s6)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 54(s6)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 55(s6)
	slli t1, t1, 24
	or t0, t0, t1
	addw s2, s2, t0
	sb s2, 52(s6)
	srli t1, s2, 8
	sb t1, 53(s6)
	srli t1, s2, 16
	sb t1, 54(s6)
	srli t1, s2, 24
	sb t1, 55(s6)
	lbu t0, 56(s6)
	lbu t1, 57(s6)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 58(s6)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 59(s6)
	slli t1, t1, 24
	or t0, t0, t1
	addw s3, s3, t0
	sb s3, 56(s6)
	srli t1, s3, 8
	sb t1, 57(s6)
	srli t1, s3, 16
	sb t1, 58(s6)
	srli t1, s3, 24
	sb t1, 59(s6)
	lbu t0, 60(s6)
	lbu t1, 61(s6)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 62(s6)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 63(s6)
	slli t1, t1, 24
	or t0, t0, t1
	addw s4, s4, t0
	sb s4, 60(s6)
	srli t1, s4, 8
	sb t1, 61(s6)
	srli t1, s4, 16
	sb t1, 62(s6)
	srli t1, s4, 24
	sb t1, 63(s6)
	addi s5, s5, 64
	lbu t0, 0(s5)
	lbu t1, 1(s5)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 2(s5)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 3(s5)
	slli t1, t1, 24
	or t0, t0, t1
	xor a2, a2, t0
	sb a2, 0(s7)
	srli t1, a2, 8
	sb t1, 1(s7)
	srli t1, a2, 16
	sb t1, 2(s7)
	srli t1, a2, 24
	sb t1, 3(s7)
	lbu t0, 4(s5)
	lbu t1, 5(s5)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 6(s5)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 7(s5)
	slli t1, t1, 24
	or t0, t0, t1
	xor a3, a3, t0
	sb a3, 4(s7)
	srli t1, a3, 8
	sb t1, 5(s7)
	srli t1, a3, 16
	sb t1, 6(s7)
	srli t1, a3, 24
	sb t1, 7(s7)
	lbu t0, 8(s5)
	lbu t1, 9(s5)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 10(s5)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 11(s5)
	slli t1, t1, 24
	or t0, t0, t1
	xor a4, a4, t0
	sb a4, 8(s7)
	srli t1, a4, 8
	sb t1, 9(s7)
	srli t1, a4, 16
	sb t1, 10(s7)
	srli t1, a4, 24
	sb t1, 11(s7)
	lbu t0, 12(s5)
	lbu t1, 13(s5)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 14(s5)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 15(s5)
	slli t1, t1, 24
	or t0, t0, t1
	xor a5, a5, t0
	sb a5, 12(s7)
	srli t1, a5, 8
	sb t1, 13(s7)
	srli t1, a5, 16
	sb t1, 14(s7)
	srli t1, a5, 24
	sb t1, 15(s7)
	lbu t0, 16(s5)
	lbu t1, 17(s5)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 18(s5)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 19(s5)
	slli t1, t1, 24
	or t0, t0, t1
	xor a6, a6, t0
	sb a6, 16(s7)
	srli t1, a6, 8
	sb t1, 17(s7)
	srli t1, a6, 16
	sb t1, 18(s7)
	srli t1, a6, 24
	sb t1, 19(s7)
	lbu t0, 20(s5)
	lbu t1, 21(s5)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 22(s5)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 23(s5)
	slli t1, t1, 24
	or t0, t0, t1
	xor a7, a7, t0
	sb a7, 20(s7)
	srli t1, a7, 8
	sb t1, 21(s7)
	srli t1, a7, 16
	sb t1, 22(s7)
	srli t1, a7, 24
	sb t1, 23(s7)
	lbu t0, 24(s5)
	lbu t1, 25(s5)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 26(s5)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 27(s5)
	slli t1, t1, 24
	or t0, t0, t1
	xor t2, t2, t0
	sb t2, 24(s7)
	srli t1, t2, 8
	sb t1, 25(s7)
	srli t1, t2, 16
	sb t1, 26(s7)
	srli t1, t2, 24
	sb t1, 27(s7)
	lbu t0, 28(s5)
	lbu t1, 29(s5)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 30(s5)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 31(s5)
	slli t1, t1, 24
	or t0, t0, t1
	xor t3, t3, t0
	sb t3, 28(s7)
	srli t1, t3, 8
	sb t1, 29(s7)
	srli t1, t3, 16
	sb t1, 30(s7)
	srli t1, t3, 24
	sb t1, 31(s7)
	lbu t0, 32(s5)
	lbu t1, 33(s5)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 34(s5)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 35(s5)
	slli t1, t1, 24
	or t0, t0, t1
	xor t4, t4, t0
	sb t4, 32(s7)
	srli t1, t4, 8
	sb t1, 33(s7)
	srli t1, t4, 16
	sb t1, 34(s7)
	srli t1, t4, 24
	sb t1, 35(s7)
	lbu t0, 36(s5)
	lbu t1, 37(s5)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 38(s5)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 39(s5)
	slli t1, t1, 24
	or t0, t0, t1
	xor t5, t5, t0
	sb t5, 36(s7)
	srli t1, t5, 8
	sb t1, 37(s7)
	srli t1, t5, 16
	sb t1, 38(s7)
	srli t1, t5, 24
	sb t1, 39(s7)
	lbu t0, 40(s5)
	lbu t1, 41(s5)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 42(s5)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 43(s5)
	slli t1, t1, 24
	or t0, t0, t1
	xor t6, t6, t0
	sb t6, 40(s7)
	srli t1, t6, 8
	sb t1, 41(s7)
	srli t1, t6, 16
	sb t1, 42(s7)
	srli t1, t6, 24
	sb t1, 43(s7)
	lbu t0, 44(s5)
	lbu t1, 45(s5)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 46(s5)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 47(s5)
	slli t1, t1, 24
	or t0, t0, t1
	xor s0, s0, t0
	sb s0, 44(s7)
	srli t1, s0, 8
	sb t1, 45(s7)
	srli t1, s0, 16
	sb t1, 46(s7)
	srli t1, s0, 24
	sb t1, 47(s7)
	lbu t0, 48(s5)
	lbu t1, 49(s5)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 50(s5)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 51(s5)
	slli t1, t1, 24
	or t0, t0, t1
	xor s1, s1, t0
	sb s1, 48(s7)
	srli t1, s1, 8
	sb t1, 49(s7)
	srli t1, s1, 16
	sb t1, 50(s7)
	srli t1, s1, 24
	sb t1, 51(s7)
	lbu t0, 52(s5)
	lbu t1, 53(s5)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 54(s5)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 55(s5)
	slli t1, t1, 24
	or t0, t0, t1
	xor s2, s2, t0
	sb s2, 52(s7)
	srli t1, s2, 8
	sb t1, 53(s7)
	srli t1, s2, 16
	sb t1, 54(s7)
	srli t1, s2, 24
	sb t1, 55(s7)
	lbu t0, 56(s5)
	lbu t1, 57(s5)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 58(s5)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 59(s5)
	slli t1, t1, 24
	or t0, t0, t1
	xor s3, s3, t0
	sb s3, 56(s7)
	srli t1, s3, 8
	sb t1, 57(s7)
	srli t1, s3, 16
	sb t1, 58(s7)
	srli t1, s3, 24
	sb t1, 59(s7)
	lbu t0, 60(s5)
	lbu t1, 61(s5)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 62(s5)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 63(s5)
	slli t1, t1, 24
	or t0, t0, t1
	xor s4, s4, t0
	sb s4, 60(s7)
	srli t1, s4, 8
	sb t1, 61(s7)
	srli t1, s4, 16
	sb t1, 62(s7)
	srli t1, s4, 24
	sb t1, 63(s7)
	addw t0, a2, s1
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor a6, a6, t1
	xor a6, a6, t0
	addw t0, a7, a3
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor t5, t5, t1
	xor t5, t5, t0
	addw t0, t6, t2
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor s3, s3, t1
	xor s3, s3, t0
	addw t0, s4, s0
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor a5, a5, t1
	xor a5, a5, t0
	addw t0, a6, a2
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t4, t4, t1
	xor t4, t4, t0
	addw t0, t5, a7
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor s2, s2, t1
	xor s2, s2, t0
	addw t0, s3, t6
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor a4, a4, t1
	xor a4, a4, t0
	addw t0, a5, s4
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t3, t3, t1
	xor t3, t3, t0
	addw t0, t4, a6
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor s1, s1, t1
	xor s1, s1, t0
	addw t0, s2, t5
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor a3, a3, t1
	xor a3, a3, t0
	addw t0, a4, s3
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor t2, t2, t1
	xor t2, t2, t0
	addw t0, t3, a5
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor s0, s0, t1
	xor s0, s0, t0
	addw t0, s1, t4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a2, a2, t1
	xor a2, a2, t0
	addw t0, a3, s2
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a7, a7, t1
	xor a7, a7, t0
	addw t0, t2, a4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor t6, t6, t1
	xor t6, t6, t0
	addw t0, s0, t3
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor s4, s4, t1
	xor s4, s4, t0
	addw t0, a2, a5
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor a3, a3, t1
	xor a3, a3, t0
	addw t0, a7, a6
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor t2, t2, t1
	xor t2, t2, t0
	addw t0, t6, t5
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor s0, s0, t1
	xor s0, s0, t0
	addw t0, s4, s3
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor s1, s1, t1
	xor s1, s1, t0
	addw t0, a3, a2
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor a4, a4, t1
	xor a4, a4, t0
	addw t0, t2, a7
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t3, t3, t1
	xor t3, t3, t0
	addw t0, s0, t6
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t4, t4, t1
	xor t4, t4, t0
	addw t0, s1, s4
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor s2, s2, t1
	xor s2, s2, t0
	addw t0, a4, a3
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor a5, a5, t1
	xor a5, a5, t0
	addw t0, t3, t2
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor a6, a6, t1
	xor a6, a6, t0
	addw t0, t4, s0
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor t5, t5, t1
	xor t5, t5, t0
	addw t0, s2, s1
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor s3, s3, t1
	xor s3, s3, t0
	addw t0, a5, a4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a2, a2, t1
	xor a2, a2, t0
	addw t0, a6, t3
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a7, a7, t1
	xor a7, a7, t0
	addw t0, t5, t4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor t6, t6, t1
	xor t6, t6, t0
	addw t0, s3, s2
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor s4, s4, t1
	xor s4, s4, t0
	addw t0, a2, s1
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor a6, a6, t1
	xor a6, a6, t0
	addw t0, a7, a3
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor t5, t5, t1
	xor t5, t5, t0
	addw t0, t6, t2
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor s3, s3, t1
	xor s3, s3, t0
	addw t0, s4, s0
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor a5, a5, t1
	xor a5, a5, t0
	addw t0, a6, a2
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t4, t4, t1
	xor t4, t4, t0
	addw t0, t5, a7
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor s2, s2, t1
	xor s2, s2, t0
	addw t0, s3, t6
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor a4, a4, t1
	xor a4, a4, t0
	addw t0, a5, s4
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t3, t3, t1
	xor t3, t3, t0
	addw t0, t4, a6
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor s1, s1, t1
	xor s1, s1, t0
	addw t0, s2, t5
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor a3, a3, t1
	xor a3, a3, t0
	addw t0, a4, s3
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor t2, t2, t1
	xor t2, t2, t0
	addw t0, t3, a5
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor s0, s0, t1
	xor s0, s0, t0
	addw t0, s1, t4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a2, a2, t1
	xor a2, a2, t0
	addw t0, a3, s2
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a7, a7, t1
	xor a7, a7, t0
	addw t0, t2, a4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor t6, t6, t1
	xor t6, t6, t0
	addw t0, s0, t3
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor s4, s4, t1
	xor s4, s4, t0
	addw t0, a2, a5
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor a3, a3, t1
	xor a3, a3, t0
	addw t0, a7, a6
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor t2, t2, t1
	xor t2, t2, t0
	addw t0, t6, t5
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor s0, s0, t1
	xor s0, s0, t0
	addw t0, s4, s3
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor s1, s1, t1
	xor s1, s1, t0
	addw t0, a3, a2
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor a4, a4, t1
	xor a4, a4, t0
	addw t0, t2, a7
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t3, t3, t1
	xor t3, t3, t0
	addw t0, s0, t6
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t4, t4, t1
	xor t4, t4, t0
	addw t0, s1, s4
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor s2, s2, t1
	xor s2, s2, t0
	addw t0, a4, a3
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor a5, a5, t1
	xor a5, a5, t0
	addw t0, t3, t2
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor a6, a6, t1
	xor a6, a6, t0
	addw t0, t4, s0
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor t5, t5, t1
	xor t5, t5, t0
	addw t0, s2, s1
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor s3, s3, t1
	xor s3, s3, t0
	addw t0, a5, a4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a2, a2, t1
	xor a2, a2, t0
	addw t0, a6, t3
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a7, a7, t1
	xor a7, a7, t0
	addw t0, t5, t4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor t6, t6, t1
	xor t6, t6, t0
	addw t0, s3, s2
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor s4, s4, t1
	xor s4, s4, t0
	addw t0, a2, s1
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor a6, a6, t1
	xor a6, a6, t0
	addw t0, a7, a3
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor t5, t5, t1
	xor t5, t5, t0
	addw t0, t6, t2
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor s3, s3, t1
	xor s3, s3, t0
	addw t0, s4, s0
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor a5, a5, t1
	xor a5, a5, t0
	addw t0, a6, a2
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t4, t4, t1
	xor t4, t4, t0
	addw t0, t5, a7
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor s2, s2, t1
	xor s2, s2, t0
	addw t0, s3, t6
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor a4, a4, t1
	xor a4, a4, t0
	addw t0, a5, s4
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t3, t3, t1
	xor t3, t3, t0
	addw t0, t4, a6
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor s1, s1, t1
	xor s1, s1, t0
	addw t0, s2, t5
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor a3, a3, t1
	xor a3, a3, t0
	addw t0, a4, s3
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor t2, t2, t1
	xor t2, t2, t0
	addw t0, t3, a5
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor s0, s0, t1
	xor s0, s0, t0
	addw t0, s1, t4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a2, a2, t1
	xor a2, a2, t0
	addw t0, a3, s2
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a7, a7, t1
	xor a7, a7, t0
	addw t0, t2, a4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor t6, t6, t1
	xor t6, t6, t0
	addw t0, s0, t3
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor s4, s4, t1
	xor s4, s4, t0
	addw t0, a2, a5
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor a3, a3, t1
	xor a3, a3, t0
	addw t0, a7, a6
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor t2, t2, t1
	xor t2, t2, t0
	addw t0, t6, t5
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor s0, s0, t1
	xor s0, s0, t0
	addw t0, s4, s3
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor s1, s1, t1
	xor s1, s1, t0
	addw t0, a3, a2
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor a4, a4, t1
	xor a4, a4, t0
	addw t0, t2, a7
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t3, t3, t1
	xor t3, t3, t0
	addw t0, s0, t6
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t4, t4, t1
	xor t4, t4, t0
	addw t0, s1, s4
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor s2, s2, t1
	xor s2, s2, t0
	addw t0, a4, a3
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor a5, a5, t1
	xor a5, a5, t0
	addw t0, t3, t2
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor a6, a6, t1
	xor a6, a6, t0
	addw t0, t4, s0
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor t5, t5, t1
	xor t5, t5, t0
	addw t0, s2, s1
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor s3, s3, t1
	xor s3, s3, t0
	addw t0, a5, a4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a2, a2, t1
	xor a2, a2, t0
	addw t0, a6, t3
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a7, a7, t1
	xor a7, a7, t0
	addw t0, t5, t4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor t6, t6, t1
	xor t6, t6, t0
	addw t0, s3, s2
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor s4, s4, t1
	xor s4, s4, t0
	addw t0, a2, s1
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor a6, a6, t1
	xor a6, a6, t0
	addw t0, a7, a3
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor t5, t5, t1
	xor t5, t5, t0
	addw t0, t6, t2
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor s3, s3, t1
	xor s3, s3, t0
	addw t0, s4, s0
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor a5, a5, t1
	xor a5, a5, t0
	addw t0, a6, a2
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t4, t4, t1
	xor t4, t4, t0
	addw t0, t5, a7
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor s2, s2, t1
	xor s2, s2, t0
	addw t0, s3, t6
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor a4, a4, t1
	xor a4, a4, t0
	addw t0, a5, s4
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t3, t3, t1
	xor t3, t3, t0
	addw t0, t4, a6
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor s1, s1, t1
	xor s1, s1, t0
	addw t0, s2, t5
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor a3, a3, t1
	xor a3, a3, t0
	addw t0, a4, s3
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor t2, t2, t1
	xor t2, t2, t0
	addw t0, t3, a5
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor s0, s0, t1
	xor s0, s0, t0
	addw t0, s1, t4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a2, a2, t1
	xor a2, a2, t0
	addw t0, a3, s2
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a7, a7, t1
	xor a7, a7, t0
	addw t0, t2, a4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor t6, t6, t1
	xor t6, t6, t0
	addw t0, s0, t3
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor s4, s4, t1
	xor s4, s4, t0
	addw t0, a2, a5
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor a3, a3, t1
	xor a3, a3, t0
	addw t0, a7, a6
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor t2, t2, t1
	xor t2, t2, t0
	addw t0, t6, t5
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor s0, s0, t1
	xor s0, s0, t0
	addw t0, s4, s3
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor s1, s1, t1
	xor s1, s1, t0
	addw t0, a3, a2
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor a4, a4, t1
	xor a4, a4, t0
	addw t0, t2, a7
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t3, t3, t1
	xor t3, t3, t0
	addw t0, s0, t6
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t4, t4, t1
	xor t4, t4, t0
	addw t0, s1, s4
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor s2, s2, t1
	xor s2, s2, t0
	addw t0, a4, a3
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor a5, a5, t1
	xor a5, a5, t0
	addw t0, t3, t2
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor a6, a6, t1
	xor a6, a6, t0
	addw t0, t4, s0
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor t5, t5, t1
	xor t5, t5, t0
	addw t0, s2, s1
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor s3, s3, t1
	xor s3, s3, t0
	addw t0, a5, a4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a2, a2, t1
	xor a2, a2, t0
	addw t0, a6, t3
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a7, a7, t1
	xor a7, a7, t0
	addw t0, t5, t4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor t6, t6, t1
	xor t6, t6, t0
	addw t0, s3, s2
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor s4, s4, t1
	xor s4, s4, t0
	lbu t0, 0(s7)
	lbu t1, 1(s7)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 2(s7)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 3(s7)
	slli t1, t1, 24
	or t0, t0, t1
	addw a2, a2, t0
	sb a2, 0(s7)
	srli t1, a2, 8
	sb t1, 1(s7)
	srli t1, a2, 16
	sb t1, 2(s7)
	srli t1, a2, 24
	sb t1, 3(s7)
	lbu t0, 4(s7)
	lbu t1, 5(s7)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 6(s7)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 7(s7)
	slli t1, t1, 24
	or t0, t0, t1
	addw a3, a3, t0
	sb a3, 4(s7)
	srli t1, a3, 8
	sb t1, 5(s7)
	srli t1, a3, 16
	sb t1, 6(s7)
	srli t1, a3, 24
	sb t1, 7(s7)
	lbu t0, 8(s7)
	lbu t1, 9(s7)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 10(s7)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 11(s7)
	slli t1, t1, 24
	or t0, t0, t1
	addw a4, a4, t0
	sb a4, 8(s7)
	srli t1, a4, 8
	sb t1, 9(s7)
	srli t1, a4, 16
	sb t1, 10(s7)
	srli t1, a4, 24
	sb t1, 11(s7)
	lbu t0, 12(s7)
	lbu t1, 13(s7)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 14(s7)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 15(s7)
	slli t1, t1, 24
	or t0, t0, t1
	addw a5, a5, t0
	sb a5, 12(s7)
	srli t1, a5, 8
	sb t1, 13(s7)
	srli t1, a5, 16
	sb t1, 14(s7)
	srli t1, a5, 24
	sb t1, 15(s7)
	lbu t0, 16(s7)
	lbu t1, 17(s7)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 18(s7)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 19(s7)
	slli t1, t1, 24
	or t0, t0, t1
	addw a6, a6, t0
	sb a6, 16(s7)
	srli t1, a6, 8
	sb t1, 17(s7)
	srli t1, a6, 16
	sb t1, 18(s7)
	srli t1, a6, 24
	sb t1, 19(s7)
	lbu t0, 20(s7)
	lbu t1, 21(s7)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 22(s7)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 23(s7)
	slli t1, t1, 24
	or t0, t0, t1
	addw a7, a7, t0
	sb a7, 20(s7)
	srli t1, a7, 8
	sb t1, 21(s7)
	srli t1, a7, 16
	sb t1, 22(s7)
	srli t1, a7, 24
	sb t1, 23(s7)
	lbu t0, 24(s7)
	lbu t1, 25(s7)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 26(s7)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 27(s7)
	slli t1, t1, 24
	or t0, t0, t1
	addw t2, t2, t0
	sb t2, 24(s7)
	srli t1, t2, 8
	sb t1, 25(s7)
	srli t1, t2, 16
	sb t1, 26(s7)
	srli t1, t2, 24
	sb t1, 27(s7)
	lbu t0, 28(s7)
	lbu t1, 29(s7)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 30(s7)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 31(s7)
	slli t1, t1, 24
	or t0, t0, t1
	addw t3, t3, t0
	sb t3, 28(s7)
	srli t1, t3, 8
	sb t1, 29(s7)
	srli t1, t3, 16
	sb t1, 30(s7)
	srli t1, t3, 24
	sb t1, 31(s7)
	lbu t0, 32(s7)
	lbu t1, 33(s7)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 34(s7)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 35(s7)
	slli t1, t1, 24
	or t0, t0, t1
	addw t4, t4, t0
	sb t4, 32(s7)
	srli t1, t4, 8
	sb t1, 33(s7)
	srli t1, t4, 16
	sb t1, 34(s7)
	srli t1, t4, 24
	sb t1, 35(s7)
	lbu t0, 36(s7)
	lbu t1, 37(s7)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 38(s7)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 39(s7)
	slli t1, t1, 24
	or t0, t0, t1
	addw t5, t5, t0
	sb t5, 36(s7)
	srli t1, t5, 8
	sb t1, 37(s7)
	srli t1, t5, 16
	sb t1, 38(s7)
	srli t1, t5, 24
	sb t1, 39(s7)
	lbu t0, 40(s7)
	lbu t1, 41(s7)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 42(s7)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 43(s7)
	slli t1, t1, 24
	or t0, t0, t1
	addw t6, t6, t0
	sb t6, 40(s7)
	srli t1, t6, 8
	sb t1, 41(s7)
	srli t1, t6, 16
	sb t1, 42(s7)
	srli t1, t6, 24
	sb t1, 43(s7)
	lbu t0, 44(s7)
	lbu t1, 45(s7)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 46(s7)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 47(s7)
	slli t1, t1, 24
	or t0, t0, t1
	addw s0, s0, t0
	sb s0, 44(s7)
	srli t1, s0, 8
	sb t1, 45(s7)
	srli t1, s0, 16
	sb t1, 46(s7)
	srli t1, s0, 24
	sb t1, 47(s7)
	lbu t0, 48(s7)
	lbu t1, 49(s7)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 50(s7)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 51(s7)
	slli t1, t1, 24
	or t0, t0, t1
	addw s1, s1, t0
	sb s1, 48(s7)
	srli t1, s1, 8
	sb t1, 49(s7)
	srli t1, s1, 16
	sb t1, 50(s7)
	srli t1, s1, 24
	sb t1, 51(s7)
	lbu t0, 52(s7)
	lbu t1, 53(s7)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 54(s7)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 55(s7)
	slli t1, t1, 24
	or t0, t0, t1
	addw s2, s2, t0
	sb s2, 52(s7)
	srli t1, s2, 8
	sb t1, 53(s7)
	srli t1, s2, 16
	sb t1, 54(s7)
	srli t1, s2, 24
	sb t1, 55(s7)
	lbu t0, 56(s7)
	lbu t1, 57(s7)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 58(s7)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 59(s7)
	slli t1, t1, 24
	or t0, t0, t1
	addw s3, s3, t0
	sb s3, 56(s7)
	srli t1, s3, 8
	sb t1, 57(s7)
	srli t1, s3, 16
	sb t1, 58(s7)
	srli t1, s3, 24
	sb t1, 59(s7)
	lbu t0, 60(s7)
	lbu t1, 61(s7)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 62(s7)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 63(s7)
	slli t1, t1, 24
	or t0, t0, t1
	addw s4, s4, t0
	sb s4, 60(s7)
	srli t1, s4, 8
	sb t1, 61(s7)
	srli t1, s4, 16
	sb t1, 62(s7)
	srli t1, s4, 24
	sb t1, 63(s7)
	addi s5, s5, 64
	addi s6, s6, 64
	addi s7, s7, 64
	addi s8, s8, -1
	bnez s8, 20b
	ld s0, 0(s10)
	ld s1, 8(s10)
	ld s2, 16(s10)
	ld s3, 24(s10)
	ld s4, 32(s10)
	ld s5, 40(s10)
	ld s6, 48(s10)
	ld s7, 56(s10)
	ld s8, 64(s10)
	ld s10, 72(s10)
	ret
	.option pop
