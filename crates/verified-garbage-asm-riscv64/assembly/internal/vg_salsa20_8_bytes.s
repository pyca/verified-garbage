// The functions of `src/internal/vg_salsa20_8_bytes.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_salsa20_8_bytes:
	.option push
	.option arch, +m, +c
	addi sp, sp, -32
	addi t0, sp, 0
	sd s0, 0(t0)
	sd s1, 8(t0)
	sd s2, 16(t0)
	sd s3, 24(t0)
	lbu a1, 0(a0)
	lbu t1, 1(a0)
	slli t1, t1, 8
	or a1, a1, t1
	lbu t1, 2(a0)
	slli t1, t1, 16
	or a1, a1, t1
	lbu t1, 3(a0)
	slli t1, t1, 24
	or a1, a1, t1
	lbu a2, 4(a0)
	lbu t1, 5(a0)
	slli t1, t1, 8
	or a2, a2, t1
	lbu t1, 6(a0)
	slli t1, t1, 16
	or a2, a2, t1
	lbu t1, 7(a0)
	slli t1, t1, 24
	or a2, a2, t1
	lbu a3, 8(a0)
	lbu t1, 9(a0)
	slli t1, t1, 8
	or a3, a3, t1
	lbu t1, 10(a0)
	slli t1, t1, 16
	or a3, a3, t1
	lbu t1, 11(a0)
	slli t1, t1, 24
	or a3, a3, t1
	lbu a4, 12(a0)
	lbu t1, 13(a0)
	slli t1, t1, 8
	or a4, a4, t1
	lbu t1, 14(a0)
	slli t1, t1, 16
	or a4, a4, t1
	lbu t1, 15(a0)
	slli t1, t1, 24
	or a4, a4, t1
	lbu a5, 16(a0)
	lbu t1, 17(a0)
	slli t1, t1, 8
	or a5, a5, t1
	lbu t1, 18(a0)
	slli t1, t1, 16
	or a5, a5, t1
	lbu t1, 19(a0)
	slli t1, t1, 24
	or a5, a5, t1
	lbu a6, 20(a0)
	lbu t1, 21(a0)
	slli t1, t1, 8
	or a6, a6, t1
	lbu t1, 22(a0)
	slli t1, t1, 16
	or a6, a6, t1
	lbu t1, 23(a0)
	slli t1, t1, 24
	or a6, a6, t1
	lbu a7, 24(a0)
	lbu t1, 25(a0)
	slli t1, t1, 8
	or a7, a7, t1
	lbu t1, 26(a0)
	slli t1, t1, 16
	or a7, a7, t1
	lbu t1, 27(a0)
	slli t1, t1, 24
	or a7, a7, t1
	lbu t2, 28(a0)
	lbu t1, 29(a0)
	slli t1, t1, 8
	or t2, t2, t1
	lbu t1, 30(a0)
	slli t1, t1, 16
	or t2, t2, t1
	lbu t1, 31(a0)
	slli t1, t1, 24
	or t2, t2, t1
	lbu t3, 32(a0)
	lbu t1, 33(a0)
	slli t1, t1, 8
	or t3, t3, t1
	lbu t1, 34(a0)
	slli t1, t1, 16
	or t3, t3, t1
	lbu t1, 35(a0)
	slli t1, t1, 24
	or t3, t3, t1
	lbu t4, 36(a0)
	lbu t1, 37(a0)
	slli t1, t1, 8
	or t4, t4, t1
	lbu t1, 38(a0)
	slli t1, t1, 16
	or t4, t4, t1
	lbu t1, 39(a0)
	slli t1, t1, 24
	or t4, t4, t1
	lbu t5, 40(a0)
	lbu t1, 41(a0)
	slli t1, t1, 8
	or t5, t5, t1
	lbu t1, 42(a0)
	slli t1, t1, 16
	or t5, t5, t1
	lbu t1, 43(a0)
	slli t1, t1, 24
	or t5, t5, t1
	lbu t6, 44(a0)
	lbu t1, 45(a0)
	slli t1, t1, 8
	or t6, t6, t1
	lbu t1, 46(a0)
	slli t1, t1, 16
	or t6, t6, t1
	lbu t1, 47(a0)
	slli t1, t1, 24
	or t6, t6, t1
	lbu s0, 48(a0)
	lbu t1, 49(a0)
	slli t1, t1, 8
	or s0, s0, t1
	lbu t1, 50(a0)
	slli t1, t1, 16
	or s0, s0, t1
	lbu t1, 51(a0)
	slli t1, t1, 24
	or s0, s0, t1
	lbu s1, 52(a0)
	lbu t1, 53(a0)
	slli t1, t1, 8
	or s1, s1, t1
	lbu t1, 54(a0)
	slli t1, t1, 16
	or s1, s1, t1
	lbu t1, 55(a0)
	slli t1, t1, 24
	or s1, s1, t1
	lbu s2, 56(a0)
	lbu t1, 57(a0)
	slli t1, t1, 8
	or s2, s2, t1
	lbu t1, 58(a0)
	slli t1, t1, 16
	or s2, s2, t1
	lbu t1, 59(a0)
	slli t1, t1, 24
	or s2, s2, t1
	lbu s3, 60(a0)
	lbu t1, 61(a0)
	slli t1, t1, 8
	or s3, s3, t1
	lbu t1, 62(a0)
	slli t1, t1, 16
	or s3, s3, t1
	lbu t1, 63(a0)
	slli t1, t1, 24
	or s3, s3, t1
	addw t0, a1, s0
	slliw t1, t0, 7
	xor a5, a5, t1
	srliw t0, t0, 25
	xor a5, a5, t0
	addw t0, a5, a1
	slliw t1, t0, 9
	xor t3, t3, t1
	srliw t0, t0, 23
	xor t3, t3, t0
	addw t0, t3, a5
	slliw t1, t0, 13
	xor s0, s0, t1
	srliw t0, t0, 19
	xor s0, s0, t0
	addw t0, s0, t3
	slliw t1, t0, 18
	xor a1, a1, t1
	srliw t0, t0, 14
	xor a1, a1, t0
	addw t0, a6, a2
	slliw t1, t0, 7
	xor t4, t4, t1
	srliw t0, t0, 25
	xor t4, t4, t0
	addw t0, t4, a6
	slliw t1, t0, 9
	xor s1, s1, t1
	srliw t0, t0, 23
	xor s1, s1, t0
	addw t0, s1, t4
	slliw t1, t0, 13
	xor a2, a2, t1
	srliw t0, t0, 19
	xor a2, a2, t0
	addw t0, a2, s1
	slliw t1, t0, 18
	xor a6, a6, t1
	srliw t0, t0, 14
	xor a6, a6, t0
	addw t0, t5, a7
	slliw t1, t0, 7
	xor s2, s2, t1
	srliw t0, t0, 25
	xor s2, s2, t0
	addw t0, s2, t5
	slliw t1, t0, 9
	xor a3, a3, t1
	srliw t0, t0, 23
	xor a3, a3, t0
	addw t0, a3, s2
	slliw t1, t0, 13
	xor a7, a7, t1
	srliw t0, t0, 19
	xor a7, a7, t0
	addw t0, a7, a3
	slliw t1, t0, 18
	xor t5, t5, t1
	srliw t0, t0, 14
	xor t5, t5, t0
	addw t0, s3, t6
	slliw t1, t0, 7
	xor a4, a4, t1
	srliw t0, t0, 25
	xor a4, a4, t0
	addw t0, a4, s3
	slliw t1, t0, 9
	xor t2, t2, t1
	srliw t0, t0, 23
	xor t2, t2, t0
	addw t0, t2, a4
	slliw t1, t0, 13
	xor t6, t6, t1
	srliw t0, t0, 19
	xor t6, t6, t0
	addw t0, t6, t2
	slliw t1, t0, 18
	xor s3, s3, t1
	srliw t0, t0, 14
	xor s3, s3, t0
	addw t0, a1, a4
	slliw t1, t0, 7
	xor a2, a2, t1
	srliw t0, t0, 25
	xor a2, a2, t0
	addw t0, a2, a1
	slliw t1, t0, 9
	xor a3, a3, t1
	srliw t0, t0, 23
	xor a3, a3, t0
	addw t0, a3, a2
	slliw t1, t0, 13
	xor a4, a4, t1
	srliw t0, t0, 19
	xor a4, a4, t0
	addw t0, a4, a3
	slliw t1, t0, 18
	xor a1, a1, t1
	srliw t0, t0, 14
	xor a1, a1, t0
	addw t0, a6, a5
	slliw t1, t0, 7
	xor a7, a7, t1
	srliw t0, t0, 25
	xor a7, a7, t0
	addw t0, a7, a6
	slliw t1, t0, 9
	xor t2, t2, t1
	srliw t0, t0, 23
	xor t2, t2, t0
	addw t0, t2, a7
	slliw t1, t0, 13
	xor a5, a5, t1
	srliw t0, t0, 19
	xor a5, a5, t0
	addw t0, a5, t2
	slliw t1, t0, 18
	xor a6, a6, t1
	srliw t0, t0, 14
	xor a6, a6, t0
	addw t0, t5, t4
	slliw t1, t0, 7
	xor t6, t6, t1
	srliw t0, t0, 25
	xor t6, t6, t0
	addw t0, t6, t5
	slliw t1, t0, 9
	xor t3, t3, t1
	srliw t0, t0, 23
	xor t3, t3, t0
	addw t0, t3, t6
	slliw t1, t0, 13
	xor t4, t4, t1
	srliw t0, t0, 19
	xor t4, t4, t0
	addw t0, t4, t3
	slliw t1, t0, 18
	xor t5, t5, t1
	srliw t0, t0, 14
	xor t5, t5, t0
	addw t0, s3, s2
	slliw t1, t0, 7
	xor s0, s0, t1
	srliw t0, t0, 25
	xor s0, s0, t0
	addw t0, s0, s3
	slliw t1, t0, 9
	xor s1, s1, t1
	srliw t0, t0, 23
	xor s1, s1, t0
	addw t0, s1, s0
	slliw t1, t0, 13
	xor s2, s2, t1
	srliw t0, t0, 19
	xor s2, s2, t0
	addw t0, s2, s1
	slliw t1, t0, 18
	xor s3, s3, t1
	srliw t0, t0, 14
	xor s3, s3, t0
	addw t0, a1, s0
	slliw t1, t0, 7
	xor a5, a5, t1
	srliw t0, t0, 25
	xor a5, a5, t0
	addw t0, a5, a1
	slliw t1, t0, 9
	xor t3, t3, t1
	srliw t0, t0, 23
	xor t3, t3, t0
	addw t0, t3, a5
	slliw t1, t0, 13
	xor s0, s0, t1
	srliw t0, t0, 19
	xor s0, s0, t0
	addw t0, s0, t3
	slliw t1, t0, 18
	xor a1, a1, t1
	srliw t0, t0, 14
	xor a1, a1, t0
	addw t0, a6, a2
	slliw t1, t0, 7
	xor t4, t4, t1
	srliw t0, t0, 25
	xor t4, t4, t0
	addw t0, t4, a6
	slliw t1, t0, 9
	xor s1, s1, t1
	srliw t0, t0, 23
	xor s1, s1, t0
	addw t0, s1, t4
	slliw t1, t0, 13
	xor a2, a2, t1
	srliw t0, t0, 19
	xor a2, a2, t0
	addw t0, a2, s1
	slliw t1, t0, 18
	xor a6, a6, t1
	srliw t0, t0, 14
	xor a6, a6, t0
	addw t0, t5, a7
	slliw t1, t0, 7
	xor s2, s2, t1
	srliw t0, t0, 25
	xor s2, s2, t0
	addw t0, s2, t5
	slliw t1, t0, 9
	xor a3, a3, t1
	srliw t0, t0, 23
	xor a3, a3, t0
	addw t0, a3, s2
	slliw t1, t0, 13
	xor a7, a7, t1
	srliw t0, t0, 19
	xor a7, a7, t0
	addw t0, a7, a3
	slliw t1, t0, 18
	xor t5, t5, t1
	srliw t0, t0, 14
	xor t5, t5, t0
	addw t0, s3, t6
	slliw t1, t0, 7
	xor a4, a4, t1
	srliw t0, t0, 25
	xor a4, a4, t0
	addw t0, a4, s3
	slliw t1, t0, 9
	xor t2, t2, t1
	srliw t0, t0, 23
	xor t2, t2, t0
	addw t0, t2, a4
	slliw t1, t0, 13
	xor t6, t6, t1
	srliw t0, t0, 19
	xor t6, t6, t0
	addw t0, t6, t2
	slliw t1, t0, 18
	xor s3, s3, t1
	srliw t0, t0, 14
	xor s3, s3, t0
	addw t0, a1, a4
	slliw t1, t0, 7
	xor a2, a2, t1
	srliw t0, t0, 25
	xor a2, a2, t0
	addw t0, a2, a1
	slliw t1, t0, 9
	xor a3, a3, t1
	srliw t0, t0, 23
	xor a3, a3, t0
	addw t0, a3, a2
	slliw t1, t0, 13
	xor a4, a4, t1
	srliw t0, t0, 19
	xor a4, a4, t0
	addw t0, a4, a3
	slliw t1, t0, 18
	xor a1, a1, t1
	srliw t0, t0, 14
	xor a1, a1, t0
	addw t0, a6, a5
	slliw t1, t0, 7
	xor a7, a7, t1
	srliw t0, t0, 25
	xor a7, a7, t0
	addw t0, a7, a6
	slliw t1, t0, 9
	xor t2, t2, t1
	srliw t0, t0, 23
	xor t2, t2, t0
	addw t0, t2, a7
	slliw t1, t0, 13
	xor a5, a5, t1
	srliw t0, t0, 19
	xor a5, a5, t0
	addw t0, a5, t2
	slliw t1, t0, 18
	xor a6, a6, t1
	srliw t0, t0, 14
	xor a6, a6, t0
	addw t0, t5, t4
	slliw t1, t0, 7
	xor t6, t6, t1
	srliw t0, t0, 25
	xor t6, t6, t0
	addw t0, t6, t5
	slliw t1, t0, 9
	xor t3, t3, t1
	srliw t0, t0, 23
	xor t3, t3, t0
	addw t0, t3, t6
	slliw t1, t0, 13
	xor t4, t4, t1
	srliw t0, t0, 19
	xor t4, t4, t0
	addw t0, t4, t3
	slliw t1, t0, 18
	xor t5, t5, t1
	srliw t0, t0, 14
	xor t5, t5, t0
	addw t0, s3, s2
	slliw t1, t0, 7
	xor s0, s0, t1
	srliw t0, t0, 25
	xor s0, s0, t0
	addw t0, s0, s3
	slliw t1, t0, 9
	xor s1, s1, t1
	srliw t0, t0, 23
	xor s1, s1, t0
	addw t0, s1, s0
	slliw t1, t0, 13
	xor s2, s2, t1
	srliw t0, t0, 19
	xor s2, s2, t0
	addw t0, s2, s1
	slliw t1, t0, 18
	xor s3, s3, t1
	srliw t0, t0, 14
	xor s3, s3, t0
	addw t0, a1, s0
	slliw t1, t0, 7
	xor a5, a5, t1
	srliw t0, t0, 25
	xor a5, a5, t0
	addw t0, a5, a1
	slliw t1, t0, 9
	xor t3, t3, t1
	srliw t0, t0, 23
	xor t3, t3, t0
	addw t0, t3, a5
	slliw t1, t0, 13
	xor s0, s0, t1
	srliw t0, t0, 19
	xor s0, s0, t0
	addw t0, s0, t3
	slliw t1, t0, 18
	xor a1, a1, t1
	srliw t0, t0, 14
	xor a1, a1, t0
	addw t0, a6, a2
	slliw t1, t0, 7
	xor t4, t4, t1
	srliw t0, t0, 25
	xor t4, t4, t0
	addw t0, t4, a6
	slliw t1, t0, 9
	xor s1, s1, t1
	srliw t0, t0, 23
	xor s1, s1, t0
	addw t0, s1, t4
	slliw t1, t0, 13
	xor a2, a2, t1
	srliw t0, t0, 19
	xor a2, a2, t0
	addw t0, a2, s1
	slliw t1, t0, 18
	xor a6, a6, t1
	srliw t0, t0, 14
	xor a6, a6, t0
	addw t0, t5, a7
	slliw t1, t0, 7
	xor s2, s2, t1
	srliw t0, t0, 25
	xor s2, s2, t0
	addw t0, s2, t5
	slliw t1, t0, 9
	xor a3, a3, t1
	srliw t0, t0, 23
	xor a3, a3, t0
	addw t0, a3, s2
	slliw t1, t0, 13
	xor a7, a7, t1
	srliw t0, t0, 19
	xor a7, a7, t0
	addw t0, a7, a3
	slliw t1, t0, 18
	xor t5, t5, t1
	srliw t0, t0, 14
	xor t5, t5, t0
	addw t0, s3, t6
	slliw t1, t0, 7
	xor a4, a4, t1
	srliw t0, t0, 25
	xor a4, a4, t0
	addw t0, a4, s3
	slliw t1, t0, 9
	xor t2, t2, t1
	srliw t0, t0, 23
	xor t2, t2, t0
	addw t0, t2, a4
	slliw t1, t0, 13
	xor t6, t6, t1
	srliw t0, t0, 19
	xor t6, t6, t0
	addw t0, t6, t2
	slliw t1, t0, 18
	xor s3, s3, t1
	srliw t0, t0, 14
	xor s3, s3, t0
	addw t0, a1, a4
	slliw t1, t0, 7
	xor a2, a2, t1
	srliw t0, t0, 25
	xor a2, a2, t0
	addw t0, a2, a1
	slliw t1, t0, 9
	xor a3, a3, t1
	srliw t0, t0, 23
	xor a3, a3, t0
	addw t0, a3, a2
	slliw t1, t0, 13
	xor a4, a4, t1
	srliw t0, t0, 19
	xor a4, a4, t0
	addw t0, a4, a3
	slliw t1, t0, 18
	xor a1, a1, t1
	srliw t0, t0, 14
	xor a1, a1, t0
	addw t0, a6, a5
	slliw t1, t0, 7
	xor a7, a7, t1
	srliw t0, t0, 25
	xor a7, a7, t0
	addw t0, a7, a6
	slliw t1, t0, 9
	xor t2, t2, t1
	srliw t0, t0, 23
	xor t2, t2, t0
	addw t0, t2, a7
	slliw t1, t0, 13
	xor a5, a5, t1
	srliw t0, t0, 19
	xor a5, a5, t0
	addw t0, a5, t2
	slliw t1, t0, 18
	xor a6, a6, t1
	srliw t0, t0, 14
	xor a6, a6, t0
	addw t0, t5, t4
	slliw t1, t0, 7
	xor t6, t6, t1
	srliw t0, t0, 25
	xor t6, t6, t0
	addw t0, t6, t5
	slliw t1, t0, 9
	xor t3, t3, t1
	srliw t0, t0, 23
	xor t3, t3, t0
	addw t0, t3, t6
	slliw t1, t0, 13
	xor t4, t4, t1
	srliw t0, t0, 19
	xor t4, t4, t0
	addw t0, t4, t3
	slliw t1, t0, 18
	xor t5, t5, t1
	srliw t0, t0, 14
	xor t5, t5, t0
	addw t0, s3, s2
	slliw t1, t0, 7
	xor s0, s0, t1
	srliw t0, t0, 25
	xor s0, s0, t0
	addw t0, s0, s3
	slliw t1, t0, 9
	xor s1, s1, t1
	srliw t0, t0, 23
	xor s1, s1, t0
	addw t0, s1, s0
	slliw t1, t0, 13
	xor s2, s2, t1
	srliw t0, t0, 19
	xor s2, s2, t0
	addw t0, s2, s1
	slliw t1, t0, 18
	xor s3, s3, t1
	srliw t0, t0, 14
	xor s3, s3, t0
	addw t0, a1, s0
	slliw t1, t0, 7
	xor a5, a5, t1
	srliw t0, t0, 25
	xor a5, a5, t0
	addw t0, a5, a1
	slliw t1, t0, 9
	xor t3, t3, t1
	srliw t0, t0, 23
	xor t3, t3, t0
	addw t0, t3, a5
	slliw t1, t0, 13
	xor s0, s0, t1
	srliw t0, t0, 19
	xor s0, s0, t0
	addw t0, s0, t3
	slliw t1, t0, 18
	xor a1, a1, t1
	srliw t0, t0, 14
	xor a1, a1, t0
	addw t0, a6, a2
	slliw t1, t0, 7
	xor t4, t4, t1
	srliw t0, t0, 25
	xor t4, t4, t0
	addw t0, t4, a6
	slliw t1, t0, 9
	xor s1, s1, t1
	srliw t0, t0, 23
	xor s1, s1, t0
	addw t0, s1, t4
	slliw t1, t0, 13
	xor a2, a2, t1
	srliw t0, t0, 19
	xor a2, a2, t0
	addw t0, a2, s1
	slliw t1, t0, 18
	xor a6, a6, t1
	srliw t0, t0, 14
	xor a6, a6, t0
	addw t0, t5, a7
	slliw t1, t0, 7
	xor s2, s2, t1
	srliw t0, t0, 25
	xor s2, s2, t0
	addw t0, s2, t5
	slliw t1, t0, 9
	xor a3, a3, t1
	srliw t0, t0, 23
	xor a3, a3, t0
	addw t0, a3, s2
	slliw t1, t0, 13
	xor a7, a7, t1
	srliw t0, t0, 19
	xor a7, a7, t0
	addw t0, a7, a3
	slliw t1, t0, 18
	xor t5, t5, t1
	srliw t0, t0, 14
	xor t5, t5, t0
	addw t0, s3, t6
	slliw t1, t0, 7
	xor a4, a4, t1
	srliw t0, t0, 25
	xor a4, a4, t0
	addw t0, a4, s3
	slliw t1, t0, 9
	xor t2, t2, t1
	srliw t0, t0, 23
	xor t2, t2, t0
	addw t0, t2, a4
	slliw t1, t0, 13
	xor t6, t6, t1
	srliw t0, t0, 19
	xor t6, t6, t0
	addw t0, t6, t2
	slliw t1, t0, 18
	xor s3, s3, t1
	srliw t0, t0, 14
	xor s3, s3, t0
	addw t0, a1, a4
	slliw t1, t0, 7
	xor a2, a2, t1
	srliw t0, t0, 25
	xor a2, a2, t0
	addw t0, a2, a1
	slliw t1, t0, 9
	xor a3, a3, t1
	srliw t0, t0, 23
	xor a3, a3, t0
	addw t0, a3, a2
	slliw t1, t0, 13
	xor a4, a4, t1
	srliw t0, t0, 19
	xor a4, a4, t0
	addw t0, a4, a3
	slliw t1, t0, 18
	xor a1, a1, t1
	srliw t0, t0, 14
	xor a1, a1, t0
	addw t0, a6, a5
	slliw t1, t0, 7
	xor a7, a7, t1
	srliw t0, t0, 25
	xor a7, a7, t0
	addw t0, a7, a6
	slliw t1, t0, 9
	xor t2, t2, t1
	srliw t0, t0, 23
	xor t2, t2, t0
	addw t0, t2, a7
	slliw t1, t0, 13
	xor a5, a5, t1
	srliw t0, t0, 19
	xor a5, a5, t0
	addw t0, a5, t2
	slliw t1, t0, 18
	xor a6, a6, t1
	srliw t0, t0, 14
	xor a6, a6, t0
	addw t0, t5, t4
	slliw t1, t0, 7
	xor t6, t6, t1
	srliw t0, t0, 25
	xor t6, t6, t0
	addw t0, t6, t5
	slliw t1, t0, 9
	xor t3, t3, t1
	srliw t0, t0, 23
	xor t3, t3, t0
	addw t0, t3, t6
	slliw t1, t0, 13
	xor t4, t4, t1
	srliw t0, t0, 19
	xor t4, t4, t0
	addw t0, t4, t3
	slliw t1, t0, 18
	xor t5, t5, t1
	srliw t0, t0, 14
	xor t5, t5, t0
	addw t0, s3, s2
	slliw t1, t0, 7
	xor s0, s0, t1
	srliw t0, t0, 25
	xor s0, s0, t0
	addw t0, s0, s3
	slliw t1, t0, 9
	xor s1, s1, t1
	srliw t0, t0, 23
	xor s1, s1, t0
	addw t0, s1, s0
	slliw t1, t0, 13
	xor s2, s2, t1
	srliw t0, t0, 19
	xor s2, s2, t0
	addw t0, s2, s1
	slliw t1, t0, 18
	xor s3, s3, t1
	srliw t0, t0, 14
	xor s3, s3, t0
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
	addw a1, a1, t0
	sb a1, 0(a0)
	srli t1, a1, 8
	sb t1, 1(a0)
	srli t1, a1, 16
	sb t1, 2(a0)
	srli t1, a1, 24
	sb t1, 3(a0)
	lbu t0, 4(a0)
	lbu t1, 5(a0)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 6(a0)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 7(a0)
	slli t1, t1, 24
	or t0, t0, t1
	addw a2, a2, t0
	sb a2, 4(a0)
	srli t1, a2, 8
	sb t1, 5(a0)
	srli t1, a2, 16
	sb t1, 6(a0)
	srli t1, a2, 24
	sb t1, 7(a0)
	lbu t0, 8(a0)
	lbu t1, 9(a0)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 10(a0)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 11(a0)
	slli t1, t1, 24
	or t0, t0, t1
	addw a3, a3, t0
	sb a3, 8(a0)
	srli t1, a3, 8
	sb t1, 9(a0)
	srli t1, a3, 16
	sb t1, 10(a0)
	srli t1, a3, 24
	sb t1, 11(a0)
	lbu t0, 12(a0)
	lbu t1, 13(a0)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 14(a0)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 15(a0)
	slli t1, t1, 24
	or t0, t0, t1
	addw a4, a4, t0
	sb a4, 12(a0)
	srli t1, a4, 8
	sb t1, 13(a0)
	srli t1, a4, 16
	sb t1, 14(a0)
	srli t1, a4, 24
	sb t1, 15(a0)
	lbu t0, 16(a0)
	lbu t1, 17(a0)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 18(a0)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 19(a0)
	slli t1, t1, 24
	or t0, t0, t1
	addw a5, a5, t0
	sb a5, 16(a0)
	srli t1, a5, 8
	sb t1, 17(a0)
	srli t1, a5, 16
	sb t1, 18(a0)
	srli t1, a5, 24
	sb t1, 19(a0)
	lbu t0, 20(a0)
	lbu t1, 21(a0)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 22(a0)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 23(a0)
	slli t1, t1, 24
	or t0, t0, t1
	addw a6, a6, t0
	sb a6, 20(a0)
	srli t1, a6, 8
	sb t1, 21(a0)
	srli t1, a6, 16
	sb t1, 22(a0)
	srli t1, a6, 24
	sb t1, 23(a0)
	lbu t0, 24(a0)
	lbu t1, 25(a0)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 26(a0)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 27(a0)
	slli t1, t1, 24
	or t0, t0, t1
	addw a7, a7, t0
	sb a7, 24(a0)
	srli t1, a7, 8
	sb t1, 25(a0)
	srli t1, a7, 16
	sb t1, 26(a0)
	srli t1, a7, 24
	sb t1, 27(a0)
	lbu t0, 28(a0)
	lbu t1, 29(a0)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 30(a0)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 31(a0)
	slli t1, t1, 24
	or t0, t0, t1
	addw t2, t2, t0
	sb t2, 28(a0)
	srli t1, t2, 8
	sb t1, 29(a0)
	srli t1, t2, 16
	sb t1, 30(a0)
	srli t1, t2, 24
	sb t1, 31(a0)
	lbu t0, 32(a0)
	lbu t1, 33(a0)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 34(a0)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 35(a0)
	slli t1, t1, 24
	or t0, t0, t1
	addw t3, t3, t0
	sb t3, 32(a0)
	srli t1, t3, 8
	sb t1, 33(a0)
	srli t1, t3, 16
	sb t1, 34(a0)
	srli t1, t3, 24
	sb t1, 35(a0)
	lbu t0, 36(a0)
	lbu t1, 37(a0)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 38(a0)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 39(a0)
	slli t1, t1, 24
	or t0, t0, t1
	addw t4, t4, t0
	sb t4, 36(a0)
	srli t1, t4, 8
	sb t1, 37(a0)
	srli t1, t4, 16
	sb t1, 38(a0)
	srli t1, t4, 24
	sb t1, 39(a0)
	lbu t0, 40(a0)
	lbu t1, 41(a0)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 42(a0)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 43(a0)
	slli t1, t1, 24
	or t0, t0, t1
	addw t5, t5, t0
	sb t5, 40(a0)
	srli t1, t5, 8
	sb t1, 41(a0)
	srli t1, t5, 16
	sb t1, 42(a0)
	srli t1, t5, 24
	sb t1, 43(a0)
	lbu t0, 44(a0)
	lbu t1, 45(a0)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 46(a0)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 47(a0)
	slli t1, t1, 24
	or t0, t0, t1
	addw t6, t6, t0
	sb t6, 44(a0)
	srli t1, t6, 8
	sb t1, 45(a0)
	srli t1, t6, 16
	sb t1, 46(a0)
	srli t1, t6, 24
	sb t1, 47(a0)
	lbu t0, 48(a0)
	lbu t1, 49(a0)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 50(a0)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 51(a0)
	slli t1, t1, 24
	or t0, t0, t1
	addw s0, s0, t0
	sb s0, 48(a0)
	srli t1, s0, 8
	sb t1, 49(a0)
	srli t1, s0, 16
	sb t1, 50(a0)
	srli t1, s0, 24
	sb t1, 51(a0)
	lbu t0, 52(a0)
	lbu t1, 53(a0)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 54(a0)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 55(a0)
	slli t1, t1, 24
	or t0, t0, t1
	addw s1, s1, t0
	sb s1, 52(a0)
	srli t1, s1, 8
	sb t1, 53(a0)
	srli t1, s1, 16
	sb t1, 54(a0)
	srli t1, s1, 24
	sb t1, 55(a0)
	lbu t0, 56(a0)
	lbu t1, 57(a0)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 58(a0)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 59(a0)
	slli t1, t1, 24
	or t0, t0, t1
	addw s2, s2, t0
	sb s2, 56(a0)
	srli t1, s2, 8
	sb t1, 57(a0)
	srli t1, s2, 16
	sb t1, 58(a0)
	srli t1, s2, 24
	sb t1, 59(a0)
	lbu t0, 60(a0)
	lbu t1, 61(a0)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 62(a0)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 63(a0)
	slli t1, t1, 24
	or t0, t0, t1
	addw s3, s3, t0
	sb s3, 60(a0)
	srli t1, s3, 8
	sb t1, 61(a0)
	srli t1, s3, 16
	sb t1, 62(a0)
	srli t1, s3, 24
	sb t1, 63(a0)
	addi t0, sp, 0
	ld s0, 0(t0)
	ld s1, 8(t0)
	ld s2, 16(t0)
	ld s3, 24(t0)
	addi sp, sp, 32
	ret
	.option pop
