// The functions of `src/internal/vg_chacha20_block.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_chacha20_block:
	.option push
	.option arch, +m, +c
	addi t0, a1, 71
	andi t0, t0, -8
	sd s0, 0(t0)
	sd s1, 8(t0)
	sd s2, 16(t0)
	sd s3, 24(t0)
	sd s4, 32(t0)
	lbu t0, 0(a0)
	lbu s3, 1(a0)
	slli s3, s3, 8
	or t0, t0, s3
	lbu s3, 2(a0)
	slli s3, s3, 16
	or t0, t0, s3
	lbu s3, 3(a0)
	slli s3, s3, 24
	or t0, t0, s3
	lbu t1, 4(a0)
	lbu s3, 5(a0)
	slli s3, s3, 8
	or t1, t1, s3
	lbu s3, 6(a0)
	slli s3, s3, 16
	or t1, t1, s3
	lbu s3, 7(a0)
	slli s3, s3, 24
	or t1, t1, s3
	lbu t2, 8(a0)
	lbu s3, 9(a0)
	slli s3, s3, 8
	or t2, t2, s3
	lbu s3, 10(a0)
	slli s3, s3, 16
	or t2, t2, s3
	lbu s3, 11(a0)
	slli s3, s3, 24
	or t2, t2, s3
	lbu t3, 12(a0)
	lbu s3, 13(a0)
	slli s3, s3, 8
	or t3, t3, s3
	lbu s3, 14(a0)
	slli s3, s3, 16
	or t3, t3, s3
	lbu s3, 15(a0)
	slli s3, s3, 24
	or t3, t3, s3
	lbu t4, 16(a0)
	lbu s3, 17(a0)
	slli s3, s3, 8
	or t4, t4, s3
	lbu s3, 18(a0)
	slli s3, s3, 16
	or t4, t4, s3
	lbu s3, 19(a0)
	slli s3, s3, 24
	or t4, t4, s3
	lbu t5, 20(a0)
	lbu s3, 21(a0)
	slli s3, s3, 8
	or t5, t5, s3
	lbu s3, 22(a0)
	slli s3, s3, 16
	or t5, t5, s3
	lbu s3, 23(a0)
	slli s3, s3, 24
	or t5, t5, s3
	lbu t6, 24(a0)
	lbu s3, 25(a0)
	slli s3, s3, 8
	or t6, t6, s3
	lbu s3, 26(a0)
	slli s3, s3, 16
	or t6, t6, s3
	lbu s3, 27(a0)
	slli s3, s3, 24
	or t6, t6, s3
	lbu a2, 28(a0)
	lbu s3, 29(a0)
	slli s3, s3, 8
	or a2, a2, s3
	lbu s3, 30(a0)
	slli s3, s3, 16
	or a2, a2, s3
	lbu s3, 31(a0)
	slli s3, s3, 24
	or a2, a2, s3
	lbu a3, 32(a0)
	lbu s3, 33(a0)
	slli s3, s3, 8
	or a3, a3, s3
	lbu s3, 34(a0)
	slli s3, s3, 16
	or a3, a3, s3
	lbu s3, 35(a0)
	slli s3, s3, 24
	or a3, a3, s3
	lbu a4, 36(a0)
	lbu s3, 37(a0)
	slli s3, s3, 8
	or a4, a4, s3
	lbu s3, 38(a0)
	slli s3, s3, 16
	or a4, a4, s3
	lbu s3, 39(a0)
	slli s3, s3, 24
	or a4, a4, s3
	lbu a5, 40(a0)
	lbu s3, 41(a0)
	slli s3, s3, 8
	or a5, a5, s3
	lbu s3, 42(a0)
	slli s3, s3, 16
	or a5, a5, s3
	lbu s3, 43(a0)
	slli s3, s3, 24
	or a5, a5, s3
	lbu a6, 44(a0)
	lbu s3, 45(a0)
	slli s3, s3, 8
	or a6, a6, s3
	lbu s3, 46(a0)
	slli s3, s3, 16
	or a6, a6, s3
	lbu s3, 47(a0)
	slli s3, s3, 24
	or a6, a6, s3
	lbu a7, 48(a0)
	lbu s3, 49(a0)
	slli s3, s3, 8
	or a7, a7, s3
	lbu s3, 50(a0)
	slli s3, s3, 16
	or a7, a7, s3
	lbu s3, 51(a0)
	slli s3, s3, 24
	or a7, a7, s3
	lbu s0, 52(a0)
	lbu s3, 53(a0)
	slli s3, s3, 8
	or s0, s0, s3
	lbu s3, 54(a0)
	slli s3, s3, 16
	or s0, s0, s3
	lbu s3, 55(a0)
	slli s3, s3, 24
	or s0, s0, s3
	lbu s1, 56(a0)
	lbu s3, 57(a0)
	slli s3, s3, 8
	or s1, s1, s3
	lbu s3, 58(a0)
	slli s3, s3, 16
	or s1, s1, s3
	lbu s3, 59(a0)
	slli s3, s3, 24
	or s1, s1, s3
	lbu s2, 60(a0)
	lbu s3, 61(a0)
	slli s3, s3, 8
	or s2, s2, s3
	lbu s3, 62(a0)
	slli s3, s3, 16
	or s2, s2, s3
	lbu s3, 63(a0)
	slli s3, s3, 24
	or s2, s2, s3
	addi s4, zero, 10
20:
	add t0, t0, t4
	xor a7, a7, t0
	slliw s3, a7, 16
	srliw a7, a7, 16
	or a7, a7, s3
	add a3, a3, a7
	xor t4, t4, a3
	slliw s3, t4, 12
	srliw t4, t4, 20
	or t4, t4, s3
	add t0, t0, t4
	xor a7, a7, t0
	slliw s3, a7, 8
	srliw a7, a7, 24
	or a7, a7, s3
	add a3, a3, a7
	xor t4, t4, a3
	slliw s3, t4, 7
	srliw t4, t4, 25
	or t4, t4, s3
	add t1, t1, t5
	xor s0, s0, t1
	slliw s3, s0, 16
	srliw s0, s0, 16
	or s0, s0, s3
	add a4, a4, s0
	xor t5, t5, a4
	slliw s3, t5, 12
	srliw t5, t5, 20
	or t5, t5, s3
	add t1, t1, t5
	xor s0, s0, t1
	slliw s3, s0, 8
	srliw s0, s0, 24
	or s0, s0, s3
	add a4, a4, s0
	xor t5, t5, a4
	slliw s3, t5, 7
	srliw t5, t5, 25
	or t5, t5, s3
	add t2, t2, t6
	xor s1, s1, t2
	slliw s3, s1, 16
	srliw s1, s1, 16
	or s1, s1, s3
	add a5, a5, s1
	xor t6, t6, a5
	slliw s3, t6, 12
	srliw t6, t6, 20
	or t6, t6, s3
	add t2, t2, t6
	xor s1, s1, t2
	slliw s3, s1, 8
	srliw s1, s1, 24
	or s1, s1, s3
	add a5, a5, s1
	xor t6, t6, a5
	slliw s3, t6, 7
	srliw t6, t6, 25
	or t6, t6, s3
	add t3, t3, a2
	xor s2, s2, t3
	slliw s3, s2, 16
	srliw s2, s2, 16
	or s2, s2, s3
	add a6, a6, s2
	xor a2, a2, a6
	slliw s3, a2, 12
	srliw a2, a2, 20
	or a2, a2, s3
	add t3, t3, a2
	xor s2, s2, t3
	slliw s3, s2, 8
	srliw s2, s2, 24
	or s2, s2, s3
	add a6, a6, s2
	xor a2, a2, a6
	slliw s3, a2, 7
	srliw a2, a2, 25
	or a2, a2, s3
	add t0, t0, t5
	xor s2, s2, t0
	slliw s3, s2, 16
	srliw s2, s2, 16
	or s2, s2, s3
	add a5, a5, s2
	xor t5, t5, a5
	slliw s3, t5, 12
	srliw t5, t5, 20
	or t5, t5, s3
	add t0, t0, t5
	xor s2, s2, t0
	slliw s3, s2, 8
	srliw s2, s2, 24
	or s2, s2, s3
	add a5, a5, s2
	xor t5, t5, a5
	slliw s3, t5, 7
	srliw t5, t5, 25
	or t5, t5, s3
	add t1, t1, t6
	xor a7, a7, t1
	slliw s3, a7, 16
	srliw a7, a7, 16
	or a7, a7, s3
	add a6, a6, a7
	xor t6, t6, a6
	slliw s3, t6, 12
	srliw t6, t6, 20
	or t6, t6, s3
	add t1, t1, t6
	xor a7, a7, t1
	slliw s3, a7, 8
	srliw a7, a7, 24
	or a7, a7, s3
	add a6, a6, a7
	xor t6, t6, a6
	slliw s3, t6, 7
	srliw t6, t6, 25
	or t6, t6, s3
	add t2, t2, a2
	xor s0, s0, t2
	slliw s3, s0, 16
	srliw s0, s0, 16
	or s0, s0, s3
	add a3, a3, s0
	xor a2, a2, a3
	slliw s3, a2, 12
	srliw a2, a2, 20
	or a2, a2, s3
	add t2, t2, a2
	xor s0, s0, t2
	slliw s3, s0, 8
	srliw s0, s0, 24
	or s0, s0, s3
	add a3, a3, s0
	xor a2, a2, a3
	slliw s3, a2, 7
	srliw a2, a2, 25
	or a2, a2, s3
	add t3, t3, t4
	xor s1, s1, t3
	slliw s3, s1, 16
	srliw s1, s1, 16
	or s1, s1, s3
	add a4, a4, s1
	xor t4, t4, a4
	slliw s3, t4, 12
	srliw t4, t4, 20
	or t4, t4, s3
	add t3, t3, t4
	xor s1, s1, t3
	slliw s3, s1, 8
	srliw s1, s1, 24
	or s1, s1, s3
	add a4, a4, s1
	xor t4, t4, a4
	slliw s3, t4, 7
	srliw t4, t4, 25
	or t4, t4, s3
	addi s4, s4, -1
	bnez s4, 20b
	lbu s3, 0(a0)
	lbu s4, 1(a0)
	slli s4, s4, 8
	or s3, s3, s4
	lbu s4, 2(a0)
	slli s4, s4, 16
	or s3, s3, s4
	lbu s4, 3(a0)
	slli s4, s4, 24
	or s3, s3, s4
	add t0, t0, s3
	sb t0, 0(a1)
	srli s3, t0, 8
	sb s3, 1(a1)
	srli s3, t0, 16
	sb s3, 2(a1)
	srli s3, t0, 24
	sb s3, 3(a1)
	lbu s3, 4(a0)
	lbu s4, 5(a0)
	slli s4, s4, 8
	or s3, s3, s4
	lbu s4, 6(a0)
	slli s4, s4, 16
	or s3, s3, s4
	lbu s4, 7(a0)
	slli s4, s4, 24
	or s3, s3, s4
	add t1, t1, s3
	sb t1, 4(a1)
	srli s3, t1, 8
	sb s3, 5(a1)
	srli s3, t1, 16
	sb s3, 6(a1)
	srli s3, t1, 24
	sb s3, 7(a1)
	lbu s3, 8(a0)
	lbu s4, 9(a0)
	slli s4, s4, 8
	or s3, s3, s4
	lbu s4, 10(a0)
	slli s4, s4, 16
	or s3, s3, s4
	lbu s4, 11(a0)
	slli s4, s4, 24
	or s3, s3, s4
	add t2, t2, s3
	sb t2, 8(a1)
	srli s3, t2, 8
	sb s3, 9(a1)
	srli s3, t2, 16
	sb s3, 10(a1)
	srli s3, t2, 24
	sb s3, 11(a1)
	lbu s3, 12(a0)
	lbu s4, 13(a0)
	slli s4, s4, 8
	or s3, s3, s4
	lbu s4, 14(a0)
	slli s4, s4, 16
	or s3, s3, s4
	lbu s4, 15(a0)
	slli s4, s4, 24
	or s3, s3, s4
	add t3, t3, s3
	sb t3, 12(a1)
	srli s3, t3, 8
	sb s3, 13(a1)
	srli s3, t3, 16
	sb s3, 14(a1)
	srli s3, t3, 24
	sb s3, 15(a1)
	lbu s3, 16(a0)
	lbu s4, 17(a0)
	slli s4, s4, 8
	or s3, s3, s4
	lbu s4, 18(a0)
	slli s4, s4, 16
	or s3, s3, s4
	lbu s4, 19(a0)
	slli s4, s4, 24
	or s3, s3, s4
	add t4, t4, s3
	sb t4, 16(a1)
	srli s3, t4, 8
	sb s3, 17(a1)
	srli s3, t4, 16
	sb s3, 18(a1)
	srli s3, t4, 24
	sb s3, 19(a1)
	lbu s3, 20(a0)
	lbu s4, 21(a0)
	slli s4, s4, 8
	or s3, s3, s4
	lbu s4, 22(a0)
	slli s4, s4, 16
	or s3, s3, s4
	lbu s4, 23(a0)
	slli s4, s4, 24
	or s3, s3, s4
	add t5, t5, s3
	sb t5, 20(a1)
	srli s3, t5, 8
	sb s3, 21(a1)
	srli s3, t5, 16
	sb s3, 22(a1)
	srli s3, t5, 24
	sb s3, 23(a1)
	lbu s3, 24(a0)
	lbu s4, 25(a0)
	slli s4, s4, 8
	or s3, s3, s4
	lbu s4, 26(a0)
	slli s4, s4, 16
	or s3, s3, s4
	lbu s4, 27(a0)
	slli s4, s4, 24
	or s3, s3, s4
	add t6, t6, s3
	sb t6, 24(a1)
	srli s3, t6, 8
	sb s3, 25(a1)
	srli s3, t6, 16
	sb s3, 26(a1)
	srli s3, t6, 24
	sb s3, 27(a1)
	lbu s3, 28(a0)
	lbu s4, 29(a0)
	slli s4, s4, 8
	or s3, s3, s4
	lbu s4, 30(a0)
	slli s4, s4, 16
	or s3, s3, s4
	lbu s4, 31(a0)
	slli s4, s4, 24
	or s3, s3, s4
	add a2, a2, s3
	sb a2, 28(a1)
	srli s3, a2, 8
	sb s3, 29(a1)
	srli s3, a2, 16
	sb s3, 30(a1)
	srli s3, a2, 24
	sb s3, 31(a1)
	lbu s3, 32(a0)
	lbu s4, 33(a0)
	slli s4, s4, 8
	or s3, s3, s4
	lbu s4, 34(a0)
	slli s4, s4, 16
	or s3, s3, s4
	lbu s4, 35(a0)
	slli s4, s4, 24
	or s3, s3, s4
	add a3, a3, s3
	sb a3, 32(a1)
	srli s3, a3, 8
	sb s3, 33(a1)
	srli s3, a3, 16
	sb s3, 34(a1)
	srli s3, a3, 24
	sb s3, 35(a1)
	lbu s3, 36(a0)
	lbu s4, 37(a0)
	slli s4, s4, 8
	or s3, s3, s4
	lbu s4, 38(a0)
	slli s4, s4, 16
	or s3, s3, s4
	lbu s4, 39(a0)
	slli s4, s4, 24
	or s3, s3, s4
	add a4, a4, s3
	sb a4, 36(a1)
	srli s3, a4, 8
	sb s3, 37(a1)
	srli s3, a4, 16
	sb s3, 38(a1)
	srli s3, a4, 24
	sb s3, 39(a1)
	lbu s3, 40(a0)
	lbu s4, 41(a0)
	slli s4, s4, 8
	or s3, s3, s4
	lbu s4, 42(a0)
	slli s4, s4, 16
	or s3, s3, s4
	lbu s4, 43(a0)
	slli s4, s4, 24
	or s3, s3, s4
	add a5, a5, s3
	sb a5, 40(a1)
	srli s3, a5, 8
	sb s3, 41(a1)
	srli s3, a5, 16
	sb s3, 42(a1)
	srli s3, a5, 24
	sb s3, 43(a1)
	lbu s3, 44(a0)
	lbu s4, 45(a0)
	slli s4, s4, 8
	or s3, s3, s4
	lbu s4, 46(a0)
	slli s4, s4, 16
	or s3, s3, s4
	lbu s4, 47(a0)
	slli s4, s4, 24
	or s3, s3, s4
	add a6, a6, s3
	sb a6, 44(a1)
	srli s3, a6, 8
	sb s3, 45(a1)
	srli s3, a6, 16
	sb s3, 46(a1)
	srli s3, a6, 24
	sb s3, 47(a1)
	lbu s3, 48(a0)
	lbu s4, 49(a0)
	slli s4, s4, 8
	or s3, s3, s4
	lbu s4, 50(a0)
	slli s4, s4, 16
	or s3, s3, s4
	lbu s4, 51(a0)
	slli s4, s4, 24
	or s3, s3, s4
	add a7, a7, s3
	sb a7, 48(a1)
	srli s3, a7, 8
	sb s3, 49(a1)
	srli s3, a7, 16
	sb s3, 50(a1)
	srli s3, a7, 24
	sb s3, 51(a1)
	lbu s3, 52(a0)
	lbu s4, 53(a0)
	slli s4, s4, 8
	or s3, s3, s4
	lbu s4, 54(a0)
	slli s4, s4, 16
	or s3, s3, s4
	lbu s4, 55(a0)
	slli s4, s4, 24
	or s3, s3, s4
	add s0, s0, s3
	sb s0, 52(a1)
	srli s3, s0, 8
	sb s3, 53(a1)
	srli s3, s0, 16
	sb s3, 54(a1)
	srli s3, s0, 24
	sb s3, 55(a1)
	lbu s3, 56(a0)
	lbu s4, 57(a0)
	slli s4, s4, 8
	or s3, s3, s4
	lbu s4, 58(a0)
	slli s4, s4, 16
	or s3, s3, s4
	lbu s4, 59(a0)
	slli s4, s4, 24
	or s3, s3, s4
	add s1, s1, s3
	sb s1, 56(a1)
	srli s3, s1, 8
	sb s3, 57(a1)
	srli s3, s1, 16
	sb s3, 58(a1)
	srli s3, s1, 24
	sb s3, 59(a1)
	lbu s3, 60(a0)
	lbu s4, 61(a0)
	slli s4, s4, 8
	or s3, s3, s4
	lbu s4, 62(a0)
	slli s4, s4, 16
	or s3, s3, s4
	lbu s4, 63(a0)
	slli s4, s4, 24
	or s3, s3, s4
	add s2, s2, s3
	sb s2, 60(a1)
	srli s3, s2, 8
	sb s3, 61(a1)
	srli s3, s2, 16
	sb s3, 62(a1)
	srli s3, s2, 24
	sb s3, 63(a1)
	addi t0, a1, 71
	andi t0, t0, -8
	ld s0, 0(t0)
	ld s1, 8(t0)
	ld s2, 16(t0)
	ld s3, 24(t0)
	ld s4, 32(t0)
	ret
	.option pop
