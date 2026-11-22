// The functions of `src/ecdsa_p521.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_p521_verify:
	.option push
	.option arch, +m, +c
	addi sp, sp, -80
	addi a5, sp, 0
	addi t0, zero, 66
	bltu a2, t0, 20f
	lbu t1, 0(a1)
	sb t1, 0(a5)
	lbu t1, 1(a1)
	sb t1, 1(a5)
	lbu t1, 2(a1)
	sb t1, 2(a5)
	lbu t1, 3(a1)
	sb t1, 3(a5)
	lbu t1, 4(a1)
	sb t1, 4(a5)
	lbu t1, 5(a1)
	sb t1, 5(a5)
	lbu t1, 6(a1)
	sb t1, 6(a5)
	lbu t1, 7(a1)
	sb t1, 7(a5)
	lbu t1, 8(a1)
	sb t1, 8(a5)
	lbu t1, 9(a1)
	sb t1, 9(a5)
	lbu t1, 10(a1)
	sb t1, 10(a5)
	lbu t1, 11(a1)
	sb t1, 11(a5)
	lbu t1, 12(a1)
	sb t1, 12(a5)
	lbu t1, 13(a1)
	sb t1, 13(a5)
	lbu t1, 14(a1)
	sb t1, 14(a5)
	lbu t1, 15(a1)
	sb t1, 15(a5)
	lbu t1, 16(a1)
	sb t1, 16(a5)
	lbu t1, 17(a1)
	sb t1, 17(a5)
	lbu t1, 18(a1)
	sb t1, 18(a5)
	lbu t1, 19(a1)
	sb t1, 19(a5)
	lbu t1, 20(a1)
	sb t1, 20(a5)
	lbu t1, 21(a1)
	sb t1, 21(a5)
	lbu t1, 22(a1)
	sb t1, 22(a5)
	lbu t1, 23(a1)
	sb t1, 23(a5)
	lbu t1, 24(a1)
	sb t1, 24(a5)
	lbu t1, 25(a1)
	sb t1, 25(a5)
	lbu t1, 26(a1)
	sb t1, 26(a5)
	lbu t1, 27(a1)
	sb t1, 27(a5)
	lbu t1, 28(a1)
	sb t1, 28(a5)
	lbu t1, 29(a1)
	sb t1, 29(a5)
	lbu t1, 30(a1)
	sb t1, 30(a5)
	lbu t1, 31(a1)
	sb t1, 31(a5)
	lbu t1, 32(a1)
	sb t1, 32(a5)
	lbu t1, 33(a1)
	sb t1, 33(a5)
	lbu t1, 34(a1)
	sb t1, 34(a5)
	lbu t1, 35(a1)
	sb t1, 35(a5)
	lbu t1, 36(a1)
	sb t1, 36(a5)
	lbu t1, 37(a1)
	sb t1, 37(a5)
	lbu t1, 38(a1)
	sb t1, 38(a5)
	lbu t1, 39(a1)
	sb t1, 39(a5)
	lbu t1, 40(a1)
	sb t1, 40(a5)
	lbu t1, 41(a1)
	sb t1, 41(a5)
	lbu t1, 42(a1)
	sb t1, 42(a5)
	lbu t1, 43(a1)
	sb t1, 43(a5)
	lbu t1, 44(a1)
	sb t1, 44(a5)
	lbu t1, 45(a1)
	sb t1, 45(a5)
	lbu t1, 46(a1)
	sb t1, 46(a5)
	lbu t1, 47(a1)
	sb t1, 47(a5)
	lbu t1, 48(a1)
	sb t1, 48(a5)
	lbu t1, 49(a1)
	sb t1, 49(a5)
	lbu t1, 50(a1)
	sb t1, 50(a5)
	lbu t1, 51(a1)
	sb t1, 51(a5)
	lbu t1, 52(a1)
	sb t1, 52(a5)
	lbu t1, 53(a1)
	sb t1, 53(a5)
	lbu t1, 54(a1)
	sb t1, 54(a5)
	lbu t1, 55(a1)
	sb t1, 55(a5)
	lbu t1, 56(a1)
	sb t1, 56(a5)
	lbu t1, 57(a1)
	sb t1, 57(a5)
	lbu t1, 58(a1)
	sb t1, 58(a5)
	lbu t1, 59(a1)
	sb t1, 59(a5)
	lbu t1, 60(a1)
	sb t1, 60(a5)
	lbu t1, 61(a1)
	sb t1, 61(a5)
	lbu t1, 62(a1)
	sb t1, 62(a5)
	lbu t1, 63(a1)
	sb t1, 63(a5)
	lbu t1, 64(a1)
	sb t1, 64(a5)
	lbu t1, 65(a1)
	sb t1, 65(a5)
	j 21f
20:
	addi t1, zero, 0
	sb t1, 0(a5)
	addi t1, zero, 0
	sb t1, 1(a5)
	addi t1, zero, 0
	sb t1, 2(a5)
	addi t1, zero, 0
	sb t1, 3(a5)
	addi t1, zero, 0
	sb t1, 4(a5)
	addi t1, zero, 0
	sb t1, 5(a5)
	addi t1, zero, 0
	sb t1, 6(a5)
	addi t1, zero, 0
	sb t1, 7(a5)
	addi t1, zero, 0
	sb t1, 8(a5)
	addi t1, zero, 0
	sb t1, 9(a5)
	addi t1, zero, 0
	sb t1, 10(a5)
	addi t1, zero, 0
	sb t1, 11(a5)
	addi t1, zero, 0
	sb t1, 12(a5)
	addi t1, zero, 0
	sb t1, 13(a5)
	addi t1, zero, 0
	sb t1, 14(a5)
	addi t1, zero, 0
	sb t1, 15(a5)
	addi t1, zero, 0
	sb t1, 16(a5)
	addi t1, zero, 0
	sb t1, 17(a5)
	addi t1, zero, 0
	sb t1, 18(a5)
	addi t1, zero, 0
	sb t1, 19(a5)
	addi t1, zero, 0
	sb t1, 20(a5)
	addi t1, zero, 0
	sb t1, 21(a5)
	addi t1, zero, 0
	sb t1, 22(a5)
	addi t1, zero, 0
	sb t1, 23(a5)
	addi t1, zero, 0
	sb t1, 24(a5)
	addi t1, zero, 0
	sb t1, 25(a5)
	addi t1, zero, 0
	sb t1, 26(a5)
	addi t1, zero, 0
	sb t1, 27(a5)
	addi t1, zero, 0
	sb t1, 28(a5)
	addi t1, zero, 0
	sb t1, 29(a5)
	addi t1, zero, 0
	sb t1, 30(a5)
	addi t1, zero, 0
	sb t1, 31(a5)
	addi t1, zero, 0
	sb t1, 32(a5)
	addi t1, zero, 0
	sb t1, 33(a5)
	addi t1, zero, 0
	sb t1, 34(a5)
	addi t1, zero, 0
	sb t1, 35(a5)
	addi t1, zero, 0
	sb t1, 36(a5)
	addi t1, zero, 0
	sb t1, 37(a5)
	addi t1, zero, 0
	sb t1, 38(a5)
	addi t1, zero, 0
	sb t1, 39(a5)
	addi t1, zero, 0
	sb t1, 40(a5)
	addi t1, zero, 0
	sb t1, 41(a5)
	addi t1, zero, 0
	sb t1, 42(a5)
	addi t1, zero, 0
	sb t1, 43(a5)
	addi t1, zero, 0
	sb t1, 44(a5)
	addi t1, zero, 0
	sb t1, 45(a5)
	addi t1, zero, 0
	sb t1, 46(a5)
	addi t1, zero, 0
	sb t1, 47(a5)
	addi t1, zero, 0
	sb t1, 48(a5)
	addi t1, zero, 0
	sb t1, 49(a5)
	addi t1, zero, 0
	sb t1, 50(a5)
	addi t1, zero, 0
	sb t1, 51(a5)
	addi t1, zero, 0
	sb t1, 52(a5)
	addi t1, zero, 0
	sb t1, 53(a5)
	addi t1, zero, 0
	sb t1, 54(a5)
	addi t1, zero, 0
	sb t1, 55(a5)
	addi t1, zero, 0
	sb t1, 56(a5)
	addi t1, zero, 0
	sb t1, 57(a5)
	addi t1, zero, 0
	sb t1, 58(a5)
	addi t1, zero, 0
	sb t1, 59(a5)
	addi t1, zero, 0
	sb t1, 60(a5)
	addi t1, zero, 0
	sb t1, 61(a5)
	addi t1, zero, 0
	sb t1, 62(a5)
	addi t1, zero, 0
	sb t1, 63(a5)
	addi t1, zero, 0
	sb t1, 64(a5)
	addi t1, zero, 0
	sb t1, 65(a5)
	addi t1, zero, 0
	sb t1, 66(a5)
	addi t1, zero, 0
	sb t1, 67(a5)
	addi t1, zero, 0
	sb t1, 68(a5)
	addi t1, zero, 0
	sb t1, 69(a5)
	addi t1, zero, 0
	sb t1, 70(a5)
	addi t1, zero, 0
	sb t1, 71(a5)
	addi t2, a5, 66
	sub t2, t2, a2
	beqz a2, 22f
24:
	lbu t1, 0(a1)
	sb t1, 0(t2)
	addi a1, a1, 1
	addi t2, t2, 1
	addi a2, a2, -1
	bnez a2, 24b
	j 23f
22:
23:
	lbu t1, 0(a5)
	lbu t2, 1(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 0(a5)
	lbu t1, 1(a5)
	lbu t2, 2(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 1(a5)
	lbu t1, 2(a5)
	lbu t2, 3(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 2(a5)
	lbu t1, 3(a5)
	lbu t2, 4(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 3(a5)
	lbu t1, 4(a5)
	lbu t2, 5(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 4(a5)
	lbu t1, 5(a5)
	lbu t2, 6(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 5(a5)
	lbu t1, 6(a5)
	lbu t2, 7(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 6(a5)
	lbu t1, 7(a5)
	lbu t2, 8(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 7(a5)
	lbu t1, 8(a5)
	lbu t2, 9(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 8(a5)
	lbu t1, 9(a5)
	lbu t2, 10(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 9(a5)
	lbu t1, 10(a5)
	lbu t2, 11(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 10(a5)
	lbu t1, 11(a5)
	lbu t2, 12(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 11(a5)
	lbu t1, 12(a5)
	lbu t2, 13(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 12(a5)
	lbu t1, 13(a5)
	lbu t2, 14(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 13(a5)
	lbu t1, 14(a5)
	lbu t2, 15(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 14(a5)
	lbu t1, 15(a5)
	lbu t2, 16(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 15(a5)
	lbu t1, 16(a5)
	lbu t2, 17(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 16(a5)
	lbu t1, 17(a5)
	lbu t2, 18(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 17(a5)
	lbu t1, 18(a5)
	lbu t2, 19(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 18(a5)
	lbu t1, 19(a5)
	lbu t2, 20(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 19(a5)
	lbu t1, 20(a5)
	lbu t2, 21(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 20(a5)
	lbu t1, 21(a5)
	lbu t2, 22(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 21(a5)
	lbu t1, 22(a5)
	lbu t2, 23(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 22(a5)
	lbu t1, 23(a5)
	lbu t2, 24(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 23(a5)
	lbu t1, 24(a5)
	lbu t2, 25(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 24(a5)
	lbu t1, 25(a5)
	lbu t2, 26(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 25(a5)
	lbu t1, 26(a5)
	lbu t2, 27(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 26(a5)
	lbu t1, 27(a5)
	lbu t2, 28(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 27(a5)
	lbu t1, 28(a5)
	lbu t2, 29(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 28(a5)
	lbu t1, 29(a5)
	lbu t2, 30(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 29(a5)
	lbu t1, 30(a5)
	lbu t2, 31(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 30(a5)
	lbu t1, 31(a5)
	lbu t2, 32(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 31(a5)
	lbu t1, 32(a5)
	lbu t2, 33(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 32(a5)
	lbu t1, 33(a5)
	lbu t2, 34(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 33(a5)
	lbu t1, 34(a5)
	lbu t2, 35(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 34(a5)
	lbu t1, 35(a5)
	lbu t2, 36(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 35(a5)
	lbu t1, 36(a5)
	lbu t2, 37(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 36(a5)
	lbu t1, 37(a5)
	lbu t2, 38(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 37(a5)
	lbu t1, 38(a5)
	lbu t2, 39(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 38(a5)
	lbu t1, 39(a5)
	lbu t2, 40(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 39(a5)
	lbu t1, 40(a5)
	lbu t2, 41(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 40(a5)
	lbu t1, 41(a5)
	lbu t2, 42(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 41(a5)
	lbu t1, 42(a5)
	lbu t2, 43(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 42(a5)
	lbu t1, 43(a5)
	lbu t2, 44(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 43(a5)
	lbu t1, 44(a5)
	lbu t2, 45(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 44(a5)
	lbu t1, 45(a5)
	lbu t2, 46(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 45(a5)
	lbu t1, 46(a5)
	lbu t2, 47(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 46(a5)
	lbu t1, 47(a5)
	lbu t2, 48(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 47(a5)
	lbu t1, 48(a5)
	lbu t2, 49(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 48(a5)
	lbu t1, 49(a5)
	lbu t2, 50(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 49(a5)
	lbu t1, 50(a5)
	lbu t2, 51(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 50(a5)
	lbu t1, 51(a5)
	lbu t2, 52(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 51(a5)
	lbu t1, 52(a5)
	lbu t2, 53(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 52(a5)
	lbu t1, 53(a5)
	lbu t2, 54(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 53(a5)
	lbu t1, 54(a5)
	lbu t2, 55(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 54(a5)
	lbu t1, 55(a5)
	lbu t2, 56(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 55(a5)
	lbu t1, 56(a5)
	lbu t2, 57(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 56(a5)
	lbu t1, 57(a5)
	lbu t2, 58(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 57(a5)
	lbu t1, 58(a5)
	lbu t2, 59(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 58(a5)
	lbu t1, 59(a5)
	lbu t2, 60(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 59(a5)
	lbu t1, 60(a5)
	lbu t2, 61(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 60(a5)
	lbu t1, 61(a5)
	lbu t2, 62(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 61(a5)
	lbu t1, 62(a5)
	lbu t2, 63(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 62(a5)
	lbu t1, 63(a5)
	lbu t2, 64(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 63(a5)
	lbu t1, 64(a5)
	lbu t2, 65(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 64(a5)
	lbu t1, 65(a5)
	lbu t2, 66(a5)
	slli t1, t1, 7
	srli t2, t2, 1
	add t1, t1, t2
	sb t1, 65(a5)
21:
	addi a1, a5, 0
	addi a2, a3, 0
	addi a3, a4, 0
	sd s0, 0(a3)
	sd s1, 8(a3)
	sd s2, 16(a3)
	sd ra, 24(a3)
	sd s3, 32(a3)
	addi s0, a3, 0
	addi s3, a3, 0
	addi s2, a0, 0
	addi t0, zero, 0
	slli t0, t0, 8
	lbu t1, 1(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 2(a0)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 457(s0)
	addi s0, s0, -2047
	lbu t0, 3(a0)
	slli t0, t0, 8
	lbu t1, 4(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 5(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 6(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 7(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 8(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 9(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 10(a0)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 449(s0)
	addi s0, s0, -2047
	lbu t0, 11(a0)
	slli t0, t0, 8
	lbu t1, 12(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 13(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 14(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 15(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 16(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 17(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 18(a0)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 441(s0)
	addi s0, s0, -2047
	lbu t0, 19(a0)
	slli t0, t0, 8
	lbu t1, 20(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 21(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 22(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 23(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 24(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 25(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 26(a0)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 433(s0)
	addi s0, s0, -2047
	lbu t0, 27(a0)
	slli t0, t0, 8
	lbu t1, 28(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 29(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 30(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 31(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 32(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 33(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 34(a0)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 425(s0)
	addi s0, s0, -2047
	lbu t0, 35(a0)
	slli t0, t0, 8
	lbu t1, 36(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 37(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 38(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 39(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 40(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 41(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 42(a0)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 417(s0)
	addi s0, s0, -2047
	lbu t0, 43(a0)
	slli t0, t0, 8
	lbu t1, 44(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 45(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 46(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 47(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 48(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 49(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 50(a0)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 409(s0)
	addi s0, s0, -2047
	lbu t0, 51(a0)
	slli t0, t0, 8
	lbu t1, 52(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 53(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 54(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 55(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 56(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 57(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 58(a0)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 401(s0)
	addi s0, s0, -2047
	lbu t0, 59(a0)
	slli t0, t0, 8
	lbu t1, 60(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 61(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 62(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 63(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 64(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 65(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 66(a0)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 393(s0)
	addi s0, s0, -2047
	addi t0, zero, 0
	slli t0, t0, 8
	lbu t1, 67(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 68(a0)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 673(s0)
	addi s0, s0, -2047
	lbu t0, 69(a0)
	slli t0, t0, 8
	lbu t1, 70(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 71(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 72(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 73(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 74(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 75(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 76(a0)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 665(s0)
	addi s0, s0, -2047
	lbu t0, 77(a0)
	slli t0, t0, 8
	lbu t1, 78(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 79(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 80(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 81(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 82(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 83(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 84(a0)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 657(s0)
	addi s0, s0, -2047
	lbu t0, 85(a0)
	slli t0, t0, 8
	lbu t1, 86(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 87(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 88(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 89(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 90(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 91(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 92(a0)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 649(s0)
	addi s0, s0, -2047
	lbu t0, 93(a0)
	slli t0, t0, 8
	lbu t1, 94(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 95(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 96(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 97(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 98(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 99(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 100(a0)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 641(s0)
	addi s0, s0, -2047
	lbu t0, 101(a0)
	slli t0, t0, 8
	lbu t1, 102(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 103(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 104(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 105(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 106(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 107(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 108(a0)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 633(s0)
	addi s0, s0, -2047
	lbu t0, 109(a0)
	slli t0, t0, 8
	lbu t1, 110(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 111(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 112(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 113(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 114(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 115(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 116(a0)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 625(s0)
	addi s0, s0, -2047
	lbu t0, 117(a0)
	slli t0, t0, 8
	lbu t1, 118(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 119(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 120(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 121(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 122(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 123(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 124(a0)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 617(s0)
	addi s0, s0, -2047
	lbu t0, 125(a0)
	slli t0, t0, 8
	lbu t1, 126(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 127(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 128(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 129(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 130(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 131(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 132(a0)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 609(s0)
	addi s0, s0, -2047
	lbu t0, 0(a0)
	xori t0, t0, 4
	addi t0, t0, -1
	srli t0, t0, 63
	addi t1, zero, 0
	sub a7, t1, t0
	addi s0, s0, 2047
	sd a7, 1185(s0)
	addi s0, s0, -2047
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 64(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 72(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 80(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 88(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 96(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 104(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 112(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 120(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 511
	add t0, t0, t1
	sd t0, 128(s0)
	lui t0, 767739
	addiw t0, t0, 1823
	slli t0, t0, 32
	lui t1, 594822
	addiw t1, t1, 1033
	add t0, t0, t1
	sd t0, 136(s0)
	lui t0, 244573
	addiw t0, t0, -1607
	slli t0, t0, 32
	lui t1, 563652
	addiw t1, t1, 1966
	add t0, t0, t1
	sd t0, 144(s0)
	lui t0, 523456
	addiw t0, t0, 329
	slli t0, t0, 32
	lui t1, 1011866
	addiw t1, t1, 1488
	add t0, t0, t1
	sd t0, 152(s0)
	lui t0, 333928
	addiw t0, t0, 1924
	slli t0, t0, 32
	lui t1, 783097
	addiw t1, t1, 1643
	add t0, t0, t1
	sd t0, 160(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -6
	add t0, t0, t1
	sd t0, 168(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 176(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 184(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 192(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 511
	add t0, t0, t1
	sd t0, 200(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 280(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 288(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 296(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 304(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 312(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 320(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 328(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 336(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 344(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 1
	add t0, t0, t1
	sd t0, 352(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 360(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 368(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 376(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 384(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 392(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 400(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 408(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 416(s0)
	lui t0, 2048
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 424(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 432(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 440(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 448(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 456(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 464(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 472(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 480(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 488(s0)
	lui t0, 1042432
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 496(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 504(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 512(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 520(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 528(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 536(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 544(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 552(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 511
	add t0, t0, t1
	sd t0, 560(s0)
	lui t0, 525267
	addiw t0, t0, -17
	slli t0, t0, 32
	lui t1, 45203
	addiw t1, t1, -1387
	add t0, t0, t1
	sd t0, 568(s0)
	lui t0, 437870
	addiw t0, t0, 1968
	slli t0, t0, 32
	lui t1, 780816
	addiw t1, t1, -1954
	add t0, t0, t1
	sd t0, 576(s0)
	lui t0, 568579
	addiw t0, t0, -561
	slli t0, t0, 32
	lui t1, 312764
	addiw t1, t1, 591
	add t0, t0, t1
	sd t0, 584(s0)
	lui t0, 231960
	addiw t0, t0, -991
	slli t0, t0, 32
	lui t1, 114073
	addiw t1, t1, -1378
	add t0, t0, t1
	sd t0, 592(s0)
	lui t0, 860178
	addiw t0, t0, 1494
	slli t0, t0, 32
	lui t1, 1027628
	addiw t1, t1, -547
	add t0, t0, t1
	sd t0, 600(s0)
	lui t0, 973137
	addiw t0, t0, -306
	slli t0, t0, 32
	lui t1, 370023
	addiw t1, t1, -1650
	add t0, t0, t1
	sd t0, 608(s0)
	lui t0, 417604
	addiw t0, t0, 1964
	slli t0, t0, 32
	lui t1, 562793
	addiw t1, t1, -864
	add t0, t0, t1
	sd t0, 616(s0)
	lui t0, 193982
	addiw t0, t0, 1842
	slli t0, t0, 32
	lui t1, 463132
	addiw t1, t1, 2017
	add t0, t0, t1
	sd t0, 624(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 231
	add t0, t0, t1
	sd t0, 632(s0)
	lui t0, 733978
	addiw t0, t0, 356
	slli t0, t0, 32
	lui t1, 531164
	addiw t1, t1, 257
	add t0, t0, t1
	sd t0, 640(s0)
	lui t0, 319436
	addiw t0, t0, -193
	slli t0, t0, 32
	lui t1, 101911
	addiw t1, t1, 734
	add t0, t0, t1
	sd t0, 648(s0)
	lui t0, 455066
	addiw t0, t0, 1114
	slli t0, t0, 32
	lui t1, 920619
	addiw t1, t1, 1313
	add t0, t0, t1
	sd t0, 656(s0)
	lui t0, 608241
	addiw t0, t0, -287
	slli t0, t0, 32
	lui t1, 605464
	addiw t1, t1, -44
	add t0, t0, t1
	sd t0, 664(s0)
	lui t0, 906506
	addiw t0, t0, 1455
	slli t0, t0, 32
	lui t1, 245631
	addiw t1, t1, 940
	add t0, t0, t1
	sd t0, 672(s0)
	lui t0, 593857
	addiw t0, t0, 1112
	slli t0, t0, 32
	lui t1, 721754
	addiw t1, t1, 1694
	add t0, t0, t1
	sd t0, 680(s0)
	lui t0, 136419
	addiw t0, t0, 577
	slli t0, t0, 32
	lui t1, 641066
	addiw t1, t1, -38
	add t0, t0, t1
	sd t0, 688(s0)
	lui t0, 945394
	addiw t0, t0, -154
	slli t0, t0, 32
	lui t1, 733469
	addiw t1, t1, -1318
	add t0, t0, t1
	sd t0, 696(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 116
	add t0, t0, t1
	sd t0, 704(s0)
	lui t0, 164961
	addiw t0, t0, -438
	slli t0, t0, 32
	lui t1, 371170
	addiw t1, t1, 1678
	add t0, t0, t1
	sd t0, 712(s0)
	lui t0, 132166
	addiw t0, t0, -182
	slli t0, t0, 32
	lui t1, 242943
	addiw t1, t1, -1869
	add t0, t0, t1
	sd t0, 720(s0)
	lui t0, 723370
	addiw t0, t0, -456
	slli t0, t0, 32
	lui t1, 275732
	addiw t1, t1, -1695
	add t0, t0, t1
	sd t0, 728(s0)
	lui t0, 132651
	addiw t0, t0, -1955
	slli t0, t0, 32
	lui t1, 526845
	addiw t1, t1, 1667
	add t0, t0, t1
	sd t0, 736(s0)
	lui t0, 91327
	addiw t0, t0, 1849
	slli t0, t0, 32
	lui t1, 314104
	addiw t1, t1, -1517
	add t0, t0, t1
	sd t0, 744(s0)
	lui t0, 213181
	addiw t0, t0, 2015
	slli t0, t0, 32
	lui t1, 571706
	addiw t1, t1, -205
	add t0, t0, t1
	sd t0, 752(s0)
	lui t0, 969928
	addiw t0, t0, -1374
	slli t0, t0, 32
	lui t1, 150205
	addiw t1, t1, -606
	add t0, t0, t1
	sd t0, 760(s0)
	lui t0, 8932
	addiw t0, t0, 1328
	slli t0, t0, 32
	lui t1, 893284
	addiw t1, t1, -371
	add t0, t0, t1
	sd t0, 768(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 480
	add t0, t0, t1
	sd t0, 776(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -3
	add t0, t0, t1
	sd t0, 928(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 936(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 944(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 952(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 960(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 968(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 976(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 984(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 511
	add t0, t0, t1
	sd t0, 992(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 825(s0)
	addi s0, s0, -2047
	lui t0, 4
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 833(s0)
	addi s0, s0, -2047
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 841(s0)
	addi s0, s0, -2047
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 849(s0)
	addi s0, s0, -2047
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 857(s0)
	addi s0, s0, -2047
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 865(s0)
	addi s0, s0, -2047
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 873(s0)
	addi s0, s0, -2047
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 881(s0)
	addi s0, s0, -2047
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 889(s0)
	addi s0, s0, -2047
	lui t0, 524614
	addiw t0, t0, 1360
	slli t0, t0, 32
	lui t1, 714118
	addiw t1, t1, 903
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 897(s0)
	addi s0, s0, -2047
	lui t0, 495482
	addiw t0, t0, 656
	slli t0, t0, 32
	lui t1, 959323
	addiw t1, t1, -2017
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 905(s0)
	addi s0, s0, -2047
	lui t0, 539052
	addiw t0, t0, -1552
	slli t0, t0, 32
	lui t1, 803305
	addiw t1, t1, 1562
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 913(s0)
	addi s0, s0, -2047
	lui t0, 776371
	addiw t0, t0, -1696
	slli t0, t0, 32
	lui t1, 387550
	addiw t1, t1, -1825
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 921(s0)
	addi s0, s0, -2047
	lui t0, 985777
	addiw t0, t0, -867
	slli t0, t0, 32
	lui t1, 692068
	addiw t1, t1, -183
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 929(s0)
	addi s0, s0, -2047
	lui t0, 1023430
	addiw t0, t0, -1467
	slli t0, t0, 32
	lui t1, 822392
	addiw t1, t1, -1916
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 937(s0)
	addi s0, s0, -2047
	lui t0, 488727
	addiw t0, t0, -711
	slli t0, t0, 32
	lui t1, 187598
	addiw t1, t1, -1654
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 945(s0)
	addi s0, s0, -2047
	lui t0, 64661
	addiw t0, t0, -751
	slli t0, t0, 32
	lui t1, 853428
	addiw t1, t1, 672
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 953(s0)
	addi s0, s0, -2047
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 77
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 961(s0)
	addi s0, s0, -2047
	addi t0, zero, 0
	slli t0, t0, 8
	lbu t1, 0(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 1(a2)
	or t0, t0, t1
	sd t0, 848(s0)
	lbu t0, 2(a2)
	slli t0, t0, 8
	lbu t1, 3(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 4(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 5(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 6(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 7(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 8(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 9(a2)
	or t0, t0, t1
	sd t0, 840(s0)
	lbu t0, 10(a2)
	slli t0, t0, 8
	lbu t1, 11(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 12(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 13(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 14(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 15(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 16(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 17(a2)
	or t0, t0, t1
	sd t0, 832(s0)
	lbu t0, 18(a2)
	slli t0, t0, 8
	lbu t1, 19(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 20(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 21(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 22(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 23(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 24(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 25(a2)
	or t0, t0, t1
	sd t0, 824(s0)
	lbu t0, 26(a2)
	slli t0, t0, 8
	lbu t1, 27(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 28(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 29(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 30(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 31(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 32(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 33(a2)
	or t0, t0, t1
	sd t0, 816(s0)
	lbu t0, 34(a2)
	slli t0, t0, 8
	lbu t1, 35(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 36(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 37(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 38(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 39(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 40(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 41(a2)
	or t0, t0, t1
	sd t0, 808(s0)
	lbu t0, 42(a2)
	slli t0, t0, 8
	lbu t1, 43(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 44(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 45(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 46(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 47(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 48(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 49(a2)
	or t0, t0, t1
	sd t0, 800(s0)
	lbu t0, 50(a2)
	slli t0, t0, 8
	lbu t1, 51(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 52(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 53(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 54(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 55(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 56(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 57(a2)
	or t0, t0, t1
	sd t0, 792(s0)
	lbu t0, 58(a2)
	slli t0, t0, 8
	lbu t1, 59(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 60(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 61(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 62(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 63(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 64(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 65(a2)
	or t0, t0, t1
	sd t0, 784(s0)
	addi t0, zero, 0
	slli t0, t0, 8
	lbu t1, 66(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 67(a2)
	or t0, t0, t1
	sd t0, 920(s0)
	lbu t0, 68(a2)
	slli t0, t0, 8
	lbu t1, 69(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 70(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 71(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 72(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 73(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 74(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 75(a2)
	or t0, t0, t1
	sd t0, 912(s0)
	lbu t0, 76(a2)
	slli t0, t0, 8
	lbu t1, 77(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 78(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 79(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 80(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 81(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 82(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 83(a2)
	or t0, t0, t1
	sd t0, 904(s0)
	lbu t0, 84(a2)
	slli t0, t0, 8
	lbu t1, 85(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 86(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 87(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 88(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 89(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 90(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 91(a2)
	or t0, t0, t1
	sd t0, 896(s0)
	lbu t0, 92(a2)
	slli t0, t0, 8
	lbu t1, 93(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 94(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 95(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 96(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 97(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 98(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 99(a2)
	or t0, t0, t1
	sd t0, 888(s0)
	lbu t0, 100(a2)
	slli t0, t0, 8
	lbu t1, 101(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 102(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 103(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 104(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 105(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 106(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 107(a2)
	or t0, t0, t1
	sd t0, 880(s0)
	lbu t0, 108(a2)
	slli t0, t0, 8
	lbu t1, 109(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 110(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 111(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 112(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 113(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 114(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 115(a2)
	or t0, t0, t1
	sd t0, 872(s0)
	lbu t0, 116(a2)
	slli t0, t0, 8
	lbu t1, 117(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 118(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 119(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 120(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 121(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 122(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 123(a2)
	or t0, t0, t1
	sd t0, 864(s0)
	lbu t0, 124(a2)
	slli t0, t0, 8
	lbu t1, 125(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 126(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 127(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 128(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 129(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 130(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 131(a2)
	or t0, t0, t1
	sd t0, 856(s0)
	addi t0, zero, 0
	slli t0, t0, 8
	lbu t1, 0(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 1(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 385(s0)
	addi s0, s0, -2047
	lbu t0, 2(a1)
	slli t0, t0, 8
	lbu t1, 3(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 4(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 5(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 6(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 7(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 8(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 9(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 377(s0)
	addi s0, s0, -2047
	lbu t0, 10(a1)
	slli t0, t0, 8
	lbu t1, 11(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 12(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 13(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 14(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 15(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 16(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 17(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 369(s0)
	addi s0, s0, -2047
	lbu t0, 18(a1)
	slli t0, t0, 8
	lbu t1, 19(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 20(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 21(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 22(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 23(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 24(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 25(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 361(s0)
	addi s0, s0, -2047
	lbu t0, 26(a1)
	slli t0, t0, 8
	lbu t1, 27(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 28(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 29(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 30(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 31(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 32(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 33(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 353(s0)
	addi s0, s0, -2047
	lbu t0, 34(a1)
	slli t0, t0, 8
	lbu t1, 35(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 36(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 37(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 38(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 39(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 40(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 41(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 345(s0)
	addi s0, s0, -2047
	lbu t0, 42(a1)
	slli t0, t0, 8
	lbu t1, 43(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 44(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 45(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 46(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 47(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 48(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 49(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 337(s0)
	addi s0, s0, -2047
	lbu t0, 50(a1)
	slli t0, t0, 8
	lbu t1, 51(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 52(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 53(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 54(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 55(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 56(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 57(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 329(s0)
	addi s0, s0, -2047
	lbu t0, 58(a1)
	slli t0, t0, 8
	lbu t1, 59(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 60(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 61(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 62(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 63(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 64(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 65(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 321(s0)
	addi s0, s0, -2047
	addi t0, s0, 2047
	ld t0, 321(t0)
	srli t0, t0, 7
	addi t1, s0, 2047
	ld t1, 329(t1)
	slli t1, t1, 57
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 321(s0)
	addi s0, s0, -2047
	addi t0, s0, 2047
	ld t0, 329(t0)
	srli t0, t0, 7
	addi t1, s0, 2047
	ld t1, 337(t1)
	slli t1, t1, 57
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 329(s0)
	addi s0, s0, -2047
	addi t0, s0, 2047
	ld t0, 337(t0)
	srli t0, t0, 7
	addi t1, s0, 2047
	ld t1, 345(t1)
	slli t1, t1, 57
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 337(s0)
	addi s0, s0, -2047
	addi t0, s0, 2047
	ld t0, 345(t0)
	srli t0, t0, 7
	addi t1, s0, 2047
	ld t1, 353(t1)
	slli t1, t1, 57
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 345(s0)
	addi s0, s0, -2047
	addi t0, s0, 2047
	ld t0, 353(t0)
	srli t0, t0, 7
	addi t1, s0, 2047
	ld t1, 361(t1)
	slli t1, t1, 57
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 353(s0)
	addi s0, s0, -2047
	addi t0, s0, 2047
	ld t0, 361(t0)
	srli t0, t0, 7
	addi t1, s0, 2047
	ld t1, 369(t1)
	slli t1, t1, 57
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 361(s0)
	addi s0, s0, -2047
	addi t0, s0, 2047
	ld t0, 369(t0)
	srli t0, t0, 7
	addi t1, s0, 2047
	ld t1, 377(t1)
	slli t1, t1, 57
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 369(s0)
	addi s0, s0, -2047
	addi t0, s0, 2047
	ld t0, 377(t0)
	srli t0, t0, 7
	addi t1, s0, 2047
	ld t1, 385(t1)
	slli t1, t1, 57
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 377(s0)
	addi s0, s0, -2047
	addi t0, s0, 2047
	ld t0, 385(t0)
	srli t0, t0, 7
	addi s0, s0, 2047
	sd t0, 385(s0)
	addi s0, s0, -2047
	addi t5, zero, 0
	ld t3, 784(s0)
	ld t4, 136(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 792(s0)
	ld t4, 144(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 800(s0)
	ld t4, 152(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 808(s0)
	ld t4, 160(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 816(s0)
	ld t4, 168(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 824(s0)
	ld t4, 176(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 832(s0)
	ld t4, 184(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 840(s0)
	ld t4, 192(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 848(s0)
	ld t4, 200(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t6, zero, 0
	sub a7, t6, t5
	addi t0, s0, 2047
	ld t0, 1185(t0)
	and t0, t0, a7
	addi s0, s0, 2047
	sd t0, 1185(s0)
	addi s0, s0, -2047
	addi t3, zero, 0
	ld t4, 784(s0)
	or t3, t3, t4
	ld t4, 792(s0)
	or t3, t3, t4
	ld t4, 800(s0)
	or t3, t3, t4
	ld t4, 808(s0)
	or t3, t3, t4
	ld t4, 816(s0)
	or t3, t3, t4
	ld t4, 824(s0)
	or t3, t3, t4
	ld t4, 832(s0)
	or t3, t3, t4
	ld t4, 840(s0)
	or t3, t3, t4
	ld t4, 848(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	xori a7, a7, -1
	addi t0, s0, 2047
	ld t0, 1185(t0)
	and t0, t0, a7
	addi s0, s0, 2047
	sd t0, 1185(s0)
	addi s0, s0, -2047
	addi t5, zero, 0
	ld t3, 856(s0)
	ld t4, 136(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 864(s0)
	ld t4, 144(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 872(s0)
	ld t4, 152(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 880(s0)
	ld t4, 160(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 888(s0)
	ld t4, 168(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 896(s0)
	ld t4, 176(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 904(s0)
	ld t4, 184(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 912(s0)
	ld t4, 192(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 920(s0)
	ld t4, 200(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t6, zero, 0
	sub a7, t6, t5
	addi t0, s0, 2047
	ld t0, 1185(t0)
	and t0, t0, a7
	addi s0, s0, 2047
	sd t0, 1185(s0)
	addi s0, s0, -2047
	addi t3, zero, 0
	ld t4, 856(s0)
	or t3, t3, t4
	ld t4, 864(s0)
	or t3, t3, t4
	ld t4, 872(s0)
	or t3, t3, t4
	ld t4, 880(s0)
	or t3, t3, t4
	ld t4, 888(s0)
	or t3, t3, t4
	ld t4, 896(s0)
	or t3, t3, t4
	ld t4, 904(s0)
	or t3, t3, t4
	ld t4, 912(s0)
	or t3, t3, t4
	ld t4, 920(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	xori a7, a7, -1
	addi t0, s0, 2047
	ld t0, 1185(t0)
	and t0, t0, a7
	addi s0, s0, 2047
	sd t0, 1185(s0)
	addi s0, s0, -2047
	addi a0, s0, 0
	call {vg_p521_check_point}
	addi s0, s3, 0
	lui t0, 79821
	addiw t0, t0, 78
	slli t0, t0, 32
	lui t1, 848222
	addiw t1, t1, -764
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 537(s0)
	addi s0, s0, -2047
	lui t0, 1011836
	addiw t0, t0, -1315
	slli t0, t0, 32
	lui t1, 939336
	addiw t1, t1, -349
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 545(s0)
	addi s0, s0, -2047
	lui t0, 76409
	addiw t0, t0, -712
	slli t0, t0, 32
	lui t1, 496727
	addiw t1, t1, 1023
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 553(s0)
	addi s0, s0, -2047
	lui t0, 866082
	addiw t0, t0, -267
	slli t0, t0, 32
	lui t1, 360310
	addiw t1, t1, -506
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 561(s0)
	addi s0, s0, -2047
	lui t0, 906978
	addiw t0, t0, 984
	slli t0, t0, 32
	lui t1, 189596
	addiw t1, t1, 2011
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 569(s0)
	addi s0, s0, -2047
	lui t0, 851773
	addiw t0, t0, 323
	slli t0, t0, 32
	lui t1, 751447
	addiw t1, t1, -450
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 577(s0)
	addi s0, s0, -2047
	lui t0, 376007
	addiw t0, t0, -670
	slli t0, t0, 32
	lui t1, 691798
	addiw t1, t1, 1980
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 585(s0)
	addi s0, s0, -2047
	lui t0, 186592
	addiw t0, t0, 977
	slli t0, t0, 32
	lui t1, 299729
	addiw t1, t1, -699
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 593(s0)
	addi s0, s0, -2047
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 61
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 601(s0)
	addi s0, s0, -2047
	lui t0, 1030144
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 609(s0)
	addi s0, s0, -2047
	lui t0, 166437
	addiw t0, t0, -2012
	slli t0, t0, 32
	lui t1, 461686
	addiw t1, t1, 973
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 617(s0)
	addi s0, s0, -2047
	lui t0, 97826
	addiw t0, t0, 1307
	slli t0, t0, 32
	lui t1, 146355
	addiw t1, t1, 476
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 625(s0)
	addi s0, s0, -2047
	lui t0, 828418
	addiw t0, t0, -1537
	slli t0, t0, 32
	lui t1, 374856
	addiw t1, t1, -1235
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 633(s0)
	addi s0, s0, -2047
	lui t0, 11636
	addiw t0, t0, -836
	slli t0, t0, 32
	lui t1, 254471
	addiw t1, t1, -1996
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 641(s0)
	addi s0, s0, -2047
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 649(s0)
	addi s0, s0, -2047
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 657(s0)
	addi s0, s0, -2047
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 665(s0)
	addi s0, s0, -2047
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 673(s0)
	addi s0, s0, -2047
	lui t0, 767739
	addiw t0, t0, 1823
	slli t0, t0, 32
	lui t1, 594822
	addiw t1, t1, 1031
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 681(s0)
	addi s0, s0, -2047
	lui t0, 244573
	addiw t0, t0, -1607
	slli t0, t0, 32
	lui t1, 563652
	addiw t1, t1, 1966
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 689(s0)
	addi s0, s0, -2047
	lui t0, 523456
	addiw t0, t0, 329
	slli t0, t0, 32
	lui t1, 1011866
	addiw t1, t1, 1488
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 697(s0)
	addi s0, s0, -2047
	lui t0, 333928
	addiw t0, t0, 1924
	slli t0, t0, 32
	lui t1, 783097
	addiw t1, t1, 1643
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 705(s0)
	addi s0, s0, -2047
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -6
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 713(s0)
	addi s0, s0, -2047
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 721(s0)
	addi s0, s0, -2047
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 729(s0)
	addi s0, s0, -2047
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 737(s0)
	addi s0, s0, -2047
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 511
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 745(s0)
	addi s0, s0, -2047
	addi a0, s0, 0
	addi a1, zero, 1504
	addi a2, zero, 856
	addi a3, zero, 2047
	addi a3, a3, 537
	call {vg_p521_mul_mod_n}
	call {vg_p521_inv_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1576
	addi a2, zero, 2047
	addi a2, a2, 321
	addi a3, zero, 2047
	addi a3, a3, 537
	call {vg_p521_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1648
	addi a2, zero, 1576
	addi a3, zero, 2047
	addi a3, a3, 105
	call {vg_p521_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 393
	addi a2, zero, 1648
	addi a3, zero, 352
	call {vg_p521_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1648
	addi a2, zero, 784
	addi a3, zero, 2047
	addi a3, a3, 537
	call {vg_p521_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1648
	addi a3, zero, 2047
	addi a3, a3, 105
	call {vg_p521_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 609
	addi a2, zero, 1792
	addi a3, zero, 352
	call {vg_p521_mul_mod_n}
	addi t0, s0, 2047
	ld t0, 609(t0)
	addi s0, s0, 2047
	sd t0, 249(s0)
	addi s0, s0, -2047
	addi t0, s0, 2047
	ld t0, 617(t0)
	addi s0, s0, 2047
	sd t0, 257(s0)
	addi s0, s0, -2047
	addi t0, s0, 2047
	ld t0, 625(t0)
	addi s0, s0, 2047
	sd t0, 265(s0)
	addi s0, s0, -2047
	addi t0, s0, 2047
	ld t0, 633(t0)
	addi s0, s0, 2047
	sd t0, 273(s0)
	addi s0, s0, -2047
	addi t0, s0, 2047
	ld t0, 641(t0)
	addi s0, s0, 2047
	sd t0, 281(s0)
	addi s0, s0, -2047
	addi t0, s0, 2047
	ld t0, 649(t0)
	addi s0, s0, 2047
	sd t0, 289(s0)
	addi s0, s0, -2047
	addi t0, s0, 2047
	ld t0, 657(t0)
	addi s0, s0, 2047
	sd t0, 297(s0)
	addi s0, s0, -2047
	addi t0, s0, 2047
	ld t0, 665(t0)
	addi s0, s0, 2047
	sd t0, 305(s0)
	addi s0, s0, -2047
	addi t0, s0, 2047
	ld t0, 673(t0)
	addi s0, s0, 2047
	sd t0, 313(s0)
	addi s0, s0, -2047
	addi t0, s0, 2047
	ld t0, 753(t0)
	sd t0, 1072(s0)
	addi t0, s0, 2047
	ld t0, 761(t0)
	sd t0, 1080(s0)
	addi t0, s0, 2047
	ld t0, 769(t0)
	sd t0, 1088(s0)
	addi t0, s0, 2047
	ld t0, 777(t0)
	sd t0, 1096(s0)
	addi t0, s0, 2047
	ld t0, 785(t0)
	sd t0, 1104(s0)
	addi t0, s0, 2047
	ld t0, 793(t0)
	sd t0, 1112(s0)
	addi t0, s0, 2047
	ld t0, 801(t0)
	sd t0, 1120(s0)
	addi t0, s0, 2047
	ld t0, 809(t0)
	sd t0, 1128(s0)
	addi t0, s0, 2047
	ld t0, 817(t0)
	sd t0, 1136(s0)
	addi t0, s0, 2047
	ld t0, 1113(t0)
	sd t0, 1144(s0)
	addi t0, s0, 2047
	ld t0, 1121(t0)
	sd t0, 1152(s0)
	addi t0, s0, 2047
	ld t0, 1129(t0)
	sd t0, 1160(s0)
	addi t0, s0, 2047
	ld t0, 1137(t0)
	sd t0, 1168(s0)
	addi t0, s0, 2047
	ld t0, 1145(t0)
	sd t0, 1176(s0)
	addi t0, s0, 2047
	ld t0, 1153(t0)
	sd t0, 1184(s0)
	addi t0, s0, 2047
	ld t0, 1161(t0)
	sd t0, 1192(s0)
	addi t0, s0, 2047
	ld t0, 1169(t0)
	sd t0, 1200(s0)
	addi t0, s0, 2047
	ld t0, 1177(t0)
	sd t0, 1208(s0)
	addi a0, s0, 0
	call {vg_p521_mul}
	addi s0, s3, 0
	addi t3, zero, 0
	addi t4, s0, 2047
	ld t4, 609(t4)
	or t3, t3, t4
	addi t4, s0, 2047
	ld t4, 617(t4)
	or t3, t3, t4
	addi t4, s0, 2047
	ld t4, 625(t4)
	or t3, t3, t4
	addi t4, s0, 2047
	ld t4, 633(t4)
	or t3, t3, t4
	addi t4, s0, 2047
	ld t4, 641(t4)
	or t3, t3, t4
	addi t4, s0, 2047
	ld t4, 649(t4)
	or t3, t3, t4
	addi t4, s0, 2047
	ld t4, 657(t4)
	or t3, t3, t4
	addi t4, s0, 2047
	ld t4, 665(t4)
	or t3, t3, t4
	addi t4, s0, 2047
	ld t4, 673(t4)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	ld t0, 1072(s0)
	ld t1, 280(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1072(s0)
	ld t0, 1080(s0)
	ld t1, 288(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1080(s0)
	ld t0, 1088(s0)
	ld t1, 296(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1088(s0)
	ld t0, 1096(s0)
	ld t1, 304(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1096(s0)
	ld t0, 1104(s0)
	ld t1, 312(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1104(s0)
	ld t0, 1112(s0)
	ld t1, 320(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1112(s0)
	ld t0, 1120(s0)
	ld t1, 328(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1120(s0)
	ld t0, 1128(s0)
	ld t1, 336(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1128(s0)
	ld t0, 1136(s0)
	ld t1, 344(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1136(s0)
	ld t0, 1144(s0)
	ld t1, 424(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1144(s0)
	ld t0, 1152(s0)
	ld t1, 432(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1152(s0)
	ld t0, 1160(s0)
	ld t1, 440(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1160(s0)
	ld t0, 1168(s0)
	ld t1, 448(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1168(s0)
	ld t0, 1176(s0)
	ld t1, 456(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1176(s0)
	ld t0, 1184(s0)
	ld t1, 464(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1184(s0)
	ld t0, 1192(s0)
	ld t1, 472(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1192(s0)
	ld t0, 1200(s0)
	ld t1, 480(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1200(s0)
	ld t0, 1208(s0)
	ld t1, 488(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1208(s0)
	ld t0, 1216(s0)
	ld t1, 280(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1216(s0)
	ld t0, 1224(s0)
	ld t1, 288(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1224(s0)
	ld t0, 1232(s0)
	ld t1, 296(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1232(s0)
	ld t0, 1240(s0)
	ld t1, 304(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1240(s0)
	ld t0, 1248(s0)
	ld t1, 312(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1248(s0)
	ld t0, 1256(s0)
	ld t1, 320(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1256(s0)
	ld t0, 1264(s0)
	ld t1, 328(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1264(s0)
	ld t0, 1272(s0)
	ld t1, 336(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1272(s0)
	ld t0, 1280(s0)
	ld t1, 344(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1280(s0)
	lui t0, 524614
	addiw t0, t0, 1360
	slli t0, t0, 32
	lui t1, 714118
	addiw t1, t1, 903
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 897(s0)
	addi s0, s0, -2047
	lui t0, 495482
	addiw t0, t0, 656
	slli t0, t0, 32
	lui t1, 959323
	addiw t1, t1, -2017
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 905(s0)
	addi s0, s0, -2047
	lui t0, 539052
	addiw t0, t0, -1552
	slli t0, t0, 32
	lui t1, 803305
	addiw t1, t1, 1562
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 913(s0)
	addi s0, s0, -2047
	lui t0, 776371
	addiw t0, t0, -1696
	slli t0, t0, 32
	lui t1, 387550
	addiw t1, t1, -1825
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 921(s0)
	addi s0, s0, -2047
	lui t0, 985777
	addiw t0, t0, -867
	slli t0, t0, 32
	lui t1, 692068
	addiw t1, t1, -183
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 929(s0)
	addi s0, s0, -2047
	lui t0, 1023430
	addiw t0, t0, -1467
	slli t0, t0, 32
	lui t1, 822392
	addiw t1, t1, -1916
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 937(s0)
	addi s0, s0, -2047
	lui t0, 488727
	addiw t0, t0, -711
	slli t0, t0, 32
	lui t1, 187598
	addiw t1, t1, -1654
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 945(s0)
	addi s0, s0, -2047
	lui t0, 64661
	addiw t0, t0, -751
	slli t0, t0, 32
	lui t1, 853428
	addiw t1, t1, 672
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 953(s0)
	addi s0, s0, -2047
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 77
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 961(s0)
	addi s0, s0, -2047
	ld t0, 1072(s0)
	sd t0, 640(s0)
	ld t0, 1080(s0)
	sd t0, 648(s0)
	ld t0, 1088(s0)
	sd t0, 656(s0)
	ld t0, 1096(s0)
	sd t0, 664(s0)
	ld t0, 1104(s0)
	sd t0, 672(s0)
	ld t0, 1112(s0)
	sd t0, 680(s0)
	ld t0, 1120(s0)
	sd t0, 688(s0)
	ld t0, 1128(s0)
	sd t0, 696(s0)
	ld t0, 1136(s0)
	sd t0, 704(s0)
	ld t0, 1144(s0)
	addi s0, s0, 2047
	sd t0, 753(s0)
	addi s0, s0, -2047
	ld t0, 1152(s0)
	addi s0, s0, 2047
	sd t0, 761(s0)
	addi s0, s0, -2047
	ld t0, 1160(s0)
	addi s0, s0, 2047
	sd t0, 769(s0)
	addi s0, s0, -2047
	ld t0, 1168(s0)
	addi s0, s0, 2047
	sd t0, 777(s0)
	addi s0, s0, -2047
	ld t0, 1176(s0)
	addi s0, s0, 2047
	sd t0, 785(s0)
	addi s0, s0, -2047
	ld t0, 1184(s0)
	addi s0, s0, 2047
	sd t0, 793(s0)
	addi s0, s0, -2047
	ld t0, 1192(s0)
	addi s0, s0, 2047
	sd t0, 801(s0)
	addi s0, s0, -2047
	ld t0, 1200(s0)
	addi s0, s0, 2047
	sd t0, 809(s0)
	addi s0, s0, -2047
	ld t0, 1208(s0)
	addi s0, s0, 2047
	sd t0, 817(s0)
	addi s0, s0, -2047
	ld t0, 1216(s0)
	addi s0, s0, 2047
	sd t0, 1113(s0)
	addi s0, s0, -2047
	ld t0, 1224(s0)
	addi s0, s0, 2047
	sd t0, 1121(s0)
	addi s0, s0, -2047
	ld t0, 1232(s0)
	addi s0, s0, 2047
	sd t0, 1129(s0)
	addi s0, s0, -2047
	ld t0, 1240(s0)
	addi s0, s0, 2047
	sd t0, 1137(s0)
	addi s0, s0, -2047
	ld t0, 1248(s0)
	addi s0, s0, 2047
	sd t0, 1145(s0)
	addi s0, s0, -2047
	ld t0, 1256(s0)
	addi s0, s0, 2047
	sd t0, 1153(s0)
	addi s0, s0, -2047
	ld t0, 1264(s0)
	addi s0, s0, 2047
	sd t0, 1161(s0)
	addi s0, s0, -2047
	ld t0, 1272(s0)
	addi s0, s0, 2047
	sd t0, 1169(s0)
	addi s0, s0, -2047
	ld t0, 1280(s0)
	addi s0, s0, 2047
	sd t0, 1177(s0)
	addi s0, s0, -2047
	addi t0, s0, 2047
	ld t0, 393(t0)
	addi s0, s0, 2047
	sd t0, 249(s0)
	addi s0, s0, -2047
	addi t0, s0, 2047
	ld t0, 401(t0)
	addi s0, s0, 2047
	sd t0, 257(s0)
	addi s0, s0, -2047
	addi t0, s0, 2047
	ld t0, 409(t0)
	addi s0, s0, 2047
	sd t0, 265(s0)
	addi s0, s0, -2047
	addi t0, s0, 2047
	ld t0, 417(t0)
	addi s0, s0, 2047
	sd t0, 273(s0)
	addi s0, s0, -2047
	addi t0, s0, 2047
	ld t0, 425(t0)
	addi s0, s0, 2047
	sd t0, 281(s0)
	addi s0, s0, -2047
	addi t0, s0, 2047
	ld t0, 433(t0)
	addi s0, s0, 2047
	sd t0, 289(s0)
	addi s0, s0, -2047
	addi t0, s0, 2047
	ld t0, 441(t0)
	addi s0, s0, 2047
	sd t0, 297(s0)
	addi s0, s0, -2047
	addi t0, s0, 2047
	ld t0, 449(t0)
	addi s0, s0, 2047
	sd t0, 305(s0)
	addi s0, s0, -2047
	addi t0, s0, 2047
	ld t0, 457(t0)
	addi s0, s0, 2047
	sd t0, 313(s0)
	addi s0, s0, -2047
	addi a0, s0, 0
	call {vg_p521_mul_g}
	addi s0, s3, 0
	addi t3, zero, 0
	addi t4, s0, 2047
	ld t4, 393(t4)
	or t3, t3, t4
	addi t4, s0, 2047
	ld t4, 401(t4)
	or t3, t3, t4
	addi t4, s0, 2047
	ld t4, 409(t4)
	or t3, t3, t4
	addi t4, s0, 2047
	ld t4, 417(t4)
	or t3, t3, t4
	addi t4, s0, 2047
	ld t4, 425(t4)
	or t3, t3, t4
	addi t4, s0, 2047
	ld t4, 433(t4)
	or t3, t3, t4
	addi t4, s0, 2047
	ld t4, 441(t4)
	or t3, t3, t4
	addi t4, s0, 2047
	ld t4, 449(t4)
	or t3, t3, t4
	addi t4, s0, 2047
	ld t4, 457(t4)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	ld t0, 1072(s0)
	ld t1, 280(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1072(s0)
	ld t0, 1080(s0)
	ld t1, 288(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1080(s0)
	ld t0, 1088(s0)
	ld t1, 296(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1088(s0)
	ld t0, 1096(s0)
	ld t1, 304(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1096(s0)
	ld t0, 1104(s0)
	ld t1, 312(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1104(s0)
	ld t0, 1112(s0)
	ld t1, 320(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1112(s0)
	ld t0, 1120(s0)
	ld t1, 328(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1120(s0)
	ld t0, 1128(s0)
	ld t1, 336(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1128(s0)
	ld t0, 1136(s0)
	ld t1, 344(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1136(s0)
	ld t0, 1144(s0)
	ld t1, 424(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1144(s0)
	ld t0, 1152(s0)
	ld t1, 432(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1152(s0)
	ld t0, 1160(s0)
	ld t1, 440(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1160(s0)
	ld t0, 1168(s0)
	ld t1, 448(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1168(s0)
	ld t0, 1176(s0)
	ld t1, 456(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1176(s0)
	ld t0, 1184(s0)
	ld t1, 464(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1184(s0)
	ld t0, 1192(s0)
	ld t1, 472(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1192(s0)
	ld t0, 1200(s0)
	ld t1, 480(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1200(s0)
	ld t0, 1208(s0)
	ld t1, 488(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1208(s0)
	ld t0, 1216(s0)
	ld t1, 280(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1216(s0)
	ld t0, 1224(s0)
	ld t1, 288(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1224(s0)
	ld t0, 1232(s0)
	ld t1, 296(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1232(s0)
	ld t0, 1240(s0)
	ld t1, 304(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1240(s0)
	ld t0, 1248(s0)
	ld t1, 312(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1248(s0)
	ld t0, 1256(s0)
	ld t1, 320(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1256(s0)
	ld t0, 1264(s0)
	ld t1, 328(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1264(s0)
	ld t0, 1272(s0)
	ld t1, 336(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1272(s0)
	ld t0, 1280(s0)
	ld t1, 344(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1280(s0)
	lui t0, 524614
	addiw t0, t0, 1360
	slli t0, t0, 32
	lui t1, 714118
	addiw t1, t1, 903
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 897(s0)
	addi s0, s0, -2047
	lui t0, 495482
	addiw t0, t0, 656
	slli t0, t0, 32
	lui t1, 959323
	addiw t1, t1, -2017
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 905(s0)
	addi s0, s0, -2047
	lui t0, 539052
	addiw t0, t0, -1552
	slli t0, t0, 32
	lui t1, 803305
	addiw t1, t1, 1562
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 913(s0)
	addi s0, s0, -2047
	lui t0, 776371
	addiw t0, t0, -1696
	slli t0, t0, 32
	lui t1, 387550
	addiw t1, t1, -1825
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 921(s0)
	addi s0, s0, -2047
	lui t0, 985777
	addiw t0, t0, -867
	slli t0, t0, 32
	lui t1, 692068
	addiw t1, t1, -183
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 929(s0)
	addi s0, s0, -2047
	lui t0, 1023430
	addiw t0, t0, -1467
	slli t0, t0, 32
	lui t1, 822392
	addiw t1, t1, -1916
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 937(s0)
	addi s0, s0, -2047
	lui t0, 488727
	addiw t0, t0, -711
	slli t0, t0, 32
	lui t1, 187598
	addiw t1, t1, -1654
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 945(s0)
	addi s0, s0, -2047
	lui t0, 64661
	addiw t0, t0, -751
	slli t0, t0, 32
	lui t1, 853428
	addiw t1, t1, 672
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 953(s0)
	addi s0, s0, -2047
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 77
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 961(s0)
	addi s0, s0, -2047
	addi a0, s0, 0
	addi a1, zero, 1720
	addi a2, zero, 1072
	addi a3, zero, 640
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1144
	addi a3, zero, 2047
	addi a3, a3, 753
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1864
	addi a2, zero, 1216
	addi a3, zero, 2047
	addi a3, a3, 1113
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1936
	addi a2, zero, 1072
	addi a3, zero, 1144
	call {vg_p521_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2008
	addi a2, zero, 640
	addi a3, zero, 2047
	addi a3, a3, 753
	call {vg_p521_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1936
	addi a2, zero, 1936
	addi a3, zero, 2008
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2008
	addi a2, zero, 1720
	addi a3, zero, 1792
	call {vg_p521_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1936
	addi a2, zero, 1936
	addi a3, zero, 2008
	call {vg_p521_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2008
	addi a2, zero, 1144
	addi a3, zero, 1216
	call {vg_p521_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1504
	addi a2, zero, 2047
	addi a2, a2, 753
	addi a3, zero, 2047
	addi a3, a3, 1113
	call {vg_p521_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2008
	addi a2, zero, 2008
	addi a3, zero, 1504
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1504
	addi a2, zero, 1792
	addi a3, zero, 1864
	call {vg_p521_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2008
	addi a2, zero, 2008
	addi a3, zero, 1504
	call {vg_p521_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1504
	addi a2, zero, 1072
	addi a3, zero, 1216
	call {vg_p521_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1576
	addi a2, zero, 640
	addi a3, zero, 2047
	addi a3, a3, 1113
	call {vg_p521_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1504
	addi a2, zero, 1504
	addi a3, zero, 1576
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1576
	addi a2, zero, 1720
	addi a3, zero, 1864
	call {vg_p521_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1576
	addi a2, zero, 1504
	addi a3, zero, 1576
	call {vg_p521_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1648
	addi a2, zero, 2047
	addi a2, a2, 897
	addi a3, zero, 1864
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1504
	addi a2, zero, 1576
	addi a3, zero, 1648
	call {vg_p521_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1648
	addi a2, zero, 1504
	addi a3, zero, 1504
	call {vg_p521_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1504
	addi a2, zero, 1504
	addi a3, zero, 1648
	call {vg_p521_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1648
	addi a2, zero, 1792
	addi a3, zero, 1504
	call {vg_p521_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1504
	addi a2, zero, 1792
	addi a3, zero, 1504
	call {vg_p521_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1576
	addi a2, zero, 2047
	addi a2, a2, 897
	addi a3, zero, 1576
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1864
	addi a3, zero, 1864
	call {vg_p521_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1864
	addi a2, zero, 1792
	addi a3, zero, 1864
	call {vg_p521_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1576
	addi a2, zero, 1576
	addi a3, zero, 1864
	call {vg_p521_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1576
	addi a2, zero, 1576
	addi a3, zero, 1720
	call {vg_p521_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1576
	addi a3, zero, 1576
	call {vg_p521_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1576
	addi a2, zero, 1792
	addi a3, zero, 1576
	call {vg_p521_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1720
	addi a3, zero, 1720
	call {vg_p521_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1720
	addi a2, zero, 1792
	addi a3, zero, 1720
	call {vg_p521_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1720
	addi a2, zero, 1720
	addi a3, zero, 1864
	call {vg_p521_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 2008
	addi a3, zero, 1576
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1864
	addi a2, zero, 1720
	addi a3, zero, 1576
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1576
	addi a2, zero, 1504
	addi a3, zero, 1648
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1576
	addi a2, zero, 1576
	addi a3, zero, 1864
	call {vg_p521_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1504
	addi a2, zero, 1936
	addi a3, zero, 1504
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1504
	addi a2, zero, 1504
	addi a3, zero, 1792
	call {vg_p521_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1648
	addi a2, zero, 2008
	addi a3, zero, 1648
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1936
	addi a3, zero, 1720
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1648
	addi a2, zero, 1648
	addi a3, zero, 1792
	call {vg_p521_add_mod_p}
	ld t0, 1504(s0)
	sd t0, 1072(s0)
	ld t0, 1512(s0)
	sd t0, 1080(s0)
	ld t0, 1520(s0)
	sd t0, 1088(s0)
	ld t0, 1528(s0)
	sd t0, 1096(s0)
	ld t0, 1536(s0)
	sd t0, 1104(s0)
	ld t0, 1544(s0)
	sd t0, 1112(s0)
	ld t0, 1552(s0)
	sd t0, 1120(s0)
	ld t0, 1560(s0)
	sd t0, 1128(s0)
	ld t0, 1568(s0)
	sd t0, 1136(s0)
	ld t0, 1576(s0)
	sd t0, 1144(s0)
	ld t0, 1584(s0)
	sd t0, 1152(s0)
	ld t0, 1592(s0)
	sd t0, 1160(s0)
	ld t0, 1600(s0)
	sd t0, 1168(s0)
	ld t0, 1608(s0)
	sd t0, 1176(s0)
	ld t0, 1616(s0)
	sd t0, 1184(s0)
	ld t0, 1624(s0)
	sd t0, 1192(s0)
	ld t0, 1632(s0)
	sd t0, 1200(s0)
	ld t0, 1640(s0)
	sd t0, 1208(s0)
	ld t0, 1648(s0)
	sd t0, 1216(s0)
	ld t0, 1656(s0)
	sd t0, 1224(s0)
	ld t0, 1664(s0)
	sd t0, 1232(s0)
	ld t0, 1672(s0)
	sd t0, 1240(s0)
	ld t0, 1680(s0)
	sd t0, 1248(s0)
	ld t0, 1688(s0)
	sd t0, 1256(s0)
	ld t0, 1696(s0)
	sd t0, 1264(s0)
	ld t0, 1704(s0)
	sd t0, 1272(s0)
	ld t0, 1712(s0)
	sd t0, 1280(s0)
	call {vg_p521_inv_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1288
	addi a2, zero, 1072
	addi a3, zero, 2047
	addi a3, a3, 105
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1288
	addi a3, zero, 352
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1432
	addi a2, zero, 1360
	addi a3, zero, 280
	call {vg_p521_add_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1648
	addi a2, zero, 784
	addi a3, zero, 2047
	addi a3, a3, 537
	call {vg_p521_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1504
	addi a2, zero, 1648
	addi a3, zero, 352
	call {vg_p521_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1576
	addi a2, zero, 1432
	addi a3, zero, 1504
	call {vg_p521_sub_mod_n}
	addi t3, zero, 0
	ld t4, 1216(s0)
	or t3, t3, t4
	ld t4, 1224(s0)
	or t3, t3, t4
	ld t4, 1232(s0)
	or t3, t3, t4
	ld t4, 1240(s0)
	or t3, t3, t4
	ld t4, 1248(s0)
	or t3, t3, t4
	ld t4, 1256(s0)
	or t3, t3, t4
	ld t4, 1264(s0)
	or t3, t3, t4
	ld t4, 1272(s0)
	or t3, t3, t4
	ld t4, 1280(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	xori a7, a7, -1
	addi t0, s0, 2047
	ld t0, 1185(t0)
	and t0, t0, a7
	addi s0, s0, 2047
	sd t0, 1185(s0)
	addi s0, s0, -2047
	addi t3, zero, 0
	ld t4, 1576(s0)
	or t3, t3, t4
	ld t4, 1584(s0)
	or t3, t3, t4
	ld t4, 1592(s0)
	or t3, t3, t4
	ld t4, 1600(s0)
	or t3, t3, t4
	ld t4, 1608(s0)
	or t3, t3, t4
	ld t4, 1616(s0)
	or t3, t3, t4
	ld t4, 1624(s0)
	or t3, t3, t4
	ld t4, 1632(s0)
	or t3, t3, t4
	ld t4, 1640(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	addi t0, s0, 2047
	ld t0, 1185(t0)
	and t0, t0, a7
	addi s0, s0, 2047
	sd t0, 1185(s0)
	addi s0, s0, -2047
	addi a0, s0, 2047
	ld a0, 1185(a0)
	andi a0, a0, 1
	ld ra, 24(s0)
	ld s2, 16(s0)
	ld s1, 8(s0)
	ld s3, 32(s0)
	ld s0, 0(s0)
	addi sp, sp, 80
	addi t0, zero, 0
	addi sp, sp, -80
	addi t1, sp, 0
	sd t0, 0(t1)
	sd t0, 8(t1)
	sd t0, 16(t1)
	sd t0, 24(t1)
	sd t0, 32(t1)
	sd t0, 40(t1)
	sd t0, 48(t1)
	sd t0, 56(t1)
	sd t0, 64(t1)
	sd t0, 72(t1)
	addi sp, sp, 80
	slli a0, a0, 32
	srli a0, a0, 32
	addi a1, zero, 0
	addi a2, zero, 0
	addi a3, zero, 0
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	addi a7, zero, 0
	addi t0, zero, 0
	addi t1, zero, 0
	addi t2, zero, 0
	addi t3, zero, 0
	addi t4, zero, 0
	addi t5, zero, 0
	addi t6, zero, 0
	ret
	.option pop

vg_ecdsa_p521_sign:
	.option push
	.option arch, +m, +c
	addi sp, sp, -512
	addi t0, sp, 0
	sd ra, 0(t0)
	sd s0, 8(t0)
	sd s1, 16(t0)
	sd s2, 24(t0)
	sd s3, 32(t0)
	sd s4, 40(t0)
	sd s5, 48(t0)
	sd s6, 56(t0)
	sd s7, 64(t0)
	sd s8, 72(t0)
	sd s9, 80(t0)
	addi s1, t0, 0
	addi s2, a0, 0
	addi s3, a1, 0
	addi s4, a2, 0
	addi s0, a4, 0
	addi s6, a5, 0
	ld s7, 32(a5)
	ld s8, 40(a5)
	addi t0, zero, 0
	sd t0, 232(s1)
	sd t0, 240(s1)
	sd t0, 248(s1)
	sd t0, 256(s1)
	sd t0, 264(s1)
	sd t0, 272(s1)
	sd t0, 280(s1)
	sd t0, 288(s1)
	sd t0, 296(s1)
	addi t1, zero, 66
	sub t2, s7, t1
	srli t3, t2, 63
	addi t4, zero, 0
	sub t3, t4, t3
	and t2, t2, t3
	add a6, t1, t2
	addi a4, s4, 0
	addi a5, s1, 298
	sub a5, a5, a6
20:
	lbu t1, 0(a4)
	sb t1, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 20b
	addi t0, zero, 257
	slli t1, t0, 16
	or t0, t0, t1
	slli t1, t0, 32
	or t0, t0, t1
	addi t1, zero, 0
	sd t1, 96(s1)
	sd t0, 160(s1)
	sd t1, 104(s1)
	sd t0, 168(s1)
	sd t1, 112(s1)
	sd t0, 176(s1)
	sd t1, 120(s1)
	sd t0, 184(s1)
	sd t1, 128(s1)
	sd t0, 192(s1)
	sd t1, 136(s1)
	sd t0, 200(s1)
	sd t1, 144(s1)
	sd t0, 208(s1)
	sd t1, 152(s1)
	sd t0, 216(s1)
	add t0, s1, s7
	addi t1, zero, 0
	sb t1, 160(t0)
	addi a0, s0, 0
	addi a1, s0, 192
	addi a2, s1, 96
	addi a3, s7, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, s8, 0
	addi a2, s1, 160
	addi a3, s7, 1
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	add a1, s8, s7
	addi a1, a1, 1
	addi a2, s3, 0
	addi a3, zero, 66
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	add a1, s8, s7
	addi a1, a1, 67
	addi a2, s1, 232
	addi a3, zero, 66
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, s0, 192
	add a2, s8, s7
	addi a2, a2, 133
	addi a3, s1, 96
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, s0, 192
	addi a2, s1, 96
	addi a3, s7, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, s8, 0
	addi a2, s1, 160
	addi a3, s7, 0
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, s0, 192
	add a2, s8, s7
	addi a2, a2, 0
	addi a3, s1, 160
	ld t1, 16(s6)
	jalr ra, 0(t1)
	add t0, s1, s7
	addi t1, zero, 1
	sb t1, 160(t0)
	addi a0, s0, 0
	addi a1, s0, 192
	addi a2, s1, 96
	addi a3, s7, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, s8, 0
	addi a2, s1, 160
	addi a3, s7, 1
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	add a1, s8, s7
	addi a1, a1, 1
	addi a2, s3, 0
	addi a3, zero, 66
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	add a1, s8, s7
	addi a1, a1, 67
	addi a2, s1, 232
	addi a3, zero, 66
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, s0, 192
	add a2, s8, s7
	addi a2, a2, 133
	addi a3, s1, 96
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, s0, 192
	addi a2, s1, 96
	addi a3, s7, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, s8, 0
	addi a2, s1, 160
	addi a3, s7, 0
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, s0, 192
	add a2, s8, s7
	addi a2, a2, 0
	addi a3, s1, 160
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi s5, zero, 8
21:
	addi s9, zero, 0
22:
	addi a0, s0, 0
	addi a1, s0, 192
	addi a2, s1, 96
	addi a3, s7, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, s8, 0
	addi a2, s1, 160
	addi a3, s7, 0
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, s0, 192
	add a2, s8, s7
	addi a2, a2, 0
	addi a3, s1, 160
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a4, s1, 160
	addi a5, s1, 368
	add a5, a5, s9
	addi a6, s7, 0
23:
	lbu t1, 0(a4)
	sb t1, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 23b
	add s9, s9, s7
	addi t0, zero, 66
	sltu t6, s9, t0
	bnez t6, 22b
	addi a0, s2, 0
	addi a1, s3, 0
	addi a2, s1, 234
	addi a3, s1, 368
	addi a4, s0, 0
	call {vg_ecdsa_p521_sign_k}
	addi s5, s5, -1
	andi t0, a0, 1
	addi t0, t0, -1
	and t6, t0, s5
	bnez t6, 24f
	addi t6, zero, 0
	j 25f
24:
	add t0, s1, s7
	addi t1, zero, 0
	sb t1, 160(t0)
	addi a0, s0, 0
	addi a1, s0, 192
	addi a2, s1, 96
	addi a3, s7, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, s8, 0
	addi a2, s1, 160
	addi a3, s7, 1
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, s0, 192
	add a2, s8, s7
	addi a2, a2, 1
	addi a3, s1, 96
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, s0, 192
	addi a2, s1, 96
	addi a3, s7, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, s8, 0
	addi a2, s1, 160
	addi a3, s7, 0
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, s0, 192
	add a2, s8, s7
	addi a2, a2, 0
	addi a3, s1, 160
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi t6, zero, 1
25:
	bnez t6, 21b
	addi t0, zero, 0
	sd t0, 96(s1)
	sd t0, 104(s1)
	sd t0, 112(s1)
	sd t0, 120(s1)
	sd t0, 128(s1)
	sd t0, 136(s1)
	sd t0, 144(s1)
	sd t0, 152(s1)
	sd t0, 160(s1)
	sd t0, 168(s1)
	sd t0, 176(s1)
	sd t0, 184(s1)
	sd t0, 192(s1)
	sd t0, 200(s1)
	sd t0, 208(s1)
	sd t0, 216(s1)
	sd t0, 224(s1)
	sd t0, 232(s1)
	sd t0, 240(s1)
	sd t0, 248(s1)
	sd t0, 256(s1)
	sd t0, 264(s1)
	sd t0, 272(s1)
	sd t0, 280(s1)
	sd t0, 288(s1)
	sd t0, 296(s1)
	sd t0, 304(s1)
	sd t0, 312(s1)
	sd t0, 320(s1)
	sd t0, 328(s1)
	sd t0, 336(s1)
	sd t0, 344(s1)
	sd t0, 352(s1)
	sd t0, 360(s1)
	sd t0, 368(s1)
	sd t0, 376(s1)
	sd t0, 384(s1)
	sd t0, 392(s1)
	sd t0, 400(s1)
	sd t0, 408(s1)
	sd t0, 416(s1)
	sd t0, 424(s1)
	sd t0, 432(s1)
	sd t0, 440(s1)
	sd t0, 448(s1)
	sd t0, 456(s1)
	sd t0, 464(s1)
	sd t0, 472(s1)
	sd t0, 480(s1)
	sd t0, 488(s1)
	sd t0, 496(s1)
	ld ra, 0(s1)
	ld s0, 8(s1)
	ld s2, 24(s1)
	ld s3, 32(s1)
	ld s4, 40(s1)
	ld s5, 48(s1)
	ld s6, 56(s1)
	ld s7, 64(s1)
	ld s8, 72(s1)
	ld s9, 80(s1)
	ld s1, 16(s1)
	addi sp, sp, 512
	addi t0, zero, 0
	addi sp, sp, -1024
	addi t1, sp, 0
	sd t0, 0(t1)
	sd t0, 8(t1)
	sd t0, 16(t1)
	sd t0, 24(t1)
	sd t0, 32(t1)
	sd t0, 40(t1)
	sd t0, 48(t1)
	sd t0, 56(t1)
	sd t0, 64(t1)
	sd t0, 72(t1)
	sd t0, 80(t1)
	sd t0, 88(t1)
	sd t0, 96(t1)
	sd t0, 104(t1)
	sd t0, 112(t1)
	sd t0, 120(t1)
	sd t0, 128(t1)
	sd t0, 136(t1)
	sd t0, 144(t1)
	sd t0, 152(t1)
	sd t0, 160(t1)
	sd t0, 168(t1)
	sd t0, 176(t1)
	sd t0, 184(t1)
	sd t0, 192(t1)
	sd t0, 200(t1)
	sd t0, 208(t1)
	sd t0, 216(t1)
	sd t0, 224(t1)
	sd t0, 232(t1)
	sd t0, 240(t1)
	sd t0, 248(t1)
	sd t0, 256(t1)
	sd t0, 264(t1)
	sd t0, 272(t1)
	sd t0, 280(t1)
	sd t0, 288(t1)
	sd t0, 296(t1)
	sd t0, 304(t1)
	sd t0, 312(t1)
	sd t0, 320(t1)
	sd t0, 328(t1)
	sd t0, 336(t1)
	sd t0, 344(t1)
	sd t0, 352(t1)
	sd t0, 360(t1)
	sd t0, 368(t1)
	sd t0, 376(t1)
	sd t0, 384(t1)
	sd t0, 392(t1)
	sd t0, 400(t1)
	sd t0, 408(t1)
	sd t0, 416(t1)
	sd t0, 424(t1)
	sd t0, 432(t1)
	sd t0, 440(t1)
	sd t0, 448(t1)
	sd t0, 456(t1)
	sd t0, 464(t1)
	sd t0, 472(t1)
	sd t0, 480(t1)
	sd t0, 488(t1)
	sd t0, 496(t1)
	sd t0, 504(t1)
	sd t0, 512(t1)
	sd t0, 520(t1)
	sd t0, 528(t1)
	sd t0, 536(t1)
	sd t0, 544(t1)
	sd t0, 552(t1)
	sd t0, 560(t1)
	sd t0, 568(t1)
	sd t0, 576(t1)
	sd t0, 584(t1)
	sd t0, 592(t1)
	sd t0, 600(t1)
	sd t0, 608(t1)
	sd t0, 616(t1)
	sd t0, 624(t1)
	sd t0, 632(t1)
	sd t0, 640(t1)
	sd t0, 648(t1)
	sd t0, 656(t1)
	sd t0, 664(t1)
	sd t0, 672(t1)
	sd t0, 680(t1)
	sd t0, 688(t1)
	sd t0, 696(t1)
	sd t0, 704(t1)
	sd t0, 712(t1)
	sd t0, 720(t1)
	sd t0, 728(t1)
	sd t0, 736(t1)
	sd t0, 744(t1)
	sd t0, 752(t1)
	sd t0, 760(t1)
	sd t0, 768(t1)
	sd t0, 776(t1)
	sd t0, 784(t1)
	sd t0, 792(t1)
	sd t0, 800(t1)
	sd t0, 808(t1)
	sd t0, 816(t1)
	sd t0, 824(t1)
	sd t0, 832(t1)
	sd t0, 840(t1)
	sd t0, 848(t1)
	sd t0, 856(t1)
	sd t0, 864(t1)
	sd t0, 872(t1)
	sd t0, 880(t1)
	sd t0, 888(t1)
	sd t0, 896(t1)
	sd t0, 904(t1)
	sd t0, 912(t1)
	sd t0, 920(t1)
	sd t0, 928(t1)
	sd t0, 936(t1)
	sd t0, 944(t1)
	sd t0, 952(t1)
	sd t0, 960(t1)
	sd t0, 968(t1)
	sd t0, 976(t1)
	sd t0, 984(t1)
	sd t0, 992(t1)
	sd t0, 1000(t1)
	sd t0, 1008(t1)
	sd t0, 1016(t1)
	addi sp, sp, 1024
	slli a0, a0, 32
	srli a0, a0, 32
	addi a1, zero, 0
	addi a2, zero, 0
	addi a3, zero, 0
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	addi a7, zero, 0
	addi t0, zero, 0
	addi t1, zero, 0
	addi t2, zero, 0
	addi t3, zero, 0
	addi t4, zero, 0
	addi t5, zero, 0
	addi t6, zero, 0
	ret
	.option pop
