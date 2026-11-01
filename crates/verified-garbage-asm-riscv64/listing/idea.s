// The functions of `src/idea.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_idea_expand_key:
	.option push
	.option arch, +m, +c
	lbu a2, 0(a0)
	slli a2, a2, 8
	lbu t0, 1(a0)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 2(a0)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 3(a0)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 4(a0)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 5(a0)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 6(a0)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 7(a0)
	or a2, a2, t0
	lbu a3, 8(a0)
	slli a3, a3, 8
	lbu t0, 9(a0)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 10(a0)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 11(a0)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 12(a0)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 13(a0)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 14(a0)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 15(a0)
	or a3, a3, t0
	srli t0, a2, 48
	sb t0, 0(a1)
	srli t0, t0, 8
	sb t0, 1(a1)
	srli t0, a2, 32
	sb t0, 2(a1)
	srli t0, t0, 8
	sb t0, 3(a1)
	srli t0, a2, 16
	sb t0, 4(a1)
	srli t0, t0, 8
	sb t0, 5(a1)
	srli t0, a2, 0
	sb t0, 6(a1)
	srli t0, t0, 8
	sb t0, 7(a1)
	srli t0, a3, 48
	sb t0, 8(a1)
	srli t0, t0, 8
	sb t0, 9(a1)
	srli t0, a3, 32
	sb t0, 10(a1)
	srli t0, t0, 8
	sb t0, 11(a1)
	srli t0, a3, 16
	sb t0, 12(a1)
	srli t0, t0, 8
	sb t0, 13(a1)
	srli t0, a3, 0
	sb t0, 14(a1)
	srli t0, t0, 8
	sb t0, 15(a1)
	srli t0, a2, 39
	srli t1, a3, 39
	slli a2, a2, 25
	slli a3, a3, 25
	or a2, a2, t1
	or a3, a3, t0
	srli t0, a2, 48
	sb t0, 16(a1)
	srli t0, t0, 8
	sb t0, 17(a1)
	srli t0, a2, 32
	sb t0, 18(a1)
	srli t0, t0, 8
	sb t0, 19(a1)
	srli t0, a2, 16
	sb t0, 20(a1)
	srli t0, t0, 8
	sb t0, 21(a1)
	srli t0, a2, 0
	sb t0, 22(a1)
	srli t0, t0, 8
	sb t0, 23(a1)
	srli t0, a3, 48
	sb t0, 24(a1)
	srli t0, t0, 8
	sb t0, 25(a1)
	srli t0, a3, 32
	sb t0, 26(a1)
	srli t0, t0, 8
	sb t0, 27(a1)
	srli t0, a3, 16
	sb t0, 28(a1)
	srli t0, t0, 8
	sb t0, 29(a1)
	srli t0, a3, 0
	sb t0, 30(a1)
	srli t0, t0, 8
	sb t0, 31(a1)
	srli t0, a2, 39
	srli t1, a3, 39
	slli a2, a2, 25
	slli a3, a3, 25
	or a2, a2, t1
	or a3, a3, t0
	srli t0, a2, 48
	sb t0, 32(a1)
	srli t0, t0, 8
	sb t0, 33(a1)
	srli t0, a2, 32
	sb t0, 34(a1)
	srli t0, t0, 8
	sb t0, 35(a1)
	srli t0, a2, 16
	sb t0, 36(a1)
	srli t0, t0, 8
	sb t0, 37(a1)
	srli t0, a2, 0
	sb t0, 38(a1)
	srli t0, t0, 8
	sb t0, 39(a1)
	srli t0, a3, 48
	sb t0, 40(a1)
	srli t0, t0, 8
	sb t0, 41(a1)
	srli t0, a3, 32
	sb t0, 42(a1)
	srli t0, t0, 8
	sb t0, 43(a1)
	srli t0, a3, 16
	sb t0, 44(a1)
	srli t0, t0, 8
	sb t0, 45(a1)
	srli t0, a3, 0
	sb t0, 46(a1)
	srli t0, t0, 8
	sb t0, 47(a1)
	srli t0, a2, 39
	srli t1, a3, 39
	slli a2, a2, 25
	slli a3, a3, 25
	or a2, a2, t1
	or a3, a3, t0
	srli t0, a2, 48
	sb t0, 48(a1)
	srli t0, t0, 8
	sb t0, 49(a1)
	srli t0, a2, 32
	sb t0, 50(a1)
	srli t0, t0, 8
	sb t0, 51(a1)
	srli t0, a2, 16
	sb t0, 52(a1)
	srli t0, t0, 8
	sb t0, 53(a1)
	srli t0, a2, 0
	sb t0, 54(a1)
	srli t0, t0, 8
	sb t0, 55(a1)
	srli t0, a3, 48
	sb t0, 56(a1)
	srli t0, t0, 8
	sb t0, 57(a1)
	srli t0, a3, 32
	sb t0, 58(a1)
	srli t0, t0, 8
	sb t0, 59(a1)
	srli t0, a3, 16
	sb t0, 60(a1)
	srli t0, t0, 8
	sb t0, 61(a1)
	srli t0, a3, 0
	sb t0, 62(a1)
	srli t0, t0, 8
	sb t0, 63(a1)
	srli t0, a2, 39
	srli t1, a3, 39
	slli a2, a2, 25
	slli a3, a3, 25
	or a2, a2, t1
	or a3, a3, t0
	srli t0, a2, 48
	sb t0, 64(a1)
	srli t0, t0, 8
	sb t0, 65(a1)
	srli t0, a2, 32
	sb t0, 66(a1)
	srli t0, t0, 8
	sb t0, 67(a1)
	srli t0, a2, 16
	sb t0, 68(a1)
	srli t0, t0, 8
	sb t0, 69(a1)
	srli t0, a2, 0
	sb t0, 70(a1)
	srli t0, t0, 8
	sb t0, 71(a1)
	srli t0, a3, 48
	sb t0, 72(a1)
	srli t0, t0, 8
	sb t0, 73(a1)
	srli t0, a3, 32
	sb t0, 74(a1)
	srli t0, t0, 8
	sb t0, 75(a1)
	srli t0, a3, 16
	sb t0, 76(a1)
	srli t0, t0, 8
	sb t0, 77(a1)
	srli t0, a3, 0
	sb t0, 78(a1)
	srli t0, t0, 8
	sb t0, 79(a1)
	srli t0, a2, 39
	srli t1, a3, 39
	slli a2, a2, 25
	slli a3, a3, 25
	or a2, a2, t1
	or a3, a3, t0
	srli t0, a2, 48
	sb t0, 80(a1)
	srli t0, t0, 8
	sb t0, 81(a1)
	srli t0, a2, 32
	sb t0, 82(a1)
	srli t0, t0, 8
	sb t0, 83(a1)
	srli t0, a2, 16
	sb t0, 84(a1)
	srli t0, t0, 8
	sb t0, 85(a1)
	srli t0, a2, 0
	sb t0, 86(a1)
	srli t0, t0, 8
	sb t0, 87(a1)
	srli t0, a3, 48
	sb t0, 88(a1)
	srli t0, t0, 8
	sb t0, 89(a1)
	srli t0, a3, 32
	sb t0, 90(a1)
	srli t0, t0, 8
	sb t0, 91(a1)
	srli t0, a3, 16
	sb t0, 92(a1)
	srli t0, t0, 8
	sb t0, 93(a1)
	srli t0, a3, 0
	sb t0, 94(a1)
	srli t0, t0, 8
	sb t0, 95(a1)
	srli t0, a2, 39
	srli t1, a3, 39
	slli a2, a2, 25
	slli a3, a3, 25
	or a2, a2, t1
	or a3, a3, t0
	srli t0, a2, 48
	sb t0, 96(a1)
	srli t0, t0, 8
	sb t0, 97(a1)
	srli t0, a2, 32
	sb t0, 98(a1)
	srli t0, t0, 8
	sb t0, 99(a1)
	srli t0, a2, 16
	sb t0, 100(a1)
	srli t0, t0, 8
	sb t0, 101(a1)
	srli t0, a2, 0
	sb t0, 102(a1)
	srli t0, t0, 8
	sb t0, 103(a1)
	ret
	.option pop

vg_idea_invert_key:
	.option push
	.option arch, +m, +c
	lui t2, 16
	addi t2, t2, -1
	lbu a3, 96(a0)
	lbu t3, 97(a0)
	slli t3, t3, 8
	or a3, a3, t3
	addi a4, a3, 0
	addi a2, zero, 15
20:
	addi t0, a4, 0
	addi t1, a4, 0
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi t0, t1, 0
	addi t1, a3, 0
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi a4, t1, 0
	addi a2, a2, -1
	bnez a2, 20b
	addi t1, a4, 0
	sb t1, 0(a1)
	srli t1, t1, 8
	sb t1, 1(a1)
	lbu a3, 98(a0)
	lbu t3, 99(a0)
	slli t3, t3, 8
	or a3, a3, t3
	addi t1, zero, 0
	sub t1, t1, a3
	and t1, t1, t2
	sb t1, 2(a1)
	srli t1, t1, 8
	sb t1, 3(a1)
	lbu a3, 100(a0)
	lbu t3, 101(a0)
	slli t3, t3, 8
	or a3, a3, t3
	addi t1, zero, 0
	sub t1, t1, a3
	and t1, t1, t2
	sb t1, 4(a1)
	srli t1, t1, 8
	sb t1, 5(a1)
	lbu a3, 102(a0)
	lbu t3, 103(a0)
	slli t3, t3, 8
	or a3, a3, t3
	addi a4, a3, 0
	addi a2, zero, 15
21:
	addi t0, a4, 0
	addi t1, a4, 0
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi t0, t1, 0
	addi t1, a3, 0
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi a4, t1, 0
	addi a2, a2, -1
	bnez a2, 21b
	addi t1, a4, 0
	sb t1, 6(a1)
	srli t1, t1, 8
	sb t1, 7(a1)
	lbu t1, 92(a0)
	lbu t3, 93(a0)
	slli t3, t3, 8
	or t1, t1, t3
	sb t1, 8(a1)
	srli t1, t1, 8
	sb t1, 9(a1)
	lbu t1, 94(a0)
	lbu t3, 95(a0)
	slli t3, t3, 8
	or t1, t1, t3
	sb t1, 10(a1)
	srli t1, t1, 8
	sb t1, 11(a1)
	lbu a3, 84(a0)
	lbu t3, 85(a0)
	slli t3, t3, 8
	or a3, a3, t3
	addi a4, a3, 0
	addi a2, zero, 15
22:
	addi t0, a4, 0
	addi t1, a4, 0
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi t0, t1, 0
	addi t1, a3, 0
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi a4, t1, 0
	addi a2, a2, -1
	bnez a2, 22b
	addi t1, a4, 0
	sb t1, 12(a1)
	srli t1, t1, 8
	sb t1, 13(a1)
	lbu a3, 88(a0)
	lbu t3, 89(a0)
	slli t3, t3, 8
	or a3, a3, t3
	addi t1, zero, 0
	sub t1, t1, a3
	and t1, t1, t2
	sb t1, 14(a1)
	srli t1, t1, 8
	sb t1, 15(a1)
	lbu a3, 86(a0)
	lbu t3, 87(a0)
	slli t3, t3, 8
	or a3, a3, t3
	addi t1, zero, 0
	sub t1, t1, a3
	and t1, t1, t2
	sb t1, 16(a1)
	srli t1, t1, 8
	sb t1, 17(a1)
	lbu a3, 90(a0)
	lbu t3, 91(a0)
	slli t3, t3, 8
	or a3, a3, t3
	addi a4, a3, 0
	addi a2, zero, 15
23:
	addi t0, a4, 0
	addi t1, a4, 0
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi t0, t1, 0
	addi t1, a3, 0
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi a4, t1, 0
	addi a2, a2, -1
	bnez a2, 23b
	addi t1, a4, 0
	sb t1, 18(a1)
	srli t1, t1, 8
	sb t1, 19(a1)
	lbu t1, 80(a0)
	lbu t3, 81(a0)
	slli t3, t3, 8
	or t1, t1, t3
	sb t1, 20(a1)
	srli t1, t1, 8
	sb t1, 21(a1)
	lbu t1, 82(a0)
	lbu t3, 83(a0)
	slli t3, t3, 8
	or t1, t1, t3
	sb t1, 22(a1)
	srli t1, t1, 8
	sb t1, 23(a1)
	lbu a3, 72(a0)
	lbu t3, 73(a0)
	slli t3, t3, 8
	or a3, a3, t3
	addi a4, a3, 0
	addi a2, zero, 15
24:
	addi t0, a4, 0
	addi t1, a4, 0
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi t0, t1, 0
	addi t1, a3, 0
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi a4, t1, 0
	addi a2, a2, -1
	bnez a2, 24b
	addi t1, a4, 0
	sb t1, 24(a1)
	srli t1, t1, 8
	sb t1, 25(a1)
	lbu a3, 76(a0)
	lbu t3, 77(a0)
	slli t3, t3, 8
	or a3, a3, t3
	addi t1, zero, 0
	sub t1, t1, a3
	and t1, t1, t2
	sb t1, 26(a1)
	srli t1, t1, 8
	sb t1, 27(a1)
	lbu a3, 74(a0)
	lbu t3, 75(a0)
	slli t3, t3, 8
	or a3, a3, t3
	addi t1, zero, 0
	sub t1, t1, a3
	and t1, t1, t2
	sb t1, 28(a1)
	srli t1, t1, 8
	sb t1, 29(a1)
	lbu a3, 78(a0)
	lbu t3, 79(a0)
	slli t3, t3, 8
	or a3, a3, t3
	addi a4, a3, 0
	addi a2, zero, 15
25:
	addi t0, a4, 0
	addi t1, a4, 0
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi t0, t1, 0
	addi t1, a3, 0
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi a4, t1, 0
	addi a2, a2, -1
	bnez a2, 25b
	addi t1, a4, 0
	sb t1, 30(a1)
	srli t1, t1, 8
	sb t1, 31(a1)
	lbu t1, 68(a0)
	lbu t3, 69(a0)
	slli t3, t3, 8
	or t1, t1, t3
	sb t1, 32(a1)
	srli t1, t1, 8
	sb t1, 33(a1)
	lbu t1, 70(a0)
	lbu t3, 71(a0)
	slli t3, t3, 8
	or t1, t1, t3
	sb t1, 34(a1)
	srli t1, t1, 8
	sb t1, 35(a1)
	lbu a3, 60(a0)
	lbu t3, 61(a0)
	slli t3, t3, 8
	or a3, a3, t3
	addi a4, a3, 0
	addi a2, zero, 15
26:
	addi t0, a4, 0
	addi t1, a4, 0
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi t0, t1, 0
	addi t1, a3, 0
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi a4, t1, 0
	addi a2, a2, -1
	bnez a2, 26b
	addi t1, a4, 0
	sb t1, 36(a1)
	srli t1, t1, 8
	sb t1, 37(a1)
	lbu a3, 64(a0)
	lbu t3, 65(a0)
	slli t3, t3, 8
	or a3, a3, t3
	addi t1, zero, 0
	sub t1, t1, a3
	and t1, t1, t2
	sb t1, 38(a1)
	srli t1, t1, 8
	sb t1, 39(a1)
	lbu a3, 62(a0)
	lbu t3, 63(a0)
	slli t3, t3, 8
	or a3, a3, t3
	addi t1, zero, 0
	sub t1, t1, a3
	and t1, t1, t2
	sb t1, 40(a1)
	srli t1, t1, 8
	sb t1, 41(a1)
	lbu a3, 66(a0)
	lbu t3, 67(a0)
	slli t3, t3, 8
	or a3, a3, t3
	addi a4, a3, 0
	addi a2, zero, 15
27:
	addi t0, a4, 0
	addi t1, a4, 0
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi t0, t1, 0
	addi t1, a3, 0
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi a4, t1, 0
	addi a2, a2, -1
	bnez a2, 27b
	addi t1, a4, 0
	sb t1, 42(a1)
	srli t1, t1, 8
	sb t1, 43(a1)
	lbu t1, 56(a0)
	lbu t3, 57(a0)
	slli t3, t3, 8
	or t1, t1, t3
	sb t1, 44(a1)
	srli t1, t1, 8
	sb t1, 45(a1)
	lbu t1, 58(a0)
	lbu t3, 59(a0)
	slli t3, t3, 8
	or t1, t1, t3
	sb t1, 46(a1)
	srli t1, t1, 8
	sb t1, 47(a1)
	lbu a3, 48(a0)
	lbu t3, 49(a0)
	slli t3, t3, 8
	or a3, a3, t3
	addi a4, a3, 0
	addi a2, zero, 15
28:
	addi t0, a4, 0
	addi t1, a4, 0
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi t0, t1, 0
	addi t1, a3, 0
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi a4, t1, 0
	addi a2, a2, -1
	bnez a2, 28b
	addi t1, a4, 0
	sb t1, 48(a1)
	srli t1, t1, 8
	sb t1, 49(a1)
	lbu a3, 52(a0)
	lbu t3, 53(a0)
	slli t3, t3, 8
	or a3, a3, t3
	addi t1, zero, 0
	sub t1, t1, a3
	and t1, t1, t2
	sb t1, 50(a1)
	srli t1, t1, 8
	sb t1, 51(a1)
	lbu a3, 50(a0)
	lbu t3, 51(a0)
	slli t3, t3, 8
	or a3, a3, t3
	addi t1, zero, 0
	sub t1, t1, a3
	and t1, t1, t2
	sb t1, 52(a1)
	srli t1, t1, 8
	sb t1, 53(a1)
	lbu a3, 54(a0)
	lbu t3, 55(a0)
	slli t3, t3, 8
	or a3, a3, t3
	addi a4, a3, 0
	addi a2, zero, 15
29:
	addi t0, a4, 0
	addi t1, a4, 0
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi t0, t1, 0
	addi t1, a3, 0
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi a4, t1, 0
	addi a2, a2, -1
	bnez a2, 29b
	addi t1, a4, 0
	sb t1, 54(a1)
	srli t1, t1, 8
	sb t1, 55(a1)
	lbu t1, 44(a0)
	lbu t3, 45(a0)
	slli t3, t3, 8
	or t1, t1, t3
	sb t1, 56(a1)
	srli t1, t1, 8
	sb t1, 57(a1)
	lbu t1, 46(a0)
	lbu t3, 47(a0)
	slli t3, t3, 8
	or t1, t1, t3
	sb t1, 58(a1)
	srli t1, t1, 8
	sb t1, 59(a1)
	lbu a3, 36(a0)
	lbu t3, 37(a0)
	slli t3, t3, 8
	or a3, a3, t3
	addi a4, a3, 0
	addi a2, zero, 15
210:
	addi t0, a4, 0
	addi t1, a4, 0
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi t0, t1, 0
	addi t1, a3, 0
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi a4, t1, 0
	addi a2, a2, -1
	bnez a2, 210b
	addi t1, a4, 0
	sb t1, 60(a1)
	srli t1, t1, 8
	sb t1, 61(a1)
	lbu a3, 40(a0)
	lbu t3, 41(a0)
	slli t3, t3, 8
	or a3, a3, t3
	addi t1, zero, 0
	sub t1, t1, a3
	and t1, t1, t2
	sb t1, 62(a1)
	srli t1, t1, 8
	sb t1, 63(a1)
	lbu a3, 38(a0)
	lbu t3, 39(a0)
	slli t3, t3, 8
	or a3, a3, t3
	addi t1, zero, 0
	sub t1, t1, a3
	and t1, t1, t2
	sb t1, 64(a1)
	srli t1, t1, 8
	sb t1, 65(a1)
	lbu a3, 42(a0)
	lbu t3, 43(a0)
	slli t3, t3, 8
	or a3, a3, t3
	addi a4, a3, 0
	addi a2, zero, 15
211:
	addi t0, a4, 0
	addi t1, a4, 0
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi t0, t1, 0
	addi t1, a3, 0
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi a4, t1, 0
	addi a2, a2, -1
	bnez a2, 211b
	addi t1, a4, 0
	sb t1, 66(a1)
	srli t1, t1, 8
	sb t1, 67(a1)
	lbu t1, 32(a0)
	lbu t3, 33(a0)
	slli t3, t3, 8
	or t1, t1, t3
	sb t1, 68(a1)
	srli t1, t1, 8
	sb t1, 69(a1)
	lbu t1, 34(a0)
	lbu t3, 35(a0)
	slli t3, t3, 8
	or t1, t1, t3
	sb t1, 70(a1)
	srli t1, t1, 8
	sb t1, 71(a1)
	lbu a3, 24(a0)
	lbu t3, 25(a0)
	slli t3, t3, 8
	or a3, a3, t3
	addi a4, a3, 0
	addi a2, zero, 15
212:
	addi t0, a4, 0
	addi t1, a4, 0
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi t0, t1, 0
	addi t1, a3, 0
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi a4, t1, 0
	addi a2, a2, -1
	bnez a2, 212b
	addi t1, a4, 0
	sb t1, 72(a1)
	srli t1, t1, 8
	sb t1, 73(a1)
	lbu a3, 28(a0)
	lbu t3, 29(a0)
	slli t3, t3, 8
	or a3, a3, t3
	addi t1, zero, 0
	sub t1, t1, a3
	and t1, t1, t2
	sb t1, 74(a1)
	srli t1, t1, 8
	sb t1, 75(a1)
	lbu a3, 26(a0)
	lbu t3, 27(a0)
	slli t3, t3, 8
	or a3, a3, t3
	addi t1, zero, 0
	sub t1, t1, a3
	and t1, t1, t2
	sb t1, 76(a1)
	srli t1, t1, 8
	sb t1, 77(a1)
	lbu a3, 30(a0)
	lbu t3, 31(a0)
	slli t3, t3, 8
	or a3, a3, t3
	addi a4, a3, 0
	addi a2, zero, 15
213:
	addi t0, a4, 0
	addi t1, a4, 0
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi t0, t1, 0
	addi t1, a3, 0
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi a4, t1, 0
	addi a2, a2, -1
	bnez a2, 213b
	addi t1, a4, 0
	sb t1, 78(a1)
	srli t1, t1, 8
	sb t1, 79(a1)
	lbu t1, 20(a0)
	lbu t3, 21(a0)
	slli t3, t3, 8
	or t1, t1, t3
	sb t1, 80(a1)
	srli t1, t1, 8
	sb t1, 81(a1)
	lbu t1, 22(a0)
	lbu t3, 23(a0)
	slli t3, t3, 8
	or t1, t1, t3
	sb t1, 82(a1)
	srli t1, t1, 8
	sb t1, 83(a1)
	lbu a3, 12(a0)
	lbu t3, 13(a0)
	slli t3, t3, 8
	or a3, a3, t3
	addi a4, a3, 0
	addi a2, zero, 15
214:
	addi t0, a4, 0
	addi t1, a4, 0
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi t0, t1, 0
	addi t1, a3, 0
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi a4, t1, 0
	addi a2, a2, -1
	bnez a2, 214b
	addi t1, a4, 0
	sb t1, 84(a1)
	srli t1, t1, 8
	sb t1, 85(a1)
	lbu a3, 16(a0)
	lbu t3, 17(a0)
	slli t3, t3, 8
	or a3, a3, t3
	addi t1, zero, 0
	sub t1, t1, a3
	and t1, t1, t2
	sb t1, 86(a1)
	srli t1, t1, 8
	sb t1, 87(a1)
	lbu a3, 14(a0)
	lbu t3, 15(a0)
	slli t3, t3, 8
	or a3, a3, t3
	addi t1, zero, 0
	sub t1, t1, a3
	and t1, t1, t2
	sb t1, 88(a1)
	srli t1, t1, 8
	sb t1, 89(a1)
	lbu a3, 18(a0)
	lbu t3, 19(a0)
	slli t3, t3, 8
	or a3, a3, t3
	addi a4, a3, 0
	addi a2, zero, 15
215:
	addi t0, a4, 0
	addi t1, a4, 0
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi t0, t1, 0
	addi t1, a3, 0
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi a4, t1, 0
	addi a2, a2, -1
	bnez a2, 215b
	addi t1, a4, 0
	sb t1, 90(a1)
	srli t1, t1, 8
	sb t1, 91(a1)
	lbu t1, 8(a0)
	lbu t3, 9(a0)
	slli t3, t3, 8
	or t1, t1, t3
	sb t1, 92(a1)
	srli t1, t1, 8
	sb t1, 93(a1)
	lbu t1, 10(a0)
	lbu t3, 11(a0)
	slli t3, t3, 8
	or t1, t1, t3
	sb t1, 94(a1)
	srli t1, t1, 8
	sb t1, 95(a1)
	lbu a3, 0(a0)
	lbu t3, 1(a0)
	slli t3, t3, 8
	or a3, a3, t3
	addi a4, a3, 0
	addi a2, zero, 15
216:
	addi t0, a4, 0
	addi t1, a4, 0
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi t0, t1, 0
	addi t1, a3, 0
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi a4, t1, 0
	addi a2, a2, -1
	bnez a2, 216b
	addi t1, a4, 0
	sb t1, 96(a1)
	srli t1, t1, 8
	sb t1, 97(a1)
	lbu a3, 2(a0)
	lbu t3, 3(a0)
	slli t3, t3, 8
	or a3, a3, t3
	addi t1, zero, 0
	sub t1, t1, a3
	and t1, t1, t2
	sb t1, 98(a1)
	srli t1, t1, 8
	sb t1, 99(a1)
	lbu a3, 4(a0)
	lbu t3, 5(a0)
	slli t3, t3, 8
	or a3, a3, t3
	addi t1, zero, 0
	sub t1, t1, a3
	and t1, t1, t2
	sb t1, 100(a1)
	srli t1, t1, 8
	sb t1, 101(a1)
	lbu a3, 6(a0)
	lbu t3, 7(a0)
	slli t3, t3, 8
	or a3, a3, t3
	addi a4, a3, 0
	addi a2, zero, 15
217:
	addi t0, a4, 0
	addi t1, a4, 0
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi t0, t1, 0
	addi t1, a3, 0
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi a4, t1, 0
	addi a2, a2, -1
	bnez a2, 217b
	addi t1, a4, 0
	sb t1, 102(a1)
	srli t1, t1, 8
	sb t1, 103(a1)
	ret
	.option pop

vg_idea_ecb:
	.option push
	.option arch, +m, +c
	lui t2, 16
	addi t2, t2, -1
	beqz a2, 20f
22:
	lbu a3, 0(a1)
	slli a3, a3, 8
	lbu t3, 1(a1)
	or a3, a3, t3
	lbu a4, 2(a1)
	slli a4, a4, 8
	lbu t3, 3(a1)
	or a4, a4, t3
	lbu a5, 4(a1)
	slli a5, a5, 8
	lbu t3, 5(a1)
	or a5, a5, t3
	lbu a6, 6(a1)
	slli a6, a6, 8
	lbu t3, 7(a1)
	or a6, a6, t3
	addi t0, a3, 0
	lbu t1, 0(a0)
	lbu t3, 1(a0)
	slli t3, t3, 8
	or t1, t1, t3
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi a3, t1, 0
	addi t0, a6, 0
	lbu t1, 6(a0)
	lbu t3, 7(a0)
	slli t3, t3, 8
	or t1, t1, t3
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi a6, t1, 0
	lbu t1, 2(a0)
	lbu t3, 3(a0)
	slli t3, t3, 8
	or t1, t1, t3
	add a4, a4, t1
	and a4, a4, t2
	lbu t1, 4(a0)
	lbu t3, 5(a0)
	slli t3, t3, 8
	or t1, t1, t3
	add a5, a5, t1
	and a5, a5, t2
	xor t0, a3, a5
	lbu t1, 8(a0)
	lbu t3, 9(a0)
	slli t3, t3, 8
	or t1, t1, t3
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi a7, t1, 0
	xor t0, a4, a6
	add t0, t0, a7
	lbu t1, 10(a0)
	lbu t3, 11(a0)
	slli t3, t3, 8
	or t1, t1, t3
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	add a7, a7, t1
	and a7, a7, t2
	xor a3, a3, t1
	xor a5, a5, t1
	xor a4, a4, a7
	xor a6, a6, a7
	addi t0, a4, 0
	addi a4, a5, 0
	addi a5, t0, 0
	addi t0, a3, 0
	lbu t1, 12(a0)
	lbu t3, 13(a0)
	slli t3, t3, 8
	or t1, t1, t3
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi a3, t1, 0
	addi t0, a6, 0
	lbu t1, 18(a0)
	lbu t3, 19(a0)
	slli t3, t3, 8
	or t1, t1, t3
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi a6, t1, 0
	lbu t1, 14(a0)
	lbu t3, 15(a0)
	slli t3, t3, 8
	or t1, t1, t3
	add a4, a4, t1
	and a4, a4, t2
	lbu t1, 16(a0)
	lbu t3, 17(a0)
	slli t3, t3, 8
	or t1, t1, t3
	add a5, a5, t1
	and a5, a5, t2
	xor t0, a3, a5
	lbu t1, 20(a0)
	lbu t3, 21(a0)
	slli t3, t3, 8
	or t1, t1, t3
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi a7, t1, 0
	xor t0, a4, a6
	add t0, t0, a7
	lbu t1, 22(a0)
	lbu t3, 23(a0)
	slli t3, t3, 8
	or t1, t1, t3
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	add a7, a7, t1
	and a7, a7, t2
	xor a3, a3, t1
	xor a5, a5, t1
	xor a4, a4, a7
	xor a6, a6, a7
	addi t0, a4, 0
	addi a4, a5, 0
	addi a5, t0, 0
	addi t0, a3, 0
	lbu t1, 24(a0)
	lbu t3, 25(a0)
	slli t3, t3, 8
	or t1, t1, t3
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi a3, t1, 0
	addi t0, a6, 0
	lbu t1, 30(a0)
	lbu t3, 31(a0)
	slli t3, t3, 8
	or t1, t1, t3
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi a6, t1, 0
	lbu t1, 26(a0)
	lbu t3, 27(a0)
	slli t3, t3, 8
	or t1, t1, t3
	add a4, a4, t1
	and a4, a4, t2
	lbu t1, 28(a0)
	lbu t3, 29(a0)
	slli t3, t3, 8
	or t1, t1, t3
	add a5, a5, t1
	and a5, a5, t2
	xor t0, a3, a5
	lbu t1, 32(a0)
	lbu t3, 33(a0)
	slli t3, t3, 8
	or t1, t1, t3
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi a7, t1, 0
	xor t0, a4, a6
	add t0, t0, a7
	lbu t1, 34(a0)
	lbu t3, 35(a0)
	slli t3, t3, 8
	or t1, t1, t3
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	add a7, a7, t1
	and a7, a7, t2
	xor a3, a3, t1
	xor a5, a5, t1
	xor a4, a4, a7
	xor a6, a6, a7
	addi t0, a4, 0
	addi a4, a5, 0
	addi a5, t0, 0
	addi t0, a3, 0
	lbu t1, 36(a0)
	lbu t3, 37(a0)
	slli t3, t3, 8
	or t1, t1, t3
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi a3, t1, 0
	addi t0, a6, 0
	lbu t1, 42(a0)
	lbu t3, 43(a0)
	slli t3, t3, 8
	or t1, t1, t3
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi a6, t1, 0
	lbu t1, 38(a0)
	lbu t3, 39(a0)
	slli t3, t3, 8
	or t1, t1, t3
	add a4, a4, t1
	and a4, a4, t2
	lbu t1, 40(a0)
	lbu t3, 41(a0)
	slli t3, t3, 8
	or t1, t1, t3
	add a5, a5, t1
	and a5, a5, t2
	xor t0, a3, a5
	lbu t1, 44(a0)
	lbu t3, 45(a0)
	slli t3, t3, 8
	or t1, t1, t3
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi a7, t1, 0
	xor t0, a4, a6
	add t0, t0, a7
	lbu t1, 46(a0)
	lbu t3, 47(a0)
	slli t3, t3, 8
	or t1, t1, t3
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	add a7, a7, t1
	and a7, a7, t2
	xor a3, a3, t1
	xor a5, a5, t1
	xor a4, a4, a7
	xor a6, a6, a7
	addi t0, a4, 0
	addi a4, a5, 0
	addi a5, t0, 0
	addi t0, a3, 0
	lbu t1, 48(a0)
	lbu t3, 49(a0)
	slli t3, t3, 8
	or t1, t1, t3
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi a3, t1, 0
	addi t0, a6, 0
	lbu t1, 54(a0)
	lbu t3, 55(a0)
	slli t3, t3, 8
	or t1, t1, t3
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi a6, t1, 0
	lbu t1, 50(a0)
	lbu t3, 51(a0)
	slli t3, t3, 8
	or t1, t1, t3
	add a4, a4, t1
	and a4, a4, t2
	lbu t1, 52(a0)
	lbu t3, 53(a0)
	slli t3, t3, 8
	or t1, t1, t3
	add a5, a5, t1
	and a5, a5, t2
	xor t0, a3, a5
	lbu t1, 56(a0)
	lbu t3, 57(a0)
	slli t3, t3, 8
	or t1, t1, t3
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi a7, t1, 0
	xor t0, a4, a6
	add t0, t0, a7
	lbu t1, 58(a0)
	lbu t3, 59(a0)
	slli t3, t3, 8
	or t1, t1, t3
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	add a7, a7, t1
	and a7, a7, t2
	xor a3, a3, t1
	xor a5, a5, t1
	xor a4, a4, a7
	xor a6, a6, a7
	addi t0, a4, 0
	addi a4, a5, 0
	addi a5, t0, 0
	addi t0, a3, 0
	lbu t1, 60(a0)
	lbu t3, 61(a0)
	slli t3, t3, 8
	or t1, t1, t3
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi a3, t1, 0
	addi t0, a6, 0
	lbu t1, 66(a0)
	lbu t3, 67(a0)
	slli t3, t3, 8
	or t1, t1, t3
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi a6, t1, 0
	lbu t1, 62(a0)
	lbu t3, 63(a0)
	slli t3, t3, 8
	or t1, t1, t3
	add a4, a4, t1
	and a4, a4, t2
	lbu t1, 64(a0)
	lbu t3, 65(a0)
	slli t3, t3, 8
	or t1, t1, t3
	add a5, a5, t1
	and a5, a5, t2
	xor t0, a3, a5
	lbu t1, 68(a0)
	lbu t3, 69(a0)
	slli t3, t3, 8
	or t1, t1, t3
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi a7, t1, 0
	xor t0, a4, a6
	add t0, t0, a7
	lbu t1, 70(a0)
	lbu t3, 71(a0)
	slli t3, t3, 8
	or t1, t1, t3
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	add a7, a7, t1
	and a7, a7, t2
	xor a3, a3, t1
	xor a5, a5, t1
	xor a4, a4, a7
	xor a6, a6, a7
	addi t0, a4, 0
	addi a4, a5, 0
	addi a5, t0, 0
	addi t0, a3, 0
	lbu t1, 72(a0)
	lbu t3, 73(a0)
	slli t3, t3, 8
	or t1, t1, t3
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi a3, t1, 0
	addi t0, a6, 0
	lbu t1, 78(a0)
	lbu t3, 79(a0)
	slli t3, t3, 8
	or t1, t1, t3
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi a6, t1, 0
	lbu t1, 74(a0)
	lbu t3, 75(a0)
	slli t3, t3, 8
	or t1, t1, t3
	add a4, a4, t1
	and a4, a4, t2
	lbu t1, 76(a0)
	lbu t3, 77(a0)
	slli t3, t3, 8
	or t1, t1, t3
	add a5, a5, t1
	and a5, a5, t2
	xor t0, a3, a5
	lbu t1, 80(a0)
	lbu t3, 81(a0)
	slli t3, t3, 8
	or t1, t1, t3
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi a7, t1, 0
	xor t0, a4, a6
	add t0, t0, a7
	lbu t1, 82(a0)
	lbu t3, 83(a0)
	slli t3, t3, 8
	or t1, t1, t3
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	add a7, a7, t1
	and a7, a7, t2
	xor a3, a3, t1
	xor a5, a5, t1
	xor a4, a4, a7
	xor a6, a6, a7
	addi t0, a4, 0
	addi a4, a5, 0
	addi a5, t0, 0
	addi t0, a3, 0
	lbu t1, 84(a0)
	lbu t3, 85(a0)
	slli t3, t3, 8
	or t1, t1, t3
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi a3, t1, 0
	addi t0, a6, 0
	lbu t1, 90(a0)
	lbu t3, 91(a0)
	slli t3, t3, 8
	or t1, t1, t3
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi a6, t1, 0
	lbu t1, 86(a0)
	lbu t3, 87(a0)
	slli t3, t3, 8
	or t1, t1, t3
	add a4, a4, t1
	and a4, a4, t2
	lbu t1, 88(a0)
	lbu t3, 89(a0)
	slli t3, t3, 8
	or t1, t1, t3
	add a5, a5, t1
	and a5, a5, t2
	xor t0, a3, a5
	lbu t1, 92(a0)
	lbu t3, 93(a0)
	slli t3, t3, 8
	or t1, t1, t3
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi a7, t1, 0
	xor t0, a4, a6
	add t0, t0, a7
	lbu t1, 94(a0)
	lbu t3, 95(a0)
	slli t3, t3, 8
	or t1, t1, t3
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	add a7, a7, t1
	and a7, a7, t2
	xor a3, a3, t1
	xor a5, a5, t1
	xor a4, a4, a7
	xor a6, a6, a7
	addi t0, a4, 0
	addi a4, a5, 0
	addi a5, t0, 0
	addi t0, a3, 0
	lbu t1, 96(a0)
	lbu t3, 97(a0)
	slli t3, t3, 8
	or t1, t1, t3
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi a3, t1, 0
	addi t0, a6, 0
	lbu t1, 102(a0)
	lbu t3, 103(a0)
	slli t3, t3, 8
	or t1, t1, t3
	addi t0, t0, -1
	and t0, t0, t2
	addi t0, t0, 1
	addi t1, t1, -1
	and t1, t1, t2
	addi t1, t1, 1
	mul t0, t0, t1
	and t1, t0, t2
	srli t0, t0, 16
	sub t1, t1, t0
	srli t0, t1, 63
	add t1, t1, t0
	slli t0, t0, 16
	add t1, t1, t0
	and t1, t1, t2
	addi a6, t1, 0
	lbu t1, 98(a0)
	lbu t3, 99(a0)
	slli t3, t3, 8
	or t1, t1, t3
	add a5, a5, t1
	and a5, a5, t2
	lbu t1, 100(a0)
	lbu t3, 101(a0)
	slli t3, t3, 8
	or t1, t1, t3
	add a4, a4, t1
	and a4, a4, t2
	sb a3, 1(a1)
	srli t3, a3, 8
	sb t3, 0(a1)
	sb a5, 3(a1)
	srli t3, a5, 8
	sb t3, 2(a1)
	sb a4, 5(a1)
	srli t3, a4, 8
	sb t3, 4(a1)
	sb a6, 7(a1)
	srli t3, a6, 8
	sb t3, 6(a1)
	addi a1, a1, 8
	addi a2, a2, -1
	bnez a2, 22b
	j 21f
20:
21:
	ret
	.option pop
