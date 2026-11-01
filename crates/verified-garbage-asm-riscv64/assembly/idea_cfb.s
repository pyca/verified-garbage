// The functions of `src/idea_cfb.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_idea_cfb64_encrypt:
	.option push
	.option arch, +m, +c
	addi sp, sp, -64
	addi t0, sp, 0
	sd s1, 0(t0)
	sd s2, 8(t0)
	sd s3, 16(t0)
	sd s4, 24(t0)
	addi s4, t0, 0
	addi s1, a1, 0
	addi s2, a1, 0
	addi s3, a3, 0
	lbu t0, 0(s2)
	lbu t2, 1(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 32(s4)
	srli t2, t0, 8
	sb t2, 33(s4)
	srli t2, t0, 16
	sb t2, 34(s4)
	srli t2, t0, 24
	sb t2, 35(s4)
	lbu t0, 4(s2)
	lbu t2, 5(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 36(s4)
	srli t2, t0, 8
	sb t2, 37(s4)
	srli t2, t0, 16
	sb t2, 38(s4)
	srli t2, t0, 24
	sb t2, 39(s4)
	addi s2, a2, 0
	beqz s3, 20f
22:
	lbu t0, 32(s4)
	lbu t2, 33(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 34(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 35(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 48(s4)
	srli t2, t0, 8
	sb t2, 49(s4)
	srli t2, t0, 16
	sb t2, 50(s4)
	srli t2, t0, 24
	sb t2, 51(s4)
	lbu t0, 36(s4)
	lbu t2, 37(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 38(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 39(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 52(s4)
	srli t2, t0, 8
	sb t2, 53(s4)
	srli t2, t0, 16
	sb t2, 54(s4)
	srli t2, t0, 24
	sb t2, 55(s4)
	lui t2, 16
	addi t2, t2, -1
	addi a1, s4, 48
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
	lbu t0, 0(s2)
	lbu t2, 1(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 48(s4)
	lbu t2, 49(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 50(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 51(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 0(s2)
	srli t2, t0, 8
	sb t2, 1(s2)
	srli t2, t0, 16
	sb t2, 2(s2)
	srli t2, t0, 24
	sb t2, 3(s2)
	lbu t0, 4(s2)
	lbu t2, 5(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 52(s4)
	lbu t2, 53(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 54(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 55(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 4(s2)
	srli t2, t0, 8
	sb t2, 5(s2)
	srli t2, t0, 16
	sb t2, 6(s2)
	srli t2, t0, 24
	sb t2, 7(s2)
	lbu t0, 0(s2)
	lbu t2, 1(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 32(s4)
	srli t2, t0, 8
	sb t2, 33(s4)
	srli t2, t0, 16
	sb t2, 34(s4)
	srli t2, t0, 24
	sb t2, 35(s4)
	lbu t0, 4(s2)
	lbu t2, 5(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 36(s4)
	srli t2, t0, 8
	sb t2, 37(s4)
	srli t2, t0, 16
	sb t2, 38(s4)
	srli t2, t0, 24
	sb t2, 39(s4)
	addi s2, s2, 8
	addi s3, s3, -1
	bnez s3, 22b
	j 21f
20:
21:
	addi s2, s1, 0
	lbu t0, 32(s4)
	lbu t2, 33(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 34(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 35(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 0(s2)
	srli t2, t0, 8
	sb t2, 1(s2)
	srli t2, t0, 16
	sb t2, 2(s2)
	srli t2, t0, 24
	sb t2, 3(s2)
	lbu t0, 36(s4)
	lbu t2, 37(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 38(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 39(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 4(s2)
	srli t2, t0, 8
	sb t2, 5(s2)
	srli t2, t0, 16
	sb t2, 6(s2)
	srli t2, t0, 24
	sb t2, 7(s2)
	addi t3, s4, 0
	ld s1, 0(t3)
	ld s2, 8(t3)
	ld s3, 16(t3)
	ld s4, 24(t3)
	addi t0, zero, 0
	addi t1, t3, 0
	addi t2, zero, 8
23:
	sd t0, 0(t1)
	addi t1, t1, 8
	addi t2, t2, -1
	bnez t2, 23b
	addi sp, sp, 64
	ret
	.option pop

vg_idea_cfb64_decrypt:
	.option push
	.option arch, +m, +c
	addi sp, sp, -64
	addi t0, sp, 0
	sd s1, 0(t0)
	sd s2, 8(t0)
	sd s3, 16(t0)
	sd s4, 24(t0)
	addi s4, t0, 0
	addi s1, a1, 0
	addi s2, a1, 0
	addi s3, a3, 0
	lbu t0, 0(s2)
	lbu t2, 1(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 32(s4)
	srli t2, t0, 8
	sb t2, 33(s4)
	srli t2, t0, 16
	sb t2, 34(s4)
	srli t2, t0, 24
	sb t2, 35(s4)
	lbu t0, 4(s2)
	lbu t2, 5(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 36(s4)
	srli t2, t0, 8
	sb t2, 37(s4)
	srli t2, t0, 16
	sb t2, 38(s4)
	srli t2, t0, 24
	sb t2, 39(s4)
	addi s2, a2, 0
	beqz s3, 20f
22:
	lbu t0, 32(s4)
	lbu t2, 33(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 34(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 35(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 48(s4)
	srli t2, t0, 8
	sb t2, 49(s4)
	srli t2, t0, 16
	sb t2, 50(s4)
	srli t2, t0, 24
	sb t2, 51(s4)
	lbu t0, 36(s4)
	lbu t2, 37(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 38(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 39(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 52(s4)
	srli t2, t0, 8
	sb t2, 53(s4)
	srli t2, t0, 16
	sb t2, 54(s4)
	srli t2, t0, 24
	sb t2, 55(s4)
	lui t2, 16
	addi t2, t2, -1
	addi a1, s4, 48
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
	lbu t0, 0(s2)
	lbu t2, 1(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 32(s4)
	srli t2, t0, 8
	sb t2, 33(s4)
	srli t2, t0, 16
	sb t2, 34(s4)
	srli t2, t0, 24
	sb t2, 35(s4)
	lbu t0, 4(s2)
	lbu t2, 5(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 36(s4)
	srli t2, t0, 8
	sb t2, 37(s4)
	srli t2, t0, 16
	sb t2, 38(s4)
	srli t2, t0, 24
	sb t2, 39(s4)
	lbu t0, 0(s2)
	lbu t2, 1(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 48(s4)
	lbu t2, 49(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 50(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 51(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 0(s2)
	srli t2, t0, 8
	sb t2, 1(s2)
	srli t2, t0, 16
	sb t2, 2(s2)
	srli t2, t0, 24
	sb t2, 3(s2)
	lbu t0, 4(s2)
	lbu t2, 5(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 52(s4)
	lbu t2, 53(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 54(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 55(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 4(s2)
	srli t2, t0, 8
	sb t2, 5(s2)
	srli t2, t0, 16
	sb t2, 6(s2)
	srli t2, t0, 24
	sb t2, 7(s2)
	addi s2, s2, 8
	addi s3, s3, -1
	bnez s3, 22b
	j 21f
20:
21:
	addi s2, s1, 0
	lbu t0, 32(s4)
	lbu t2, 33(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 34(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 35(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 0(s2)
	srli t2, t0, 8
	sb t2, 1(s2)
	srli t2, t0, 16
	sb t2, 2(s2)
	srli t2, t0, 24
	sb t2, 3(s2)
	lbu t0, 36(s4)
	lbu t2, 37(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 38(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 39(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 4(s2)
	srli t2, t0, 8
	sb t2, 5(s2)
	srli t2, t0, 16
	sb t2, 6(s2)
	srli t2, t0, 24
	sb t2, 7(s2)
	addi t3, s4, 0
	ld s1, 0(t3)
	ld s2, 8(t3)
	ld s3, 16(t3)
	ld s4, 24(t3)
	addi t0, zero, 0
	addi t1, t3, 0
	addi t2, zero, 8
23:
	sd t0, 0(t1)
	addi t1, t1, 8
	addi t2, t2, -1
	bnez t2, 23b
	addi sp, sp, 64
	ret
	.option pop
