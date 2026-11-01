// The functions of `src/internal/vg_p256_sub_mod_p.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p256_sub_mod_p:
	.option push
	.option arch, +m, +c
	slli a1, a1, 32
	srli a1, a1, 32
	slli a2, a2, 32
	srli a2, a2, 32
	slli a3, a3, 32
	srli a3, a3, 32
	add t2, a0, a1
	add t4, a0, a2
	add t5, a0, a3
	addi a3, a0, 2047
	addi a3, a3, 1
	or t0, t2, t4
	or t0, t0, t5
	andi t0, t0, 7
	beqz t0, 20f
	addi t1, t2, 0
	lbu a4, 0(t4)
	lbu a5, 1(t4)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 2(t4)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 3(t4)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 1952(a3)
	lbu a4, 4(t4)
	lbu a5, 5(t4)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 6(t4)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 7(t4)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 1956(a3)
	lbu a4, 8(t4)
	lbu a5, 9(t4)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 10(t4)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 11(t4)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 1960(a3)
	lbu a4, 12(t4)
	lbu a5, 13(t4)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 14(t4)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 15(t4)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 1964(a3)
	lbu a4, 16(t4)
	lbu a5, 17(t4)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 18(t4)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 19(t4)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 1968(a3)
	lbu a4, 20(t4)
	lbu a5, 21(t4)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 22(t4)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 23(t4)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 1972(a3)
	lbu a4, 24(t4)
	lbu a5, 25(t4)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 26(t4)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 27(t4)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 1976(a3)
	lbu a4, 28(t4)
	lbu a5, 29(t4)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 30(t4)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 31(t4)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 1980(a3)
	lbu a4, 0(t5)
	lbu a5, 1(t5)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 2(t5)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 3(t5)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 1984(a3)
	lbu a4, 4(t5)
	lbu a5, 5(t5)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 6(t5)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 7(t5)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 1988(a3)
	lbu a4, 8(t5)
	lbu a5, 9(t5)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 10(t5)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 11(t5)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 1992(a3)
	lbu a4, 12(t5)
	lbu a5, 13(t5)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 14(t5)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 15(t5)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 1996(a3)
	lbu a4, 16(t5)
	lbu a5, 17(t5)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 18(t5)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 19(t5)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 2000(a3)
	lbu a4, 20(t5)
	lbu a5, 21(t5)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 22(t5)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 23(t5)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 2004(a3)
	lbu a4, 24(t5)
	lbu a5, 25(t5)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 26(t5)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 27(t5)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 2008(a3)
	lbu a4, 28(t5)
	lbu a5, 29(t5)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 30(t5)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 31(t5)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 2012(a3)
	addi t4, a3, 1952
	addi t5, a3, 1984
	addi t2, a3, 2016
	ld a1, 0(t4)
	ld t3, 8(t4)
	ld t6, 16(t4)
	ld a4, 24(t4)
	ld a5, 0(t5)
	ld a6, 8(t5)
	ld a7, 16(t5)
	ld t0, 24(t5)
	sltu a2, a1, a5
	sub a1, a1, a5
	sltu a5, t3, a6
	sub t3, t3, a6
	sltu a0, t3, a2
	sub t3, t3, a2
	add a2, a5, a0
	sltu a5, t6, a7
	sub t4, t6, a7
	sltu a0, t4, a2
	sub t4, t4, a2
	add a2, a5, a0
	sltu a5, a4, t0
	sub t5, a4, t0
	sltu a0, t5, a2
	sub t5, t5, a2
	add a2, a5, a0
	addi t0, zero, 0
	sub t0, t0, a2
	addi t6, t0, 0
	add a1, a1, t6
	sltu a7, a1, t6
	sd a1, 0(t2)
	srli t6, t0, 32
	add t3, t3, t6
	sltu a0, t3, t6
	add t3, t3, a7
	sltu a7, t3, a7
	add a7, a7, a0
	sd t3, 8(t2)
	addi t6, zero, 0
	add t4, t4, t6
	sltu a0, t4, t6
	add t4, t4, a7
	sltu a7, t4, a7
	add a7, a7, a0
	sd t4, 16(t2)
	slli t6, t0, 32
	srli a4, t0, 63
	or t6, t6, a4
	add t5, t5, t6
	sltu a0, t5, t6
	add t5, t5, a7
	sltu a7, t5, a7
	add a7, a7, a0
	sd t5, 24(t2)
	lwu a4, 2016(a3)
	sb a4, 0(t1)
	srli a5, a4, 8
	sb a5, 1(t1)
	srli a5, a4, 16
	sb a5, 2(t1)
	srli a5, a4, 24
	sb a5, 3(t1)
	lwu a4, 2020(a3)
	sb a4, 4(t1)
	srli a5, a4, 8
	sb a5, 5(t1)
	srli a5, a4, 16
	sb a5, 6(t1)
	srli a5, a4, 24
	sb a5, 7(t1)
	lwu a4, 2024(a3)
	sb a4, 8(t1)
	srli a5, a4, 8
	sb a5, 9(t1)
	srli a5, a4, 16
	sb a5, 10(t1)
	srli a5, a4, 24
	sb a5, 11(t1)
	lwu a4, 2028(a3)
	sb a4, 12(t1)
	srli a5, a4, 8
	sb a5, 13(t1)
	srli a5, a4, 16
	sb a5, 14(t1)
	srli a5, a4, 24
	sb a5, 15(t1)
	lwu a4, 2032(a3)
	sb a4, 16(t1)
	srli a5, a4, 8
	sb a5, 17(t1)
	srli a5, a4, 16
	sb a5, 18(t1)
	srli a5, a4, 24
	sb a5, 19(t1)
	lwu a4, 2036(a3)
	sb a4, 20(t1)
	srli a5, a4, 8
	sb a5, 21(t1)
	srli a5, a4, 16
	sb a5, 22(t1)
	srli a5, a4, 24
	sb a5, 23(t1)
	lwu a4, 2040(a3)
	sb a4, 24(t1)
	srli a5, a4, 8
	sb a5, 25(t1)
	srli a5, a4, 16
	sb a5, 26(t1)
	srli a5, a4, 24
	sb a5, 27(t1)
	lwu a4, 2044(a3)
	sb a4, 28(t1)
	srli a5, a4, 8
	sb a5, 29(t1)
	srli a5, a4, 16
	sb a5, 30(t1)
	srli a5, a4, 24
	sb a5, 31(t1)
	j 21f
20:
	ld a1, 0(t4)
	ld t3, 8(t4)
	ld t6, 16(t4)
	ld a4, 24(t4)
	ld a5, 0(t5)
	ld a6, 8(t5)
	ld a7, 16(t5)
	ld t0, 24(t5)
	sltu a2, a1, a5
	sub a1, a1, a5
	sltu a5, t3, a6
	sub t3, t3, a6
	sltu a0, t3, a2
	sub t3, t3, a2
	add a2, a5, a0
	sltu a5, t6, a7
	sub t4, t6, a7
	sltu a0, t4, a2
	sub t4, t4, a2
	add a2, a5, a0
	sltu a5, a4, t0
	sub t5, a4, t0
	sltu a0, t5, a2
	sub t5, t5, a2
	add a2, a5, a0
	addi t0, zero, 0
	sub t0, t0, a2
	addi t6, t0, 0
	add a1, a1, t6
	sltu a7, a1, t6
	sd a1, 0(t2)
	srli t6, t0, 32
	add t3, t3, t6
	sltu a0, t3, t6
	add t3, t3, a7
	sltu a7, t3, a7
	add a7, a7, a0
	sd t3, 8(t2)
	addi t6, zero, 0
	add t4, t4, t6
	sltu a0, t4, t6
	add t4, t4, a7
	sltu a7, t4, a7
	add a7, a7, a0
	sd t4, 16(t2)
	slli t6, t0, 32
	srli a4, t0, 63
	or t6, t6, a4
	add t5, t5, t6
	sltu a0, t5, t6
	add t5, t5, a7
	sltu a7, t5, a7
	add a7, a7, a0
	sd t5, 24(t2)
21:
	ret
	.option pop
