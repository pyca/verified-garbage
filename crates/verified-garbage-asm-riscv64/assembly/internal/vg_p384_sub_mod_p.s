// The functions of `src/internal/vg_p384_sub_mod_p.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p384_sub_mod_p:
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
	sw a4, 1856(a3)
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
	sw a4, 1860(a3)
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
	sw a4, 1864(a3)
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
	sw a4, 1868(a3)
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
	sw a4, 1872(a3)
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
	sw a4, 1876(a3)
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
	sw a4, 1880(a3)
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
	sw a4, 1884(a3)
	lbu a4, 32(t4)
	lbu a5, 33(t4)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 34(t4)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 35(t4)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 1888(a3)
	lbu a4, 36(t4)
	lbu a5, 37(t4)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 38(t4)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 39(t4)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 1892(a3)
	lbu a4, 40(t4)
	lbu a5, 41(t4)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 42(t4)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 43(t4)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 1896(a3)
	lbu a4, 44(t4)
	lbu a5, 45(t4)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 46(t4)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 47(t4)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 1900(a3)
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
	sw a4, 1904(a3)
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
	sw a4, 1908(a3)
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
	sw a4, 1912(a3)
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
	sw a4, 1916(a3)
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
	sw a4, 1920(a3)
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
	sw a4, 1924(a3)
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
	sw a4, 1928(a3)
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
	sw a4, 1932(a3)
	lbu a4, 32(t5)
	lbu a5, 33(t5)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 34(t5)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 35(t5)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 1936(a3)
	lbu a4, 36(t5)
	lbu a5, 37(t5)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 38(t5)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 39(t5)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 1940(a3)
	lbu a4, 40(t5)
	lbu a5, 41(t5)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 42(t5)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 43(t5)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 1944(a3)
	lbu a4, 44(t5)
	lbu a5, 45(t5)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 46(t5)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 47(t5)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 1948(a3)
	addi t4, a3, 1856
	addi t5, a3, 1904
	addi t2, a3, 1952
	addi a0, t4, 0
	addi a7, t5, 0
	addi a2, zero, 0
	ld t5, 0(a0)
	ld a5, 0(a7)
	sltu a6, t5, a5
	sub t5, t5, a5
	sltu t0, t5, a2
	sub t5, t5, a2
	add a2, a6, t0
	ld t6, 8(a0)
	ld a5, 8(a7)
	sltu a6, t6, a5
	sub t6, t6, a5
	sltu t0, t6, a2
	sub t6, t6, a2
	add a2, a6, t0
	ld t3, 16(a0)
	ld a5, 16(a7)
	sltu a6, t3, a5
	sub t3, t3, a5
	sltu t0, t3, a2
	sub t3, t3, a2
	add a2, a6, t0
	ld t4, 24(a0)
	ld a5, 24(a7)
	sltu a6, t4, a5
	sub t4, t4, a5
	sltu t0, t4, a2
	sub t4, t4, a2
	add a2, a6, t0
	ld a1, 32(a0)
	ld a5, 32(a7)
	sltu a6, a1, a5
	sub a1, a1, a5
	sltu t0, a1, a2
	sub a1, a1, a2
	add a2, a6, t0
	ld a4, 40(a0)
	ld a5, 40(a7)
	sltu a6, a4, a5
	sub a4, a4, a5
	sltu t0, a4, a2
	sub a4, a4, a2
	add a2, a6, t0
	addi t0, zero, 0
	sub t0, t0, a2
	addi a7, zero, 0
	srli a6, t0, 32
	add t5, t5, a6
	sltu a0, t5, a6
	add t5, t5, a7
	sltu a7, t5, a7
	add a7, a7, a0
	sd t5, 0(t2)
	slli a6, t0, 32
	add t6, t6, a6
	sltu a0, t6, a6
	add t6, t6, a7
	sltu a7, t6, a7
	add a7, a7, a0
	sd t6, 8(t2)
	slli a6, t0, 1
	add t3, t3, a6
	sltu a0, t3, a6
	add t3, t3, a7
	sltu a7, t3, a7
	add a7, a7, a0
	sd t3, 16(t2)
	addi a6, t0, 0
	add t4, t4, a6
	sltu a0, t4, a6
	add t4, t4, a7
	sltu a7, t4, a7
	add a7, a7, a0
	sd t4, 24(t2)
	addi a6, t0, 0
	add a1, a1, a6
	sltu a0, a1, a6
	add a1, a1, a7
	sltu a7, a1, a7
	add a7, a7, a0
	sd a1, 32(t2)
	addi a6, t0, 0
	add a4, a4, a6
	sltu a0, a4, a6
	add a4, a4, a7
	sltu a7, a4, a7
	add a7, a7, a0
	sd a4, 40(t2)
	lwu a4, 1952(a3)
	sb a4, 0(t1)
	srli a5, a4, 8
	sb a5, 1(t1)
	srli a5, a4, 16
	sb a5, 2(t1)
	srli a5, a4, 24
	sb a5, 3(t1)
	lwu a4, 1956(a3)
	sb a4, 4(t1)
	srli a5, a4, 8
	sb a5, 5(t1)
	srli a5, a4, 16
	sb a5, 6(t1)
	srli a5, a4, 24
	sb a5, 7(t1)
	lwu a4, 1960(a3)
	sb a4, 8(t1)
	srli a5, a4, 8
	sb a5, 9(t1)
	srli a5, a4, 16
	sb a5, 10(t1)
	srli a5, a4, 24
	sb a5, 11(t1)
	lwu a4, 1964(a3)
	sb a4, 12(t1)
	srli a5, a4, 8
	sb a5, 13(t1)
	srli a5, a4, 16
	sb a5, 14(t1)
	srli a5, a4, 24
	sb a5, 15(t1)
	lwu a4, 1968(a3)
	sb a4, 16(t1)
	srli a5, a4, 8
	sb a5, 17(t1)
	srli a5, a4, 16
	sb a5, 18(t1)
	srli a5, a4, 24
	sb a5, 19(t1)
	lwu a4, 1972(a3)
	sb a4, 20(t1)
	srli a5, a4, 8
	sb a5, 21(t1)
	srli a5, a4, 16
	sb a5, 22(t1)
	srli a5, a4, 24
	sb a5, 23(t1)
	lwu a4, 1976(a3)
	sb a4, 24(t1)
	srli a5, a4, 8
	sb a5, 25(t1)
	srli a5, a4, 16
	sb a5, 26(t1)
	srli a5, a4, 24
	sb a5, 27(t1)
	lwu a4, 1980(a3)
	sb a4, 28(t1)
	srli a5, a4, 8
	sb a5, 29(t1)
	srli a5, a4, 16
	sb a5, 30(t1)
	srli a5, a4, 24
	sb a5, 31(t1)
	lwu a4, 1984(a3)
	sb a4, 32(t1)
	srli a5, a4, 8
	sb a5, 33(t1)
	srli a5, a4, 16
	sb a5, 34(t1)
	srli a5, a4, 24
	sb a5, 35(t1)
	lwu a4, 1988(a3)
	sb a4, 36(t1)
	srli a5, a4, 8
	sb a5, 37(t1)
	srli a5, a4, 16
	sb a5, 38(t1)
	srli a5, a4, 24
	sb a5, 39(t1)
	lwu a4, 1992(a3)
	sb a4, 40(t1)
	srli a5, a4, 8
	sb a5, 41(t1)
	srli a5, a4, 16
	sb a5, 42(t1)
	srli a5, a4, 24
	sb a5, 43(t1)
	lwu a4, 1996(a3)
	sb a4, 44(t1)
	srli a5, a4, 8
	sb a5, 45(t1)
	srli a5, a4, 16
	sb a5, 46(t1)
	srli a5, a4, 24
	sb a5, 47(t1)
	j 21f
20:
	addi a0, t4, 0
	addi a7, t5, 0
	addi a2, zero, 0
	ld t5, 0(a0)
	ld a5, 0(a7)
	sltu a6, t5, a5
	sub t5, t5, a5
	sltu t0, t5, a2
	sub t5, t5, a2
	add a2, a6, t0
	ld t6, 8(a0)
	ld a5, 8(a7)
	sltu a6, t6, a5
	sub t6, t6, a5
	sltu t0, t6, a2
	sub t6, t6, a2
	add a2, a6, t0
	ld t3, 16(a0)
	ld a5, 16(a7)
	sltu a6, t3, a5
	sub t3, t3, a5
	sltu t0, t3, a2
	sub t3, t3, a2
	add a2, a6, t0
	ld t4, 24(a0)
	ld a5, 24(a7)
	sltu a6, t4, a5
	sub t4, t4, a5
	sltu t0, t4, a2
	sub t4, t4, a2
	add a2, a6, t0
	ld a1, 32(a0)
	ld a5, 32(a7)
	sltu a6, a1, a5
	sub a1, a1, a5
	sltu t0, a1, a2
	sub a1, a1, a2
	add a2, a6, t0
	ld a4, 40(a0)
	ld a5, 40(a7)
	sltu a6, a4, a5
	sub a4, a4, a5
	sltu t0, a4, a2
	sub a4, a4, a2
	add a2, a6, t0
	addi t0, zero, 0
	sub t0, t0, a2
	addi a7, zero, 0
	srli a6, t0, 32
	add t5, t5, a6
	sltu a0, t5, a6
	add t5, t5, a7
	sltu a7, t5, a7
	add a7, a7, a0
	sd t5, 0(t2)
	slli a6, t0, 32
	add t6, t6, a6
	sltu a0, t6, a6
	add t6, t6, a7
	sltu a7, t6, a7
	add a7, a7, a0
	sd t6, 8(t2)
	slli a6, t0, 1
	add t3, t3, a6
	sltu a0, t3, a6
	add t3, t3, a7
	sltu a7, t3, a7
	add a7, a7, a0
	sd t3, 16(t2)
	addi a6, t0, 0
	add t4, t4, a6
	sltu a0, t4, a6
	add t4, t4, a7
	sltu a7, t4, a7
	add a7, a7, a0
	sd t4, 24(t2)
	addi a6, t0, 0
	add a1, a1, a6
	sltu a0, a1, a6
	add a1, a1, a7
	sltu a7, a1, a7
	add a7, a7, a0
	sd a1, 32(t2)
	addi a6, t0, 0
	add a4, a4, a6
	sltu a0, a4, a6
	add a4, a4, a7
	sltu a7, a4, a7
	add a7, a7, a0
	sd a4, 40(t2)
21:
	ret
	.option pop
