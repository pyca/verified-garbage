// The functions of `src/internal/vg_p384_mul_mod_p.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p384_mul_mod_p:
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
	beq t4, t5, 22f
	ld t3, 0(t4)
	ld t6, 8(t4)
	ld a1, 16(t4)
	ld a2, 24(t4)
	ld a4, 32(t4)
	ld a5, 40(t4)
	sd t3, 1664(a3)
	sd t6, 1672(a3)
	sd a1, 1680(a3)
	sd a2, 1688(a3)
	sd a4, 1696(a3)
	sd a5, 1704(a3)
	ld t3, 0(t5)
	ld t6, 8(t5)
	ld a1, 16(t5)
	ld a2, 24(t5)
	ld a4, 32(t5)
	ld a5, 40(t5)
	sd t3, 1712(a3)
	sd t6, 1720(a3)
	sd a1, 1728(a3)
	sd a2, 1736(a3)
	sd a4, 1744(a3)
	sd a5, 1752(a3)
	ld t3, 1712(a3)
	ld t4, 1720(a3)
	ld t5, 1728(a3)
	ld t6, 1736(a3)
	ld a1, 1744(a3)
	ld a2, 1752(a3)
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	ld t0, 1664(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 1760(a3)
	addi a4, zero, 0
	ld t0, 1672(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 1664(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 1768(a3)
	addi a5, zero, 0
	ld t0, 1680(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 1672(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 1664(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 1776(a3)
	addi a6, zero, 0
	ld t0, 1688(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 1680(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 1672(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 1664(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 1784(a3)
	addi a4, zero, 0
	ld t0, 1696(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 1688(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 1680(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 1672(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 1664(a3)
	mul a7, t0, a1
	mulhu t0, t0, a1
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 1792(a3)
	addi a5, zero, 0
	ld t0, 1704(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 1696(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 1688(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 1680(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 1672(a3)
	mul a7, t0, a1
	mulhu t0, t0, a1
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 1664(a3)
	mul a7, t0, a2
	mulhu t0, t0, a2
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 1800(a3)
	addi a6, zero, 0
	ld t0, 1704(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 1696(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 1688(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 1680(a3)
	mul a7, t0, a1
	mulhu t0, t0, a1
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 1672(a3)
	mul a7, t0, a2
	mulhu t0, t0, a2
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 1808(a3)
	addi a4, zero, 0
	ld t0, 1704(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 1696(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 1688(a3)
	mul a7, t0, a1
	mulhu t0, t0, a1
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 1680(a3)
	mul a7, t0, a2
	mulhu t0, t0, a2
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 1816(a3)
	addi a5, zero, 0
	ld t0, 1704(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 1696(a3)
	mul a7, t0, a1
	mulhu t0, t0, a1
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 1688(a3)
	mul a7, t0, a2
	mulhu t0, t0, a2
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 1824(a3)
	addi a6, zero, 0
	ld t0, 1704(a3)
	mul a7, t0, a1
	mulhu t0, t0, a1
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 1696(a3)
	mul a7, t0, a2
	mulhu t0, t0, a2
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 1832(a3)
	addi a4, zero, 0
	ld t0, 1704(a3)
	mul a7, t0, a2
	mulhu t0, t0, a2
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 1840(a3)
	addi a5, zero, 0
	sd a6, 1848(a3)
	addi a6, zero, 0
	j 23f
22:
	ld t3, 0(t4)
	ld t6, 8(t4)
	ld a1, 16(t4)
	ld a2, 24(t4)
	ld a4, 32(t4)
	ld a5, 40(t4)
	sd t3, 1664(a3)
	sd t6, 1672(a3)
	sd a1, 1680(a3)
	sd a2, 1688(a3)
	sd a4, 1696(a3)
	sd a5, 1704(a3)
	ld t3, 1664(a3)
	ld t4, 1672(a3)
	ld t5, 1680(a3)
	ld t6, 1688(a3)
	ld a1, 1696(a3)
	ld a2, 1704(a3)
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	sd a4, 1760(a3)
	addi a4, zero, 0
	mul a7, t3, t4
	mulhu t0, t3, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 1768(a3)
	addi a5, zero, 0
	mul a7, t3, t5
	mulhu t0, t3, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 1776(a3)
	addi a6, zero, 0
	mul a7, t3, t6
	mulhu t0, t3, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	mul a7, t4, t5
	mulhu t0, t4, t5
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 1784(a3)
	addi a4, zero, 0
	mul a7, t3, a1
	mulhu t0, t3, a1
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	mul a7, t4, t6
	mulhu t0, t4, t6
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 1792(a3)
	addi a5, zero, 0
	mul a7, t3, a2
	mulhu t0, t3, a2
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	mul a7, t4, a1
	mulhu t0, t4, a1
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	mul a7, t5, t6
	mulhu t0, t5, t6
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 1800(a3)
	addi a6, zero, 0
	mul a7, t4, a2
	mulhu t0, t4, a2
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	mul a7, t5, a1
	mulhu t0, t5, a1
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 1808(a3)
	addi a4, zero, 0
	mul a7, t5, a2
	mulhu t0, t5, a2
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	mul a7, t6, a1
	mulhu t0, t6, a1
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 1816(a3)
	addi a5, zero, 0
	mul a7, t6, a2
	mulhu t0, t6, a2
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 1824(a3)
	addi a6, zero, 0
	mul a7, a1, a2
	mulhu t0, a1, a2
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 1832(a3)
	addi a4, zero, 0
	sd a5, 1840(a3)
	addi a5, zero, 0
	sd a6, 1848(a3)
	addi a6, zero, 0
	addi a5, zero, 0
	addi a4, zero, 0
	srli a7, a5, 63
	ld a5, 1760(a3)
	slli a6, a5, 1
	or a6, a6, a7
	ld t3, 1664(a3)
	mul t0, t3, t3
	mulhu t3, t3, t3
	add a6, a6, t0
	sltu a7, a6, t0
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 1760(a3)
	srli a7, a5, 63
	ld a5, 1768(a3)
	slli a6, a5, 1
	or a6, a6, a7
	add a6, a6, t3
	sltu a7, a6, t3
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 1768(a3)
	srli a7, a5, 63
	ld a5, 1776(a3)
	slli a6, a5, 1
	or a6, a6, a7
	ld t3, 1672(a3)
	mul t0, t3, t3
	mulhu t3, t3, t3
	add a6, a6, t0
	sltu a7, a6, t0
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 1776(a3)
	srli a7, a5, 63
	ld a5, 1784(a3)
	slli a6, a5, 1
	or a6, a6, a7
	add a6, a6, t3
	sltu a7, a6, t3
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 1784(a3)
	srli a7, a5, 63
	ld a5, 1792(a3)
	slli a6, a5, 1
	or a6, a6, a7
	ld t3, 1680(a3)
	mul t0, t3, t3
	mulhu t3, t3, t3
	add a6, a6, t0
	sltu a7, a6, t0
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 1792(a3)
	srli a7, a5, 63
	ld a5, 1800(a3)
	slli a6, a5, 1
	or a6, a6, a7
	add a6, a6, t3
	sltu a7, a6, t3
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 1800(a3)
	srli a7, a5, 63
	ld a5, 1808(a3)
	slli a6, a5, 1
	or a6, a6, a7
	ld t3, 1688(a3)
	mul t0, t3, t3
	mulhu t3, t3, t3
	add a6, a6, t0
	sltu a7, a6, t0
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 1808(a3)
	srli a7, a5, 63
	ld a5, 1816(a3)
	slli a6, a5, 1
	or a6, a6, a7
	add a6, a6, t3
	sltu a7, a6, t3
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 1816(a3)
	srli a7, a5, 63
	ld a5, 1824(a3)
	slli a6, a5, 1
	or a6, a6, a7
	ld t3, 1696(a3)
	mul t0, t3, t3
	mulhu t3, t3, t3
	add a6, a6, t0
	sltu a7, a6, t0
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 1824(a3)
	srli a7, a5, 63
	ld a5, 1832(a3)
	slli a6, a5, 1
	or a6, a6, a7
	add a6, a6, t3
	sltu a7, a6, t3
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 1832(a3)
	srli a7, a5, 63
	ld a5, 1840(a3)
	slli a6, a5, 1
	or a6, a6, a7
	ld t3, 1704(a3)
	mul t0, t3, t3
	mulhu t3, t3, t3
	add a6, a6, t0
	sltu a7, a6, t0
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 1840(a3)
	srli a7, a5, 63
	ld a5, 1848(a3)
	slli a6, a5, 1
	or a6, a6, a7
	add a6, a6, t3
	sltu a7, a6, t3
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 1848(a3)
23:
	ld t3, 1760(a3)
	ld t4, 1768(a3)
	ld t5, 1776(a3)
	addi a2, zero, 0
	ld t6, 1784(a3)
	slli t0, t3, 32
	add t3, t3, t0
	sd t3, 1760(a3)
	slli a4, t3, 32
	srli a5, t3, 32
	sltu a6, t3, a4
	add a6, a6, a5
	sltu a7, a4, a6
	sub a4, a4, a6
	sub a5, a5, a7
	add a5, a5, t3
	sltu a6, a5, t3
	sltu a7, t4, a4
	sub t4, t4, a4
	sltu t0, t5, a5
	sub t5, t5, a5
	sltu a4, t5, a7
	sub t5, t5, a7
	add a7, t0, a4
	add a6, a6, a2
	add a6, a6, a7
	sltu a2, t6, a6
	sub t6, t6, a6
	ld t3, 1792(a3)
	slli t0, t4, 32
	add t4, t4, t0
	sd t4, 1768(a3)
	slli a4, t4, 32
	srli a5, t4, 32
	sltu a6, t4, a4
	add a6, a6, a5
	sltu a7, a4, a6
	sub a4, a4, a6
	sub a5, a5, a7
	add a5, a5, t4
	sltu a6, a5, t4
	sltu a7, t5, a4
	sub t5, t5, a4
	sltu t0, t6, a5
	sub t6, t6, a5
	sltu a4, t6, a7
	sub t6, t6, a7
	add a7, t0, a4
	add a6, a6, a2
	add a6, a6, a7
	sltu a2, t3, a6
	sub t3, t3, a6
	ld t4, 1800(a3)
	slli t0, t5, 32
	add t5, t5, t0
	sd t5, 1776(a3)
	slli a4, t5, 32
	srli a5, t5, 32
	sltu a6, t5, a4
	add a6, a6, a5
	sltu a7, a4, a6
	sub a4, a4, a6
	sub a5, a5, a7
	add a5, a5, t5
	sltu a6, a5, t5
	sltu a7, t6, a4
	sub t6, t6, a4
	sltu t0, t3, a5
	sub t3, t3, a5
	sltu a4, t3, a7
	sub t3, t3, a7
	add a7, t0, a4
	add a6, a6, a2
	add a6, a6, a7
	sltu a2, t4, a6
	sub t4, t4, a6
	ld t5, 1808(a3)
	slli t0, t6, 32
	add t6, t6, t0
	sd t6, 1784(a3)
	slli a4, t6, 32
	srli a5, t6, 32
	sltu a6, t6, a4
	add a6, a6, a5
	sltu a7, a4, a6
	sub a4, a4, a6
	sub a5, a5, a7
	add a5, a5, t6
	sltu a6, a5, t6
	sltu a7, t3, a4
	sub t3, t3, a4
	sltu t0, t4, a5
	sub t4, t4, a5
	sltu a4, t4, a7
	sub t4, t4, a7
	add a7, t0, a4
	add a6, a6, a2
	add a6, a6, a7
	sltu a2, t5, a6
	sub t5, t5, a6
	ld t6, 1816(a3)
	slli t0, t3, 32
	add t3, t3, t0
	sd t3, 1792(a3)
	slli a4, t3, 32
	srli a5, t3, 32
	sltu a6, t3, a4
	add a6, a6, a5
	sltu a7, a4, a6
	sub a4, a4, a6
	sub a5, a5, a7
	add a5, a5, t3
	sltu a6, a5, t3
	sltu a7, t4, a4
	sub t4, t4, a4
	sltu t0, t5, a5
	sub t5, t5, a5
	sltu a4, t5, a7
	sub t5, t5, a7
	add a7, t0, a4
	add a6, a6, a2
	add a6, a6, a7
	sltu a2, t6, a6
	sub t6, t6, a6
	ld t3, 1824(a3)
	slli t0, t4, 32
	add t4, t4, t0
	sd t4, 1800(a3)
	slli a4, t4, 32
	srli a5, t4, 32
	sltu a6, t4, a4
	add a6, a6, a5
	sltu a7, a4, a6
	sub a4, a4, a6
	sub a5, a5, a7
	add a5, a5, t4
	sltu a6, a5, t4
	sltu a7, t5, a4
	sub t5, t5, a4
	sltu t0, t6, a5
	sub t6, t6, a5
	sltu a4, t6, a7
	sub t6, t6, a7
	add a7, t0, a4
	add a6, a6, a2
	add a6, a6, a7
	sltu a2, t3, a6
	sub t3, t3, a6
	ld t4, 1832(a3)
	ld a1, 1840(a3)
	ld a4, 1848(a3)
	sltu a5, t4, a2
	sub t4, t4, a2
	sltu a2, a1, a5
	sub a1, a1, a5
	sltu a5, a4, a2
	sub a4, a4, a2
	addi a2, zero, 0
	ld a7, 1760(a3)
	add t5, t5, a7
	sltu a6, t5, a7
	add t5, t5, a2
	sltu a2, t5, a2
	add a2, a2, a6
	ld a7, 1768(a3)
	add t6, t6, a7
	sltu a6, t6, a7
	add t6, t6, a2
	sltu a2, t6, a2
	add a2, a2, a6
	ld a7, 1776(a3)
	add t3, t3, a7
	sltu a6, t3, a7
	add t3, t3, a2
	sltu a2, t3, a2
	add a2, a2, a6
	ld a7, 1784(a3)
	add t4, t4, a7
	sltu a6, t4, a7
	add t4, t4, a2
	sltu a2, t4, a2
	add a2, a2, a6
	ld a7, 1792(a3)
	add a1, a1, a7
	sltu a6, a1, a7
	add a1, a1, a2
	sltu a2, a1, a2
	add a2, a2, a6
	ld a7, 1800(a3)
	add a4, a4, a7
	sltu a6, a4, a7
	add a4, a4, a2
	sltu a2, a4, a2
	add a2, a2, a6
	sub a2, a2, a5
	addi a7, zero, 0
	addi t0, zero, -1
	slli t0, t0, 32
	addi t0, t0, 1
	add a5, t5, t0
	sltu a0, a5, t0
	add a5, a5, a7
	sltu a7, a5, a7
	add a7, a7, a0
	sd a5, 0(t2)
	addi t0, zero, -1
	srli t0, t0, 32
	add a5, t6, t0
	sltu a0, a5, t0
	add a5, a5, a7
	sltu a7, a5, a7
	add a7, a7, a0
	sd a5, 8(t2)
	addi t0, zero, 1
	add a5, t3, t0
	sltu a0, a5, t0
	add a5, a5, a7
	sltu a7, a5, a7
	add a7, a7, a0
	sd a5, 16(t2)
	addi t0, zero, 0
	add a5, t4, t0
	sltu a0, a5, t0
	add a5, a5, a7
	sltu a7, a5, a7
	add a7, a7, a0
	sd a5, 24(t2)
	add a5, a1, t0
	sltu a0, a5, t0
	add a5, a5, a7
	sltu a7, a5, a7
	add a7, a7, a0
	sd a5, 32(t2)
	add a5, a4, t0
	sltu a0, a5, t0
	add a5, a5, a7
	sltu a7, a5, a7
	add a7, a7, a0
	sd a5, 40(t2)
	or a7, a7, a2
	addi t0, zero, 0
	sub t0, t0, a7
	ld a5, 0(t2)
	xor a5, a5, t5
	and a5, a5, t0
	xor a5, a5, t5
	sd a5, 0(t2)
	ld a5, 8(t2)
	xor a5, a5, t6
	and a5, a5, t0
	xor a5, a5, t6
	sd a5, 8(t2)
	ld a5, 16(t2)
	xor a5, a5, t3
	and a5, a5, t0
	xor a5, a5, t3
	sd a5, 16(t2)
	ld a5, 24(t2)
	xor a5, a5, t4
	and a5, a5, t0
	xor a5, a5, t4
	sd a5, 24(t2)
	ld a5, 32(t2)
	xor a5, a5, a1
	and a5, a5, t0
	xor a5, a5, a1
	sd a5, 32(t2)
	ld a5, 40(t2)
	xor a5, a5, a4
	and a5, a5, t0
	xor a5, a5, a4
	sd a5, 40(t2)
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
	beq t4, t5, 24f
	ld t3, 0(t4)
	ld t6, 8(t4)
	ld a1, 16(t4)
	ld a2, 24(t4)
	ld a4, 32(t4)
	ld a5, 40(t4)
	sd t3, 1664(a3)
	sd t6, 1672(a3)
	sd a1, 1680(a3)
	sd a2, 1688(a3)
	sd a4, 1696(a3)
	sd a5, 1704(a3)
	ld t3, 0(t5)
	ld t6, 8(t5)
	ld a1, 16(t5)
	ld a2, 24(t5)
	ld a4, 32(t5)
	ld a5, 40(t5)
	sd t3, 1712(a3)
	sd t6, 1720(a3)
	sd a1, 1728(a3)
	sd a2, 1736(a3)
	sd a4, 1744(a3)
	sd a5, 1752(a3)
	ld t3, 1712(a3)
	ld t4, 1720(a3)
	ld t5, 1728(a3)
	ld t6, 1736(a3)
	ld a1, 1744(a3)
	ld a2, 1752(a3)
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	ld t0, 1664(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 1760(a3)
	addi a4, zero, 0
	ld t0, 1672(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 1664(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 1768(a3)
	addi a5, zero, 0
	ld t0, 1680(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 1672(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 1664(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 1776(a3)
	addi a6, zero, 0
	ld t0, 1688(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 1680(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 1672(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 1664(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 1784(a3)
	addi a4, zero, 0
	ld t0, 1696(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 1688(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 1680(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 1672(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 1664(a3)
	mul a7, t0, a1
	mulhu t0, t0, a1
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 1792(a3)
	addi a5, zero, 0
	ld t0, 1704(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 1696(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 1688(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 1680(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 1672(a3)
	mul a7, t0, a1
	mulhu t0, t0, a1
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 1664(a3)
	mul a7, t0, a2
	mulhu t0, t0, a2
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 1800(a3)
	addi a6, zero, 0
	ld t0, 1704(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 1696(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 1688(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 1680(a3)
	mul a7, t0, a1
	mulhu t0, t0, a1
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 1672(a3)
	mul a7, t0, a2
	mulhu t0, t0, a2
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 1808(a3)
	addi a4, zero, 0
	ld t0, 1704(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 1696(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 1688(a3)
	mul a7, t0, a1
	mulhu t0, t0, a1
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 1680(a3)
	mul a7, t0, a2
	mulhu t0, t0, a2
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 1816(a3)
	addi a5, zero, 0
	ld t0, 1704(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 1696(a3)
	mul a7, t0, a1
	mulhu t0, t0, a1
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 1688(a3)
	mul a7, t0, a2
	mulhu t0, t0, a2
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 1824(a3)
	addi a6, zero, 0
	ld t0, 1704(a3)
	mul a7, t0, a1
	mulhu t0, t0, a1
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 1696(a3)
	mul a7, t0, a2
	mulhu t0, t0, a2
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 1832(a3)
	addi a4, zero, 0
	ld t0, 1704(a3)
	mul a7, t0, a2
	mulhu t0, t0, a2
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 1840(a3)
	addi a5, zero, 0
	sd a6, 1848(a3)
	addi a6, zero, 0
	j 25f
24:
	ld t3, 0(t4)
	ld t6, 8(t4)
	ld a1, 16(t4)
	ld a2, 24(t4)
	ld a4, 32(t4)
	ld a5, 40(t4)
	sd t3, 1664(a3)
	sd t6, 1672(a3)
	sd a1, 1680(a3)
	sd a2, 1688(a3)
	sd a4, 1696(a3)
	sd a5, 1704(a3)
	ld t3, 1664(a3)
	ld t4, 1672(a3)
	ld t5, 1680(a3)
	ld t6, 1688(a3)
	ld a1, 1696(a3)
	ld a2, 1704(a3)
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	sd a4, 1760(a3)
	addi a4, zero, 0
	mul a7, t3, t4
	mulhu t0, t3, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 1768(a3)
	addi a5, zero, 0
	mul a7, t3, t5
	mulhu t0, t3, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 1776(a3)
	addi a6, zero, 0
	mul a7, t3, t6
	mulhu t0, t3, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	mul a7, t4, t5
	mulhu t0, t4, t5
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 1784(a3)
	addi a4, zero, 0
	mul a7, t3, a1
	mulhu t0, t3, a1
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	mul a7, t4, t6
	mulhu t0, t4, t6
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 1792(a3)
	addi a5, zero, 0
	mul a7, t3, a2
	mulhu t0, t3, a2
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	mul a7, t4, a1
	mulhu t0, t4, a1
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	mul a7, t5, t6
	mulhu t0, t5, t6
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 1800(a3)
	addi a6, zero, 0
	mul a7, t4, a2
	mulhu t0, t4, a2
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	mul a7, t5, a1
	mulhu t0, t5, a1
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 1808(a3)
	addi a4, zero, 0
	mul a7, t5, a2
	mulhu t0, t5, a2
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	mul a7, t6, a1
	mulhu t0, t6, a1
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 1816(a3)
	addi a5, zero, 0
	mul a7, t6, a2
	mulhu t0, t6, a2
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 1824(a3)
	addi a6, zero, 0
	mul a7, a1, a2
	mulhu t0, a1, a2
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 1832(a3)
	addi a4, zero, 0
	sd a5, 1840(a3)
	addi a5, zero, 0
	sd a6, 1848(a3)
	addi a6, zero, 0
	addi a5, zero, 0
	addi a4, zero, 0
	srli a7, a5, 63
	ld a5, 1760(a3)
	slli a6, a5, 1
	or a6, a6, a7
	ld t3, 1664(a3)
	mul t0, t3, t3
	mulhu t3, t3, t3
	add a6, a6, t0
	sltu a7, a6, t0
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 1760(a3)
	srli a7, a5, 63
	ld a5, 1768(a3)
	slli a6, a5, 1
	or a6, a6, a7
	add a6, a6, t3
	sltu a7, a6, t3
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 1768(a3)
	srli a7, a5, 63
	ld a5, 1776(a3)
	slli a6, a5, 1
	or a6, a6, a7
	ld t3, 1672(a3)
	mul t0, t3, t3
	mulhu t3, t3, t3
	add a6, a6, t0
	sltu a7, a6, t0
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 1776(a3)
	srli a7, a5, 63
	ld a5, 1784(a3)
	slli a6, a5, 1
	or a6, a6, a7
	add a6, a6, t3
	sltu a7, a6, t3
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 1784(a3)
	srli a7, a5, 63
	ld a5, 1792(a3)
	slli a6, a5, 1
	or a6, a6, a7
	ld t3, 1680(a3)
	mul t0, t3, t3
	mulhu t3, t3, t3
	add a6, a6, t0
	sltu a7, a6, t0
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 1792(a3)
	srli a7, a5, 63
	ld a5, 1800(a3)
	slli a6, a5, 1
	or a6, a6, a7
	add a6, a6, t3
	sltu a7, a6, t3
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 1800(a3)
	srli a7, a5, 63
	ld a5, 1808(a3)
	slli a6, a5, 1
	or a6, a6, a7
	ld t3, 1688(a3)
	mul t0, t3, t3
	mulhu t3, t3, t3
	add a6, a6, t0
	sltu a7, a6, t0
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 1808(a3)
	srli a7, a5, 63
	ld a5, 1816(a3)
	slli a6, a5, 1
	or a6, a6, a7
	add a6, a6, t3
	sltu a7, a6, t3
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 1816(a3)
	srli a7, a5, 63
	ld a5, 1824(a3)
	slli a6, a5, 1
	or a6, a6, a7
	ld t3, 1696(a3)
	mul t0, t3, t3
	mulhu t3, t3, t3
	add a6, a6, t0
	sltu a7, a6, t0
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 1824(a3)
	srli a7, a5, 63
	ld a5, 1832(a3)
	slli a6, a5, 1
	or a6, a6, a7
	add a6, a6, t3
	sltu a7, a6, t3
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 1832(a3)
	srli a7, a5, 63
	ld a5, 1840(a3)
	slli a6, a5, 1
	or a6, a6, a7
	ld t3, 1704(a3)
	mul t0, t3, t3
	mulhu t3, t3, t3
	add a6, a6, t0
	sltu a7, a6, t0
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 1840(a3)
	srli a7, a5, 63
	ld a5, 1848(a3)
	slli a6, a5, 1
	or a6, a6, a7
	add a6, a6, t3
	sltu a7, a6, t3
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 1848(a3)
25:
	ld t3, 1760(a3)
	ld t4, 1768(a3)
	ld t5, 1776(a3)
	addi a2, zero, 0
	ld t6, 1784(a3)
	slli t0, t3, 32
	add t3, t3, t0
	sd t3, 1760(a3)
	slli a4, t3, 32
	srli a5, t3, 32
	sltu a6, t3, a4
	add a6, a6, a5
	sltu a7, a4, a6
	sub a4, a4, a6
	sub a5, a5, a7
	add a5, a5, t3
	sltu a6, a5, t3
	sltu a7, t4, a4
	sub t4, t4, a4
	sltu t0, t5, a5
	sub t5, t5, a5
	sltu a4, t5, a7
	sub t5, t5, a7
	add a7, t0, a4
	add a6, a6, a2
	add a6, a6, a7
	sltu a2, t6, a6
	sub t6, t6, a6
	ld t3, 1792(a3)
	slli t0, t4, 32
	add t4, t4, t0
	sd t4, 1768(a3)
	slli a4, t4, 32
	srli a5, t4, 32
	sltu a6, t4, a4
	add a6, a6, a5
	sltu a7, a4, a6
	sub a4, a4, a6
	sub a5, a5, a7
	add a5, a5, t4
	sltu a6, a5, t4
	sltu a7, t5, a4
	sub t5, t5, a4
	sltu t0, t6, a5
	sub t6, t6, a5
	sltu a4, t6, a7
	sub t6, t6, a7
	add a7, t0, a4
	add a6, a6, a2
	add a6, a6, a7
	sltu a2, t3, a6
	sub t3, t3, a6
	ld t4, 1800(a3)
	slli t0, t5, 32
	add t5, t5, t0
	sd t5, 1776(a3)
	slli a4, t5, 32
	srli a5, t5, 32
	sltu a6, t5, a4
	add a6, a6, a5
	sltu a7, a4, a6
	sub a4, a4, a6
	sub a5, a5, a7
	add a5, a5, t5
	sltu a6, a5, t5
	sltu a7, t6, a4
	sub t6, t6, a4
	sltu t0, t3, a5
	sub t3, t3, a5
	sltu a4, t3, a7
	sub t3, t3, a7
	add a7, t0, a4
	add a6, a6, a2
	add a6, a6, a7
	sltu a2, t4, a6
	sub t4, t4, a6
	ld t5, 1808(a3)
	slli t0, t6, 32
	add t6, t6, t0
	sd t6, 1784(a3)
	slli a4, t6, 32
	srli a5, t6, 32
	sltu a6, t6, a4
	add a6, a6, a5
	sltu a7, a4, a6
	sub a4, a4, a6
	sub a5, a5, a7
	add a5, a5, t6
	sltu a6, a5, t6
	sltu a7, t3, a4
	sub t3, t3, a4
	sltu t0, t4, a5
	sub t4, t4, a5
	sltu a4, t4, a7
	sub t4, t4, a7
	add a7, t0, a4
	add a6, a6, a2
	add a6, a6, a7
	sltu a2, t5, a6
	sub t5, t5, a6
	ld t6, 1816(a3)
	slli t0, t3, 32
	add t3, t3, t0
	sd t3, 1792(a3)
	slli a4, t3, 32
	srli a5, t3, 32
	sltu a6, t3, a4
	add a6, a6, a5
	sltu a7, a4, a6
	sub a4, a4, a6
	sub a5, a5, a7
	add a5, a5, t3
	sltu a6, a5, t3
	sltu a7, t4, a4
	sub t4, t4, a4
	sltu t0, t5, a5
	sub t5, t5, a5
	sltu a4, t5, a7
	sub t5, t5, a7
	add a7, t0, a4
	add a6, a6, a2
	add a6, a6, a7
	sltu a2, t6, a6
	sub t6, t6, a6
	ld t3, 1824(a3)
	slli t0, t4, 32
	add t4, t4, t0
	sd t4, 1800(a3)
	slli a4, t4, 32
	srli a5, t4, 32
	sltu a6, t4, a4
	add a6, a6, a5
	sltu a7, a4, a6
	sub a4, a4, a6
	sub a5, a5, a7
	add a5, a5, t4
	sltu a6, a5, t4
	sltu a7, t5, a4
	sub t5, t5, a4
	sltu t0, t6, a5
	sub t6, t6, a5
	sltu a4, t6, a7
	sub t6, t6, a7
	add a7, t0, a4
	add a6, a6, a2
	add a6, a6, a7
	sltu a2, t3, a6
	sub t3, t3, a6
	ld t4, 1832(a3)
	ld a1, 1840(a3)
	ld a4, 1848(a3)
	sltu a5, t4, a2
	sub t4, t4, a2
	sltu a2, a1, a5
	sub a1, a1, a5
	sltu a5, a4, a2
	sub a4, a4, a2
	addi a2, zero, 0
	ld a7, 1760(a3)
	add t5, t5, a7
	sltu a6, t5, a7
	add t5, t5, a2
	sltu a2, t5, a2
	add a2, a2, a6
	ld a7, 1768(a3)
	add t6, t6, a7
	sltu a6, t6, a7
	add t6, t6, a2
	sltu a2, t6, a2
	add a2, a2, a6
	ld a7, 1776(a3)
	add t3, t3, a7
	sltu a6, t3, a7
	add t3, t3, a2
	sltu a2, t3, a2
	add a2, a2, a6
	ld a7, 1784(a3)
	add t4, t4, a7
	sltu a6, t4, a7
	add t4, t4, a2
	sltu a2, t4, a2
	add a2, a2, a6
	ld a7, 1792(a3)
	add a1, a1, a7
	sltu a6, a1, a7
	add a1, a1, a2
	sltu a2, a1, a2
	add a2, a2, a6
	ld a7, 1800(a3)
	add a4, a4, a7
	sltu a6, a4, a7
	add a4, a4, a2
	sltu a2, a4, a2
	add a2, a2, a6
	sub a2, a2, a5
	addi a7, zero, 0
	addi t0, zero, -1
	slli t0, t0, 32
	addi t0, t0, 1
	add a5, t5, t0
	sltu a0, a5, t0
	add a5, a5, a7
	sltu a7, a5, a7
	add a7, a7, a0
	sd a5, 0(t2)
	addi t0, zero, -1
	srli t0, t0, 32
	add a5, t6, t0
	sltu a0, a5, t0
	add a5, a5, a7
	sltu a7, a5, a7
	add a7, a7, a0
	sd a5, 8(t2)
	addi t0, zero, 1
	add a5, t3, t0
	sltu a0, a5, t0
	add a5, a5, a7
	sltu a7, a5, a7
	add a7, a7, a0
	sd a5, 16(t2)
	addi t0, zero, 0
	add a5, t4, t0
	sltu a0, a5, t0
	add a5, a5, a7
	sltu a7, a5, a7
	add a7, a7, a0
	sd a5, 24(t2)
	add a5, a1, t0
	sltu a0, a5, t0
	add a5, a5, a7
	sltu a7, a5, a7
	add a7, a7, a0
	sd a5, 32(t2)
	add a5, a4, t0
	sltu a0, a5, t0
	add a5, a5, a7
	sltu a7, a5, a7
	add a7, a7, a0
	sd a5, 40(t2)
	or a7, a7, a2
	addi t0, zero, 0
	sub t0, t0, a7
	ld a5, 0(t2)
	xor a5, a5, t5
	and a5, a5, t0
	xor a5, a5, t5
	sd a5, 0(t2)
	ld a5, 8(t2)
	xor a5, a5, t6
	and a5, a5, t0
	xor a5, a5, t6
	sd a5, 8(t2)
	ld a5, 16(t2)
	xor a5, a5, t3
	and a5, a5, t0
	xor a5, a5, t3
	sd a5, 16(t2)
	ld a5, 24(t2)
	xor a5, a5, t4
	and a5, a5, t0
	xor a5, a5, t4
	sd a5, 24(t2)
	ld a5, 32(t2)
	xor a5, a5, a1
	and a5, a5, t0
	xor a5, a5, a1
	sd a5, 32(t2)
	ld a5, 40(t2)
	xor a5, a5, a4
	and a5, a5, t0
	xor a5, a5, a4
	sd a5, 40(t2)
21:
	ret
	.option pop
