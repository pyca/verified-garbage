// The functions of `src/p256_mont.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p256_mul_mod_p:
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
	beq t4, t5, 22f
	ld t3, 0(t4)
	ld t6, 8(t4)
	ld a1, 16(t4)
	ld a4, 24(t4)
	sd t3, 1792(a3)
	sd t6, 1800(a3)
	sd a1, 1808(a3)
	sd a4, 1816(a3)
	ld t3, 0(t5)
	ld t6, 8(t5)
	ld a1, 16(t5)
	ld a4, 24(t5)
	sd t3, 1824(a3)
	sd t6, 1832(a3)
	sd a1, 1840(a3)
	sd a4, 1848(a3)
	ld t3, 1824(a3)
	ld t4, 1832(a3)
	ld t5, 1840(a3)
	ld t6, 1848(a3)
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	ld t0, 1792(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 1856(a3)
	addi a4, zero, 0
	ld t0, 1800(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 1792(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 1864(a3)
	addi a5, zero, 0
	ld t0, 1808(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 1800(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 1792(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 1872(a3)
	addi a6, zero, 0
	ld t0, 1816(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 1808(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 1800(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 1792(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 1880(a3)
	addi a4, zero, 0
	ld t0, 1816(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 1808(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 1800(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 1888(a3)
	addi a5, zero, 0
	ld t0, 1816(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 1808(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 1896(a3)
	addi a6, zero, 0
	ld t0, 1816(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 1904(a3)
	addi a4, zero, 0
	sd a5, 1912(a3)
	addi a5, zero, 0
	j 23f
22:
	ld t3, 0(t4)
	ld t6, 8(t4)
	ld a1, 16(t4)
	ld a4, 24(t4)
	sd t3, 1792(a3)
	sd t6, 1800(a3)
	sd a1, 1808(a3)
	sd a4, 1816(a3)
	ld t3, 1792(a3)
	ld t4, 1800(a3)
	ld t5, 1808(a3)
	ld t6, 1816(a3)
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	sd a4, 1856(a3)
	addi a4, zero, 0
	mul a7, t3, t4
	mulhu t0, t3, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 1864(a3)
	addi a5, zero, 0
	mul a7, t3, t5
	mulhu t0, t3, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 1872(a3)
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
	sd a4, 1880(a3)
	addi a4, zero, 0
	mul a7, t4, t6
	mulhu t0, t4, t6
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 1888(a3)
	addi a5, zero, 0
	mul a7, t5, t6
	mulhu t0, t5, t6
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 1896(a3)
	addi a6, zero, 0
	sd a4, 1904(a3)
	addi a4, zero, 0
	sd a5, 1912(a3)
	addi a5, zero, 0
	addi a5, zero, 0
	addi a4, zero, 0
	srli a7, a5, 63
	ld a5, 1856(a3)
	slli a6, a5, 1
	or a6, a6, a7
	ld t3, 1792(a3)
	mul t0, t3, t3
	mulhu t3, t3, t3
	add a6, a6, t0
	sltu a7, a6, t0
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 1856(a3)
	srli a7, a5, 63
	ld a5, 1864(a3)
	slli a6, a5, 1
	or a6, a6, a7
	add a6, a6, t3
	sltu a7, a6, t3
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 1864(a3)
	srli a7, a5, 63
	ld a5, 1872(a3)
	slli a6, a5, 1
	or a6, a6, a7
	ld t3, 1800(a3)
	mul t0, t3, t3
	mulhu t3, t3, t3
	add a6, a6, t0
	sltu a7, a6, t0
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 1872(a3)
	srli a7, a5, 63
	ld a5, 1880(a3)
	slli a6, a5, 1
	or a6, a6, a7
	add a6, a6, t3
	sltu a7, a6, t3
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 1880(a3)
	srli a7, a5, 63
	ld a5, 1888(a3)
	slli a6, a5, 1
	or a6, a6, a7
	ld t3, 1808(a3)
	mul t0, t3, t3
	mulhu t3, t3, t3
	add a6, a6, t0
	sltu a7, a6, t0
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 1888(a3)
	srli a7, a5, 63
	ld a5, 1896(a3)
	slli a6, a5, 1
	or a6, a6, a7
	add a6, a6, t3
	sltu a7, a6, t3
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 1896(a3)
	srli a7, a5, 63
	ld a5, 1904(a3)
	slli a6, a5, 1
	or a6, a6, a7
	ld t3, 1816(a3)
	mul t0, t3, t3
	mulhu t3, t3, t3
	add a6, a6, t0
	sltu a7, a6, t0
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 1904(a3)
	srli a7, a5, 63
	ld a5, 1912(a3)
	slli a6, a5, 1
	or a6, a6, a7
	add a6, a6, t3
	sltu a7, a6, t3
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 1912(a3)
23:
	ld t3, 1856(a3)
	ld t4, 1864(a3)
	ld t5, 1872(a3)
	ld t6, 1880(a3)
	addi a2, zero, 0
	ld a1, 1888(a3)
	slli a4, t3, 32
	srli a5, t3, 32
	sub a6, t3, a4
	sltu a7, t3, a4
	sub t0, t3, a5
	sub a7, t0, a7
	add t4, t4, a4
	sltu t0, t4, a4
	add a5, a5, t0
	add t5, t5, a5
	sltu t0, t5, a5
	add t6, t6, a6
	sltu a4, t6, a6
	add t6, t6, t0
	sltu t0, t6, t0
	add t0, t0, a4
	add a7, a7, t0
	add a7, a7, a2
	add a1, a1, a7
	sltu a2, a1, a7
	ld t3, 1896(a3)
	slli a4, t4, 32
	srli a5, t4, 32
	sub a6, t4, a4
	sltu a7, t4, a4
	sub t0, t4, a5
	sub a7, t0, a7
	add t5, t5, a4
	sltu t0, t5, a4
	add a5, a5, t0
	add t6, t6, a5
	sltu t0, t6, a5
	add a1, a1, a6
	sltu a4, a1, a6
	add a1, a1, t0
	sltu t0, a1, t0
	add t0, t0, a4
	add a7, a7, t0
	add a7, a7, a2
	add t3, t3, a7
	sltu a2, t3, a7
	ld t4, 1904(a3)
	slli a4, t5, 32
	srli a5, t5, 32
	sub a6, t5, a4
	sltu a7, t5, a4
	sub t0, t5, a5
	sub a7, t0, a7
	add t6, t6, a4
	sltu t0, t6, a4
	add a5, a5, t0
	add a1, a1, a5
	sltu t0, a1, a5
	add t3, t3, a6
	sltu a4, t3, a6
	add t3, t3, t0
	sltu t0, t3, t0
	add t0, t0, a4
	add a7, a7, t0
	add a7, a7, a2
	add t4, t4, a7
	sltu a2, t4, a7
	ld t5, 1912(a3)
	slli a4, t6, 32
	srli a5, t6, 32
	sub a6, t6, a4
	sltu a7, t6, a4
	sub t0, t6, a5
	sub a7, t0, a7
	add a1, a1, a4
	sltu t0, a1, a4
	add a5, a5, t0
	add t3, t3, a5
	sltu t0, t3, a5
	add t4, t4, a6
	sltu a4, t4, a6
	add t4, t4, t0
	sltu t0, t4, t0
	add t0, t0, a4
	add a7, a7, t0
	add a7, a7, a2
	add t5, t5, a7
	sltu a2, t5, a7
	addi t6, a1, 1
	sltu a7, t6, a1
	addi t0, zero, -1
	slli t0, t0, 32
	add a4, t3, t0
	sltu a0, a4, t0
	add a4, a4, a7
	sltu a7, a4, a7
	add a7, a7, a0
	addi t0, zero, -1
	add a5, t4, t0
	sltu a0, a5, t0
	add a5, a5, a7
	sltu a7, a5, a7
	add a7, a7, a0
	addi t0, zero, -1
	srli t0, t0, 32
	addi t0, t0, -1
	add a6, t5, t0
	sltu a0, a6, t0
	add a6, a6, a7
	sltu a7, a6, a7
	add a7, a7, a0
	or a7, a7, a2
	addi t0, zero, 0
	sub t0, t0, a7
	xor t6, t6, a1
	and t6, t6, t0
	xor t6, t6, a1
	sd t6, 0(t2)
	xor a4, a4, t3
	and a4, a4, t0
	xor a4, a4, t3
	sd a4, 8(t2)
	xor a5, a5, t4
	and a5, a5, t0
	xor a5, a5, t4
	sd a5, 16(t2)
	xor a6, a6, t5
	and a6, a6, t0
	xor a6, a6, t5
	sd a6, 24(t2)
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
	beq t4, t5, 24f
	ld t3, 0(t4)
	ld t6, 8(t4)
	ld a1, 16(t4)
	ld a4, 24(t4)
	sd t3, 1792(a3)
	sd t6, 1800(a3)
	sd a1, 1808(a3)
	sd a4, 1816(a3)
	ld t3, 0(t5)
	ld t6, 8(t5)
	ld a1, 16(t5)
	ld a4, 24(t5)
	sd t3, 1824(a3)
	sd t6, 1832(a3)
	sd a1, 1840(a3)
	sd a4, 1848(a3)
	ld t3, 1824(a3)
	ld t4, 1832(a3)
	ld t5, 1840(a3)
	ld t6, 1848(a3)
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	ld t0, 1792(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 1856(a3)
	addi a4, zero, 0
	ld t0, 1800(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 1792(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 1864(a3)
	addi a5, zero, 0
	ld t0, 1808(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 1800(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 1792(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 1872(a3)
	addi a6, zero, 0
	ld t0, 1816(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 1808(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 1800(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 1792(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 1880(a3)
	addi a4, zero, 0
	ld t0, 1816(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 1808(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 1800(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 1888(a3)
	addi a5, zero, 0
	ld t0, 1816(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 1808(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 1896(a3)
	addi a6, zero, 0
	ld t0, 1816(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 1904(a3)
	addi a4, zero, 0
	sd a5, 1912(a3)
	addi a5, zero, 0
	j 25f
24:
	ld t3, 0(t4)
	ld t6, 8(t4)
	ld a1, 16(t4)
	ld a4, 24(t4)
	sd t3, 1792(a3)
	sd t6, 1800(a3)
	sd a1, 1808(a3)
	sd a4, 1816(a3)
	ld t3, 1792(a3)
	ld t4, 1800(a3)
	ld t5, 1808(a3)
	ld t6, 1816(a3)
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	sd a4, 1856(a3)
	addi a4, zero, 0
	mul a7, t3, t4
	mulhu t0, t3, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 1864(a3)
	addi a5, zero, 0
	mul a7, t3, t5
	mulhu t0, t3, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 1872(a3)
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
	sd a4, 1880(a3)
	addi a4, zero, 0
	mul a7, t4, t6
	mulhu t0, t4, t6
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 1888(a3)
	addi a5, zero, 0
	mul a7, t5, t6
	mulhu t0, t5, t6
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 1896(a3)
	addi a6, zero, 0
	sd a4, 1904(a3)
	addi a4, zero, 0
	sd a5, 1912(a3)
	addi a5, zero, 0
	addi a5, zero, 0
	addi a4, zero, 0
	srli a7, a5, 63
	ld a5, 1856(a3)
	slli a6, a5, 1
	or a6, a6, a7
	ld t3, 1792(a3)
	mul t0, t3, t3
	mulhu t3, t3, t3
	add a6, a6, t0
	sltu a7, a6, t0
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 1856(a3)
	srli a7, a5, 63
	ld a5, 1864(a3)
	slli a6, a5, 1
	or a6, a6, a7
	add a6, a6, t3
	sltu a7, a6, t3
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 1864(a3)
	srli a7, a5, 63
	ld a5, 1872(a3)
	slli a6, a5, 1
	or a6, a6, a7
	ld t3, 1800(a3)
	mul t0, t3, t3
	mulhu t3, t3, t3
	add a6, a6, t0
	sltu a7, a6, t0
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 1872(a3)
	srli a7, a5, 63
	ld a5, 1880(a3)
	slli a6, a5, 1
	or a6, a6, a7
	add a6, a6, t3
	sltu a7, a6, t3
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 1880(a3)
	srli a7, a5, 63
	ld a5, 1888(a3)
	slli a6, a5, 1
	or a6, a6, a7
	ld t3, 1808(a3)
	mul t0, t3, t3
	mulhu t3, t3, t3
	add a6, a6, t0
	sltu a7, a6, t0
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 1888(a3)
	srli a7, a5, 63
	ld a5, 1896(a3)
	slli a6, a5, 1
	or a6, a6, a7
	add a6, a6, t3
	sltu a7, a6, t3
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 1896(a3)
	srli a7, a5, 63
	ld a5, 1904(a3)
	slli a6, a5, 1
	or a6, a6, a7
	ld t3, 1816(a3)
	mul t0, t3, t3
	mulhu t3, t3, t3
	add a6, a6, t0
	sltu a7, a6, t0
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 1904(a3)
	srli a7, a5, 63
	ld a5, 1912(a3)
	slli a6, a5, 1
	or a6, a6, a7
	add a6, a6, t3
	sltu a7, a6, t3
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 1912(a3)
25:
	ld t3, 1856(a3)
	ld t4, 1864(a3)
	ld t5, 1872(a3)
	ld t6, 1880(a3)
	addi a2, zero, 0
	ld a1, 1888(a3)
	slli a4, t3, 32
	srli a5, t3, 32
	sub a6, t3, a4
	sltu a7, t3, a4
	sub t0, t3, a5
	sub a7, t0, a7
	add t4, t4, a4
	sltu t0, t4, a4
	add a5, a5, t0
	add t5, t5, a5
	sltu t0, t5, a5
	add t6, t6, a6
	sltu a4, t6, a6
	add t6, t6, t0
	sltu t0, t6, t0
	add t0, t0, a4
	add a7, a7, t0
	add a7, a7, a2
	add a1, a1, a7
	sltu a2, a1, a7
	ld t3, 1896(a3)
	slli a4, t4, 32
	srli a5, t4, 32
	sub a6, t4, a4
	sltu a7, t4, a4
	sub t0, t4, a5
	sub a7, t0, a7
	add t5, t5, a4
	sltu t0, t5, a4
	add a5, a5, t0
	add t6, t6, a5
	sltu t0, t6, a5
	add a1, a1, a6
	sltu a4, a1, a6
	add a1, a1, t0
	sltu t0, a1, t0
	add t0, t0, a4
	add a7, a7, t0
	add a7, a7, a2
	add t3, t3, a7
	sltu a2, t3, a7
	ld t4, 1904(a3)
	slli a4, t5, 32
	srli a5, t5, 32
	sub a6, t5, a4
	sltu a7, t5, a4
	sub t0, t5, a5
	sub a7, t0, a7
	add t6, t6, a4
	sltu t0, t6, a4
	add a5, a5, t0
	add a1, a1, a5
	sltu t0, a1, a5
	add t3, t3, a6
	sltu a4, t3, a6
	add t3, t3, t0
	sltu t0, t3, t0
	add t0, t0, a4
	add a7, a7, t0
	add a7, a7, a2
	add t4, t4, a7
	sltu a2, t4, a7
	ld t5, 1912(a3)
	slli a4, t6, 32
	srli a5, t6, 32
	sub a6, t6, a4
	sltu a7, t6, a4
	sub t0, t6, a5
	sub a7, t0, a7
	add a1, a1, a4
	sltu t0, a1, a4
	add a5, a5, t0
	add t3, t3, a5
	sltu t0, t3, a5
	add t4, t4, a6
	sltu a4, t4, a6
	add t4, t4, t0
	sltu t0, t4, t0
	add t0, t0, a4
	add a7, a7, t0
	add a7, a7, a2
	add t5, t5, a7
	sltu a2, t5, a7
	addi t6, a1, 1
	sltu a7, t6, a1
	addi t0, zero, -1
	slli t0, t0, 32
	add a4, t3, t0
	sltu a0, a4, t0
	add a4, a4, a7
	sltu a7, a4, a7
	add a7, a7, a0
	addi t0, zero, -1
	add a5, t4, t0
	sltu a0, a5, t0
	add a5, a5, a7
	sltu a7, a5, a7
	add a7, a7, a0
	addi t0, zero, -1
	srli t0, t0, 32
	addi t0, t0, -1
	add a6, t5, t0
	sltu a0, a6, t0
	add a6, a6, a7
	sltu a7, a6, a7
	add a7, a7, a0
	or a7, a7, a2
	addi t0, zero, 0
	sub t0, t0, a7
	xor t6, t6, a1
	and t6, t6, t0
	xor t6, t6, a1
	sd t6, 0(t2)
	xor a4, a4, t3
	and a4, a4, t0
	xor a4, a4, t3
	sd a4, 8(t2)
	xor a5, a5, t4
	and a5, a5, t0
	xor a5, a5, t4
	sd a5, 16(t2)
	xor a6, a6, t5
	and a6, a6, t0
	xor a6, a6, t5
	sd a6, 24(t2)
21:
	ret
	.option pop

vg_p256_add_mod_p:
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
	add a1, a1, a5
	sltu a2, a1, a5
	add t3, t3, a6
	sltu a5, t3, a6
	add t3, t3, a2
	sltu a2, t3, a2
	add a2, a2, a5
	add t4, t6, a7
	sltu a5, t4, a7
	add t4, t4, a2
	sltu a2, t4, a2
	add a2, a2, a5
	add t5, a4, t0
	sltu a5, t5, t0
	add t5, t5, a2
	sltu a2, t5, a2
	add a2, a2, a5
	addi t6, a1, 1
	sltu a7, t6, a1
	addi t0, zero, -1
	slli t0, t0, 32
	add a4, t3, t0
	sltu a0, a4, t0
	add a4, a4, a7
	sltu a7, a4, a7
	add a7, a7, a0
	addi t0, zero, -1
	add a5, t4, t0
	sltu a0, a5, t0
	add a5, a5, a7
	sltu a7, a5, a7
	add a7, a7, a0
	addi t0, zero, -1
	srli t0, t0, 32
	addi t0, t0, -1
	add a6, t5, t0
	sltu a0, a6, t0
	add a6, a6, a7
	sltu a7, a6, a7
	add a7, a7, a0
	or a7, a7, a2
	addi t0, zero, 0
	sub t0, t0, a7
	xor t6, t6, a1
	and t6, t6, t0
	xor t6, t6, a1
	sd t6, 0(t2)
	xor a4, a4, t3
	and a4, a4, t0
	xor a4, a4, t3
	sd a4, 8(t2)
	xor a5, a5, t4
	and a5, a5, t0
	xor a5, a5, t4
	sd a5, 16(t2)
	xor a6, a6, t5
	and a6, a6, t0
	xor a6, a6, t5
	sd a6, 24(t2)
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
	add a1, a1, a5
	sltu a2, a1, a5
	add t3, t3, a6
	sltu a5, t3, a6
	add t3, t3, a2
	sltu a2, t3, a2
	add a2, a2, a5
	add t4, t6, a7
	sltu a5, t4, a7
	add t4, t4, a2
	sltu a2, t4, a2
	add a2, a2, a5
	add t5, a4, t0
	sltu a5, t5, t0
	add t5, t5, a2
	sltu a2, t5, a2
	add a2, a2, a5
	addi t6, a1, 1
	sltu a7, t6, a1
	addi t0, zero, -1
	slli t0, t0, 32
	add a4, t3, t0
	sltu a0, a4, t0
	add a4, a4, a7
	sltu a7, a4, a7
	add a7, a7, a0
	addi t0, zero, -1
	add a5, t4, t0
	sltu a0, a5, t0
	add a5, a5, a7
	sltu a7, a5, a7
	add a7, a7, a0
	addi t0, zero, -1
	srli t0, t0, 32
	addi t0, t0, -1
	add a6, t5, t0
	sltu a0, a6, t0
	add a6, a6, a7
	sltu a7, a6, a7
	add a7, a7, a0
	or a7, a7, a2
	addi t0, zero, 0
	sub t0, t0, a7
	xor t6, t6, a1
	and t6, t6, t0
	xor t6, t6, a1
	sd t6, 0(t2)
	xor a4, a4, t3
	and a4, a4, t0
	xor a4, a4, t3
	sd a4, 8(t2)
	xor a5, a5, t4
	and a5, a5, t0
	xor a5, a5, t4
	sd a5, 16(t2)
	xor a6, a6, t5
	and a6, a6, t0
	xor a6, a6, t5
	sd a6, 24(t2)
21:
	ret
	.option pop

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

vg_p256_mul_mod_n:
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
	beq t4, t5, 22f
	ld t3, 0(t4)
	ld t6, 8(t4)
	ld a1, 16(t4)
	ld a4, 24(t4)
	sd t3, 1792(a3)
	sd t6, 1800(a3)
	sd a1, 1808(a3)
	sd a4, 1816(a3)
	ld t3, 0(t5)
	ld t6, 8(t5)
	ld a1, 16(t5)
	ld a4, 24(t5)
	sd t3, 1824(a3)
	sd t6, 1832(a3)
	sd a1, 1840(a3)
	sd a4, 1848(a3)
	ld t3, 1824(a3)
	ld t4, 1832(a3)
	ld t5, 1840(a3)
	ld t6, 1848(a3)
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	ld t0, 1792(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 1856(a3)
	addi a4, zero, 0
	ld t0, 1800(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 1792(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 1864(a3)
	addi a5, zero, 0
	ld t0, 1808(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 1800(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 1792(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 1872(a3)
	addi a6, zero, 0
	ld t0, 1816(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 1808(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 1800(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 1792(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 1880(a3)
	addi a4, zero, 0
	ld t0, 1816(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 1808(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 1800(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 1888(a3)
	addi a5, zero, 0
	ld t0, 1816(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 1808(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 1896(a3)
	addi a6, zero, 0
	ld t0, 1816(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 1904(a3)
	addi a4, zero, 0
	sd a5, 1912(a3)
	addi a5, zero, 0
	j 23f
22:
	ld t3, 0(t4)
	ld t6, 8(t4)
	ld a1, 16(t4)
	ld a4, 24(t4)
	sd t3, 1792(a3)
	sd t6, 1800(a3)
	sd a1, 1808(a3)
	sd a4, 1816(a3)
	ld t3, 1792(a3)
	ld t4, 1800(a3)
	ld t5, 1808(a3)
	ld t6, 1816(a3)
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	sd a4, 1856(a3)
	addi a4, zero, 0
	mul a7, t3, t4
	mulhu t0, t3, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 1864(a3)
	addi a5, zero, 0
	mul a7, t3, t5
	mulhu t0, t3, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 1872(a3)
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
	sd a4, 1880(a3)
	addi a4, zero, 0
	mul a7, t4, t6
	mulhu t0, t4, t6
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 1888(a3)
	addi a5, zero, 0
	mul a7, t5, t6
	mulhu t0, t5, t6
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 1896(a3)
	addi a6, zero, 0
	sd a4, 1904(a3)
	addi a4, zero, 0
	sd a5, 1912(a3)
	addi a5, zero, 0
	addi a5, zero, 0
	addi a4, zero, 0
	srli a7, a5, 63
	ld a5, 1856(a3)
	slli a6, a5, 1
	or a6, a6, a7
	ld t3, 1792(a3)
	mul t0, t3, t3
	mulhu t3, t3, t3
	add a6, a6, t0
	sltu a7, a6, t0
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 1856(a3)
	srli a7, a5, 63
	ld a5, 1864(a3)
	slli a6, a5, 1
	or a6, a6, a7
	add a6, a6, t3
	sltu a7, a6, t3
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 1864(a3)
	srli a7, a5, 63
	ld a5, 1872(a3)
	slli a6, a5, 1
	or a6, a6, a7
	ld t3, 1800(a3)
	mul t0, t3, t3
	mulhu t3, t3, t3
	add a6, a6, t0
	sltu a7, a6, t0
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 1872(a3)
	srli a7, a5, 63
	ld a5, 1880(a3)
	slli a6, a5, 1
	or a6, a6, a7
	add a6, a6, t3
	sltu a7, a6, t3
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 1880(a3)
	srli a7, a5, 63
	ld a5, 1888(a3)
	slli a6, a5, 1
	or a6, a6, a7
	ld t3, 1808(a3)
	mul t0, t3, t3
	mulhu t3, t3, t3
	add a6, a6, t0
	sltu a7, a6, t0
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 1888(a3)
	srli a7, a5, 63
	ld a5, 1896(a3)
	slli a6, a5, 1
	or a6, a6, a7
	add a6, a6, t3
	sltu a7, a6, t3
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 1896(a3)
	srli a7, a5, 63
	ld a5, 1904(a3)
	slli a6, a5, 1
	or a6, a6, a7
	ld t3, 1816(a3)
	mul t0, t3, t3
	mulhu t3, t3, t3
	add a6, a6, t0
	sltu a7, a6, t0
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 1904(a3)
	srli a7, a5, 63
	ld a5, 1912(a3)
	slli a6, a5, 1
	or a6, a6, a7
	add a6, a6, t3
	sltu a7, a6, t3
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 1912(a3)
23:
	ld t3, 1856(a3)
	ld t4, 1864(a3)
	ld t5, 1872(a3)
	ld t6, 1880(a3)
	addi a2, zero, 0
	ld a1, 1888(a3)
	lui t0, 838941
	addiw t0, t0, -1877
	slli t0, t0, 32
	lui a0, 974860
	addiw a0, a0, -945
	add t0, t0, a0
	mul t3, t3, t0
	lui a4, 998301
	addiw a4, a4, -1341
	slli a4, a4, 32
	lui a0, 1033778
	addiw a0, a0, 1361
	add a4, a4, a0
	mulhu a4, t3, a4
	lui a5, 773744
	addiw a5, a5, -1362
	slli a5, a5, 32
	lui a0, 684410
	addiw a0, a0, -380
	add a5, a5, a0
	mulhu a6, t3, a5
	mul a5, t3, a5
	addi a0, zero, 0
	sltu a0, a0, t3
	add a4, a4, a0
	add a5, a5, a4
	sltu a7, a5, a4
	add a6, a6, a7
	add t4, t4, a5
	sltu a0, t4, a5
	add t5, t5, a6
	sltu a7, t5, a6
	add t5, t5, a0
	sltu a0, t5, a0
	add a0, a0, a7
	slli a4, t3, 32
	srli a5, t3, 32
	sub a6, t3, a4
	sltu a7, t3, a4
	sub t0, t3, a5
	sub a7, t0, a7
	addi t0, zero, 0
	sub a4, t0, t3
	sltu t0, t0, t3
	sltu a5, a6, t0
	sub a6, a6, t0
	sub a7, a7, a5
	add t5, t5, a4
	sltu t0, t5, a4
	add t0, t0, a0
	add t6, t6, t0
	sltu a0, t6, t0
	add t6, t6, a6
	sltu a5, t6, a6
	add a0, a0, a5
	add a7, a7, a0
	add a7, a7, a2
	add a1, a1, a7
	sltu a2, a1, a7
	ld t3, 1896(a3)
	lui t0, 838941
	addiw t0, t0, -1877
	slli t0, t0, 32
	lui a0, 974860
	addiw a0, a0, -945
	add t0, t0, a0
	mul t4, t4, t0
	lui a4, 998301
	addiw a4, a4, -1341
	slli a4, a4, 32
	lui a0, 1033778
	addiw a0, a0, 1361
	add a4, a4, a0
	mulhu a4, t4, a4
	lui a5, 773744
	addiw a5, a5, -1362
	slli a5, a5, 32
	lui a0, 684410
	addiw a0, a0, -380
	add a5, a5, a0
	mulhu a6, t4, a5
	mul a5, t4, a5
	addi a0, zero, 0
	sltu a0, a0, t4
	add a4, a4, a0
	add a5, a5, a4
	sltu a7, a5, a4
	add a6, a6, a7
	add t5, t5, a5
	sltu a0, t5, a5
	add t6, t6, a6
	sltu a7, t6, a6
	add t6, t6, a0
	sltu a0, t6, a0
	add a0, a0, a7
	slli a4, t4, 32
	srli a5, t4, 32
	sub a6, t4, a4
	sltu a7, t4, a4
	sub t0, t4, a5
	sub a7, t0, a7
	addi t0, zero, 0
	sub a4, t0, t4
	sltu t0, t0, t4
	sltu a5, a6, t0
	sub a6, a6, t0
	sub a7, a7, a5
	add t6, t6, a4
	sltu t0, t6, a4
	add t0, t0, a0
	add a1, a1, t0
	sltu a0, a1, t0
	add a1, a1, a6
	sltu a5, a1, a6
	add a0, a0, a5
	add a7, a7, a0
	add a7, a7, a2
	add t3, t3, a7
	sltu a2, t3, a7
	ld t4, 1904(a3)
	lui t0, 838941
	addiw t0, t0, -1877
	slli t0, t0, 32
	lui a0, 974860
	addiw a0, a0, -945
	add t0, t0, a0
	mul t5, t5, t0
	lui a4, 998301
	addiw a4, a4, -1341
	slli a4, a4, 32
	lui a0, 1033778
	addiw a0, a0, 1361
	add a4, a4, a0
	mulhu a4, t5, a4
	lui a5, 773744
	addiw a5, a5, -1362
	slli a5, a5, 32
	lui a0, 684410
	addiw a0, a0, -380
	add a5, a5, a0
	mulhu a6, t5, a5
	mul a5, t5, a5
	addi a0, zero, 0
	sltu a0, a0, t5
	add a4, a4, a0
	add a5, a5, a4
	sltu a7, a5, a4
	add a6, a6, a7
	add t6, t6, a5
	sltu a0, t6, a5
	add a1, a1, a6
	sltu a7, a1, a6
	add a1, a1, a0
	sltu a0, a1, a0
	add a0, a0, a7
	slli a4, t5, 32
	srli a5, t5, 32
	sub a6, t5, a4
	sltu a7, t5, a4
	sub t0, t5, a5
	sub a7, t0, a7
	addi t0, zero, 0
	sub a4, t0, t5
	sltu t0, t0, t5
	sltu a5, a6, t0
	sub a6, a6, t0
	sub a7, a7, a5
	add a1, a1, a4
	sltu t0, a1, a4
	add t0, t0, a0
	add t3, t3, t0
	sltu a0, t3, t0
	add t3, t3, a6
	sltu a5, t3, a6
	add a0, a0, a5
	add a7, a7, a0
	add a7, a7, a2
	add t4, t4, a7
	sltu a2, t4, a7
	ld t5, 1912(a3)
	lui t0, 838941
	addiw t0, t0, -1877
	slli t0, t0, 32
	lui a0, 974860
	addiw a0, a0, -945
	add t0, t0, a0
	mul t6, t6, t0
	lui a4, 998301
	addiw a4, a4, -1341
	slli a4, a4, 32
	lui a0, 1033778
	addiw a0, a0, 1361
	add a4, a4, a0
	mulhu a4, t6, a4
	lui a5, 773744
	addiw a5, a5, -1362
	slli a5, a5, 32
	lui a0, 684410
	addiw a0, a0, -380
	add a5, a5, a0
	mulhu a6, t6, a5
	mul a5, t6, a5
	addi a0, zero, 0
	sltu a0, a0, t6
	add a4, a4, a0
	add a5, a5, a4
	sltu a7, a5, a4
	add a6, a6, a7
	add a1, a1, a5
	sltu a0, a1, a5
	add t3, t3, a6
	sltu a7, t3, a6
	add t3, t3, a0
	sltu a0, t3, a0
	add a0, a0, a7
	slli a4, t6, 32
	srli a5, t6, 32
	sub a6, t6, a4
	sltu a7, t6, a4
	sub t0, t6, a5
	sub a7, t0, a7
	addi t0, zero, 0
	sub a4, t0, t6
	sltu t0, t0, t6
	sltu a5, a6, t0
	sub a6, a6, t0
	sub a7, a7, a5
	add t3, t3, a4
	sltu t0, t3, a4
	add t0, t0, a0
	add t4, t4, t0
	sltu a0, t4, t0
	add t4, t4, a6
	sltu a5, t4, a6
	add a0, a0, a5
	add a7, a7, a0
	add a7, a7, a2
	add t5, t5, a7
	sltu a2, t5, a7
	lui t0, 50275
	addiw t0, t0, 1341
	slli t0, t0, 32
	lui a0, 14798
	addiw a0, a0, -1361
	add t0, t0, a0
	add t6, a1, t0
	sltu a7, t6, t0
	lui t0, 274832
	addiw t0, t0, 1362
	slli t0, t0, 32
	lui a0, 364166
	addiw a0, a0, 379
	add t0, t0, a0
	add a4, t3, t0
	sltu a0, a4, t0
	add a4, a4, a7
	sltu a7, a4, a7
	add a7, a7, a0
	add a5, t4, a7
	sltu a7, a5, a7
	addi t0, zero, -1
	srli t0, t0, 32
	add a6, t5, t0
	sltu a0, a6, t0
	add a6, a6, a7
	sltu a7, a6, a7
	add a7, a7, a0
	or a7, a7, a2
	addi t0, zero, 0
	sub t0, t0, a7
	xor t6, t6, a1
	and t6, t6, t0
	xor t6, t6, a1
	sd t6, 0(t2)
	xor a4, a4, t3
	and a4, a4, t0
	xor a4, a4, t3
	sd a4, 8(t2)
	xor a5, a5, t4
	and a5, a5, t0
	xor a5, a5, t4
	sd a5, 16(t2)
	xor a6, a6, t5
	and a6, a6, t0
	xor a6, a6, t5
	sd a6, 24(t2)
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
	beq t4, t5, 24f
	ld t3, 0(t4)
	ld t6, 8(t4)
	ld a1, 16(t4)
	ld a4, 24(t4)
	sd t3, 1792(a3)
	sd t6, 1800(a3)
	sd a1, 1808(a3)
	sd a4, 1816(a3)
	ld t3, 0(t5)
	ld t6, 8(t5)
	ld a1, 16(t5)
	ld a4, 24(t5)
	sd t3, 1824(a3)
	sd t6, 1832(a3)
	sd a1, 1840(a3)
	sd a4, 1848(a3)
	ld t3, 1824(a3)
	ld t4, 1832(a3)
	ld t5, 1840(a3)
	ld t6, 1848(a3)
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	ld t0, 1792(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 1856(a3)
	addi a4, zero, 0
	ld t0, 1800(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 1792(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 1864(a3)
	addi a5, zero, 0
	ld t0, 1808(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 1800(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 1792(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 1872(a3)
	addi a6, zero, 0
	ld t0, 1816(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 1808(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 1800(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 1792(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 1880(a3)
	addi a4, zero, 0
	ld t0, 1816(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 1808(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 1800(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 1888(a3)
	addi a5, zero, 0
	ld t0, 1816(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 1808(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 1896(a3)
	addi a6, zero, 0
	ld t0, 1816(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 1904(a3)
	addi a4, zero, 0
	sd a5, 1912(a3)
	addi a5, zero, 0
	j 25f
24:
	ld t3, 0(t4)
	ld t6, 8(t4)
	ld a1, 16(t4)
	ld a4, 24(t4)
	sd t3, 1792(a3)
	sd t6, 1800(a3)
	sd a1, 1808(a3)
	sd a4, 1816(a3)
	ld t3, 1792(a3)
	ld t4, 1800(a3)
	ld t5, 1808(a3)
	ld t6, 1816(a3)
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	sd a4, 1856(a3)
	addi a4, zero, 0
	mul a7, t3, t4
	mulhu t0, t3, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 1864(a3)
	addi a5, zero, 0
	mul a7, t3, t5
	mulhu t0, t3, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 1872(a3)
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
	sd a4, 1880(a3)
	addi a4, zero, 0
	mul a7, t4, t6
	mulhu t0, t4, t6
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 1888(a3)
	addi a5, zero, 0
	mul a7, t5, t6
	mulhu t0, t5, t6
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 1896(a3)
	addi a6, zero, 0
	sd a4, 1904(a3)
	addi a4, zero, 0
	sd a5, 1912(a3)
	addi a5, zero, 0
	addi a5, zero, 0
	addi a4, zero, 0
	srli a7, a5, 63
	ld a5, 1856(a3)
	slli a6, a5, 1
	or a6, a6, a7
	ld t3, 1792(a3)
	mul t0, t3, t3
	mulhu t3, t3, t3
	add a6, a6, t0
	sltu a7, a6, t0
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 1856(a3)
	srli a7, a5, 63
	ld a5, 1864(a3)
	slli a6, a5, 1
	or a6, a6, a7
	add a6, a6, t3
	sltu a7, a6, t3
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 1864(a3)
	srli a7, a5, 63
	ld a5, 1872(a3)
	slli a6, a5, 1
	or a6, a6, a7
	ld t3, 1800(a3)
	mul t0, t3, t3
	mulhu t3, t3, t3
	add a6, a6, t0
	sltu a7, a6, t0
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 1872(a3)
	srli a7, a5, 63
	ld a5, 1880(a3)
	slli a6, a5, 1
	or a6, a6, a7
	add a6, a6, t3
	sltu a7, a6, t3
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 1880(a3)
	srli a7, a5, 63
	ld a5, 1888(a3)
	slli a6, a5, 1
	or a6, a6, a7
	ld t3, 1808(a3)
	mul t0, t3, t3
	mulhu t3, t3, t3
	add a6, a6, t0
	sltu a7, a6, t0
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 1888(a3)
	srli a7, a5, 63
	ld a5, 1896(a3)
	slli a6, a5, 1
	or a6, a6, a7
	add a6, a6, t3
	sltu a7, a6, t3
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 1896(a3)
	srli a7, a5, 63
	ld a5, 1904(a3)
	slli a6, a5, 1
	or a6, a6, a7
	ld t3, 1816(a3)
	mul t0, t3, t3
	mulhu t3, t3, t3
	add a6, a6, t0
	sltu a7, a6, t0
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 1904(a3)
	srli a7, a5, 63
	ld a5, 1912(a3)
	slli a6, a5, 1
	or a6, a6, a7
	add a6, a6, t3
	sltu a7, a6, t3
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 1912(a3)
25:
	ld t3, 1856(a3)
	ld t4, 1864(a3)
	ld t5, 1872(a3)
	ld t6, 1880(a3)
	addi a2, zero, 0
	ld a1, 1888(a3)
	lui t0, 838941
	addiw t0, t0, -1877
	slli t0, t0, 32
	lui a0, 974860
	addiw a0, a0, -945
	add t0, t0, a0
	mul t3, t3, t0
	lui a4, 998301
	addiw a4, a4, -1341
	slli a4, a4, 32
	lui a0, 1033778
	addiw a0, a0, 1361
	add a4, a4, a0
	mulhu a4, t3, a4
	lui a5, 773744
	addiw a5, a5, -1362
	slli a5, a5, 32
	lui a0, 684410
	addiw a0, a0, -380
	add a5, a5, a0
	mulhu a6, t3, a5
	mul a5, t3, a5
	addi a0, zero, 0
	sltu a0, a0, t3
	add a4, a4, a0
	add a5, a5, a4
	sltu a7, a5, a4
	add a6, a6, a7
	add t4, t4, a5
	sltu a0, t4, a5
	add t5, t5, a6
	sltu a7, t5, a6
	add t5, t5, a0
	sltu a0, t5, a0
	add a0, a0, a7
	slli a4, t3, 32
	srli a5, t3, 32
	sub a6, t3, a4
	sltu a7, t3, a4
	sub t0, t3, a5
	sub a7, t0, a7
	addi t0, zero, 0
	sub a4, t0, t3
	sltu t0, t0, t3
	sltu a5, a6, t0
	sub a6, a6, t0
	sub a7, a7, a5
	add t5, t5, a4
	sltu t0, t5, a4
	add t0, t0, a0
	add t6, t6, t0
	sltu a0, t6, t0
	add t6, t6, a6
	sltu a5, t6, a6
	add a0, a0, a5
	add a7, a7, a0
	add a7, a7, a2
	add a1, a1, a7
	sltu a2, a1, a7
	ld t3, 1896(a3)
	lui t0, 838941
	addiw t0, t0, -1877
	slli t0, t0, 32
	lui a0, 974860
	addiw a0, a0, -945
	add t0, t0, a0
	mul t4, t4, t0
	lui a4, 998301
	addiw a4, a4, -1341
	slli a4, a4, 32
	lui a0, 1033778
	addiw a0, a0, 1361
	add a4, a4, a0
	mulhu a4, t4, a4
	lui a5, 773744
	addiw a5, a5, -1362
	slli a5, a5, 32
	lui a0, 684410
	addiw a0, a0, -380
	add a5, a5, a0
	mulhu a6, t4, a5
	mul a5, t4, a5
	addi a0, zero, 0
	sltu a0, a0, t4
	add a4, a4, a0
	add a5, a5, a4
	sltu a7, a5, a4
	add a6, a6, a7
	add t5, t5, a5
	sltu a0, t5, a5
	add t6, t6, a6
	sltu a7, t6, a6
	add t6, t6, a0
	sltu a0, t6, a0
	add a0, a0, a7
	slli a4, t4, 32
	srli a5, t4, 32
	sub a6, t4, a4
	sltu a7, t4, a4
	sub t0, t4, a5
	sub a7, t0, a7
	addi t0, zero, 0
	sub a4, t0, t4
	sltu t0, t0, t4
	sltu a5, a6, t0
	sub a6, a6, t0
	sub a7, a7, a5
	add t6, t6, a4
	sltu t0, t6, a4
	add t0, t0, a0
	add a1, a1, t0
	sltu a0, a1, t0
	add a1, a1, a6
	sltu a5, a1, a6
	add a0, a0, a5
	add a7, a7, a0
	add a7, a7, a2
	add t3, t3, a7
	sltu a2, t3, a7
	ld t4, 1904(a3)
	lui t0, 838941
	addiw t0, t0, -1877
	slli t0, t0, 32
	lui a0, 974860
	addiw a0, a0, -945
	add t0, t0, a0
	mul t5, t5, t0
	lui a4, 998301
	addiw a4, a4, -1341
	slli a4, a4, 32
	lui a0, 1033778
	addiw a0, a0, 1361
	add a4, a4, a0
	mulhu a4, t5, a4
	lui a5, 773744
	addiw a5, a5, -1362
	slli a5, a5, 32
	lui a0, 684410
	addiw a0, a0, -380
	add a5, a5, a0
	mulhu a6, t5, a5
	mul a5, t5, a5
	addi a0, zero, 0
	sltu a0, a0, t5
	add a4, a4, a0
	add a5, a5, a4
	sltu a7, a5, a4
	add a6, a6, a7
	add t6, t6, a5
	sltu a0, t6, a5
	add a1, a1, a6
	sltu a7, a1, a6
	add a1, a1, a0
	sltu a0, a1, a0
	add a0, a0, a7
	slli a4, t5, 32
	srli a5, t5, 32
	sub a6, t5, a4
	sltu a7, t5, a4
	sub t0, t5, a5
	sub a7, t0, a7
	addi t0, zero, 0
	sub a4, t0, t5
	sltu t0, t0, t5
	sltu a5, a6, t0
	sub a6, a6, t0
	sub a7, a7, a5
	add a1, a1, a4
	sltu t0, a1, a4
	add t0, t0, a0
	add t3, t3, t0
	sltu a0, t3, t0
	add t3, t3, a6
	sltu a5, t3, a6
	add a0, a0, a5
	add a7, a7, a0
	add a7, a7, a2
	add t4, t4, a7
	sltu a2, t4, a7
	ld t5, 1912(a3)
	lui t0, 838941
	addiw t0, t0, -1877
	slli t0, t0, 32
	lui a0, 974860
	addiw a0, a0, -945
	add t0, t0, a0
	mul t6, t6, t0
	lui a4, 998301
	addiw a4, a4, -1341
	slli a4, a4, 32
	lui a0, 1033778
	addiw a0, a0, 1361
	add a4, a4, a0
	mulhu a4, t6, a4
	lui a5, 773744
	addiw a5, a5, -1362
	slli a5, a5, 32
	lui a0, 684410
	addiw a0, a0, -380
	add a5, a5, a0
	mulhu a6, t6, a5
	mul a5, t6, a5
	addi a0, zero, 0
	sltu a0, a0, t6
	add a4, a4, a0
	add a5, a5, a4
	sltu a7, a5, a4
	add a6, a6, a7
	add a1, a1, a5
	sltu a0, a1, a5
	add t3, t3, a6
	sltu a7, t3, a6
	add t3, t3, a0
	sltu a0, t3, a0
	add a0, a0, a7
	slli a4, t6, 32
	srli a5, t6, 32
	sub a6, t6, a4
	sltu a7, t6, a4
	sub t0, t6, a5
	sub a7, t0, a7
	addi t0, zero, 0
	sub a4, t0, t6
	sltu t0, t0, t6
	sltu a5, a6, t0
	sub a6, a6, t0
	sub a7, a7, a5
	add t3, t3, a4
	sltu t0, t3, a4
	add t0, t0, a0
	add t4, t4, t0
	sltu a0, t4, t0
	add t4, t4, a6
	sltu a5, t4, a6
	add a0, a0, a5
	add a7, a7, a0
	add a7, a7, a2
	add t5, t5, a7
	sltu a2, t5, a7
	lui t0, 50275
	addiw t0, t0, 1341
	slli t0, t0, 32
	lui a0, 14798
	addiw a0, a0, -1361
	add t0, t0, a0
	add t6, a1, t0
	sltu a7, t6, t0
	lui t0, 274832
	addiw t0, t0, 1362
	slli t0, t0, 32
	lui a0, 364166
	addiw a0, a0, 379
	add t0, t0, a0
	add a4, t3, t0
	sltu a0, a4, t0
	add a4, a4, a7
	sltu a7, a4, a7
	add a7, a7, a0
	add a5, t4, a7
	sltu a7, a5, a7
	addi t0, zero, -1
	srli t0, t0, 32
	add a6, t5, t0
	sltu a0, a6, t0
	add a6, a6, a7
	sltu a7, a6, a7
	add a7, a7, a0
	or a7, a7, a2
	addi t0, zero, 0
	sub t0, t0, a7
	xor t6, t6, a1
	and t6, t6, t0
	xor t6, t6, a1
	sd t6, 0(t2)
	xor a4, a4, t3
	and a4, a4, t0
	xor a4, a4, t3
	sd a4, 8(t2)
	xor a5, a5, t4
	and a5, a5, t0
	xor a5, a5, t4
	sd a5, 16(t2)
	xor a6, a6, t5
	and a6, a6, t0
	xor a6, a6, t5
	sd a6, 24(t2)
21:
	ret
	.option pop

vg_p256_add_mod_n:
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
	add a1, a1, a5
	sltu a2, a1, a5
	add t3, t3, a6
	sltu a5, t3, a6
	add t3, t3, a2
	sltu a2, t3, a2
	add a2, a2, a5
	add t4, t6, a7
	sltu a5, t4, a7
	add t4, t4, a2
	sltu a2, t4, a2
	add a2, a2, a5
	add t5, a4, t0
	sltu a5, t5, t0
	add t5, t5, a2
	sltu a2, t5, a2
	add a2, a2, a5
	lui t0, 50275
	addiw t0, t0, 1341
	slli t0, t0, 32
	lui a0, 14798
	addiw a0, a0, -1361
	add t0, t0, a0
	add t6, a1, t0
	sltu a7, t6, t0
	lui t0, 274832
	addiw t0, t0, 1362
	slli t0, t0, 32
	lui a0, 364166
	addiw a0, a0, 379
	add t0, t0, a0
	add a4, t3, t0
	sltu a0, a4, t0
	add a4, a4, a7
	sltu a7, a4, a7
	add a7, a7, a0
	add a5, t4, a7
	sltu a7, a5, a7
	addi t0, zero, -1
	srli t0, t0, 32
	add a6, t5, t0
	sltu a0, a6, t0
	add a6, a6, a7
	sltu a7, a6, a7
	add a7, a7, a0
	or a7, a7, a2
	addi t0, zero, 0
	sub t0, t0, a7
	xor t6, t6, a1
	and t6, t6, t0
	xor t6, t6, a1
	sd t6, 0(t2)
	xor a4, a4, t3
	and a4, a4, t0
	xor a4, a4, t3
	sd a4, 8(t2)
	xor a5, a5, t4
	and a5, a5, t0
	xor a5, a5, t4
	sd a5, 16(t2)
	xor a6, a6, t5
	and a6, a6, t0
	xor a6, a6, t5
	sd a6, 24(t2)
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
	add a1, a1, a5
	sltu a2, a1, a5
	add t3, t3, a6
	sltu a5, t3, a6
	add t3, t3, a2
	sltu a2, t3, a2
	add a2, a2, a5
	add t4, t6, a7
	sltu a5, t4, a7
	add t4, t4, a2
	sltu a2, t4, a2
	add a2, a2, a5
	add t5, a4, t0
	sltu a5, t5, t0
	add t5, t5, a2
	sltu a2, t5, a2
	add a2, a2, a5
	lui t0, 50275
	addiw t0, t0, 1341
	slli t0, t0, 32
	lui a0, 14798
	addiw a0, a0, -1361
	add t0, t0, a0
	add t6, a1, t0
	sltu a7, t6, t0
	lui t0, 274832
	addiw t0, t0, 1362
	slli t0, t0, 32
	lui a0, 364166
	addiw a0, a0, 379
	add t0, t0, a0
	add a4, t3, t0
	sltu a0, a4, t0
	add a4, a4, a7
	sltu a7, a4, a7
	add a7, a7, a0
	add a5, t4, a7
	sltu a7, a5, a7
	addi t0, zero, -1
	srli t0, t0, 32
	add a6, t5, t0
	sltu a0, a6, t0
	add a6, a6, a7
	sltu a7, a6, a7
	add a7, a7, a0
	or a7, a7, a2
	addi t0, zero, 0
	sub t0, t0, a7
	xor t6, t6, a1
	and t6, t6, t0
	xor t6, t6, a1
	sd t6, 0(t2)
	xor a4, a4, t3
	and a4, a4, t0
	xor a4, a4, t3
	sd a4, 8(t2)
	xor a5, a5, t4
	and a5, a5, t0
	xor a5, a5, t4
	sd a5, 16(t2)
	xor a6, a6, t5
	and a6, a6, t0
	xor a6, a6, t5
	sd a6, 24(t2)
21:
	ret
	.option pop

vg_p256_sub_mod_n:
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
	lui t6, 998301
	addiw t6, t6, -1341
	slli t6, t6, 32
	lui a0, 1033778
	addiw a0, a0, 1361
	add t6, t6, a0
	and t6, t6, t0
	add a1, a1, t6
	sltu a7, a1, t6
	sd a1, 0(t2)
	lui t6, 773744
	addiw t6, t6, -1362
	slli t6, t6, 32
	lui a0, 684410
	addiw a0, a0, -380
	add t6, t6, a0
	and t6, t6, t0
	add t3, t3, t6
	sltu a0, t3, t6
	add t3, t3, a7
	sltu a7, t3, a7
	add a7, a7, a0
	sd t3, 8(t2)
	addi t6, t0, 0
	add t4, t4, t6
	sltu a0, t4, t6
	add t4, t4, a7
	sltu a7, t4, a7
	add a7, a7, a0
	sd t4, 16(t2)
	slli t6, t0, 32
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
	lui t6, 998301
	addiw t6, t6, -1341
	slli t6, t6, 32
	lui a0, 1033778
	addiw a0, a0, 1361
	add t6, t6, a0
	and t6, t6, t0
	add a1, a1, t6
	sltu a7, a1, t6
	sd a1, 0(t2)
	lui t6, 773744
	addiw t6, t6, -1362
	slli t6, t6, 32
	lui a0, 684410
	addiw a0, a0, -380
	add t6, t6, a0
	and t6, t6, t0
	add t3, t3, t6
	sltu a0, t3, t6
	add t3, t3, a7
	sltu a7, t3, a7
	add a7, a7, a0
	sd t3, 8(t2)
	addi t6, t0, 0
	add t4, t4, t6
	sltu a0, t4, t6
	add t4, t4, a7
	sltu a7, t4, a7
	add a7, a7, a0
	sd t4, 16(t2)
	slli t6, t0, 32
	add t5, t5, t6
	sltu a0, t5, t6
	add t5, t5, a7
	sltu a7, t5, a7
	add a7, a7, a0
	sd t5, 24(t2)
21:
	ret
	.option pop
