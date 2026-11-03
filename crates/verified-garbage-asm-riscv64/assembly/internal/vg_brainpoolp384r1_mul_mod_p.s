// The functions of `src/internal/vg_brainpoolp384r1_mul_mod_p.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_brainpoolp384r1_mul_mod_p:
	.option push
	.option arch, +m, +c
	add t2, a0, a1
	add t4, a0, a2
	add t5, a0, a3
	addi a3, a0, 2047
	addi a3, a3, 1
	beq t4, t5, 20f
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
	j 21f
20:
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
21:
	ld t5, 1760(a3)
	ld t6, 1768(a3)
	ld t3, 1776(a3)
	ld t4, 1784(a3)
	ld a1, 1792(a3)
	ld a0, 1800(a3)
	addi a2, zero, 0
	lui t0, 632555
	addiw t0, t0, -1683
	slli t0, t0, 32
	lui a5, 961005
	addiw a5, a5, -2011
	add t0, t0, a5
	mul t5, t5, t0
	lui a4, 554096
	addiw a4, a4, 19
	slli a4, a4, 32
	lui a5, 200831
	addiw a5, a5, -941
	add a4, a4, a5
	mulhu a4, t5, a4
	addi a5, zero, 0
	sltu a5, a5, t5
	add a4, a4, a5
	lui a6, 707898
	addiw a6, a6, 1834
	slli a6, a6, 32
	lui a7, 590290
	addiw a7, a7, -1423
	add a6, a6, a7
	mul a5, t5, a6
	mulhu a6, t5, a6
	add a5, a5, a4
	sltu a7, a5, a4
	add a6, a6, a7
	add t6, t6, a5
	sltu a7, t6, a5
	add a4, a6, a7
	lui a6, 76574
	addiw a6, a6, -1511
	slli a6, a6, 32
	lui a7, 523121
	addiw a7, a7, 291
	add a6, a6, a7
	mul a5, t5, a6
	mulhu a6, t5, a6
	add a5, a5, a4
	sltu a7, a5, a4
	add a6, a6, a7
	add t3, t3, a5
	sltu a7, t3, a5
	add a4, a6, a7
	lui a6, 86775
	addiw a6, a6, 266
	slli a6, a6, 32
	lui a7, 972101
	addiw a7, a7, 1716
	add a6, a6, a7
	mul a5, t5, a6
	mulhu a6, t5, a6
	add a5, a5, a4
	sltu a7, a5, a4
	add a6, a6, a7
	add t4, t4, a5
	sltu a7, t4, a5
	add a4, a6, a7
	lui a6, 62935
	addiw a6, a6, -130
	slli a6, a6, 32
	lui a7, 331364
	addiw a7, a7, 479
	add a6, a6, a7
	mul a5, t5, a6
	mulhu a6, t5, a6
	add a5, a5, a4
	sltu a7, a5, a4
	add a6, a6, a7
	add a1, a1, a5
	sltu a7, a1, a5
	add a4, a6, a7
	lui a6, 576402
	addiw a6, a6, -381
	slli a6, a6, 32
	lui a7, 668551
	addiw a7, a7, -728
	add a6, a6, a7
	mul a5, t5, a6
	mulhu a6, t5, a6
	add a5, a5, a4
	sltu a7, a5, a4
	add a6, a6, a7
	add a0, a0, a5
	sltu a7, a0, a5
	add a4, a6, a7
	ld t5, 1808(a3)
	add t5, t5, a4
	sltu a7, t5, a4
	add t5, t5, a2
	sltu a2, t5, a2
	add a2, a2, a7
	lui t0, 632555
	addiw t0, t0, -1683
	slli t0, t0, 32
	lui a5, 961005
	addiw a5, a5, -2011
	add t0, t0, a5
	mul t6, t6, t0
	lui a4, 554096
	addiw a4, a4, 19
	slli a4, a4, 32
	lui a5, 200831
	addiw a5, a5, -941
	add a4, a4, a5
	mulhu a4, t6, a4
	addi a5, zero, 0
	sltu a5, a5, t6
	add a4, a4, a5
	lui a6, 707898
	addiw a6, a6, 1834
	slli a6, a6, 32
	lui a7, 590290
	addiw a7, a7, -1423
	add a6, a6, a7
	mul a5, t6, a6
	mulhu a6, t6, a6
	add a5, a5, a4
	sltu a7, a5, a4
	add a6, a6, a7
	add t3, t3, a5
	sltu a7, t3, a5
	add a4, a6, a7
	lui a6, 76574
	addiw a6, a6, -1511
	slli a6, a6, 32
	lui a7, 523121
	addiw a7, a7, 291
	add a6, a6, a7
	mul a5, t6, a6
	mulhu a6, t6, a6
	add a5, a5, a4
	sltu a7, a5, a4
	add a6, a6, a7
	add t4, t4, a5
	sltu a7, t4, a5
	add a4, a6, a7
	lui a6, 86775
	addiw a6, a6, 266
	slli a6, a6, 32
	lui a7, 972101
	addiw a7, a7, 1716
	add a6, a6, a7
	mul a5, t6, a6
	mulhu a6, t6, a6
	add a5, a5, a4
	sltu a7, a5, a4
	add a6, a6, a7
	add a1, a1, a5
	sltu a7, a1, a5
	add a4, a6, a7
	lui a6, 62935
	addiw a6, a6, -130
	slli a6, a6, 32
	lui a7, 331364
	addiw a7, a7, 479
	add a6, a6, a7
	mul a5, t6, a6
	mulhu a6, t6, a6
	add a5, a5, a4
	sltu a7, a5, a4
	add a6, a6, a7
	add a0, a0, a5
	sltu a7, a0, a5
	add a4, a6, a7
	lui a6, 576402
	addiw a6, a6, -381
	slli a6, a6, 32
	lui a7, 668551
	addiw a7, a7, -728
	add a6, a6, a7
	mul a5, t6, a6
	mulhu a6, t6, a6
	add a5, a5, a4
	sltu a7, a5, a4
	add a6, a6, a7
	add t5, t5, a5
	sltu a7, t5, a5
	add a4, a6, a7
	ld t6, 1816(a3)
	add t6, t6, a4
	sltu a7, t6, a4
	add t6, t6, a2
	sltu a2, t6, a2
	add a2, a2, a7
	lui t0, 632555
	addiw t0, t0, -1683
	slli t0, t0, 32
	lui a5, 961005
	addiw a5, a5, -2011
	add t0, t0, a5
	mul t3, t3, t0
	lui a4, 554096
	addiw a4, a4, 19
	slli a4, a4, 32
	lui a5, 200831
	addiw a5, a5, -941
	add a4, a4, a5
	mulhu a4, t3, a4
	addi a5, zero, 0
	sltu a5, a5, t3
	add a4, a4, a5
	lui a6, 707898
	addiw a6, a6, 1834
	slli a6, a6, 32
	lui a7, 590290
	addiw a7, a7, -1423
	add a6, a6, a7
	mul a5, t3, a6
	mulhu a6, t3, a6
	add a5, a5, a4
	sltu a7, a5, a4
	add a6, a6, a7
	add t4, t4, a5
	sltu a7, t4, a5
	add a4, a6, a7
	lui a6, 76574
	addiw a6, a6, -1511
	slli a6, a6, 32
	lui a7, 523121
	addiw a7, a7, 291
	add a6, a6, a7
	mul a5, t3, a6
	mulhu a6, t3, a6
	add a5, a5, a4
	sltu a7, a5, a4
	add a6, a6, a7
	add a1, a1, a5
	sltu a7, a1, a5
	add a4, a6, a7
	lui a6, 86775
	addiw a6, a6, 266
	slli a6, a6, 32
	lui a7, 972101
	addiw a7, a7, 1716
	add a6, a6, a7
	mul a5, t3, a6
	mulhu a6, t3, a6
	add a5, a5, a4
	sltu a7, a5, a4
	add a6, a6, a7
	add a0, a0, a5
	sltu a7, a0, a5
	add a4, a6, a7
	lui a6, 62935
	addiw a6, a6, -130
	slli a6, a6, 32
	lui a7, 331364
	addiw a7, a7, 479
	add a6, a6, a7
	mul a5, t3, a6
	mulhu a6, t3, a6
	add a5, a5, a4
	sltu a7, a5, a4
	add a6, a6, a7
	add t5, t5, a5
	sltu a7, t5, a5
	add a4, a6, a7
	lui a6, 576402
	addiw a6, a6, -381
	slli a6, a6, 32
	lui a7, 668551
	addiw a7, a7, -728
	add a6, a6, a7
	mul a5, t3, a6
	mulhu a6, t3, a6
	add a5, a5, a4
	sltu a7, a5, a4
	add a6, a6, a7
	add t6, t6, a5
	sltu a7, t6, a5
	add a4, a6, a7
	ld t3, 1824(a3)
	add t3, t3, a4
	sltu a7, t3, a4
	add t3, t3, a2
	sltu a2, t3, a2
	add a2, a2, a7
	lui t0, 632555
	addiw t0, t0, -1683
	slli t0, t0, 32
	lui a5, 961005
	addiw a5, a5, -2011
	add t0, t0, a5
	mul t4, t4, t0
	lui a4, 554096
	addiw a4, a4, 19
	slli a4, a4, 32
	lui a5, 200831
	addiw a5, a5, -941
	add a4, a4, a5
	mulhu a4, t4, a4
	addi a5, zero, 0
	sltu a5, a5, t4
	add a4, a4, a5
	lui a6, 707898
	addiw a6, a6, 1834
	slli a6, a6, 32
	lui a7, 590290
	addiw a7, a7, -1423
	add a6, a6, a7
	mul a5, t4, a6
	mulhu a6, t4, a6
	add a5, a5, a4
	sltu a7, a5, a4
	add a6, a6, a7
	add a1, a1, a5
	sltu a7, a1, a5
	add a4, a6, a7
	lui a6, 76574
	addiw a6, a6, -1511
	slli a6, a6, 32
	lui a7, 523121
	addiw a7, a7, 291
	add a6, a6, a7
	mul a5, t4, a6
	mulhu a6, t4, a6
	add a5, a5, a4
	sltu a7, a5, a4
	add a6, a6, a7
	add a0, a0, a5
	sltu a7, a0, a5
	add a4, a6, a7
	lui a6, 86775
	addiw a6, a6, 266
	slli a6, a6, 32
	lui a7, 972101
	addiw a7, a7, 1716
	add a6, a6, a7
	mul a5, t4, a6
	mulhu a6, t4, a6
	add a5, a5, a4
	sltu a7, a5, a4
	add a6, a6, a7
	add t5, t5, a5
	sltu a7, t5, a5
	add a4, a6, a7
	lui a6, 62935
	addiw a6, a6, -130
	slli a6, a6, 32
	lui a7, 331364
	addiw a7, a7, 479
	add a6, a6, a7
	mul a5, t4, a6
	mulhu a6, t4, a6
	add a5, a5, a4
	sltu a7, a5, a4
	add a6, a6, a7
	add t6, t6, a5
	sltu a7, t6, a5
	add a4, a6, a7
	lui a6, 576402
	addiw a6, a6, -381
	slli a6, a6, 32
	lui a7, 668551
	addiw a7, a7, -728
	add a6, a6, a7
	mul a5, t4, a6
	mulhu a6, t4, a6
	add a5, a5, a4
	sltu a7, a5, a4
	add a6, a6, a7
	add t3, t3, a5
	sltu a7, t3, a5
	add a4, a6, a7
	ld t4, 1832(a3)
	add t4, t4, a4
	sltu a7, t4, a4
	add t4, t4, a2
	sltu a2, t4, a2
	add a2, a2, a7
	lui t0, 632555
	addiw t0, t0, -1683
	slli t0, t0, 32
	lui a5, 961005
	addiw a5, a5, -2011
	add t0, t0, a5
	mul a1, a1, t0
	lui a4, 554096
	addiw a4, a4, 19
	slli a4, a4, 32
	lui a5, 200831
	addiw a5, a5, -941
	add a4, a4, a5
	mulhu a4, a1, a4
	addi a5, zero, 0
	sltu a5, a5, a1
	add a4, a4, a5
	lui a6, 707898
	addiw a6, a6, 1834
	slli a6, a6, 32
	lui a7, 590290
	addiw a7, a7, -1423
	add a6, a6, a7
	mul a5, a1, a6
	mulhu a6, a1, a6
	add a5, a5, a4
	sltu a7, a5, a4
	add a6, a6, a7
	add a0, a0, a5
	sltu a7, a0, a5
	add a4, a6, a7
	lui a6, 76574
	addiw a6, a6, -1511
	slli a6, a6, 32
	lui a7, 523121
	addiw a7, a7, 291
	add a6, a6, a7
	mul a5, a1, a6
	mulhu a6, a1, a6
	add a5, a5, a4
	sltu a7, a5, a4
	add a6, a6, a7
	add t5, t5, a5
	sltu a7, t5, a5
	add a4, a6, a7
	lui a6, 86775
	addiw a6, a6, 266
	slli a6, a6, 32
	lui a7, 972101
	addiw a7, a7, 1716
	add a6, a6, a7
	mul a5, a1, a6
	mulhu a6, a1, a6
	add a5, a5, a4
	sltu a7, a5, a4
	add a6, a6, a7
	add t6, t6, a5
	sltu a7, t6, a5
	add a4, a6, a7
	lui a6, 62935
	addiw a6, a6, -130
	slli a6, a6, 32
	lui a7, 331364
	addiw a7, a7, 479
	add a6, a6, a7
	mul a5, a1, a6
	mulhu a6, a1, a6
	add a5, a5, a4
	sltu a7, a5, a4
	add a6, a6, a7
	add t3, t3, a5
	sltu a7, t3, a5
	add a4, a6, a7
	lui a6, 576402
	addiw a6, a6, -381
	slli a6, a6, 32
	lui a7, 668551
	addiw a7, a7, -728
	add a6, a6, a7
	mul a5, a1, a6
	mulhu a6, a1, a6
	add a5, a5, a4
	sltu a7, a5, a4
	add a6, a6, a7
	add t4, t4, a5
	sltu a7, t4, a5
	add a4, a6, a7
	ld a1, 1840(a3)
	add a1, a1, a4
	sltu a7, a1, a4
	add a1, a1, a2
	sltu a2, a1, a2
	add a2, a2, a7
	lui t0, 632555
	addiw t0, t0, -1683
	slli t0, t0, 32
	lui a5, 961005
	addiw a5, a5, -2011
	add t0, t0, a5
	mul a0, a0, t0
	lui a4, 554096
	addiw a4, a4, 19
	slli a4, a4, 32
	lui a5, 200831
	addiw a5, a5, -941
	add a4, a4, a5
	mulhu a4, a0, a4
	addi a5, zero, 0
	sltu a5, a5, a0
	add a4, a4, a5
	lui a6, 707898
	addiw a6, a6, 1834
	slli a6, a6, 32
	lui a7, 590290
	addiw a7, a7, -1423
	add a6, a6, a7
	mul a5, a0, a6
	mulhu a6, a0, a6
	add a5, a5, a4
	sltu a7, a5, a4
	add a6, a6, a7
	add t5, t5, a5
	sltu a7, t5, a5
	add a4, a6, a7
	lui a6, 76574
	addiw a6, a6, -1511
	slli a6, a6, 32
	lui a7, 523121
	addiw a7, a7, 291
	add a6, a6, a7
	mul a5, a0, a6
	mulhu a6, a0, a6
	add a5, a5, a4
	sltu a7, a5, a4
	add a6, a6, a7
	add t6, t6, a5
	sltu a7, t6, a5
	add a4, a6, a7
	lui a6, 86775
	addiw a6, a6, 266
	slli a6, a6, 32
	lui a7, 972101
	addiw a7, a7, 1716
	add a6, a6, a7
	mul a5, a0, a6
	mulhu a6, a0, a6
	add a5, a5, a4
	sltu a7, a5, a4
	add a6, a6, a7
	add t3, t3, a5
	sltu a7, t3, a5
	add a4, a6, a7
	lui a6, 62935
	addiw a6, a6, -130
	slli a6, a6, 32
	lui a7, 331364
	addiw a7, a7, 479
	add a6, a6, a7
	mul a5, a0, a6
	mulhu a6, a0, a6
	add a5, a5, a4
	sltu a7, a5, a4
	add a6, a6, a7
	add t4, t4, a5
	sltu a7, t4, a5
	add a4, a6, a7
	lui a6, 576402
	addiw a6, a6, -381
	slli a6, a6, 32
	lui a7, 668551
	addiw a7, a7, -728
	add a6, a6, a7
	mul a5, a0, a6
	mulhu a6, a0, a6
	add a5, a5, a4
	sltu a7, a5, a4
	add a6, a6, a7
	add a1, a1, a5
	sltu a7, a1, a5
	add a4, a6, a7
	ld a0, 1848(a3)
	add a0, a0, a4
	sltu a7, a0, a4
	add a0, a0, a2
	sltu a2, a0, a2
	add a2, a2, a7
	addi a4, a0, 0
	addi a7, zero, 0
	lui t0, 494480
	addiw t0, t0, -19
	slli t0, t0, 32
	lui a6, 847745
	addiw a6, a6, 941
	add t0, t0, a6
	add a5, t5, t0
	sltu a0, a5, t0
	add a5, a5, a7
	sltu a7, a5, a7
	add a7, a7, a0
	sd a5, 0(t2)
	lui t0, 340678
	addiw t0, t0, -1834
	slli t0, t0, 32
	lui a6, 458286
	addiw a6, a6, 1422
	add t0, t0, a6
	add a5, t6, t0
	sltu a0, a5, t0
	add a5, a5, a7
	sltu a7, a5, a7
	add a7, a7, a0
	sd a5, 8(t2)
	lui t0, 972002
	addiw t0, t0, 1511
	slli t0, t0, 32
	lui a6, 525455
	addiw a6, a6, -292
	add t0, t0, a6
	add a5, t3, t0
	sltu a0, a5, t0
	add a5, a5, a7
	sltu a7, a5, a7
	add a7, a7, a0
	sd a5, 16(t2)
	lui t0, 961801
	addiw t0, t0, -266
	slli t0, t0, 32
	lui a6, 76475
	addiw a6, a6, -1717
	add t0, t0, a6
	add a5, t4, t0
	sltu a0, a5, t0
	add a5, a5, a7
	sltu a7, a5, a7
	add a7, a7, a0
	sd a5, 24(t2)
	lui t0, 985641
	addiw t0, t0, 130
	slli t0, t0, 32
	lui a6, 717212
	addiw a6, a6, -480
	add t0, t0, a6
	add a5, a1, t0
	sltu a0, a5, t0
	add a5, a5, a7
	sltu a7, a5, a7
	add a7, a7, a0
	sd a5, 32(t2)
	lui t0, 472174
	addiw t0, t0, 381
	slli t0, t0, 32
	lui a6, 380025
	addiw a6, a6, 727
	add t0, t0, a6
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
	ret
	.option pop
