// The functions of `src/internal/vg_p384_mul_mod_p.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p384_mul_mod_p:
	.option push
	.option arch, +m, +c
	add t2, a0, a1
	add t4, a0, a2
	add t5, a0, a3
	addi a3, a0, 2047
	addi a3, a3, 1
	sd s6, 1664(a3)
	sd s7, 1672(a3)
	sd s8, 1680(a3)
	sd s9, 1688(a3)
	sd s10, 1696(a3)
	sd s11, 1704(a3)
	sd t1, 1712(a3)
	beq t4, t5, 20f
	ld a0, 0(t4)
	ld a1, 8(t4)
	ld a4, 24(t4)
	ld a2, 16(t4)
	ld a5, 32(t4)
	ld a6, 40(t4)
	ld t4, 0(t5)
	mulhu t3, a0, t4
	mul t1, a1, t4
	mul a7, a2, t4
	mulhu s11, a1, t4
	add t1, t1, t3
	sltu t6, t1, t3
	mul s7, a4, t4
	add t3, s11, t6
	add a7, a7, t3
	sltu s6, a7, t3
	mulhu s11, a2, t4
	add t3, s11, s6
	mul s9, a6, t4
	mulhu s11, a4, t4
	add s7, s7, t3
	sltu s10, s7, t3
	mul t0, a0, t4
	mul s8, a5, t4
	add t3, s11, s10
	mulhu s11, a5, t4
	sd t0, 1760(a3)
	add s8, s8, t3
	sltu t6, s8, t3
	add t3, s11, t6
	mulhu s11, a6, t4
	ld t4, 8(t5)
	add s9, s9, t3
	sltu s6, s9, t3
	add t3, s11, s6
	mul t6, a0, t4
	add t1, t1, t6
	mul s10, a4, t4
	mul s6, a2, t4
	mulhu s11, a1, t4
	sltu t6, t1, t6
	sd t1, 1768(a3)
	add s7, s7, s6
	addi t0, t3, 0
	sltu s6, s7, s6
	add s8, s8, s10
	mulhu t3, a0, t4
	add t3, t3, t6
	sltu s10, s8, s10
	mul t6, a1, t4
	add a7, a7, t6
	sltu t6, a7, t6
	add a7, a7, t3
	add t6, s11, t6
	sltu s11, a7, t3
	add t3, t6, s11
	mulhu s11, a2, t4
	mul t6, a5, t4
	add s6, s11, s6
	add s7, s7, t3
	sltu s11, s7, t3
	add t3, s6, s11
	mulhu s11, a4, t4
	mul s6, a6, t4
	add s10, s11, s10
	add t0, t0, s6
	add s8, s8, t3
	sltu s11, s8, t3
	add t3, s10, s11
	mulhu s11, a5, t4
	sltu s6, t0, s6
	add s9, s9, t6
	sltu t6, s9, t6
	add t6, s11, t6
	add s9, s9, t3
	sltu s11, s9, t3
	add t3, t6, s11
	mulhu s11, a6, t4
	ld t4, 16(t5)
	mul t6, a0, t4
	add a7, a7, t6
	add t0, t0, t3
	add s6, s11, s6
	sltu s11, t0, t3
	add t3, s6, s11
	mul s10, a4, t4
	mul s6, a2, t4
	sltu t6, a7, t6
	mulhu s11, a1, t4
	add s8, s8, s6
	addi t1, t3, 0
	mulhu t3, a0, t4
	sd a7, 1776(a3)
	add s9, s9, s10
	sltu s10, s9, s10
	sltu s6, s8, s6
	add t3, t3, t6
	mul t6, a1, t4
	add s7, s7, t6
	sltu t6, s7, t6
	add t6, s11, t6
	add s7, s7, t3
	sltu s11, s7, t3
	add t3, t6, s11
	add s8, s8, t3
	mul t6, a5, t4
	mulhu s11, a2, t4
	add s6, s11, s6
	add t0, t0, t6
	sltu s11, s8, t3
	add t3, s6, s11
	add s9, s9, t3
	mulhu s11, a4, t4
	add s10, s11, s10
	mul s6, a6, t4
	sltu t6, t0, t6
	sltu s11, s9, t3
	add t3, s10, s11
	add t1, t1, s6
	mulhu s11, a5, t4
	add t6, s11, t6
	sltu s6, t1, s6
	add t0, t0, t3
	sltu s11, t0, t3
	add t3, t6, s11
	mulhu s11, a6, t4
	add t1, t1, t3
	ld t4, 24(t5)
	mul s10, a4, t4
	add s6, s11, s6
	mul t6, a0, t4
	sltu s11, t1, t3
	add s7, s7, t6
	add t3, s6, s11
	addi a7, t3, 0
	mulhu t3, a0, t4
	sltu t6, s7, t6
	mul s6, a2, t4
	mulhu s11, a1, t4
	add t3, t3, t6
	sd s7, 1784(a3)
	add t0, t0, s10
	sltu s10, t0, s10
	mul t6, a1, t4
	add s8, s8, t6
	sltu t6, s8, t6
	add s9, s9, s6
	add s8, s8, t3
	add t6, s11, t6
	sltu s11, s8, t3
	sltu s6, s9, s6
	add t3, t6, s11
	mulhu s11, a2, t4
	add s9, s9, t3
	add s6, s11, s6
	mul t6, a5, t4
	sltu s11, s9, t3
	add t3, s6, s11
	mulhu s11, a4, t4
	add t1, t1, t6
	add t0, t0, t3
	add s10, s11, s10
	sltu s11, t0, t3
	sltu t6, t1, t6
	mul s6, a6, t4
	add a7, a7, s6
	add t3, s10, s11
	mulhu s11, a5, t4
	sltu s6, a7, s6
	add t6, s11, t6
	add t1, t1, t3
	sltu s11, t1, t3
	add t3, t6, s11
	mulhu s11, a6, t4
	ld t4, 32(t5)
	add s6, s11, s6
	mul t6, a0, t4
	add a7, a7, t3
	sltu s11, a7, t3
	add s8, s8, t6
	mul s10, a4, t4
	add t3, s6, s11
	sltu t6, s8, t6
	addi s7, t3, 0
	sd s8, 1792(a3)
	mulhu t3, a0, t4
	add t3, t3, t6
	mul t6, a1, t4
	add t1, t1, s10
	mul s6, a2, t4
	mulhu s11, a1, t4
	add s9, s9, t6
	sltu t6, s9, t6
	add s9, s9, t3
	add t6, s11, t6
	sltu s11, s9, t3
	sltu s10, t1, s10
	add t0, t0, s6
	add t3, t6, s11
	mulhu s11, a2, t4
	sltu s6, t0, s6
	add t0, t0, t3
	add s6, s11, s6
	mul t6, a5, t4
	sltu s11, t0, t3
	add t3, s6, s11
	add t1, t1, t3
	add a7, a7, t6
	mul s6, a6, t4
	sltu t6, a7, t6
	mulhu s11, a4, t4
	add s10, s11, s10
	add s7, s7, s6
	sltu s11, t1, t3
	add t3, s10, s11
	add a7, a7, t3
	mulhu s11, a5, t4
	add t6, s11, t6
	sltu s11, a7, t3
	add t3, t6, s11
	sltu s6, s7, s6
	mulhu s11, a6, t4
	add s7, s7, t3
	ld t4, 40(t5)
	add s6, s11, s6
	mul t6, a0, t4
	sltu s11, s7, t3
	add t3, s6, s11
	mul s6, a2, t4
	add s9, s9, t6
	mul s10, a4, t4
	addi s8, t3, 0
	add t1, t1, s6
	add a7, a7, s10
	mulhu t3, a0, t4
	sltu t6, s9, t6
	add t3, t3, t6
	mul t6, a1, t4
	add t0, t0, t6
	sltu t6, t0, t6
	mulhu s11, a1, t4
	sltu s6, t1, s6
	add t6, s11, t6
	sd s9, 1800(a3)
	add t0, t0, t3
	sd t0, 1808(a3)
	sltu s11, t0, t3
	add t3, t6, s11
	add t1, t1, t3
	mul t6, a5, t4
	mulhu s11, a2, t4
	add s6, s11, s6
	add s7, s7, t6
	sltu s11, t1, t3
	sltu s10, a7, s10
	sltu t6, s7, t6
	add t3, s6, s11
	add a7, a7, t3
	mul s6, a6, t4
	sd t1, 1816(a3)
	add s8, s8, s6
	mulhu s11, a4, t4
	add s10, s11, s10
	sd a7, 1824(a3)
	sltu s11, a7, t3
	add t3, s10, s11
	add s7, s7, t3
	sd s7, 1832(a3)
	sltu s6, s8, s6
	mulhu s11, a5, t4
	add t6, s11, t6
	sltu s11, s7, t3
	add t3, t6, s11
	add s8, s8, t3
	mulhu s11, a6, t4
	add s6, s11, s6
	sltu s11, s8, t3
	sd s8, 1840(a3)
	add t3, s6, s11
	addi s9, t3, 0
	sd s9, 1848(a3)
	j 21f
20:
	ld a1, 8(t4)
	ld a0, 0(t4)
	ld a2, 16(t4)
	mul a7, a2, a0
	ld a4, 24(t4)
	mulhu t3, a1, a0
	mul s7, a4, a0
	add a7, a7, t3
	sltu t6, a7, t3
	mulhu s11, a2, a0
	mul t1, a1, a0
	ld a6, 40(t4)
	ld a5, 32(t4)
	mul s9, a6, a0
	add t3, s11, t6
	add s7, s7, t3
	mul s8, a5, a0
	sltu s6, s7, t3
	mulhu s11, a4, a0
	add t3, s11, s6
	sd t1, 1768(a3)
	sd a7, 1776(a3)
	mul s6, a5, a1
	add s8, s8, t3
	sltu s10, s8, t3
	mulhu s11, a5, a0
	add t3, s11, s10
	mulhu s11, a6, a0
	add s9, s9, t3
	mul s10, a6, a1
	sltu t6, s9, t3
	add s9, s9, s6
	sltu s6, s9, s6
	add t3, s11, t6
	mulhu s11, a4, a1
	mul t6, a2, a1
	addi t0, t3, 0
	add t0, t0, s10
	sltu s10, t0, s10
	add s7, s7, t6
	mulhu t3, a2, a1
	sltu t6, s7, t6
	sd s7, 1784(a3)
	add t3, t3, t6
	mul t6, a4, a1
	add s8, s8, t6
	sltu t6, s8, t6
	add s8, s8, t3
	sd s8, 1792(a3)
	add t6, s11, t6
	sltu s11, s8, t3
	add t3, t6, s11
	mulhu s11, a5, a1
	add s9, s9, t3
	add s6, s11, s6
	mul t6, a4, a2
	sltu s11, s9, t3
	add t3, s6, s11
	add s9, s9, t6
	mulhu s11, a6, a1
	sltu t6, s9, t6
	add s10, s11, s10
	sd s9, 1800(a3)
	add t0, t0, t3
	mul s6, a6, a2
	sltu s11, t0, t3
	add t3, s10, s11
	addi t1, t3, 0
	mulhu s11, a5, a2
	mulhu t3, a4, a2
	add t3, t3, t6
	mul t6, a5, a2
	add t0, t0, t6
	sltu t6, t0, t6
	add t6, s11, t6
	add t0, t0, t3
	sltu s11, t0, t3
	add t3, t6, s11
	add t1, t1, s6
	sd t0, 1808(a3)
	mulhu s11, a6, a2
	addi t4, zero, 0
	mul t6, a5, a4
	mul t0, a0, a0
	sltu s6, t1, s6
	add t1, t1, t3
	add s6, s11, s6
	sltu s11, t1, t3
	add t1, t1, t6
	add t3, s6, s11
	addi a7, t3, 0
	mulhu t3, a5, a4
	sltu t6, t1, t6
	mulhu s11, a6, a4
	add t3, t3, t6
	sd t1, 1816(a3)
	mul t6, a6, a4
	mulhu t1, a0, a0
	add a7, a7, t6
	mulhu s9, a1, a1
	sltu t6, a7, t6
	add a7, a7, t3
	add t6, s11, t6
	sltu s11, a7, t3
	add t3, t6, s11
	sd a7, 1824(a3)
	mul t6, a6, a5
	addi s7, t3, 0
	mulhu t3, a6, a5
	add s7, s7, t6
	sltu t6, s7, t6
	sd s7, 1832(a3)
	add t3, t3, t6
	addi s8, t3, 0
	sd s8, 1840(a3)
	addi t3, zero, 0
	sd t3, 1760(a3)
	mul s8, a1, a1
	ld s7, 1768(a3)
	ld a7, 1760(a3)
	srli t5, a7, 63
	slli a7, a7, 1
	sd t3, 1848(a3)
	add a7, a7, t4
	add a7, a7, t0
	srli t4, s7, 63
	slli s7, s7, 1
	sltu t0, a7, t0
	add s7, s7, t5
	add a7, a7, t3
	sltu t3, a7, t3
	add t3, t3, t0
	ld t0, 1776(a3)
	add s7, s7, t1
	sltu t1, s7, t1
	sd a7, 1760(a3)
	add s7, s7, t3
	srli t5, t0, 63
	sd s7, 1768(a3)
	sltu t3, s7, t3
	add t3, t3, t1
	slli t0, t0, 1
	mulhu s7, a2, a2
	ld t1, 1784(a3)
	add t0, t0, t4
	srli t4, t1, 63
	slli t1, t1, 1
	mul a7, a2, a2
	add t1, t1, t5
	add t0, t0, s8
	sltu s8, t0, s8
	add t0, t0, t3
	add t1, t1, s9
	sltu t3, t0, t3
	add t3, t3, s8
	ld s8, 1792(a3)
	sd t0, 1776(a3)
	sltu s9, t1, s9
	srli t5, s8, 63
	add t1, t1, t3
	slli s8, s8, 1
	add s8, s8, t4
	sltu t3, t1, t3
	add s8, s8, a7
	sd t1, 1784(a3)
	sltu a7, s8, a7
	add t3, t3, s9
	ld s9, 1800(a3)
	srli t4, s9, 63
	mulhu t1, a4, a4
	slli s9, s9, 1
	add s9, s9, t5
	add s8, s8, t3
	sltu t3, s8, t3
	add t3, t3, a7
	mul t0, a4, a4
	ld a7, 1808(a3)
	add s9, s9, s7
	sd s8, 1792(a3)
	sltu s7, s9, s7
	add s9, s9, t3
	sltu t3, s9, t3
	sd s9, 1800(a3)
	mulhu s9, a5, a5
	srli t5, a7, 63
	slli a7, a7, 1
	add a7, a7, t4
	add t3, t3, s7
	ld s7, 1816(a3)
	add a7, a7, t0
	sltu t0, a7, t0
	add a7, a7, t3
	mul s8, a5, a5
	srli t4, s7, 63
	slli s7, s7, 1
	sd a7, 1808(a3)
	sltu t3, a7, t3
	add t3, t3, t0
	add s7, s7, t5
	ld t0, 1824(a3)
	add s7, s7, t1
	sltu t1, s7, t1
	add s7, s7, t3
	srli t5, t0, 63
	sd s7, 1816(a3)
	slli t0, t0, 1
	add t0, t0, t4
	sltu t3, s7, t3
	add t3, t3, t1
	ld t1, 1832(a3)
	mul a7, a6, a6
	add t0, t0, s8
	srli t4, t1, 63
	sltu s8, t0, s8
	add t0, t0, t3
	slli t1, t1, 1
	sltu t3, t0, t3
	add t3, t3, s8
	add t1, t1, t5
	ld s8, 1840(a3)
	add t1, t1, s9
	sltu s9, t1, s9
	add t1, t1, t3
	sd t0, 1824(a3)
	mulhu s7, a6, a6
	sd t1, 1832(a3)
	sltu t3, t1, t3
	srli t5, s8, 63
	slli s8, s8, 1
	add t3, t3, s9
	add s8, s8, t4
	ld s9, 1848(a3)
	add s8, s8, a7
	srli t4, s9, 63
	sltu a7, s8, a7
	add s8, s8, t3
	sd s8, 1840(a3)
	slli s9, s9, 1
	add s9, s9, t5
	add s9, s9, s7
	sltu s7, s9, s7
	sltu t3, s8, t3
	add t3, t3, a7
	add s9, s9, t3
	sltu t3, s9, t3
	sd s9, 1848(a3)
	add t3, t3, s7
21:
	ld t3, 1760(a3)
	ld t6, 1784(a3)
	addi a2, zero, 0
	ld t5, 1776(a3)
	slli t0, t3, 32
	ld t4, 1768(a3)
	add t3, t3, t0
	slli a4, t3, 32
	srli a5, t3, 32
	sd t3, 1760(a3)
	sltu a6, t3, a4
	add a6, a6, a5
	sltu a7, a4, a6
	sub a5, a5, a7
	sub a4, a4, a6
	add a5, a5, t3
	sltu a7, t4, a4
	sub t4, t4, a4
	sltu t0, t5, a5
	sub t5, t5, a5
	sltu a4, t5, a7
	sub t5, t5, a7
	sltu a6, a5, t3
	add a7, t0, a4
	add a6, a6, a2
	slli t0, t4, 32
	add a6, a6, a7
	add t4, t4, t0
	sltu a2, t6, a6
	srli a5, t4, 32
	slli a4, t4, 32
	sub t6, t6, a6
	ld t3, 1792(a3)
	sltu a6, t4, a4
	add a6, a6, a5
	sltu a7, a4, a6
	sub a5, a5, a7
	sub a4, a4, a6
	sltu a7, t5, a4
	add a5, a5, t4
	sub t5, t5, a4
	sltu t0, t6, a5
	sub t6, t6, a5
	sltu a4, t6, a7
	sub t6, t6, a7
	sd t4, 1768(a3)
	add a7, t0, a4
	sltu a6, a5, t4
	add a6, a6, a2
	slli t0, t5, 32
	add a6, a6, a7
	sltu a2, t3, a6
	add t5, t5, t0
	sub t3, t3, a6
	slli a4, t5, 32
	srli a5, t5, 32
	sltu a6, t5, a4
	add a6, a6, a5
	sd t5, 1776(a3)
	sltu a7, a4, a6
	sub a5, a5, a7
	sub a4, a4, a6
	sltu a7, t6, a4
	add a5, a5, t5
	sltu a6, a5, t5
	sltu t0, t3, a5
	sub t3, t3, a5
	sub t6, t6, a4
	sltu a4, t3, a7
	sub t3, t3, a7
	ld t5, 1808(a3)
	add a7, t0, a4
	slli t0, t6, 32
	add a6, a6, a2
	add t6, t6, t0
	add a6, a6, a7
	ld t4, 1800(a3)
	sltu a2, t4, a6
	slli a4, t6, 32
	sub t4, t4, a6
	sd t6, 1784(a3)
	sltu a6, t6, a4
	srli a5, t6, 32
	add a6, a6, a5
	sltu a7, a4, a6
	sub a5, a5, a7
	sub a4, a4, a6
	sltu a7, t3, a4
	add a5, a5, t6
	sltu a6, a5, t6
	sltu t0, t4, a5
	sub t4, t4, a5
	sub t3, t3, a4
	sltu a4, t4, a7
	add a6, a6, a2
	ld t6, 1816(a3)
	sub t4, t4, a7
	ld a1, 1840(a3)
	add a7, t0, a4
	slli t0, t3, 32
	add a6, a6, a7
	add t3, t3, t0
	sltu a2, t5, a6
	slli a4, t3, 32
	srli a5, t3, 32
	sub t5, t5, a6
	sltu a6, t3, a4
	add a6, a6, a5
	sltu a7, a4, a6
	sub a5, a5, a7
	sub a4, a4, a6
	add a5, a5, t3
	sd t3, 1792(a3)
	sltu a7, t4, a4
	sltu a6, a5, t3
	sltu t0, t5, a5
	sub t4, t4, a4
	sub t5, t5, a5
	sltu a4, t5, a7
	sub t5, t5, a7
	add a6, a6, a2
	add a7, t0, a4
	slli t0, t4, 32
	add t4, t4, t0
	srli a5, t4, 32
	slli a4, t4, 32
	ld t3, 1824(a3)
	add a6, a6, a7
	sltu a2, t6, a6
	sd t4, 1800(a3)
	sub t6, t6, a6
	sltu a6, t4, a4
	add a6, a6, a5
	sltu a7, a4, a6
	sub a4, a4, a6
	sub a5, a5, a7
	add a5, a5, t4
	sltu t0, t6, a5
	sltu a7, t5, a4
	sub t5, t5, a4
	sltu a6, a5, t4
	sub t6, t6, a5
	sltu a4, t6, a7
	sub t6, t6, a7
	add a6, a6, a2
	add a7, t0, a4
	ld t4, 1832(a3)
	add a6, a6, a7
	sltu a2, t3, a6
	sub t3, t3, a6
	sltu a5, t4, a2
	ld a7, 1760(a3)
	sub t4, t4, a2
	sltu a2, a1, a5
	ld a4, 1848(a3)
	sub a1, a1, a5
	add t5, t5, a7
	sltu a5, a4, a2
	sub a4, a4, a2
	addi t0, zero, -1
	slli t0, t0, 32
	sltu a6, t5, a7
	addi t0, t0, 1
	addi a2, zero, 0
	add t5, t5, a2
	sltu a2, t5, a2
	ld a7, 1768(a3)
	add t6, t6, a7
	add a2, a2, a6
	sltu a6, t6, a7
	add t6, t6, a2
	ld a7, 1776(a3)
	sltu a2, t6, a2
	add a2, a2, a6
	add t3, t3, a7
	sltu a6, t3, a7
	ld a7, 1784(a3)
	add t3, t3, a2
	add t4, t4, a7
	sltu a2, t3, a2
	add a2, a2, a6
	sltu a6, t4, a7
	add t4, t4, a2
	ld a7, 1792(a3)
	add a1, a1, a7
	sltu a2, t4, a2
	add a2, a2, a6
	sltu a6, a1, a7
	ld a7, 1800(a3)
	add s6, t5, t0
	add a1, a1, a2
	sltu a2, a1, a2
	add a2, a2, a6
	add a4, a4, a7
	sltu a6, a4, a7
	add a4, a4, a2
	sltu a2, a4, a2
	add a2, a2, a6
	sub a2, a2, a5
	addi a5, zero, -1
	srli a5, a5, 32
	sltu a7, s6, t0
	add s7, t6, a5
	sltu a0, s7, a5
	add s7, s7, a7
	sltu a7, s7, a7
	add a7, a7, a0
	addi a7, a7, 1
	add s8, t3, a7
	xor s6, s6, t5
	sltu a7, s8, a7
	add s9, t4, a7
	sltu a7, s9, a7
	add s10, a1, a7
	sltu a7, s10, a7
	xor s7, s7, t6
	add s11, a4, a7
	addi t0, zero, 0
	sltu a7, s11, a7
	xor s9, s9, t4
	or a7, a7, a2
	xor s11, s11, a4
	sub t0, t0, a7
	and s7, s7, t0
	xor s8, s8, t3
	xor s10, s10, a1
	and s6, s6, t0
	and s10, s10, t0
	and s9, s9, t0
	xor s6, s6, t5
	xor s10, s10, a1
	and s8, s8, t0
	sd s6, 0(t2)
	xor s7, s7, t6
	xor s8, s8, t3
	sd s7, 8(t2)
	xor s9, s9, t4
	sd s8, 16(t2)
	sd s9, 24(t2)
	and s11, s11, t0
	sd s10, 32(t2)
	xor s11, s11, a4
	sd s11, 40(t2)
	ld s6, 1664(a3)
	ld s7, 1672(a3)
	ld s8, 1680(a3)
	ld s9, 1688(a3)
	ld s10, 1696(a3)
	ld s11, 1704(a3)
	ld t1, 1712(a3)
	ret
	.option pop
