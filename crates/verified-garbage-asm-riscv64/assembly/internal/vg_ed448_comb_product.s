// The functions of `src/internal/vg_ed448_comb_product.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed448_comb_product:
	.option push
	.option arch, +m, +c
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	ld a1, 0(s1)
	ld a2, 0(s2)
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 8(s1)
	ld a2, 0(s2)
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 0(s1)
	ld a2, 8(s2)
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 952(a3)
	addi a4, zero, 0
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 16(s1)
	ld a2, 0(s2)
	add a5, a5, t3
	sltu t3, a5, t3
	add t6, t6, t3
	add a6, a6, t6
	sltu t6, a6, t6
	add a4, a4, t6
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 8(s1)
	ld a2, 8(s2)
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 960(a3)
	addi a5, zero, 0
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 0(s1)
	ld a2, 16(s2)
	add a6, a6, t3
	sltu t3, a6, t3
	add t6, t6, t3
	add a4, a4, t6
	sltu t6, a4, t6
	add a5, a5, t6
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 24(s1)
	ld a2, 0(s2)
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 16(s1)
	ld a2, 8(s2)
	add a6, a6, t3
	sltu t3, a6, t3
	add t6, t6, t3
	add a4, a4, t6
	sltu t6, a4, t6
	add a5, a5, t6
	sd a6, 968(a3)
	addi a6, zero, 0
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 8(s1)
	ld a2, 16(s2)
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 0(s1)
	ld a2, 24(s2)
	add a4, a4, t3
	sltu t3, a4, t3
	add t6, t6, t3
	add a5, a5, t6
	sltu t6, a5, t6
	add a6, a6, t6
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 32(s1)
	ld a2, 0(s2)
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 24(s1)
	ld a2, 8(s2)
	add a4, a4, t3
	sltu t3, a4, t3
	add t6, t6, t3
	add a5, a5, t6
	sltu t6, a5, t6
	add a6, a6, t6
	sd a4, 976(a3)
	addi a4, zero, 0
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 16(s1)
	ld a2, 16(s2)
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 8(s1)
	ld a2, 24(s2)
	add a5, a5, t3
	sltu t3, a5, t3
	add t6, t6, t3
	add a6, a6, t6
	sltu t6, a6, t6
	add a4, a4, t6
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 0(s1)
	ld a2, 32(s2)
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 40(s1)
	ld a2, 0(s2)
	add a5, a5, t3
	sltu t3, a5, t3
	add t6, t6, t3
	add a6, a6, t6
	sltu t6, a6, t6
	add a4, a4, t6
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 32(s1)
	ld a2, 8(s2)
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 984(a3)
	addi a5, zero, 0
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 24(s1)
	ld a2, 16(s2)
	add a6, a6, t3
	sltu t3, a6, t3
	add t6, t6, t3
	add a4, a4, t6
	sltu t6, a4, t6
	add a5, a5, t6
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 16(s1)
	ld a2, 24(s2)
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 8(s1)
	ld a2, 32(s2)
	add a6, a6, t3
	sltu t3, a6, t3
	add t6, t6, t3
	add a4, a4, t6
	sltu t6, a4, t6
	add a5, a5, t6
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 0(s1)
	ld a2, 40(s2)
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 48(s1)
	ld a2, 0(s2)
	add a6, a6, t3
	sltu t3, a6, t3
	add t6, t6, t3
	add a4, a4, t6
	sltu t6, a4, t6
	add a5, a5, t6
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 40(s1)
	ld a2, 8(s2)
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 992(a3)
	addi a6, zero, 0
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 32(s1)
	ld a2, 16(s2)
	add a4, a4, t3
	sltu t3, a4, t3
	add t6, t6, t3
	add a5, a5, t6
	sltu t6, a5, t6
	add a6, a6, t6
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 24(s1)
	ld a2, 24(s2)
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 16(s1)
	ld a2, 32(s2)
	add a4, a4, t3
	sltu t3, a4, t3
	add t6, t6, t3
	add a5, a5, t6
	sltu t6, a5, t6
	add a6, a6, t6
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 8(s1)
	ld a2, 40(s2)
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 0(s1)
	ld a2, 48(s2)
	add a4, a4, t3
	sltu t3, a4, t3
	add t6, t6, t3
	add a5, a5, t6
	sltu t6, a5, t6
	add a6, a6, t6
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 48(s1)
	ld a2, 8(s2)
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 40(s1)
	ld a2, 16(s2)
	add a4, a4, t3
	sltu t3, a4, t3
	add t6, t6, t3
	add a5, a5, t6
	sltu t6, a5, t6
	add a6, a6, t6
	sd a4, 1000(a3)
	addi a4, zero, 0
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 32(s1)
	ld a2, 24(s2)
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 24(s1)
	ld a2, 32(s2)
	add a5, a5, t3
	sltu t3, a5, t3
	add t6, t6, t3
	add a6, a6, t6
	sltu t6, a6, t6
	add a4, a4, t6
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 16(s1)
	ld a2, 40(s2)
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 8(s1)
	ld a2, 48(s2)
	add a5, a5, t3
	sltu t3, a5, t3
	add t6, t6, t3
	add a6, a6, t6
	sltu t6, a6, t6
	add a4, a4, t6
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 48(s1)
	ld a2, 16(s2)
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 40(s1)
	ld a2, 24(s2)
	add a5, a5, t3
	sltu t3, a5, t3
	add t6, t6, t3
	add a6, a6, t6
	sltu t6, a6, t6
	add a4, a4, t6
	sd a5, 1008(a3)
	addi a5, zero, 0
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 32(s1)
	ld a2, 32(s2)
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 24(s1)
	ld a2, 40(s2)
	add a6, a6, t3
	sltu t3, a6, t3
	add t6, t6, t3
	add a4, a4, t6
	sltu t6, a4, t6
	add a5, a5, t6
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 16(s1)
	ld a2, 48(s2)
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 48(s1)
	ld a2, 24(s2)
	add a6, a6, t3
	sltu t3, a6, t3
	add t6, t6, t3
	add a4, a4, t6
	sltu t6, a4, t6
	add a5, a5, t6
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 40(s1)
	ld a2, 32(s2)
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 1016(a3)
	addi a6, zero, 0
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 32(s1)
	ld a2, 40(s2)
	add a4, a4, t3
	sltu t3, a4, t3
	add t6, t6, t3
	add a5, a5, t6
	sltu t6, a5, t6
	add a6, a6, t6
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 24(s1)
	ld a2, 48(s2)
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 48(s1)
	ld a2, 32(s2)
	add a4, a4, t3
	sltu t3, a4, t3
	add t6, t6, t3
	add a5, a5, t6
	sltu t6, a5, t6
	add a6, a6, t6
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 40(s1)
	ld a2, 40(s2)
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 1024(a3)
	addi a4, zero, 0
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 32(s1)
	ld a2, 48(s2)
	add a5, a5, t3
	sltu t3, a5, t3
	add t6, t6, t3
	add a6, a6, t6
	sltu t6, a6, t6
	add a4, a4, t6
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 48(s1)
	ld a2, 40(s2)
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 40(s1)
	ld a2, 48(s2)
	add a5, a5, t3
	sltu t3, a5, t3
	add t6, t6, t3
	add a6, a6, t6
	sltu t6, a6, t6
	add a4, a4, t6
	sd a5, 1032(a3)
	addi a5, zero, 0
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 48(s1)
	ld a2, 48(s2)
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	mul a7, a1, a2
	mulhu t0, a1, a2
	add a6, a6, t3
	sltu t3, a6, t3
	add t6, t6, t3
	add a4, a4, t6
	sltu t6, a4, t6
	add a5, a5, t6
	sd a6, 1040(a3)
	addi a6, zero, 0
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 1048(a3)
	addi a4, zero, 0
	sd a5, 1056(a3)
	addi a5, zero, 0
	ld t3, 952(a3)
	ld a7, 1008(a3)
	add t3, t3, a7
	sltu a5, t3, a7
	ld a7, 1032(a3)
	srli a7, a7, 32
	ld t0, 1040(a3)
	slli t0, t0, 32
	or a7, a7, t0
	add t3, t3, a7
	sltu a7, t3, a7
	add a5, a5, a7
	ld t4, 960(a3)
	ld a7, 1016(a3)
	add t4, t4, a7
	sltu a6, t4, a7
	ld a7, 1040(a3)
	srli a7, a7, 32
	ld t0, 1048(a3)
	slli t0, t0, 32
	or a7, a7, t0
	add t4, t4, a7
	sltu a7, t4, a7
	add a6, a6, a7
	add t4, t4, a5
	sltu a7, t4, a5
	add a6, a6, a7
	ld t5, 968(a3)
	ld a7, 1024(a3)
	add t5, t5, a7
	sltu a5, t5, a7
	ld a7, 1048(a3)
	srli a7, a7, 32
	ld t0, 1056(a3)
	slli t0, t0, 32
	or a7, a7, t0
	add t5, t5, a7
	sltu a7, t5, a7
	add a5, a5, a7
	add t5, t5, a6
	sltu a7, t5, a6
	add a5, a5, a7
	ld t6, 976(a3)
	ld a7, 1032(a3)
	add t6, t6, a7
	sltu a6, t6, a7
	srli a7, a7, 32
	slli a7, a7, 32
	add t6, t6, a7
	sltu a7, t6, a7
	add a6, a6, a7
	ld a7, 1056(a3)
	srli a7, a7, 32
	ld t0, 1008(a3)
	slli t0, t0, 32
	or a7, a7, t0
	add t6, t6, a7
	sltu a7, t6, a7
	add a6, a6, a7
	add t6, t6, a5
	sltu a7, t6, a5
	add a6, a6, a7
	ld a1, 984(a3)
	ld a7, 1040(a3)
	add a1, a1, a7
	sltu a5, a1, a7
	add a1, a1, a7
	sltu a7, a1, a7
	add a5, a5, a7
	ld a7, 1008(a3)
	srli a7, a7, 32
	ld t0, 1016(a3)
	slli t0, t0, 32
	or a7, a7, t0
	add a1, a1, a7
	sltu a7, a1, a7
	add a5, a5, a7
	add a1, a1, a6
	sltu a7, a1, a6
	add a5, a5, a7
	ld a2, 992(a3)
	ld a7, 1048(a3)
	add a2, a2, a7
	sltu a6, a2, a7
	add a2, a2, a7
	sltu a7, a2, a7
	add a6, a6, a7
	ld a7, 1016(a3)
	srli a7, a7, 32
	ld t0, 1024(a3)
	slli t0, t0, 32
	or a7, a7, t0
	add a2, a2, a7
	sltu a7, a2, a7
	add a6, a6, a7
	add a2, a2, a5
	sltu a7, a2, a5
	add a6, a6, a7
	ld a4, 1000(a3)
	ld a7, 1056(a3)
	add a4, a4, a7
	sltu a5, a4, a7
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, a7
	ld a7, 1024(a3)
	srli a7, a7, 32
	ld t0, 1032(a3)
	slli t0, t0, 32
	or a7, a7, t0
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, a7
	add a4, a4, a6
	sltu a7, a4, a6
	add a5, a5, a7
	add t3, t3, a5
	sltu t0, t3, a5
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu t0, t6, t0
	slli a7, a5, 32
	add t6, t6, a7
	sltu a7, t6, a7
	add t0, t0, a7
	add a1, a1, t0
	sltu t0, a1, t0
	add a2, a2, t0
	sltu t0, a2, t0
	add a4, a4, t0
	sltu a5, a4, t0
	add t3, t3, a5
	sltu t0, t3, a5
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu t0, t6, t0
	slli a7, a5, 32
	add t6, t6, a7
	sltu a7, t6, a7
	add t0, t0, a7
	add a1, a1, t0
	sltu t0, a1, t0
	add a2, a2, t0
	sltu t0, a2, t0
	add a4, a4, t0
	sltu a5, a4, t0
	sd t3, 0(a0)
	sd t4, 8(a0)
	sd t5, 16(a0)
	sd t6, 24(a0)
	sd a1, 32(a0)
	sd a2, 40(a0)
	sd a4, 48(a0)
	ret
	.option pop
