// The functions of `src/internal/vg_p256_mul_mod_p.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p256_mul_mod_p:
	.option push
	.option arch, +m, +c
	add t2, a0, a1
	add t4, a0, a2
	add t5, a0, a3
	addi a3, a0, 2047
	addi a3, a3, 1
	ld a0, 0(t4)
	ld a4, 8(t4)
	ld a5, 0(t5)
	mulhu a6, a5, a0
	mul a5, a5, a0
	ld a7, 8(t5)
	mulhu t0, a7, a0
	mul a7, a7, a0
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	ld a7, 0(t5)
	mulhu t6, a7, a4
	mul a7, a7, a4
	add a6, a6, a7
	sltu a7, a6, a7
	add t6, t6, a7
	add t0, t0, t6
	sltu t6, t0, t6
	slli a7, a5, 32
	srli a1, a5, 32
	add a6, a6, a7
	sltu a7, a6, a7
	add a1, a1, a7
	add t0, t0, a1
	sltu a1, t0, a1
	add t6, t6, a1
	ld a7, 16(t4)
	ld t3, 16(t5)
	mulhu a1, t3, a0
	mul t3, t3, a0
	add t0, t0, t3
	sltu t3, t0, t3
	add a1, a1, t3
	add t6, t6, a1
	sltu a1, t6, a1
	ld t3, 8(t5)
	mulhu a2, t3, a4
	mul t3, t3, a4
	add t0, t0, t3
	sltu t3, t0, t3
	add a2, a2, t3
	add t6, t6, a2
	sltu a2, t6, a2
	add a1, a1, a2
	ld t3, 0(t5)
	mulhu a2, t3, a7
	mul t3, t3, a7
	add t0, t0, t3
	sltu t3, t0, t3
	add a2, a2, t3
	add t6, t6, a2
	sltu a2, t6, a2
	add a1, a1, a2
	slli t3, a6, 32
	srli a2, a6, 32
	add t0, t0, t3
	sltu t3, t0, t3
	add a2, a2, t3
	add t6, t6, a2
	sltu a2, t6, a2
	add a1, a1, a2
	slli a2, a5, 32
	sltu t3, a5, a2
	sub a2, a5, a2
	sub t3, a5, t3
	srli a5, a5, 32
	sub t3, t3, a5
	add t6, t6, a2
	sltu a2, t6, a2
	add t3, t3, a2
	add a1, a1, t3
	sltu t3, a1, t3
	ld a5, 24(t5)
	mulhu a2, a5, a0
	mul a5, a5, a0
	add t6, t6, a5
	sltu a5, t6, a5
	add a2, a2, a5
	add a1, a1, a2
	sltu a2, a1, a2
	add t3, t3, a2
	ld a0, 24(t4)
	ld a5, 16(t5)
	mulhu a2, a5, a4
	mul a5, a5, a4
	add t6, t6, a5
	sltu a5, t6, a5
	add a2, a2, a5
	add a1, a1, a2
	sltu a2, a1, a2
	add t3, t3, a2
	ld a5, 8(t5)
	mulhu a2, a5, a7
	mul a5, a5, a7
	add t6, t6, a5
	sltu a5, t6, a5
	add a2, a2, a5
	add a1, a1, a2
	sltu a2, a1, a2
	add t3, t3, a2
	ld a5, 0(t5)
	mulhu a2, a5, a0
	mul a5, a5, a0
	add t6, t6, a5
	sltu a5, t6, a5
	add a2, a2, a5
	add a1, a1, a2
	sltu a2, a1, a2
	add t3, t3, a2
	slli a5, t0, 32
	srli a2, t0, 32
	add t6, t6, a5
	sltu a5, t6, a5
	add a2, a2, a5
	add a1, a1, a2
	sltu a2, a1, a2
	add t3, t3, a2
	slli a5, a6, 32
	sltu t4, a6, a5
	sub a5, a6, a5
	sub t4, a6, t4
	srli a6, a6, 32
	sub t4, t4, a6
	add a1, a1, a5
	sltu a5, a1, a5
	add t4, t4, a5
	add t3, t3, t4
	sltu t4, t3, t4
	ld a6, 24(t5)
	mulhu a2, a6, a4
	mul a5, a6, a4
	add a1, a1, a5
	sltu a5, a1, a5
	add a2, a2, a5
	add t3, t3, a2
	sltu a2, t3, a2
	add t4, t4, a2
	ld a5, 16(t5)
	mulhu a2, a5, a7
	mul a5, a5, a7
	add a1, a1, a5
	sltu a5, a1, a5
	add a2, a2, a5
	add t3, t3, a2
	sltu a2, t3, a2
	add t4, t4, a2
	ld a5, 8(t5)
	mulhu a2, a5, a0
	mul a5, a5, a0
	add a1, a1, a5
	sltu a5, a1, a5
	add a2, a2, a5
	add t3, t3, a2
	sltu a2, t3, a2
	add t4, t4, a2
	slli a5, t6, 32
	srli a2, t6, 32
	add a1, a1, a5
	sltu a5, a1, a5
	add a2, a2, a5
	add t3, t3, a2
	sltu a2, t3, a2
	add t4, t4, a2
	ld a5, 16(t5)
	slli a4, t0, 32
	sltu t5, t0, a4
	sub a4, t0, a4
	sub t5, t0, t5
	srli t0, t0, 32
	sub t5, t5, t0
	add t3, t3, a4
	sltu a4, t3, a4
	add t5, t5, a4
	add t4, t4, t5
	sltu t5, t4, t5
	mulhu a2, a5, a0
	mul a5, a5, a0
	add t3, t3, a5
	sltu a5, t3, a5
	add a2, a2, a5
	add t4, t4, a2
	sltu a2, t4, a2
	add t5, t5, a2
	mulhu a2, a6, a7
	mul a5, a6, a7
	add t3, t3, a5
	sltu a5, t3, a5
	add a2, a2, a5
	add t4, t4, a2
	sltu a2, t4, a2
	add t5, t5, a2
	slli a4, t6, 32
	sltu a2, t6, a4
	sub a4, t6, a4
	sub a2, t6, a2
	srli t6, t6, 32
	sub a2, a2, t6
	add t4, t4, a4
	sltu a4, t4, a4
	add a2, a2, a4
	add t5, t5, a2
	sltu a2, t5, a2
	mulhu a5, a6, a0
	mul a4, a6, a0
	add t4, t4, a4
	sltu a4, t4, a4
	add a5, a5, a4
	add t5, t5, a5
	sltu a5, t5, a5
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
	ret
	.option pop
