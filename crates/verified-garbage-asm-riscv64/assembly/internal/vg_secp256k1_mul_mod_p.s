// The functions of `src/internal/vg_secp256k1_mul_mod_p.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_secp256k1_mul_mod_p:
	.option push
	.option arch, +m, +c
	add t2, a0, a1
	add t4, a0, a2
	add t5, a0, a3
	addi a3, a0, 2047
	addi a3, a3, 1
	sd t1, 1792(a3)
	sd s7, 1800(a3)
	sd s8, 1808(a3)
	beq t4, t5, 20f
	ld a0, 0(t4)
	ld a4, 24(t4)
	ld a1, 8(t4)
	ld a2, 16(t4)
	ld t4, 0(t5)
	mulhu t3, a0, t4
	mul a7, a1, t4
	add a7, a7, t3
	mul a5, a2, t4
	sltu t6, a7, t3
	mulhu s8, a1, t4
	mul t0, a0, t4
	add t3, s8, t6
	mulhu s8, a2, t4
	add a5, a5, t3
	sltu t1, a5, t3
	mul a6, a4, t4
	sd t0, 1856(a3)
	add t3, s8, t1
	mulhu s8, a4, t4
	ld t4, 8(t5)
	add a6, a6, t3
	sltu s7, a6, t3
	add t3, s8, s7
	mul t6, a0, t4
	mul t1, a2, t4
	mulhu s8, a1, t4
	addi t0, t3, 0
	mul s7, a4, t4
	mulhu t3, a0, t4
	add a7, a7, t6
	add t0, t0, s7
	sltu t6, a7, t6
	sd a7, 1864(a3)
	add a6, a6, t1
	add t3, t3, t6
	sltu s7, t0, s7
	mul t6, a1, t4
	add a5, a5, t6
	sltu t1, a6, t1
	sltu t6, a5, t6
	add t6, s8, t6
	add a5, a5, t3
	sltu s8, a5, t3
	add t3, t6, s8
	add a6, a6, t3
	mulhu s8, a2, t4
	add t1, s8, t1
	sltu s8, a6, t3
	add t3, t1, s8
	mulhu s8, a4, t4
	add t0, t0, t3
	ld t4, 16(t5)
	mul t6, a0, t4
	mul t1, a2, t4
	add s7, s8, s7
	sltu s8, t0, t3
	add t0, t0, t1
	add t3, s7, s8
	addi a7, t3, 0
	add a5, a5, t6
	sltu t1, t0, t1
	sltu t6, a5, t6
	mulhu t3, a0, t4
	add t3, t3, t6
	mul t6, a1, t4
	mul s7, a4, t4
	add a6, a6, t6
	add a7, a7, s7
	sltu t6, a6, t6
	mulhu s8, a1, t4
	add t6, s8, t6
	add a6, a6, t3
	sltu s8, a6, t3
	add t3, t6, s8
	sd a5, 1872(a3)
	sltu s7, a7, s7
	mulhu s8, a2, t4
	add t0, t0, t3
	add t1, s8, t1
	sltu s8, t0, t3
	add t3, t1, s8
	mulhu s8, a4, t4
	ld t4, 24(t5)
	mul t6, a0, t4
	add a7, a7, t3
	mul t1, a2, t4
	add s7, s8, s7
	sltu s8, a7, t3
	add a6, a6, t6
	add t3, s7, s8
	addi a5, t3, 0
	sltu t6, a6, t6
	mulhu t3, a0, t4
	add a7, a7, t1
	add t3, t3, t6
	mul t6, a1, t4
	mul s7, a4, t4
	add t0, t0, t6
	sd a6, 1880(a3)
	mulhu s8, a1, t4
	sltu t6, t0, t6
	add t0, t0, t3
	sltu t1, a7, t1
	add t6, s8, t6
	sd t0, 1888(a3)
	sltu s8, t0, t3
	add t3, t6, s8
	add a5, a5, s7
	add a7, a7, t3
	mulhu s8, a2, t4
	sltu s7, a5, s7
	sd a7, 1896(a3)
	add t1, s8, t1
	sltu s8, a7, t3
	add t3, t1, s8
	mulhu s8, a4, t4
	add s7, s8, s7
	add a5, a5, t3
	sltu s8, a5, t3
	sd a5, 1904(a3)
	add t3, s7, s8
	addi a6, t3, 0
	sd a6, 1912(a3)
	j 21f
20:
	ld a0, 0(t4)
	ld a2, 16(t4)
	ld a1, 8(t4)
	mul a5, a2, a0
	mulhu t3, a1, a0
	ld a4, 24(t4)
	add a5, a5, t3
	addi t4, zero, 0
	mulhu s8, a2, a0
	sltu t6, a5, t3
	add t3, s8, t6
	mul a7, a1, a0
	mul a6, a4, a0
	mul t6, a2, a1
	add a6, a6, t3
	mulhu s8, a4, a0
	sltu t1, a6, t3
	add a6, a6, t6
	sd a7, 1864(a3)
	sd a5, 1872(a3)
	add t3, s8, t1
	mulhu s8, a4, a1
	addi t0, t3, 0
	mulhu t3, a2, a1
	sd a6, 1880(a3)
	sltu t6, a6, t6
	ld a6, 1864(a3)
	add t3, t3, t6
	mul t6, a4, a1
	add t0, t0, t6
	sltu t6, t0, t6
	add t6, s8, t6
	add t0, t0, t3
	sltu s8, t0, t3
	add t3, t6, s8
	mul t6, a4, a2
	addi a7, t3, 0
	add a7, a7, t6
	mulhu t3, a4, a2
	sd t0, 1888(a3)
	sltu t6, a7, t6
	mul t0, a0, a0
	sd a7, 1896(a3)
	add t3, t3, t6
	addi a5, t3, 0
	sd a5, 1904(a3)
	addi t3, zero, 0
	sd t3, 1856(a3)
	ld a5, 1856(a3)
	srli t5, a5, 63
	slli a5, a5, 1
	add a5, a5, t4
	srli t4, a6, 63
	add a5, a5, t0
	mulhu a7, a0, a0
	sd t3, 1912(a3)
	slli a6, a6, 1
	sltu t0, a5, t0
	add a5, a5, t3
	sd a5, 1856(a3)
	sltu t3, a5, t3
	ld a5, 1872(a3)
	add a6, a6, t5
	add t3, t3, t0
	add a6, a6, a7
	sltu a7, a6, a7
	mul t0, a1, a1
	srli t5, a5, 63
	slli a5, a5, 1
	add a6, a6, t3
	sd a6, 1864(a3)
	add a5, a5, t4
	add a5, a5, t0
	sltu t3, a6, t3
	ld a6, 1880(a3)
	sltu t0, a5, t0
	add t3, t3, a7
	add a5, a5, t3
	srli t4, a6, 63
	mulhu a7, a1, a1
	sltu t3, a5, t3
	sd a5, 1872(a3)
	slli a6, a6, 1
	add a6, a6, t5
	add t3, t3, t0
	mul t0, a2, a2
	add a6, a6, a7
	ld a5, 1888(a3)
	sltu a7, a6, a7
	srli t5, a5, 63
	slli a5, a5, 1
	add a6, a6, t3
	sltu t3, a6, t3
	add t3, t3, a7
	sd a6, 1880(a3)
	add a5, a5, t4
	mulhu a7, a2, a2
	add a5, a5, t0
	ld a6, 1896(a3)
	sltu t0, a5, t0
	add a5, a5, t3
	srli t4, a6, 63
	slli a6, a6, 1
	sltu t3, a5, t3
	add t3, t3, t0
	add a6, a6, t5
	sd a5, 1888(a3)
	ld a5, 1904(a3)
	mul t0, a4, a4
	add a6, a6, a7
	srli t5, a5, 63
	sltu a7, a6, a7
	add a6, a6, t3
	sd a6, 1896(a3)
	slli a5, a5, 1
	sltu t3, a6, t3
	add t3, t3, a7
	add a5, a5, t4
	ld a6, 1912(a3)
	srli t4, a6, 63
	add a5, a5, t0
	sltu t0, a5, t0
	add a5, a5, t3
	sltu t3, a5, t3
	add t3, t3, t0
	slli a6, a6, 1
	add a6, a6, t5
	mulhu a7, a4, a4
	add a6, a6, a7
	sltu a7, a6, a7
	sd a5, 1904(a3)
	add a6, a6, t3
	sd a6, 1912(a3)
	sltu t3, a6, t3
	add t3, t3, a7
21:
	ld a0, 1856(a3)
	lui t5, 885633
	addiw t5, t5, -1762
	ld t0, 1888(a3)
	lui t6, 860755
	addiw t6, t6, 1329
	slli t5, t5, 32
	lui s8, 0
	add t5, t5, t6
	mul a0, a0, t5
	ld a2, 1872(a3)
	ld a6, 1912(a3)
	addiw s8, s8, 1
	lui t6, 0
	slli s8, s8, 32
	addiw t6, t6, 977
	ld a4, 1880(a3)
	ld a1, 1864(a3)
	add s8, s8, t6
	ld a7, 1896(a3)
	mulhu t3, a0, s8
	ld a5, 1904(a3)
	add t0, t0, a0
	sltu t6, a1, t3
	sub a1, a1, t3
	sltu t4, t0, a0
	mul a1, a1, t5
	mulhu t3, a1, s8
	add t3, t3, t6
	sltu t6, a2, t3
	add a7, a7, a1
	sub a2, a2, t3
	mul a2, a2, t5
	mulhu t3, a2, s8
	add t3, t3, t6
	sltu t6, a4, t3
	sub a4, a4, t3
	add a5, a5, a2
	mul a4, a4, t5
	mulhu t3, a4, s8
	add t3, t3, t6
	sltu t6, a7, a1
	add a7, a7, t4
	sub s8, s8, t3
	sltu t4, a7, t4
	sltu t5, t0, t3
	add t4, t4, t6
	add a0, t0, s8
	sltu t6, a5, a2
	add a5, a5, t4
	add a6, a6, a4
	sltu t4, a5, t4
	add t4, t4, t6
	sltu t6, a6, a4
	add a6, a6, t4
	sub t0, t0, t3
	sltu t4, a6, t4
	add t4, t4, t6
	sltu t6, a0, s8
	sltu t3, a7, t5
	add a1, a7, t6
	xor a0, a0, t0
	sltu t6, a1, t6
	sub a7, a7, t5
	add a2, a5, t6
	sltu t6, a2, t6
	sltu t5, a5, t3
	add a4, a6, t6
	sltu t6, a4, t6
	sub a5, a5, t3
	sub a6, a6, t5
	or t4, t4, t6
	addi t6, zero, 0
	sub t4, t6, t4
	xor a1, a1, a7
	and a0, a0, t4
	and a1, a1, t4
	xor a0, a0, t0
	sd a0, 0(t2)
	xor a2, a2, a5
	xor a1, a1, a7
	xor a4, a4, a6
	sd a1, 8(t2)
	and a2, a2, t4
	xor a2, a2, a5
	sd a2, 16(t2)
	and a4, a4, t4
	xor a4, a4, a6
	sd a4, 24(t2)
	ld t1, 1792(a3)
	ld s7, 1800(a3)
	ld s8, 1808(a3)
	ret
	.option pop
