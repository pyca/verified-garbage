// The functions of `src/internal/vg_p192_mul_mod_p.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p192_mul_mod_p:
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
	j 21f
20:
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
21:
	sd s7, 1792(a3)
	sd s8, 1800(a3)
	sd s9, 1808(a3)
	sd s10, 1816(a3)
	sd s11, 1824(a3)
	lui s7, 0
	addiw s7, s7, 0
	slli s7, s7, 32
	lui a0, 0
	addiw a0, a0, 1
	add s7, s7, a0
	lui s8, 0
	addiw s8, s8, 0
	slli s8, s8, 32
	lui a0, 0
	addiw a0, a0, -1
	add s8, s8, a0
	lui s9, 0
	addiw s9, s9, 0
	slli s9, s9, 32
	lui a0, 0
	addiw a0, a0, -2
	add s9, s9, a0
	lui s10, 0
	addiw s10, s10, 0
	slli s10, s10, 32
	lui a0, 0
	addiw a0, a0, -1
	add s10, s10, a0
	lui s11, 0
	addiw s11, s11, 0
	slli s11, s11, 32
	lui a0, 0
	addiw a0, a0, 0
	add s11, s11, a0
	ld t3, 1856(a3)
	ld t4, 1864(a3)
	ld t5, 1872(a3)
	ld t6, 1880(a3)
	addi a2, zero, 0
	ld a1, 1888(a3)
	mul t3, t3, s7
	mulhu a4, t3, s8
	addi a0, zero, 0
	sltu a0, a0, t3
	add a4, a4, a0
	mul a5, t3, s9
	mulhu a6, t3, s9
	add a5, a5, a4
	sltu a7, a5, a4
	add a6, a6, a7
	add t4, t4, a5
	sltu a7, t4, a5
	add a4, a6, a7
	mul a5, t3, s10
	mulhu a6, t3, s10
	add a5, a5, a4
	sltu a7, a5, a4
	add a6, a6, a7
	add t5, t5, a5
	sltu a7, t5, a5
	add a4, a6, a7
	mul a5, t3, s11
	mulhu a6, t3, s11
	add a5, a5, a4
	sltu a7, a5, a4
	add a6, a6, a7
	add t6, t6, a5
	sltu a7, t6, a5
	add a4, a6, a7
	add a1, a1, a4
	sltu a7, a1, a4
	add a1, a1, a2
	sltu a2, a1, a2
	add a2, a2, a7
	ld t3, 1896(a3)
	mul t4, t4, s7
	mulhu a4, t4, s8
	addi a0, zero, 0
	sltu a0, a0, t4
	add a4, a4, a0
	mul a5, t4, s9
	mulhu a6, t4, s9
	add a5, a5, a4
	sltu a7, a5, a4
	add a6, a6, a7
	add t5, t5, a5
	sltu a7, t5, a5
	add a4, a6, a7
	mul a5, t4, s10
	mulhu a6, t4, s10
	add a5, a5, a4
	sltu a7, a5, a4
	add a6, a6, a7
	add t6, t6, a5
	sltu a7, t6, a5
	add a4, a6, a7
	mul a5, t4, s11
	mulhu a6, t4, s11
	add a5, a5, a4
	sltu a7, a5, a4
	add a6, a6, a7
	add a1, a1, a5
	sltu a7, a1, a5
	add a4, a6, a7
	add t3, t3, a4
	sltu a7, t3, a4
	add t3, t3, a2
	sltu a2, t3, a2
	add a2, a2, a7
	ld t4, 1904(a3)
	mul t5, t5, s7
	mulhu a4, t5, s8
	addi a0, zero, 0
	sltu a0, a0, t5
	add a4, a4, a0
	mul a5, t5, s9
	mulhu a6, t5, s9
	add a5, a5, a4
	sltu a7, a5, a4
	add a6, a6, a7
	add t6, t6, a5
	sltu a7, t6, a5
	add a4, a6, a7
	mul a5, t5, s10
	mulhu a6, t5, s10
	add a5, a5, a4
	sltu a7, a5, a4
	add a6, a6, a7
	add a1, a1, a5
	sltu a7, a1, a5
	add a4, a6, a7
	mul a5, t5, s11
	mulhu a6, t5, s11
	add a5, a5, a4
	sltu a7, a5, a4
	add a6, a6, a7
	add t3, t3, a5
	sltu a7, t3, a5
	add a4, a6, a7
	add t4, t4, a4
	sltu a7, t4, a4
	add t4, t4, a2
	sltu a2, t4, a2
	add a2, a2, a7
	ld t5, 1912(a3)
	mul t6, t6, s7
	mulhu a4, t6, s8
	addi a0, zero, 0
	sltu a0, a0, t6
	add a4, a4, a0
	mul a5, t6, s9
	mulhu a6, t6, s9
	add a5, a5, a4
	sltu a7, a5, a4
	add a6, a6, a7
	add a1, a1, a5
	sltu a7, a1, a5
	add a4, a6, a7
	mul a5, t6, s10
	mulhu a6, t6, s10
	add a5, a5, a4
	sltu a7, a5, a4
	add a6, a6, a7
	add t3, t3, a5
	sltu a7, t3, a5
	add a4, a6, a7
	mul a5, t6, s11
	mulhu a6, t6, s11
	add a5, a5, a4
	sltu a7, a5, a4
	add a6, a6, a7
	add t4, t4, a5
	sltu a7, t4, a5
	add a4, a6, a7
	add t5, t5, a4
	sltu a7, t5, a4
	add t5, t5, a2
	sltu a2, t5, a2
	add a2, a2, a7
	ld s7, 1792(a3)
	ld s8, 1800(a3)
	ld s9, 1808(a3)
	ld s10, 1816(a3)
	ld s11, 1824(a3)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui a0, 0
	addiw a0, a0, 1
	add t0, t0, a0
	add t6, a1, t0
	sltu a7, t6, t0
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui a0, 0
	addiw a0, a0, 1
	add t0, t0, a0
	add a4, t3, t0
	sltu a0, a4, t0
	add a4, a4, a7
	sltu a7, a4, a7
	add a7, a7, a0
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui a0, 0
	addiw a0, a0, 0
	add t0, t0, a0
	add a5, t4, t0
	sltu a0, a5, t0
	add a5, a5, a7
	sltu a7, a5, a7
	add a7, a7, a0
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui a0, 0
	addiw a0, a0, -1
	add t0, t0, a0
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
