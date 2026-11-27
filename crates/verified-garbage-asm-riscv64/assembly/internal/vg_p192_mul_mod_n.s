// The functions of `src/internal/vg_p192_mul_mod_n.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p192_mul_mod_n:
	.option push
	.option arch, +m, +c
	add t2, a0, a1
	add t4, a0, a2
	add t5, a0, a3
	addi a3, a0, 2047
	addi a3, a3, 1
	sd s11, 1792(a3)
	sd s7, 1800(a3)
	sd s8, 1808(a3)
	sd s9, 1816(a3)
	sd s10, 1824(a3)
	beq t4, t5, 20f
	ld a4, 24(t4)
	ld a1, 8(t4)
	ld a0, 0(t4)
	ld a2, 16(t4)
	ld t4, 0(t5)
	mul a7, a1, t4
	mulhu t3, a0, t4
	add a7, a7, t3
	sltu t6, a7, t3
	mulhu s9, a1, t4
	mul t0, a0, t4
	add t3, s9, t6
	mul a5, a2, t4
	sd t0, 1856(a3)
	mulhu s9, a4, t4
	mulhu s10, a2, t4
	mul a6, a4, t4
	add a5, a5, t3
	sltu s11, a5, t3
	ld t4, 8(t5)
	mul t6, a0, t4
	add t3, s10, s11
	mulhu s10, a2, t4
	mul s11, a2, t4
	add a6, a6, t3
	sltu s7, a6, t3
	add a7, a7, t6
	add t3, s9, s7
	addi t0, t3, 0
	sltu t6, a7, t6
	add a6, a6, s11
	mul s7, a4, t4
	mulhu t3, a0, t4
	add t0, t0, s7
	sd a7, 1864(a3)
	add t3, t3, t6
	sltu s7, t0, s7
	mul t6, a1, t4
	add a5, a5, t6
	sltu t6, a5, t6
	mulhu s9, a1, t4
	sltu s11, a6, s11
	add a5, a5, t3
	add t6, s9, t6
	add s11, s10, s11
	sltu s9, a5, t3
	add t3, t6, s9
	add a6, a6, t3
	mulhu s9, a4, t4
	sltu s10, a6, t3
	add t3, s11, s10
	ld t4, 16(t5)
	add t0, t0, t3
	mul t6, a0, t4
	add s7, s9, s7
	sltu s9, t0, t3
	mul s11, a2, t4
	add t3, s7, s9
	mulhu s9, a1, t4
	add a5, a5, t6
	sltu t6, a5, t6
	addi a7, t3, 0
	add t0, t0, s11
	mulhu t3, a0, t4
	sd a5, 1872(a3)
	add t3, t3, t6
	sltu s11, t0, s11
	mul t6, a1, t4
	mul s7, a4, t4
	add a6, a6, t6
	mulhu s10, a2, t4
	add a7, a7, s7
	sltu t6, a6, t6
	add t6, s9, t6
	add a6, a6, t3
	sltu s9, a6, t3
	add s11, s10, s11
	add t3, t6, s9
	add t0, t0, t3
	sltu s7, a7, s7
	mulhu s9, a4, t4
	ld t4, 24(t5)
	sltu s10, t0, t3
	add s7, s9, s7
	mul t6, a0, t4
	add t3, s11, s10
	mul s11, a2, t4
	add a7, a7, t3
	sltu s9, a7, t3
	add t3, s7, s9
	mulhu s9, a1, t4
	mul s7, a4, t4
	addi a5, t3, 0
	add a5, a5, s7
	mulhu t3, a0, t4
	add a6, a6, t6
	sltu t6, a6, t6
	sd a6, 1880(a3)
	add t3, t3, t6
	add a7, a7, s11
	mul t6, a1, t4
	mulhu s10, a2, t4
	sltu s11, a7, s11
	sltu s7, a5, s7
	add s11, s10, s11
	add t0, t0, t6
	sltu t6, t0, t6
	add t6, s9, t6
	add t0, t0, t3
	sltu s9, t0, t3
	add t3, t6, s9
	mulhu s9, a4, t4
	add a7, a7, t3
	sd t0, 1888(a3)
	sd a7, 1896(a3)
	sltu s10, a7, t3
	add s7, s9, s7
	add t3, s11, s10
	add a5, a5, t3
	sltu s9, a5, t3
	sd a5, 1904(a3)
	add t3, s7, s9
	addi a6, t3, 0
	sd a6, 1912(a3)
	j 21f
20:
	ld a2, 16(t4)
	ld a0, 0(t4)
	mul a5, a2, a0
	ld a1, 8(t4)
	ld a4, 24(t4)
	mul a6, a4, a0
	mulhu t3, a1, a0
	add a5, a5, t3
	mulhu s9, a2, a0
	mul a7, a1, a0
	mulhu s10, a4, a0
	addi t4, zero, 0
	sltu t6, a5, t3
	add t3, s9, t6
	mul t6, a2, a1
	add a6, a6, t3
	sltu s11, a6, t3
	add a6, a6, t6
	sd a7, 1864(a3)
	add t3, s10, s11
	addi t0, t3, 0
	mulhu t3, a2, a1
	mulhu s9, a4, a1
	sltu t6, a6, t6
	sd a5, 1872(a3)
	add t3, t3, t6
	mul t6, a4, a1
	sd a6, 1880(a3)
	add t0, t0, t6
	sltu t6, t0, t6
	add t0, t0, t3
	add t6, s9, t6
	sltu s9, t0, t3
	sd t0, 1888(a3)
	mul t0, a0, a0
	add t3, t6, s9
	addi a7, t3, 0
	mul t6, a4, a2
	ld a6, 1864(a3)
	add a7, a7, t6
	mulhu t3, a4, a2
	sd a7, 1896(a3)
	sltu t6, a7, t6
	add t3, t3, t6
	addi a5, t3, 0
	sd a5, 1904(a3)
	addi t3, zero, 0
	sd t3, 1856(a3)
	mulhu a7, a0, a0
	sd t3, 1912(a3)
	ld a5, 1856(a3)
	srli t5, a5, 63
	slli a5, a5, 1
	add a5, a5, t4
	srli t4, a6, 63
	slli a6, a6, 1
	add a5, a5, t0
	sltu t0, a5, t0
	add a5, a5, t3
	add a6, a6, t5
	add a6, a6, a7
	sltu t3, a5, t3
	sltu a7, a6, a7
	sd a5, 1856(a3)
	add t3, t3, t0
	ld a5, 1872(a3)
	add a6, a6, t3
	sd a6, 1864(a3)
	mul t0, a1, a1
	srli t5, a5, 63
	sltu t3, a6, t3
	add t3, t3, a7
	ld a6, 1880(a3)
	mulhu a7, a1, a1
	slli a5, a5, 1
	add a5, a5, t4
	add a5, a5, t0
	sltu t0, a5, t0
	add a5, a5, t3
	sltu t3, a5, t3
	srli t4, a6, 63
	slli a6, a6, 1
	add t3, t3, t0
	sd a5, 1872(a3)
	ld a5, 1888(a3)
	add a6, a6, t5
	add a6, a6, a7
	mul t0, a2, a2
	srli t5, a5, 63
	sltu a7, a6, a7
	add a6, a6, t3
	sltu t3, a6, t3
	sd a6, 1880(a3)
	add t3, t3, a7
	slli a5, a5, 1
	ld a6, 1896(a3)
	mulhu a7, a2, a2
	add a5, a5, t4
	add a5, a5, t0
	srli t4, a6, 63
	sltu t0, a5, t0
	add a5, a5, t3
	sltu t3, a5, t3
	sd a5, 1888(a3)
	slli a6, a6, 1
	add a6, a6, t5
	add a6, a6, a7
	add t3, t3, t0
	sltu a7, a6, a7
	ld a5, 1904(a3)
	mul t0, a4, a4
	add a6, a6, t3
	sd a6, 1896(a3)
	sltu t3, a6, t3
	ld a6, 1912(a3)
	srli t5, a5, 63
	add t3, t3, a7
	mulhu a7, a4, a4
	slli a5, a5, 1
	add a5, a5, t4
	add a5, a5, t0
	srli t4, a6, 63
	sltu t0, a5, t0
	add a5, a5, t3
	slli a6, a6, 1
	add a6, a6, t5
	sd a5, 1904(a3)
	add a6, a6, a7
	sltu a7, a6, a7
	sltu t3, a5, t3
	add t3, t3, t0
	add a6, a6, t3
	sltu t3, a6, t3
	add t3, t3, a7
	sd a6, 1912(a3)
21:
	lui a1, 0
	lui t6, 740643
	lui a0, 83645
	addiw a0, a0, -1614
	ld t0, 1856(a3)
	lui t5, 557671
	addiw t5, t5, 519
	slli a0, a0, 32
	addiw t6, t6, -1999
	add a0, a0, t6
	ld a6, 1880(a3)
	lui t6, 56765
	ld a5, 1872(a3)
	addiw t6, t6, -209
	slli t5, t5, 32
	add t5, t5, t6
	mul t0, t0, t5
	ld a7, 1864(a3)
	addiw a1, a1, 0
	slli a1, a1, 32
	lui s11, 630256
	addiw s11, s11, -1994
	lui a2, 0
	addi t6, zero, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	add a1, a1, s11
	lui s7, 0
	mulhu t3, t0, a0
	addiw s7, s7, -1
	lui a4, 0
	sltu t6, t6, t0
	mulhu s9, a1, t0
	lui s8, 0
	add a2, a2, s7
	mul s11, a2, t0
	add t3, t3, t6
	addiw s8, s8, 0
	addiw a4, a4, 0
	mul t6, a1, t0
	slli a4, a4, 32
	mulhu s10, a2, t0
	addi t4, zero, 0
	add a7, a7, t6
	sltu t6, a7, t6
	add a5, a5, s11
	add a7, a7, t3
	sltu s11, a5, s11
	add a4, a4, s8
	add t6, s9, t6
	sltu s9, a7, t3
	mul s7, a4, t0
	add t3, t6, s9
	add s11, s10, s11
	mul a7, a7, t5
	mulhu s9, a4, t0
	add a5, a5, t3
	sltu s10, a5, t3
	ld t0, 1888(a3)
	add a6, a6, s7
	sltu s7, a6, s7
	add t3, s11, s10
	add a6, a6, t3
	add s7, s9, s7
	sltu s9, a6, t3
	add t3, s7, s9
	mulhu s9, a1, a7
	add t0, t0, t3
	sltu t6, t0, t3
	mul s11, a2, a7
	add t0, t0, t4
	sltu t4, t0, t4
	add t4, t4, t6
	addi t6, zero, 0
	mulhu t3, a7, a0
	mulhu s10, a2, a7
	sltu t6, t6, a7
	add a6, a6, s11
	add t3, t3, t6
	mul t6, a1, a7
	mul s7, a4, a7
	add a5, a5, t6
	sltu t6, a5, t6
	add t6, s9, t6
	sltu s11, a6, s11
	add s11, s10, s11
	add a5, a5, t3
	sltu s9, a5, t3
	add t3, t6, s9
	mulhu s9, a4, a7
	add t0, t0, s7
	mul a5, a5, t5
	add a6, a6, t3
	sltu s10, a6, t3
	ld a7, 1896(a3)
	sltu s7, t0, s7
	add t3, s11, s10
	add t0, t0, t3
	add s7, s9, s7
	sltu s9, t0, t3
	add t3, s7, s9
	mulhu s10, a2, a5
	add a7, a7, t3
	mul s11, a2, a5
	sltu t6, a7, t3
	mulhu s9, a1, a5
	add a7, a7, t4
	sltu t4, a7, t4
	add t4, t4, t6
	addi t6, zero, 0
	mul s7, a4, a5
	mulhu t3, a5, a0
	add t0, t0, s11
	sltu t6, t6, a5
	sltu s11, t0, s11
	add t3, t3, t6
	mul t6, a1, a5
	add a6, a6, t6
	add s11, s10, s11
	sltu t6, a6, t6
	add t6, s9, t6
	add a7, a7, s7
	sltu s7, a7, s7
	add a6, a6, t3
	sltu s9, a6, t3
	add t3, t6, s9
	mulhu s9, a4, a5
	mul a6, a6, t5
	ld a5, 1904(a3)
	add t0, t0, t3
	add s7, s9, s7
	sltu s10, t0, t3
	add t3, s11, s10
	mul s11, a2, a6
	add a7, a7, t3
	mulhu s10, a2, a6
	sltu s9, a7, t3
	add t3, s7, s9
	add a5, a5, t3
	mulhu s9, a1, a6
	sltu t6, a5, t3
	add a5, a5, t4
	mul s7, a4, a6
	sltu t4, a5, t4
	add t4, t4, t6
	mulhu t3, a6, a0
	addi t6, zero, 0
	sltu t6, t6, a6
	add t3, t3, t6
	mul t6, a1, a6
	add t0, t0, t6
	sltu t6, t0, t6
	add t6, s9, t6
	add t0, t0, t3
	add a5, a5, s7
	add a7, a7, s11
	sltu s9, t0, t3
	add t3, t6, s9
	sltu s11, a7, s11
	add a7, a7, t3
	add s11, s10, s11
	sltu s7, a5, s7
	mulhu s9, a4, a6
	ld a6, 1912(a3)
	add s7, s9, s7
	sltu s10, a7, t3
	add t3, s11, s10
	sltu s11, a7, a1
	add a5, a5, t3
	sltu s9, a5, t3
	add t3, s7, s9
	sltu s7, a5, a2
	add a6, a6, t3
	sltu t6, a6, t3
	addi t3, zero, 0
	add a6, a6, t4
	sub a1, a7, a1
	sub a2, a5, a2
	sltu t4, a6, t4
	add t4, t4, t6
	sltu s8, a6, a4
	sltu t6, t0, a0
	sub a0, t0, a0
	sltu s9, a0, t3
	sub a0, a0, t3
	add t3, t6, s9
	sltu s10, a1, t3
	sub a1, a1, t3
	add t3, s11, s10
	sltu s9, a2, t3
	sub a2, a2, t3
	sub a4, a6, a4
	add t3, s7, s9
	sltu s10, a4, t3
	xor a7, a7, a1
	xor t0, t0, a0
	sub a4, a4, t3
	add t3, s8, s10
	xor a5, a5, a2
	sub t4, t4, t3
	and t0, t0, t4
	xor t0, t0, a0
	sd t0, 0(t2)
	and a7, a7, t4
	xor a7, a7, a1
	and a5, a5, t4
	sd a7, 8(t2)
	xor a6, a6, a4
	xor a5, a5, a2
	sd a5, 16(t2)
	and a6, a6, t4
	xor a6, a6, a4
	sd a6, 24(t2)
	ld s11, 1792(a3)
	ld s7, 1800(a3)
	ld s8, 1808(a3)
	ld s9, 1816(a3)
	ld s10, 1824(a3)
	ret
	.option pop
