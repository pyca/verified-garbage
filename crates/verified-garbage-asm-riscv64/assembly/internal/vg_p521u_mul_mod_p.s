// The functions of `src/internal/vg_p521u_mul_mod_p.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p521u_mul_mod_p:
	.option push
	.option arch, +m, +c
	add t2, a0, a1
	add t4, a0, a2
	add t5, a0, a3
	addi a3, a0, 2047
	addi a3, a3, 2047
	addi a3, a3, 2047
	addi a3, a3, 3
	beq t4, t5, 20f
	addi a6, zero, -1
	srli a6, a6, 6
	ld a1, 0(t5)
	slli a1, a1, 1
	sd a1, 1544(a3)
	ld a1, 8(t5)
	slli a1, a1, 1
	sd a1, 1552(a3)
	ld a1, 16(t5)
	slli a1, a1, 1
	sd a1, 1560(a3)
	ld a1, 24(t5)
	slli a1, a1, 1
	sd a1, 1568(a3)
	ld a1, 32(t5)
	slli a1, a1, 1
	sd a1, 1576(a3)
	ld a1, 40(t5)
	slli a1, a1, 1
	sd a1, 1584(a3)
	ld a1, 48(t5)
	slli a1, a1, 1
	sd a1, 1592(a3)
	ld a1, 56(t5)
	slli a1, a1, 1
	sd a1, 1600(a3)
	ld a1, 64(t5)
	slli a1, a1, 1
	sd a1, 1608(a3)
	addi a4, zero, 0
	addi a5, zero, 0
	ld a1, 0(t4)
	ld a2, 0(t5)
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 8(t4)
	ld a2, 1608(a3)
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 16(t4)
	ld a2, 1600(a3)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 24(t4)
	ld a2, 1592(a3)
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 32(t4)
	ld a2, 1584(a3)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 40(t4)
	ld a2, 1576(a3)
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 48(t4)
	ld a2, 1568(a3)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 56(t4)
	ld a2, 1560(a3)
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 64(t4)
	ld a2, 1552(a3)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 0(t4)
	ld a2, 8(t5)
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 8(t4)
	ld a2, 0(t5)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	and a7, a4, a6
	sd a7, 1472(a3)
	srli a7, a4, 58
	slli t0, a5, 6
	or a4, a7, t0
	srli a5, a5, 58
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 16(t4)
	ld a2, 1608(a3)
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 24(t4)
	ld a2, 1600(a3)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 32(t4)
	ld a2, 1592(a3)
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 40(t4)
	ld a2, 1584(a3)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 48(t4)
	ld a2, 1576(a3)
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 56(t4)
	ld a2, 1568(a3)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 64(t4)
	ld a2, 1560(a3)
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 0(t4)
	ld a2, 16(t5)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 8(t4)
	ld a2, 8(t5)
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	and t3, a4, a6
	sd t3, 1480(a3)
	srli t3, a4, 58
	slli t6, a5, 6
	or a4, t3, t6
	srli a5, a5, 58
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 16(t4)
	ld a2, 0(t5)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 24(t4)
	ld a2, 1608(a3)
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 32(t4)
	ld a2, 1600(a3)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 40(t4)
	ld a2, 1592(a3)
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 48(t4)
	ld a2, 1584(a3)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 56(t4)
	ld a2, 1576(a3)
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 64(t4)
	ld a2, 1568(a3)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 0(t4)
	ld a2, 24(t5)
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 8(t4)
	ld a2, 16(t5)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	and a7, a4, a6
	sd a7, 1488(a3)
	srli a7, a4, 58
	slli t0, a5, 6
	or a4, a7, t0
	srli a5, a5, 58
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 16(t4)
	ld a2, 8(t5)
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 24(t4)
	ld a2, 0(t5)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 32(t4)
	ld a2, 1608(a3)
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 40(t4)
	ld a2, 1600(a3)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 48(t4)
	ld a2, 1592(a3)
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 56(t4)
	ld a2, 1584(a3)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 64(t4)
	ld a2, 1576(a3)
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 0(t4)
	ld a2, 32(t5)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 8(t4)
	ld a2, 24(t5)
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	and t3, a4, a6
	sd t3, 1496(a3)
	srli t3, a4, 58
	slli t6, a5, 6
	or a4, t3, t6
	srli a5, a5, 58
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 16(t4)
	ld a2, 16(t5)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 24(t4)
	ld a2, 8(t5)
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 32(t4)
	ld a2, 0(t5)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 40(t4)
	ld a2, 1608(a3)
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 48(t4)
	ld a2, 1600(a3)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 56(t4)
	ld a2, 1592(a3)
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 64(t4)
	ld a2, 1584(a3)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 0(t4)
	ld a2, 40(t5)
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 8(t4)
	ld a2, 32(t5)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	and a7, a4, a6
	sd a7, 1504(a3)
	srli a7, a4, 58
	slli t0, a5, 6
	or a4, a7, t0
	srli a5, a5, 58
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 16(t4)
	ld a2, 24(t5)
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 24(t4)
	ld a2, 16(t5)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 32(t4)
	ld a2, 8(t5)
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 40(t4)
	ld a2, 0(t5)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 48(t4)
	ld a2, 1608(a3)
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 56(t4)
	ld a2, 1600(a3)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 64(t4)
	ld a2, 1592(a3)
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 0(t4)
	ld a2, 48(t5)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 8(t4)
	ld a2, 40(t5)
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	and t3, a4, a6
	sd t3, 1512(a3)
	srli t3, a4, 58
	slli t6, a5, 6
	or a4, t3, t6
	srli a5, a5, 58
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 16(t4)
	ld a2, 32(t5)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 24(t4)
	ld a2, 24(t5)
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 32(t4)
	ld a2, 16(t5)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 40(t4)
	ld a2, 8(t5)
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 48(t4)
	ld a2, 0(t5)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 56(t4)
	ld a2, 1608(a3)
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 64(t4)
	ld a2, 1600(a3)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 0(t4)
	ld a2, 56(t5)
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 8(t4)
	ld a2, 48(t5)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	and a7, a4, a6
	sd a7, 1520(a3)
	srli a7, a4, 58
	slli t0, a5, 6
	or a4, a7, t0
	srli a5, a5, 58
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 16(t4)
	ld a2, 40(t5)
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 24(t4)
	ld a2, 32(t5)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 32(t4)
	ld a2, 24(t5)
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 40(t4)
	ld a2, 16(t5)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 48(t4)
	ld a2, 8(t5)
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 56(t4)
	ld a2, 0(t5)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 64(t4)
	ld a2, 1608(a3)
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 0(t4)
	ld a2, 64(t5)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 8(t4)
	ld a2, 56(t5)
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	and t3, a4, a6
	sd t3, 1528(a3)
	srli t3, a4, 58
	slli t6, a5, 6
	or a4, t3, t6
	srli a5, a5, 58
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 16(t4)
	ld a2, 48(t5)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 24(t4)
	ld a2, 40(t5)
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 32(t4)
	ld a2, 32(t5)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 40(t4)
	ld a2, 24(t5)
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 48(t4)
	ld a2, 16(t5)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 56(t4)
	ld a2, 8(t5)
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 64(t4)
	ld a2, 0(t5)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	mul a7, a1, a2
	mulhu t0, a1, a2
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	and a7, a4, a6
	sd a7, 1536(a3)
	srli a7, a4, 58
	slli t0, a5, 6
	or a4, a7, t0
	srli a5, a5, 58
	ld a1, 1472(a3)
	ld a2, 1480(a3)
	slli t3, a4, 1
	and t3, t3, a6
	add a1, a1, t3
	srli t3, a4, 57
	slli t6, a5, 7
	add t3, t3, t6
	add a2, a2, t3
	srli t3, a1, 58
	and a1, a1, a6
	add a2, a2, t3
	sd a1, 0(t2)
	sd a2, 8(t2)
	ld a1, 1488(a3)
	sd a1, 16(t2)
	ld a1, 1496(a3)
	sd a1, 24(t2)
	ld a1, 1504(a3)
	sd a1, 32(t2)
	ld a1, 1512(a3)
	sd a1, 40(t2)
	ld a1, 1520(a3)
	sd a1, 48(t2)
	ld a1, 1528(a3)
	sd a1, 56(t2)
	ld a1, 1536(a3)
	sd a1, 64(t2)
	j 21f
20:
	addi a6, zero, -1
	srli a6, a6, 6
	ld a1, 0(t4)
	slli a1, a1, 1
	sd a1, 1544(a3)
	ld a1, 8(t4)
	slli a1, a1, 1
	sd a1, 1552(a3)
	ld a1, 16(t4)
	slli a1, a1, 1
	sd a1, 1560(a3)
	ld a1, 24(t4)
	slli a1, a1, 1
	sd a1, 1568(a3)
	ld a1, 32(t4)
	slli a1, a1, 1
	sd a1, 1576(a3)
	ld a1, 40(t4)
	slli a1, a1, 1
	sd a1, 1584(a3)
	ld a1, 48(t4)
	slli a1, a1, 1
	sd a1, 1592(a3)
	ld a1, 56(t4)
	slli a1, a1, 1
	sd a1, 1600(a3)
	ld a1, 64(t4)
	slli a1, a1, 1
	sd a1, 1608(a3)
	addi a4, zero, 0
	addi a5, zero, 0
	ld a1, 0(t4)
	ld a2, 0(t4)
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 1584(a3)
	ld a2, 1576(a3)
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 1592(a3)
	ld a2, 1568(a3)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 1600(a3)
	ld a2, 1560(a3)
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 1608(a3)
	ld a2, 1552(a3)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 8(t4)
	ld a2, 1544(a3)
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 1592(a3)
	ld a2, 1576(a3)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	and a7, a4, a6
	sd a7, 1472(a3)
	srli a7, a4, 58
	slli t0, a5, 6
	or a4, a7, t0
	srli a5, a5, 58
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 1600(a3)
	ld a2, 1568(a3)
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 1608(a3)
	ld a2, 1560(a3)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 40(t4)
	ld a2, 1584(a3)
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 16(t4)
	ld a2, 1544(a3)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 8(t4)
	ld a2, 8(t4)
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	and t3, a4, a6
	sd t3, 1480(a3)
	srli t3, a4, 58
	slli t6, a5, 6
	or a4, t3, t6
	srli a5, a5, 58
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 1592(a3)
	ld a2, 1584(a3)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 1600(a3)
	ld a2, 1576(a3)
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 1608(a3)
	ld a2, 1568(a3)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 16(t4)
	ld a2, 1552(a3)
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 24(t4)
	ld a2, 1544(a3)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	and a7, a4, a6
	sd a7, 1488(a3)
	srli a7, a4, 58
	slli t0, a5, 6
	or a4, a7, t0
	srli a5, a5, 58
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 1600(a3)
	ld a2, 1584(a3)
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 1608(a3)
	ld a2, 1576(a3)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 48(t4)
	ld a2, 1592(a3)
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 24(t4)
	ld a2, 1552(a3)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 32(t4)
	ld a2, 1544(a3)
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	and t3, a4, a6
	sd t3, 1496(a3)
	srli t3, a4, 58
	slli t6, a5, 6
	or a4, t3, t6
	srli a5, a5, 58
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 16(t4)
	ld a2, 16(t4)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 1600(a3)
	ld a2, 1592(a3)
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 1608(a3)
	ld a2, 1584(a3)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 24(t4)
	ld a2, 1560(a3)
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 32(t4)
	ld a2, 1552(a3)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	and a7, a4, a6
	sd a7, 1504(a3)
	srli a7, a4, 58
	slli t0, a5, 6
	or a4, a7, t0
	srli a5, a5, 58
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 40(t4)
	ld a2, 1544(a3)
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 1608(a3)
	ld a2, 1592(a3)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 56(t4)
	ld a2, 1600(a3)
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 32(t4)
	ld a2, 1560(a3)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 40(t4)
	ld a2, 1552(a3)
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	and t3, a4, a6
	sd t3, 1512(a3)
	srli t3, a4, 58
	slli t6, a5, 6
	or a4, t3, t6
	srli a5, a5, 58
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 48(t4)
	ld a2, 1544(a3)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 24(t4)
	ld a2, 24(t4)
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 1608(a3)
	ld a2, 1600(a3)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 32(t4)
	ld a2, 1568(a3)
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 40(t4)
	ld a2, 1560(a3)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	and a7, a4, a6
	sd a7, 1520(a3)
	srli a7, a4, 58
	slli t0, a5, 6
	or a4, a7, t0
	srli a5, a5, 58
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 48(t4)
	ld a2, 1552(a3)
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 56(t4)
	ld a2, 1544(a3)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 64(t4)
	ld a2, 1608(a3)
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 40(t4)
	ld a2, 1568(a3)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 48(t4)
	ld a2, 1560(a3)
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	and t3, a4, a6
	sd t3, 1528(a3)
	srli t3, a4, 58
	slli t6, a5, 6
	or a4, t3, t6
	srli a5, a5, 58
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 56(t4)
	ld a2, 1552(a3)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	mul a7, a1, a2
	mulhu t0, a1, a2
	ld a1, 64(t4)
	ld a2, 1544(a3)
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	mul t3, a1, a2
	mulhu t6, a1, a2
	ld a1, 32(t4)
	ld a2, 32(t4)
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	mul a7, a1, a2
	mulhu t0, a1, a2
	add a4, a4, t3
	sltu t3, a4, t3
	add a5, a5, t6
	add a5, a5, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add a5, a5, t0
	add a5, a5, a7
	and a7, a4, a6
	sd a7, 1536(a3)
	srli a7, a4, 58
	slli t0, a5, 6
	or a4, a7, t0
	srli a5, a5, 58
	ld a1, 1472(a3)
	ld a2, 1480(a3)
	slli t3, a4, 1
	and t3, t3, a6
	add a1, a1, t3
	srli t3, a4, 57
	slli t6, a5, 7
	add t3, t3, t6
	add a2, a2, t3
	srli t3, a1, 58
	and a1, a1, a6
	add a2, a2, t3
	sd a1, 0(t2)
	sd a2, 8(t2)
	ld a1, 1488(a3)
	sd a1, 16(t2)
	ld a1, 1496(a3)
	sd a1, 24(t2)
	ld a1, 1504(a3)
	sd a1, 32(t2)
	ld a1, 1512(a3)
	sd a1, 40(t2)
	ld a1, 1520(a3)
	sd a1, 48(t2)
	ld a1, 1528(a3)
	sd a1, 56(t2)
	ld a1, 1536(a3)
	sd a1, 64(t2)
21:
	ret
	.option pop
