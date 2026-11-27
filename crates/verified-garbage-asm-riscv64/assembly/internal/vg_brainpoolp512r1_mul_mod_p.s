// The functions of `src/internal/vg_brainpoolp512r1_mul_mod_p.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_brainpoolp512r1_mul_mod_p:
	.option push
	.option arch, +m, +c
	add t2, a0, a1
	add t4, a0, a2
	add t5, a0, a3
	addi a3, a0, 2047
	addi a3, a3, 2047
	addi a3, a3, 2047
	addi a3, a3, 3
	sd s6, 1536(a3)
	sd s7, 1544(a3)
	sd s8, 1552(a3)
	sd s9, 1560(a3)
	sd s10, 1568(a3)
	sd s11, 1576(a3)
	beq t4, t5, 20f
	ld a0, 0(t4)
	ld a1, 8(t4)
	ld a2, 16(t4)
	ld a4, 24(t4)
	ld a5, 32(t4)
	ld a6, 0(t5)
	mul t0, a0, a6
	mulhu t3, a0, a6
	mul t1, a1, a6
	mulhu s6, a1, a6
	add t1, t1, t3
	sltu t6, t1, t3
	add t3, s6, t6
	mul a7, a2, a6
	mulhu s6, a2, a6
	add a7, a7, t3
	sltu t6, a7, t3
	add t3, s6, t6
	mul s7, a4, a6
	mulhu s6, a4, a6
	add s7, s7, t3
	sltu t6, s7, t3
	add t3, s6, t6
	mul s8, a5, a6
	mulhu s6, a5, a6
	add s8, s8, t3
	sltu t6, s8, t3
	add t3, s6, t6
	ld s6, 40(t4)
	mul s9, s6, a6
	mulhu s6, s6, a6
	add s9, s9, t3
	sltu t6, s9, t3
	add t3, s6, t6
	ld s6, 48(t4)
	mul s10, s6, a6
	mulhu s6, s6, a6
	add s10, s10, t3
	sltu t6, s10, t3
	add t3, s6, t6
	ld s6, 56(t4)
	mul s11, s6, a6
	mulhu s6, s6, a6
	add s11, s11, t3
	sltu t6, s11, t3
	add t3, s6, t6
	sd t0, 1872(a3)
	addi t0, t3, 0
	ld a6, 8(t5)
	mul t6, a0, a6
	mulhu t3, a0, a6
	add t1, t1, t6
	sltu t6, t1, t6
	add t3, t3, t6
	mul t6, a1, a6
	mulhu s6, a1, a6
	add a7, a7, t6
	sltu t6, a7, t6
	add s6, s6, t6
	add a7, a7, t3
	sltu t6, a7, t3
	add t3, s6, t6
	mul t6, a2, a6
	mulhu s6, a2, a6
	add s7, s7, t6
	sltu t6, s7, t6
	add s6, s6, t6
	add s7, s7, t3
	sltu t6, s7, t3
	add t3, s6, t6
	mul t6, a4, a6
	mulhu s6, a4, a6
	add s8, s8, t6
	sltu t6, s8, t6
	add s6, s6, t6
	add s8, s8, t3
	sltu t6, s8, t3
	add t3, s6, t6
	mul t6, a5, a6
	mulhu s6, a5, a6
	add s9, s9, t6
	sltu t6, s9, t6
	add s6, s6, t6
	add s9, s9, t3
	sltu t6, s9, t3
	add t3, s6, t6
	ld s6, 40(t4)
	mul t6, s6, a6
	mulhu s6, s6, a6
	add s10, s10, t6
	sltu t6, s10, t6
	add s6, s6, t6
	add s10, s10, t3
	sltu t6, s10, t3
	add t3, s6, t6
	ld s6, 48(t4)
	mul t6, s6, a6
	mulhu s6, s6, a6
	add s11, s11, t6
	sltu t6, s11, t6
	add s6, s6, t6
	add s11, s11, t3
	sltu t6, s11, t3
	add t3, s6, t6
	ld s6, 56(t4)
	mul t6, s6, a6
	mulhu s6, s6, a6
	add t0, t0, t6
	sltu t6, t0, t6
	add s6, s6, t6
	add t0, t0, t3
	sltu t6, t0, t3
	add t3, s6, t6
	sd t1, 1880(a3)
	addi t1, t3, 0
	ld a6, 16(t5)
	mul t6, a0, a6
	mulhu t3, a0, a6
	add a7, a7, t6
	sltu t6, a7, t6
	add t3, t3, t6
	mul t6, a1, a6
	mulhu s6, a1, a6
	add s7, s7, t6
	sltu t6, s7, t6
	add s6, s6, t6
	add s7, s7, t3
	sltu t6, s7, t3
	add t3, s6, t6
	mul t6, a2, a6
	mulhu s6, a2, a6
	add s8, s8, t6
	sltu t6, s8, t6
	add s6, s6, t6
	add s8, s8, t3
	sltu t6, s8, t3
	add t3, s6, t6
	mul t6, a4, a6
	mulhu s6, a4, a6
	add s9, s9, t6
	sltu t6, s9, t6
	add s6, s6, t6
	add s9, s9, t3
	sltu t6, s9, t3
	add t3, s6, t6
	mul t6, a5, a6
	mulhu s6, a5, a6
	add s10, s10, t6
	sltu t6, s10, t6
	add s6, s6, t6
	add s10, s10, t3
	sltu t6, s10, t3
	add t3, s6, t6
	ld s6, 40(t4)
	mul t6, s6, a6
	mulhu s6, s6, a6
	add s11, s11, t6
	sltu t6, s11, t6
	add s6, s6, t6
	add s11, s11, t3
	sltu t6, s11, t3
	add t3, s6, t6
	ld s6, 48(t4)
	mul t6, s6, a6
	mulhu s6, s6, a6
	add t0, t0, t6
	sltu t6, t0, t6
	add s6, s6, t6
	add t0, t0, t3
	sltu t6, t0, t3
	add t3, s6, t6
	ld s6, 56(t4)
	mul t6, s6, a6
	mulhu s6, s6, a6
	add t1, t1, t6
	sltu t6, t1, t6
	add s6, s6, t6
	add t1, t1, t3
	sltu t6, t1, t3
	add t3, s6, t6
	sd a7, 1888(a3)
	addi a7, t3, 0
	ld a6, 24(t5)
	mul t6, a0, a6
	mulhu t3, a0, a6
	add s7, s7, t6
	sltu t6, s7, t6
	add t3, t3, t6
	mul t6, a1, a6
	mulhu s6, a1, a6
	add s8, s8, t6
	sltu t6, s8, t6
	add s6, s6, t6
	add s8, s8, t3
	sltu t6, s8, t3
	add t3, s6, t6
	mul t6, a2, a6
	mulhu s6, a2, a6
	add s9, s9, t6
	sltu t6, s9, t6
	add s6, s6, t6
	add s9, s9, t3
	sltu t6, s9, t3
	add t3, s6, t6
	mul t6, a4, a6
	mulhu s6, a4, a6
	add s10, s10, t6
	sltu t6, s10, t6
	add s6, s6, t6
	add s10, s10, t3
	sltu t6, s10, t3
	add t3, s6, t6
	mul t6, a5, a6
	mulhu s6, a5, a6
	add s11, s11, t6
	sltu t6, s11, t6
	add s6, s6, t6
	add s11, s11, t3
	sltu t6, s11, t3
	add t3, s6, t6
	ld s6, 40(t4)
	mul t6, s6, a6
	mulhu s6, s6, a6
	add t0, t0, t6
	sltu t6, t0, t6
	add s6, s6, t6
	add t0, t0, t3
	sltu t6, t0, t3
	add t3, s6, t6
	ld s6, 48(t4)
	mul t6, s6, a6
	mulhu s6, s6, a6
	add t1, t1, t6
	sltu t6, t1, t6
	add s6, s6, t6
	add t1, t1, t3
	sltu t6, t1, t3
	add t3, s6, t6
	ld s6, 56(t4)
	mul t6, s6, a6
	mulhu s6, s6, a6
	add a7, a7, t6
	sltu t6, a7, t6
	add s6, s6, t6
	add a7, a7, t3
	sltu t6, a7, t3
	add t3, s6, t6
	sd s7, 1896(a3)
	addi s7, t3, 0
	ld a6, 32(t5)
	mul t6, a0, a6
	mulhu t3, a0, a6
	add s8, s8, t6
	sltu t6, s8, t6
	add t3, t3, t6
	mul t6, a1, a6
	mulhu s6, a1, a6
	add s9, s9, t6
	sltu t6, s9, t6
	add s6, s6, t6
	add s9, s9, t3
	sltu t6, s9, t3
	add t3, s6, t6
	mul t6, a2, a6
	mulhu s6, a2, a6
	add s10, s10, t6
	sltu t6, s10, t6
	add s6, s6, t6
	add s10, s10, t3
	sltu t6, s10, t3
	add t3, s6, t6
	mul t6, a4, a6
	mulhu s6, a4, a6
	add s11, s11, t6
	sltu t6, s11, t6
	add s6, s6, t6
	add s11, s11, t3
	sltu t6, s11, t3
	add t3, s6, t6
	mul t6, a5, a6
	mulhu s6, a5, a6
	add t0, t0, t6
	sltu t6, t0, t6
	add s6, s6, t6
	add t0, t0, t3
	sltu t6, t0, t3
	add t3, s6, t6
	ld s6, 40(t4)
	mul t6, s6, a6
	mulhu s6, s6, a6
	add t1, t1, t6
	sltu t6, t1, t6
	add s6, s6, t6
	add t1, t1, t3
	sltu t6, t1, t3
	add t3, s6, t6
	ld s6, 48(t4)
	mul t6, s6, a6
	mulhu s6, s6, a6
	add a7, a7, t6
	sltu t6, a7, t6
	add s6, s6, t6
	add a7, a7, t3
	sltu t6, a7, t3
	add t3, s6, t6
	ld s6, 56(t4)
	mul t6, s6, a6
	mulhu s6, s6, a6
	add s7, s7, t6
	sltu t6, s7, t6
	add s6, s6, t6
	add s7, s7, t3
	sltu t6, s7, t3
	add t3, s6, t6
	sd s8, 1904(a3)
	addi s8, t3, 0
	ld a6, 40(t5)
	mul t6, a0, a6
	mulhu t3, a0, a6
	add s9, s9, t6
	sltu t6, s9, t6
	add t3, t3, t6
	mul t6, a1, a6
	mulhu s6, a1, a6
	add s10, s10, t6
	sltu t6, s10, t6
	add s6, s6, t6
	add s10, s10, t3
	sltu t6, s10, t3
	add t3, s6, t6
	mul t6, a2, a6
	mulhu s6, a2, a6
	add s11, s11, t6
	sltu t6, s11, t6
	add s6, s6, t6
	add s11, s11, t3
	sltu t6, s11, t3
	add t3, s6, t6
	mul t6, a4, a6
	mulhu s6, a4, a6
	add t0, t0, t6
	sltu t6, t0, t6
	add s6, s6, t6
	add t0, t0, t3
	sltu t6, t0, t3
	add t3, s6, t6
	mul t6, a5, a6
	mulhu s6, a5, a6
	add t1, t1, t6
	sltu t6, t1, t6
	add s6, s6, t6
	add t1, t1, t3
	sltu t6, t1, t3
	add t3, s6, t6
	ld s6, 40(t4)
	mul t6, s6, a6
	mulhu s6, s6, a6
	add a7, a7, t6
	sltu t6, a7, t6
	add s6, s6, t6
	add a7, a7, t3
	sltu t6, a7, t3
	add t3, s6, t6
	ld s6, 48(t4)
	mul t6, s6, a6
	mulhu s6, s6, a6
	add s7, s7, t6
	sltu t6, s7, t6
	add s6, s6, t6
	add s7, s7, t3
	sltu t6, s7, t3
	add t3, s6, t6
	ld s6, 56(t4)
	mul t6, s6, a6
	mulhu s6, s6, a6
	add s8, s8, t6
	sltu t6, s8, t6
	add s6, s6, t6
	add s8, s8, t3
	sltu t6, s8, t3
	add t3, s6, t6
	sd s9, 1912(a3)
	addi s9, t3, 0
	ld a6, 48(t5)
	mul t6, a0, a6
	mulhu t3, a0, a6
	add s10, s10, t6
	sltu t6, s10, t6
	add t3, t3, t6
	mul t6, a1, a6
	mulhu s6, a1, a6
	add s11, s11, t6
	sltu t6, s11, t6
	add s6, s6, t6
	add s11, s11, t3
	sltu t6, s11, t3
	add t3, s6, t6
	mul t6, a2, a6
	mulhu s6, a2, a6
	add t0, t0, t6
	sltu t6, t0, t6
	add s6, s6, t6
	add t0, t0, t3
	sltu t6, t0, t3
	add t3, s6, t6
	mul t6, a4, a6
	mulhu s6, a4, a6
	add t1, t1, t6
	sltu t6, t1, t6
	add s6, s6, t6
	add t1, t1, t3
	sltu t6, t1, t3
	add t3, s6, t6
	mul t6, a5, a6
	mulhu s6, a5, a6
	add a7, a7, t6
	sltu t6, a7, t6
	add s6, s6, t6
	add a7, a7, t3
	sltu t6, a7, t3
	add t3, s6, t6
	ld s6, 40(t4)
	mul t6, s6, a6
	mulhu s6, s6, a6
	add s7, s7, t6
	sltu t6, s7, t6
	add s6, s6, t6
	add s7, s7, t3
	sltu t6, s7, t3
	add t3, s6, t6
	ld s6, 48(t4)
	mul t6, s6, a6
	mulhu s6, s6, a6
	add s8, s8, t6
	sltu t6, s8, t6
	add s6, s6, t6
	add s8, s8, t3
	sltu t6, s8, t3
	add t3, s6, t6
	ld s6, 56(t4)
	mul t6, s6, a6
	mulhu s6, s6, a6
	add s9, s9, t6
	sltu t6, s9, t6
	add s6, s6, t6
	add s9, s9, t3
	sltu t6, s9, t3
	add t3, s6, t6
	sd s10, 1920(a3)
	addi s10, t3, 0
	ld a6, 56(t5)
	mul t6, a0, a6
	mulhu t3, a0, a6
	add s11, s11, t6
	sltu t6, s11, t6
	add t3, t3, t6
	mul t6, a1, a6
	mulhu s6, a1, a6
	add t0, t0, t6
	sltu t6, t0, t6
	add s6, s6, t6
	add t0, t0, t3
	sltu t6, t0, t3
	add t3, s6, t6
	mul t6, a2, a6
	mulhu s6, a2, a6
	add t1, t1, t6
	sltu t6, t1, t6
	add s6, s6, t6
	add t1, t1, t3
	sltu t6, t1, t3
	add t3, s6, t6
	mul t6, a4, a6
	mulhu s6, a4, a6
	add a7, a7, t6
	sltu t6, a7, t6
	add s6, s6, t6
	add a7, a7, t3
	sltu t6, a7, t3
	add t3, s6, t6
	mul t6, a5, a6
	mulhu s6, a5, a6
	add s7, s7, t6
	sltu t6, s7, t6
	add s6, s6, t6
	add s7, s7, t3
	sltu t6, s7, t3
	add t3, s6, t6
	ld s6, 40(t4)
	mul t6, s6, a6
	mulhu s6, s6, a6
	add s8, s8, t6
	sltu t6, s8, t6
	add s6, s6, t6
	add s8, s8, t3
	sltu t6, s8, t3
	add t3, s6, t6
	ld s6, 48(t4)
	mul t6, s6, a6
	mulhu s6, s6, a6
	add s9, s9, t6
	sltu t6, s9, t6
	add s6, s6, t6
	add s9, s9, t3
	sltu t6, s9, t3
	add t3, s6, t6
	ld s6, 56(t4)
	mul t6, s6, a6
	mulhu s6, s6, a6
	add s10, s10, t6
	sltu t6, s10, t6
	add s6, s6, t6
	add s10, s10, t3
	sltu t6, s10, t3
	add t3, s6, t6
	sd s11, 1928(a3)
	addi s11, t3, 0
	sd t0, 1936(a3)
	sd t1, 1944(a3)
	sd a7, 1952(a3)
	sd s7, 1960(a3)
	sd s8, 1968(a3)
	sd s9, 1976(a3)
	sd s10, 1984(a3)
	sd s11, 1992(a3)
	j 21f
20:
	ld a0, 0(t4)
	ld a1, 8(t4)
	ld a2, 16(t4)
	ld a4, 24(t4)
	ld a5, 32(t4)
	ld a6, 40(t4)
	ld t5, 48(t4)
	mul t1, a1, a0
	mulhu t3, a1, a0
	mul a7, a2, a0
	mulhu s6, a2, a0
	add a7, a7, t3
	sltu t6, a7, t3
	add t3, s6, t6
	mul s7, a4, a0
	mulhu s6, a4, a0
	add s7, s7, t3
	sltu t6, s7, t3
	add t3, s6, t6
	mul s8, a5, a0
	mulhu s6, a5, a0
	add s8, s8, t3
	sltu t6, s8, t3
	add t3, s6, t6
	mul s9, a6, a0
	mulhu s6, a6, a0
	add s9, s9, t3
	sltu t6, s9, t3
	add t3, s6, t6
	mul s10, t5, a0
	mulhu s6, t5, a0
	add s10, s10, t3
	sltu t6, s10, t3
	add t3, s6, t6
	ld s6, 56(t4)
	mul s11, s6, a0
	mulhu s6, s6, a0
	add s11, s11, t3
	sltu t6, s11, t3
	add t3, s6, t6
	addi t0, t3, 0
	sd t1, 1880(a3)
	sd a7, 1888(a3)
	mul t6, a2, a1
	mulhu t3, a2, a1
	add s7, s7, t6
	sltu t6, s7, t6
	add t3, t3, t6
	mul t6, a4, a1
	mulhu s6, a4, a1
	add s8, s8, t6
	sltu t6, s8, t6
	add s6, s6, t6
	add s8, s8, t3
	sltu t6, s8, t3
	add t3, s6, t6
	mul t6, a5, a1
	mulhu s6, a5, a1
	add s9, s9, t6
	sltu t6, s9, t6
	add s6, s6, t6
	add s9, s9, t3
	sltu t6, s9, t3
	add t3, s6, t6
	mul t6, a6, a1
	mulhu s6, a6, a1
	add s10, s10, t6
	sltu t6, s10, t6
	add s6, s6, t6
	add s10, s10, t3
	sltu t6, s10, t3
	add t3, s6, t6
	mul t6, t5, a1
	mulhu s6, t5, a1
	add s11, s11, t6
	sltu t6, s11, t6
	add s6, s6, t6
	add s11, s11, t3
	sltu t6, s11, t3
	add t3, s6, t6
	ld s6, 56(t4)
	mul t6, s6, a1
	mulhu s6, s6, a1
	add t0, t0, t6
	sltu t6, t0, t6
	add s6, s6, t6
	add t0, t0, t3
	sltu t6, t0, t3
	add t3, s6, t6
	addi t1, t3, 0
	sd s7, 1896(a3)
	sd s8, 1904(a3)
	mul t6, a4, a2
	mulhu t3, a4, a2
	add s9, s9, t6
	sltu t6, s9, t6
	add t3, t3, t6
	mul t6, a5, a2
	mulhu s6, a5, a2
	add s10, s10, t6
	sltu t6, s10, t6
	add s6, s6, t6
	add s10, s10, t3
	sltu t6, s10, t3
	add t3, s6, t6
	mul t6, a6, a2
	mulhu s6, a6, a2
	add s11, s11, t6
	sltu t6, s11, t6
	add s6, s6, t6
	add s11, s11, t3
	sltu t6, s11, t3
	add t3, s6, t6
	mul t6, t5, a2
	mulhu s6, t5, a2
	add t0, t0, t6
	sltu t6, t0, t6
	add s6, s6, t6
	add t0, t0, t3
	sltu t6, t0, t3
	add t3, s6, t6
	ld s6, 56(t4)
	mul t6, s6, a2
	mulhu s6, s6, a2
	add t1, t1, t6
	sltu t6, t1, t6
	add s6, s6, t6
	add t1, t1, t3
	sltu t6, t1, t3
	add t3, s6, t6
	addi a7, t3, 0
	sd s9, 1912(a3)
	sd s10, 1920(a3)
	mul t6, a5, a4
	mulhu t3, a5, a4
	add s11, s11, t6
	sltu t6, s11, t6
	add t3, t3, t6
	mul t6, a6, a4
	mulhu s6, a6, a4
	add t0, t0, t6
	sltu t6, t0, t6
	add s6, s6, t6
	add t0, t0, t3
	sltu t6, t0, t3
	add t3, s6, t6
	mul t6, t5, a4
	mulhu s6, t5, a4
	add t1, t1, t6
	sltu t6, t1, t6
	add s6, s6, t6
	add t1, t1, t3
	sltu t6, t1, t3
	add t3, s6, t6
	ld s6, 56(t4)
	mul t6, s6, a4
	mulhu s6, s6, a4
	add a7, a7, t6
	sltu t6, a7, t6
	add s6, s6, t6
	add a7, a7, t3
	sltu t6, a7, t3
	add t3, s6, t6
	addi s7, t3, 0
	sd s11, 1928(a3)
	sd t0, 1936(a3)
	mul t6, a6, a5
	mulhu t3, a6, a5
	add t1, t1, t6
	sltu t6, t1, t6
	add t3, t3, t6
	mul t6, t5, a5
	mulhu s6, t5, a5
	add a7, a7, t6
	sltu t6, a7, t6
	add s6, s6, t6
	add a7, a7, t3
	sltu t6, a7, t3
	add t3, s6, t6
	ld s6, 56(t4)
	mul t6, s6, a5
	mulhu s6, s6, a5
	add s7, s7, t6
	sltu t6, s7, t6
	add s6, s6, t6
	add s7, s7, t3
	sltu t6, s7, t3
	add t3, s6, t6
	addi s8, t3, 0
	sd t1, 1944(a3)
	sd a7, 1952(a3)
	mul t6, t5, a6
	mulhu t3, t5, a6
	add s7, s7, t6
	sltu t6, s7, t6
	add t3, t3, t6
	ld s6, 56(t4)
	mul t6, s6, a6
	mulhu s6, s6, a6
	add s8, s8, t6
	sltu t6, s8, t6
	add s6, s6, t6
	add s8, s8, t3
	sltu t6, s8, t3
	add t3, s6, t6
	addi s9, t3, 0
	sd s7, 1960(a3)
	sd s8, 1968(a3)
	ld s6, 56(t4)
	mul t6, s6, t5
	mulhu t3, s6, t5
	add s9, s9, t6
	sltu t6, s9, t6
	add t3, t3, t6
	addi s10, t3, 0
	sd s9, 1976(a3)
	sd s10, 1984(a3)
	addi a2, zero, 0
	sd a2, 1872(a3)
	sd a2, 1992(a3)
	addi a5, zero, 0
	ld a6, 0(t4)
	mul t0, a6, a6
	mulhu a1, a6, a6
	ld a7, 1872(a3)
	srli a4, a7, 63
	slli a7, a7, 1
	add a7, a7, a2
	add a7, a7, t0
	sltu a6, a7, t0
	add a7, a7, a5
	sltu a5, a7, a5
	add a5, a5, a6
	sd a7, 1872(a3)
	ld a7, 1880(a3)
	srli a2, a7, 63
	slli a7, a7, 1
	add a7, a7, a4
	add a7, a7, a1
	sltu a6, a7, a1
	add a7, a7, a5
	sltu a5, a7, a5
	add a5, a5, a6
	sd a7, 1880(a3)
	ld a6, 8(t4)
	mul t0, a6, a6
	mulhu a1, a6, a6
	ld a7, 1888(a3)
	srli a4, a7, 63
	slli a7, a7, 1
	add a7, a7, a2
	add a7, a7, t0
	sltu a6, a7, t0
	add a7, a7, a5
	sltu a5, a7, a5
	add a5, a5, a6
	sd a7, 1888(a3)
	ld a7, 1896(a3)
	srli a2, a7, 63
	slli a7, a7, 1
	add a7, a7, a4
	add a7, a7, a1
	sltu a6, a7, a1
	add a7, a7, a5
	sltu a5, a7, a5
	add a5, a5, a6
	sd a7, 1896(a3)
	ld a6, 16(t4)
	mul t0, a6, a6
	mulhu a1, a6, a6
	ld a7, 1904(a3)
	srli a4, a7, 63
	slli a7, a7, 1
	add a7, a7, a2
	add a7, a7, t0
	sltu a6, a7, t0
	add a7, a7, a5
	sltu a5, a7, a5
	add a5, a5, a6
	sd a7, 1904(a3)
	ld a7, 1912(a3)
	srli a2, a7, 63
	slli a7, a7, 1
	add a7, a7, a4
	add a7, a7, a1
	sltu a6, a7, a1
	add a7, a7, a5
	sltu a5, a7, a5
	add a5, a5, a6
	sd a7, 1912(a3)
	ld a6, 24(t4)
	mul t0, a6, a6
	mulhu a1, a6, a6
	ld a7, 1920(a3)
	srli a4, a7, 63
	slli a7, a7, 1
	add a7, a7, a2
	add a7, a7, t0
	sltu a6, a7, t0
	add a7, a7, a5
	sltu a5, a7, a5
	add a5, a5, a6
	sd a7, 1920(a3)
	ld a7, 1928(a3)
	srli a2, a7, 63
	slli a7, a7, 1
	add a7, a7, a4
	add a7, a7, a1
	sltu a6, a7, a1
	add a7, a7, a5
	sltu a5, a7, a5
	add a5, a5, a6
	sd a7, 1928(a3)
	ld a6, 32(t4)
	mul t0, a6, a6
	mulhu a1, a6, a6
	ld a7, 1936(a3)
	srli a4, a7, 63
	slli a7, a7, 1
	add a7, a7, a2
	add a7, a7, t0
	sltu a6, a7, t0
	add a7, a7, a5
	sltu a5, a7, a5
	add a5, a5, a6
	sd a7, 1936(a3)
	ld a7, 1944(a3)
	srli a2, a7, 63
	slli a7, a7, 1
	add a7, a7, a4
	add a7, a7, a1
	sltu a6, a7, a1
	add a7, a7, a5
	sltu a5, a7, a5
	add a5, a5, a6
	sd a7, 1944(a3)
	ld a6, 40(t4)
	mul t0, a6, a6
	mulhu a1, a6, a6
	ld a7, 1952(a3)
	srli a4, a7, 63
	slli a7, a7, 1
	add a7, a7, a2
	add a7, a7, t0
	sltu a6, a7, t0
	add a7, a7, a5
	sltu a5, a7, a5
	add a5, a5, a6
	sd a7, 1952(a3)
	ld a7, 1960(a3)
	srli a2, a7, 63
	slli a7, a7, 1
	add a7, a7, a4
	add a7, a7, a1
	sltu a6, a7, a1
	add a7, a7, a5
	sltu a5, a7, a5
	add a5, a5, a6
	sd a7, 1960(a3)
	ld a6, 48(t4)
	mul t0, a6, a6
	mulhu a1, a6, a6
	ld a7, 1968(a3)
	srli a4, a7, 63
	slli a7, a7, 1
	add a7, a7, a2
	add a7, a7, t0
	sltu a6, a7, t0
	add a7, a7, a5
	sltu a5, a7, a5
	add a5, a5, a6
	sd a7, 1968(a3)
	ld a7, 1976(a3)
	srli a2, a7, 63
	slli a7, a7, 1
	add a7, a7, a4
	add a7, a7, a1
	sltu a6, a7, a1
	add a7, a7, a5
	sltu a5, a7, a5
	add a5, a5, a6
	sd a7, 1976(a3)
	ld a6, 56(t4)
	mul t0, a6, a6
	mulhu a1, a6, a6
	ld a7, 1984(a3)
	srli a4, a7, 63
	slli a7, a7, 1
	add a7, a7, a2
	add a7, a7, t0
	sltu a6, a7, t0
	add a7, a7, a5
	sltu a5, a7, a5
	add a5, a5, a6
	sd a7, 1984(a3)
	ld a7, 1992(a3)
	srli a2, a7, 63
	slli a7, a7, 1
	add a7, a7, a4
	add a7, a7, a1
	sltu a6, a7, a1
	add a7, a7, a5
	sltu a5, a7, a5
	add a5, a5, a6
	sd a7, 1992(a3)
21:
	lui a0, 166566
	addiw a0, a0, 86
	slli a0, a0, 32
	lui t6, 361381
	addiw t6, t6, -1805
	add a0, a0, t6
	lui a1, 165920
	addiw a1, a1, -209
	slli a1, a1, 32
	lui t6, 186412
	addiw t6, t6, 1669
	add a1, a1, t6
	lui a2, 715994
	addiw a2, a2, 299
	slli a2, a2, 32
	lui t6, 944696
	addiw t6, t6, 230
	add a2, a2, t6
	lui a4, 513242
	addiw a4, a4, -1279
	slli a4, a4, 32
	lui t6, 638055
	addiw t6, t6, -1982
	add a4, a4, t6
	lui a5, 878138
	addiw a5, a5, -822
	slli a5, a5, 32
	lui t6, 459569
	addiw t6, t6, -1935
	add a5, a5, t6
	lui a6, 832265
	addiw a6, a6, -588
	slli a6, a6, 32
	lui t6, 736413
	addiw t6, t6, 526
	add a6, a6, t6
	lui t5, 261454
	addiw t5, t5, 1710
	slli t5, t5, 32
	lui t6, 212128
	addiw t6, t6, -1017
	add t5, t5, t6
	lui s6, 699866
	addiw s6, s6, -583
	slli s6, s6, 32
	lui t6, 900764
	addiw t6, t6, 1163
	add s6, s6, t6
	sd s6, 1584(a3)
	lui s6, 539059
	addiw s6, s6, 544
	slli s6, s6, 32
	lui t6, 514207
	addiw t6, t6, -59
	add s6, s6, t6
	sd s6, 1592(a3)
	ld t0, 1872(a3)
	ld t1, 1880(a3)
	ld a7, 1888(a3)
	ld s7, 1896(a3)
	ld s8, 1904(a3)
	ld s9, 1912(a3)
	ld s10, 1920(a3)
	ld s11, 1928(a3)
	addi t4, zero, 0
	ld t6, 1592(a3)
	mul t0, t0, t6
	mulhu t3, t0, a0
	addi t6, zero, 0
	sltu t6, t6, t0
	add t3, t3, t6
	mul t6, a1, t0
	mulhu s6, a1, t0
	add t1, t1, t6
	sltu t6, t1, t6
	add s6, s6, t6
	add t1, t1, t3
	sltu t6, t1, t3
	add t3, s6, t6
	mul t6, a2, t0
	mulhu s6, a2, t0
	add a7, a7, t6
	sltu t6, a7, t6
	add s6, s6, t6
	add a7, a7, t3
	sltu t6, a7, t3
	add t3, s6, t6
	mul t6, a4, t0
	mulhu s6, a4, t0
	add s7, s7, t6
	sltu t6, s7, t6
	add s6, s6, t6
	add s7, s7, t3
	sltu t6, s7, t3
	add t3, s6, t6
	mul t6, a5, t0
	mulhu s6, a5, t0
	add s8, s8, t6
	sltu t6, s8, t6
	add s6, s6, t6
	add s8, s8, t3
	sltu t6, s8, t3
	add t3, s6, t6
	mul t6, a6, t0
	mulhu s6, a6, t0
	add s9, s9, t6
	sltu t6, s9, t6
	add s6, s6, t6
	add s9, s9, t3
	sltu t6, s9, t3
	add t3, s6, t6
	mul t6, t5, t0
	mulhu s6, t5, t0
	add s10, s10, t6
	sltu t6, s10, t6
	add s6, s6, t6
	add s10, s10, t3
	sltu t6, s10, t3
	add t3, s6, t6
	ld s6, 1584(a3)
	mul t6, s6, t0
	mulhu s6, s6, t0
	add s11, s11, t6
	sltu t6, s11, t6
	add s6, s6, t6
	add s11, s11, t3
	sltu t6, s11, t3
	add t3, s6, t6
	ld t0, 1936(a3)
	add t0, t0, t3
	sltu t6, t0, t3
	add t0, t0, t4
	sltu t4, t0, t4
	add t4, t4, t6
	ld t6, 1592(a3)
	mul t1, t1, t6
	mulhu t3, t1, a0
	addi t6, zero, 0
	sltu t6, t6, t1
	add t3, t3, t6
	mul t6, a1, t1
	mulhu s6, a1, t1
	add a7, a7, t6
	sltu t6, a7, t6
	add s6, s6, t6
	add a7, a7, t3
	sltu t6, a7, t3
	add t3, s6, t6
	mul t6, a2, t1
	mulhu s6, a2, t1
	add s7, s7, t6
	sltu t6, s7, t6
	add s6, s6, t6
	add s7, s7, t3
	sltu t6, s7, t3
	add t3, s6, t6
	mul t6, a4, t1
	mulhu s6, a4, t1
	add s8, s8, t6
	sltu t6, s8, t6
	add s6, s6, t6
	add s8, s8, t3
	sltu t6, s8, t3
	add t3, s6, t6
	mul t6, a5, t1
	mulhu s6, a5, t1
	add s9, s9, t6
	sltu t6, s9, t6
	add s6, s6, t6
	add s9, s9, t3
	sltu t6, s9, t3
	add t3, s6, t6
	mul t6, a6, t1
	mulhu s6, a6, t1
	add s10, s10, t6
	sltu t6, s10, t6
	add s6, s6, t6
	add s10, s10, t3
	sltu t6, s10, t3
	add t3, s6, t6
	mul t6, t5, t1
	mulhu s6, t5, t1
	add s11, s11, t6
	sltu t6, s11, t6
	add s6, s6, t6
	add s11, s11, t3
	sltu t6, s11, t3
	add t3, s6, t6
	ld s6, 1584(a3)
	mul t6, s6, t1
	mulhu s6, s6, t1
	add t0, t0, t6
	sltu t6, t0, t6
	add s6, s6, t6
	add t0, t0, t3
	sltu t6, t0, t3
	add t3, s6, t6
	ld t1, 1944(a3)
	add t1, t1, t3
	sltu t6, t1, t3
	add t1, t1, t4
	sltu t4, t1, t4
	add t4, t4, t6
	ld t6, 1592(a3)
	mul a7, a7, t6
	mulhu t3, a7, a0
	addi t6, zero, 0
	sltu t6, t6, a7
	add t3, t3, t6
	mul t6, a1, a7
	mulhu s6, a1, a7
	add s7, s7, t6
	sltu t6, s7, t6
	add s6, s6, t6
	add s7, s7, t3
	sltu t6, s7, t3
	add t3, s6, t6
	mul t6, a2, a7
	mulhu s6, a2, a7
	add s8, s8, t6
	sltu t6, s8, t6
	add s6, s6, t6
	add s8, s8, t3
	sltu t6, s8, t3
	add t3, s6, t6
	mul t6, a4, a7
	mulhu s6, a4, a7
	add s9, s9, t6
	sltu t6, s9, t6
	add s6, s6, t6
	add s9, s9, t3
	sltu t6, s9, t3
	add t3, s6, t6
	mul t6, a5, a7
	mulhu s6, a5, a7
	add s10, s10, t6
	sltu t6, s10, t6
	add s6, s6, t6
	add s10, s10, t3
	sltu t6, s10, t3
	add t3, s6, t6
	mul t6, a6, a7
	mulhu s6, a6, a7
	add s11, s11, t6
	sltu t6, s11, t6
	add s6, s6, t6
	add s11, s11, t3
	sltu t6, s11, t3
	add t3, s6, t6
	mul t6, t5, a7
	mulhu s6, t5, a7
	add t0, t0, t6
	sltu t6, t0, t6
	add s6, s6, t6
	add t0, t0, t3
	sltu t6, t0, t3
	add t3, s6, t6
	ld s6, 1584(a3)
	mul t6, s6, a7
	mulhu s6, s6, a7
	add t1, t1, t6
	sltu t6, t1, t6
	add s6, s6, t6
	add t1, t1, t3
	sltu t6, t1, t3
	add t3, s6, t6
	ld a7, 1952(a3)
	add a7, a7, t3
	sltu t6, a7, t3
	add a7, a7, t4
	sltu t4, a7, t4
	add t4, t4, t6
	ld t6, 1592(a3)
	mul s7, s7, t6
	mulhu t3, s7, a0
	addi t6, zero, 0
	sltu t6, t6, s7
	add t3, t3, t6
	mul t6, a1, s7
	mulhu s6, a1, s7
	add s8, s8, t6
	sltu t6, s8, t6
	add s6, s6, t6
	add s8, s8, t3
	sltu t6, s8, t3
	add t3, s6, t6
	mul t6, a2, s7
	mulhu s6, a2, s7
	add s9, s9, t6
	sltu t6, s9, t6
	add s6, s6, t6
	add s9, s9, t3
	sltu t6, s9, t3
	add t3, s6, t6
	mul t6, a4, s7
	mulhu s6, a4, s7
	add s10, s10, t6
	sltu t6, s10, t6
	add s6, s6, t6
	add s10, s10, t3
	sltu t6, s10, t3
	add t3, s6, t6
	mul t6, a5, s7
	mulhu s6, a5, s7
	add s11, s11, t6
	sltu t6, s11, t6
	add s6, s6, t6
	add s11, s11, t3
	sltu t6, s11, t3
	add t3, s6, t6
	mul t6, a6, s7
	mulhu s6, a6, s7
	add t0, t0, t6
	sltu t6, t0, t6
	add s6, s6, t6
	add t0, t0, t3
	sltu t6, t0, t3
	add t3, s6, t6
	mul t6, t5, s7
	mulhu s6, t5, s7
	add t1, t1, t6
	sltu t6, t1, t6
	add s6, s6, t6
	add t1, t1, t3
	sltu t6, t1, t3
	add t3, s6, t6
	ld s6, 1584(a3)
	mul t6, s6, s7
	mulhu s6, s6, s7
	add a7, a7, t6
	sltu t6, a7, t6
	add s6, s6, t6
	add a7, a7, t3
	sltu t6, a7, t3
	add t3, s6, t6
	ld s7, 1960(a3)
	add s7, s7, t3
	sltu t6, s7, t3
	add s7, s7, t4
	sltu t4, s7, t4
	add t4, t4, t6
	ld t6, 1592(a3)
	mul s8, s8, t6
	mulhu t3, s8, a0
	addi t6, zero, 0
	sltu t6, t6, s8
	add t3, t3, t6
	mul t6, a1, s8
	mulhu s6, a1, s8
	add s9, s9, t6
	sltu t6, s9, t6
	add s6, s6, t6
	add s9, s9, t3
	sltu t6, s9, t3
	add t3, s6, t6
	mul t6, a2, s8
	mulhu s6, a2, s8
	add s10, s10, t6
	sltu t6, s10, t6
	add s6, s6, t6
	add s10, s10, t3
	sltu t6, s10, t3
	add t3, s6, t6
	mul t6, a4, s8
	mulhu s6, a4, s8
	add s11, s11, t6
	sltu t6, s11, t6
	add s6, s6, t6
	add s11, s11, t3
	sltu t6, s11, t3
	add t3, s6, t6
	mul t6, a5, s8
	mulhu s6, a5, s8
	add t0, t0, t6
	sltu t6, t0, t6
	add s6, s6, t6
	add t0, t0, t3
	sltu t6, t0, t3
	add t3, s6, t6
	mul t6, a6, s8
	mulhu s6, a6, s8
	add t1, t1, t6
	sltu t6, t1, t6
	add s6, s6, t6
	add t1, t1, t3
	sltu t6, t1, t3
	add t3, s6, t6
	mul t6, t5, s8
	mulhu s6, t5, s8
	add a7, a7, t6
	sltu t6, a7, t6
	add s6, s6, t6
	add a7, a7, t3
	sltu t6, a7, t3
	add t3, s6, t6
	ld s6, 1584(a3)
	mul t6, s6, s8
	mulhu s6, s6, s8
	add s7, s7, t6
	sltu t6, s7, t6
	add s6, s6, t6
	add s7, s7, t3
	sltu t6, s7, t3
	add t3, s6, t6
	ld s8, 1968(a3)
	add s8, s8, t3
	sltu t6, s8, t3
	add s8, s8, t4
	sltu t4, s8, t4
	add t4, t4, t6
	ld t6, 1592(a3)
	mul s9, s9, t6
	mulhu t3, s9, a0
	addi t6, zero, 0
	sltu t6, t6, s9
	add t3, t3, t6
	mul t6, a1, s9
	mulhu s6, a1, s9
	add s10, s10, t6
	sltu t6, s10, t6
	add s6, s6, t6
	add s10, s10, t3
	sltu t6, s10, t3
	add t3, s6, t6
	mul t6, a2, s9
	mulhu s6, a2, s9
	add s11, s11, t6
	sltu t6, s11, t6
	add s6, s6, t6
	add s11, s11, t3
	sltu t6, s11, t3
	add t3, s6, t6
	mul t6, a4, s9
	mulhu s6, a4, s9
	add t0, t0, t6
	sltu t6, t0, t6
	add s6, s6, t6
	add t0, t0, t3
	sltu t6, t0, t3
	add t3, s6, t6
	mul t6, a5, s9
	mulhu s6, a5, s9
	add t1, t1, t6
	sltu t6, t1, t6
	add s6, s6, t6
	add t1, t1, t3
	sltu t6, t1, t3
	add t3, s6, t6
	mul t6, a6, s9
	mulhu s6, a6, s9
	add a7, a7, t6
	sltu t6, a7, t6
	add s6, s6, t6
	add a7, a7, t3
	sltu t6, a7, t3
	add t3, s6, t6
	mul t6, t5, s9
	mulhu s6, t5, s9
	add s7, s7, t6
	sltu t6, s7, t6
	add s6, s6, t6
	add s7, s7, t3
	sltu t6, s7, t3
	add t3, s6, t6
	ld s6, 1584(a3)
	mul t6, s6, s9
	mulhu s6, s6, s9
	add s8, s8, t6
	sltu t6, s8, t6
	add s6, s6, t6
	add s8, s8, t3
	sltu t6, s8, t3
	add t3, s6, t6
	ld s9, 1976(a3)
	add s9, s9, t3
	sltu t6, s9, t3
	add s9, s9, t4
	sltu t4, s9, t4
	add t4, t4, t6
	ld t6, 1592(a3)
	mul s10, s10, t6
	mulhu t3, s10, a0
	addi t6, zero, 0
	sltu t6, t6, s10
	add t3, t3, t6
	mul t6, a1, s10
	mulhu s6, a1, s10
	add s11, s11, t6
	sltu t6, s11, t6
	add s6, s6, t6
	add s11, s11, t3
	sltu t6, s11, t3
	add t3, s6, t6
	mul t6, a2, s10
	mulhu s6, a2, s10
	add t0, t0, t6
	sltu t6, t0, t6
	add s6, s6, t6
	add t0, t0, t3
	sltu t6, t0, t3
	add t3, s6, t6
	mul t6, a4, s10
	mulhu s6, a4, s10
	add t1, t1, t6
	sltu t6, t1, t6
	add s6, s6, t6
	add t1, t1, t3
	sltu t6, t1, t3
	add t3, s6, t6
	mul t6, a5, s10
	mulhu s6, a5, s10
	add a7, a7, t6
	sltu t6, a7, t6
	add s6, s6, t6
	add a7, a7, t3
	sltu t6, a7, t3
	add t3, s6, t6
	mul t6, a6, s10
	mulhu s6, a6, s10
	add s7, s7, t6
	sltu t6, s7, t6
	add s6, s6, t6
	add s7, s7, t3
	sltu t6, s7, t3
	add t3, s6, t6
	mul t6, t5, s10
	mulhu s6, t5, s10
	add s8, s8, t6
	sltu t6, s8, t6
	add s6, s6, t6
	add s8, s8, t3
	sltu t6, s8, t3
	add t3, s6, t6
	ld s6, 1584(a3)
	mul t6, s6, s10
	mulhu s6, s6, s10
	add s9, s9, t6
	sltu t6, s9, t6
	add s6, s6, t6
	add s9, s9, t3
	sltu t6, s9, t3
	add t3, s6, t6
	ld s10, 1984(a3)
	add s10, s10, t3
	sltu t6, s10, t3
	add s10, s10, t4
	sltu t4, s10, t4
	add t4, t4, t6
	ld t6, 1592(a3)
	mul s11, s11, t6
	mulhu t3, s11, a0
	addi t6, zero, 0
	sltu t6, t6, s11
	add t3, t3, t6
	mul t6, a1, s11
	mulhu s6, a1, s11
	add t0, t0, t6
	sltu t6, t0, t6
	add s6, s6, t6
	add t0, t0, t3
	sltu t6, t0, t3
	add t3, s6, t6
	mul t6, a2, s11
	mulhu s6, a2, s11
	add t1, t1, t6
	sltu t6, t1, t6
	add s6, s6, t6
	add t1, t1, t3
	sltu t6, t1, t3
	add t3, s6, t6
	mul t6, a4, s11
	mulhu s6, a4, s11
	add a7, a7, t6
	sltu t6, a7, t6
	add s6, s6, t6
	add a7, a7, t3
	sltu t6, a7, t3
	add t3, s6, t6
	mul t6, a5, s11
	mulhu s6, a5, s11
	add s7, s7, t6
	sltu t6, s7, t6
	add s6, s6, t6
	add s7, s7, t3
	sltu t6, s7, t3
	add t3, s6, t6
	mul t6, a6, s11
	mulhu s6, a6, s11
	add s8, s8, t6
	sltu t6, s8, t6
	add s6, s6, t6
	add s8, s8, t3
	sltu t6, s8, t3
	add t3, s6, t6
	mul t6, t5, s11
	mulhu s6, t5, s11
	add s9, s9, t6
	sltu t6, s9, t6
	add s6, s6, t6
	add s9, s9, t3
	sltu t6, s9, t3
	add t3, s6, t6
	ld s6, 1584(a3)
	mul t6, s6, s11
	mulhu s6, s6, s11
	add s10, s10, t6
	sltu t6, s10, t6
	add s6, s6, t6
	add s10, s10, t3
	sltu t6, s10, t3
	add t3, s6, t6
	ld s11, 1992(a3)
	add s11, s11, t3
	sltu t6, s11, t3
	add s11, s11, t4
	sltu t4, s11, t4
	add t4, t4, t6
	addi t3, zero, 0
	sltu t6, t0, a0
	sub s6, t0, a0
	sltu a0, s6, t3
	sub s6, s6, t3
	add t3, t6, a0
	sd s6, 1616(a3)
	sltu t6, t1, a1
	sub s6, t1, a1
	sltu a1, s6, t3
	sub s6, s6, t3
	add t3, t6, a1
	sd s6, 1624(a3)
	sltu t6, a7, a2
	sub s6, a7, a2
	sltu a2, s6, t3
	sub s6, s6, t3
	add t3, t6, a2
	sd s6, 1632(a3)
	sltu t6, s7, a4
	sub s6, s7, a4
	sltu a4, s6, t3
	sub s6, s6, t3
	add t3, t6, a4
	sd s6, 1640(a3)
	sltu t6, s8, a5
	sub s6, s8, a5
	sltu a5, s6, t3
	sub s6, s6, t3
	add t3, t6, a5
	sd s6, 1648(a3)
	sltu t6, s9, a6
	sub s6, s9, a6
	sltu a6, s6, t3
	sub s6, s6, t3
	add t3, t6, a6
	sd s6, 1656(a3)
	sltu t6, s10, t5
	sub s6, s10, t5
	sltu t5, s6, t3
	sub s6, s6, t3
	add t3, t6, t5
	sd s6, 1664(a3)
	ld a0, 1584(a3)
	sltu t6, s11, a0
	sub s6, s11, a0
	sltu a0, s6, t3
	sub s6, s6, t3
	add t3, t6, a0
	sd s6, 1672(a3)
	sub t4, t4, t3
	ld t6, 1616(a3)
	xor s6, t0, t6
	and s6, s6, t4
	xor t6, t6, s6
	sd t6, 0(t2)
	ld t6, 1624(a3)
	xor s6, t1, t6
	and s6, s6, t4
	xor t6, t6, s6
	sd t6, 8(t2)
	ld t6, 1632(a3)
	xor s6, a7, t6
	and s6, s6, t4
	xor t6, t6, s6
	sd t6, 16(t2)
	ld t6, 1640(a3)
	xor s6, s7, t6
	and s6, s6, t4
	xor t6, t6, s6
	sd t6, 24(t2)
	ld t6, 1648(a3)
	xor s6, s8, t6
	and s6, s6, t4
	xor t6, t6, s6
	sd t6, 32(t2)
	ld t6, 1656(a3)
	xor s6, s9, t6
	and s6, s6, t4
	xor t6, t6, s6
	sd t6, 40(t2)
	ld t6, 1664(a3)
	xor s6, s10, t6
	and s6, s6, t4
	xor t6, t6, s6
	sd t6, 48(t2)
	ld t6, 1672(a3)
	xor s6, s11, t6
	and s6, s6, t4
	xor t6, t6, s6
	sd t6, 56(t2)
	ld s6, 1536(a3)
	ld s7, 1544(a3)
	ld s8, 1552(a3)
	ld s9, 1560(a3)
	ld s10, 1568(a3)
	ld s11, 1576(a3)
	ret
	.option pop
