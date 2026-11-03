// The functions of `src/internal/vg_p521_mul_mod_p.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p521_mul_mod_p:
	.option push
	.option arch, +m, +c
	add t2, a0, a1
	add t4, a0, a2
	add t5, a0, a3
	addi a3, a0, 2047
	addi a3, a3, 2047
	addi a3, a3, 2047
	addi a3, a3, 3
	addi a7, zero, 0
	sd a7, 1472(a3)
	sd a7, 1480(a3)
	sd a7, 1488(a3)
	sd a7, 1496(a3)
	sd a7, 1504(a3)
	sd a7, 1512(a3)
	sd a7, 1520(a3)
	sd a7, 1528(a3)
	sd a7, 1536(a3)
	ld a4, 0(t5)
	addi a5, zero, 0
	ld a6, 0(t4)
	ld a7, 1472(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1472(a3)
	ld a6, 8(t4)
	ld a7, 1480(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1480(a3)
	ld a6, 16(t4)
	ld a7, 1488(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1488(a3)
	ld a6, 24(t4)
	ld a7, 1496(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1496(a3)
	ld a6, 32(t4)
	ld a7, 1504(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1504(a3)
	ld a6, 40(t4)
	ld a7, 1512(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1512(a3)
	ld a6, 48(t4)
	ld a7, 1520(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1520(a3)
	ld a6, 56(t4)
	ld a7, 1528(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1528(a3)
	ld a6, 64(t4)
	ld a7, 1536(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1536(a3)
	sd a5, 1544(a3)
	ld a4, 8(t5)
	addi a5, zero, 0
	ld a6, 0(t4)
	ld a7, 1480(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1480(a3)
	ld a6, 8(t4)
	ld a7, 1488(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1488(a3)
	ld a6, 16(t4)
	ld a7, 1496(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1496(a3)
	ld a6, 24(t4)
	ld a7, 1504(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1504(a3)
	ld a6, 32(t4)
	ld a7, 1512(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1512(a3)
	ld a6, 40(t4)
	ld a7, 1520(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1520(a3)
	ld a6, 48(t4)
	ld a7, 1528(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1528(a3)
	ld a6, 56(t4)
	ld a7, 1536(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1536(a3)
	ld a6, 64(t4)
	ld a7, 1544(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1544(a3)
	sd a5, 1552(a3)
	ld a4, 16(t5)
	addi a5, zero, 0
	ld a6, 0(t4)
	ld a7, 1488(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1488(a3)
	ld a6, 8(t4)
	ld a7, 1496(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1496(a3)
	ld a6, 16(t4)
	ld a7, 1504(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1504(a3)
	ld a6, 24(t4)
	ld a7, 1512(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1512(a3)
	ld a6, 32(t4)
	ld a7, 1520(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1520(a3)
	ld a6, 40(t4)
	ld a7, 1528(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1528(a3)
	ld a6, 48(t4)
	ld a7, 1536(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1536(a3)
	ld a6, 56(t4)
	ld a7, 1544(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1544(a3)
	ld a6, 64(t4)
	ld a7, 1552(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1552(a3)
	sd a5, 1560(a3)
	ld a4, 24(t5)
	addi a5, zero, 0
	ld a6, 0(t4)
	ld a7, 1496(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1496(a3)
	ld a6, 8(t4)
	ld a7, 1504(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1504(a3)
	ld a6, 16(t4)
	ld a7, 1512(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1512(a3)
	ld a6, 24(t4)
	ld a7, 1520(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1520(a3)
	ld a6, 32(t4)
	ld a7, 1528(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1528(a3)
	ld a6, 40(t4)
	ld a7, 1536(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1536(a3)
	ld a6, 48(t4)
	ld a7, 1544(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1544(a3)
	ld a6, 56(t4)
	ld a7, 1552(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1552(a3)
	ld a6, 64(t4)
	ld a7, 1560(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1560(a3)
	sd a5, 1568(a3)
	ld a4, 32(t5)
	addi a5, zero, 0
	ld a6, 0(t4)
	ld a7, 1504(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1504(a3)
	ld a6, 8(t4)
	ld a7, 1512(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1512(a3)
	ld a6, 16(t4)
	ld a7, 1520(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1520(a3)
	ld a6, 24(t4)
	ld a7, 1528(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1528(a3)
	ld a6, 32(t4)
	ld a7, 1536(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1536(a3)
	ld a6, 40(t4)
	ld a7, 1544(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1544(a3)
	ld a6, 48(t4)
	ld a7, 1552(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1552(a3)
	ld a6, 56(t4)
	ld a7, 1560(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1560(a3)
	ld a6, 64(t4)
	ld a7, 1568(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1568(a3)
	sd a5, 1576(a3)
	ld a4, 40(t5)
	addi a5, zero, 0
	ld a6, 0(t4)
	ld a7, 1512(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1512(a3)
	ld a6, 8(t4)
	ld a7, 1520(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1520(a3)
	ld a6, 16(t4)
	ld a7, 1528(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1528(a3)
	ld a6, 24(t4)
	ld a7, 1536(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1536(a3)
	ld a6, 32(t4)
	ld a7, 1544(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1544(a3)
	ld a6, 40(t4)
	ld a7, 1552(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1552(a3)
	ld a6, 48(t4)
	ld a7, 1560(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1560(a3)
	ld a6, 56(t4)
	ld a7, 1568(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1568(a3)
	ld a6, 64(t4)
	ld a7, 1576(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1576(a3)
	sd a5, 1584(a3)
	ld a4, 48(t5)
	addi a5, zero, 0
	ld a6, 0(t4)
	ld a7, 1520(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1520(a3)
	ld a6, 8(t4)
	ld a7, 1528(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1528(a3)
	ld a6, 16(t4)
	ld a7, 1536(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1536(a3)
	ld a6, 24(t4)
	ld a7, 1544(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1544(a3)
	ld a6, 32(t4)
	ld a7, 1552(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1552(a3)
	ld a6, 40(t4)
	ld a7, 1560(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1560(a3)
	ld a6, 48(t4)
	ld a7, 1568(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1568(a3)
	ld a6, 56(t4)
	ld a7, 1576(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1576(a3)
	ld a6, 64(t4)
	ld a7, 1584(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1584(a3)
	sd a5, 1592(a3)
	ld a4, 56(t5)
	addi a5, zero, 0
	ld a6, 0(t4)
	ld a7, 1528(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1528(a3)
	ld a6, 8(t4)
	ld a7, 1536(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1536(a3)
	ld a6, 16(t4)
	ld a7, 1544(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1544(a3)
	ld a6, 24(t4)
	ld a7, 1552(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1552(a3)
	ld a6, 32(t4)
	ld a7, 1560(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1560(a3)
	ld a6, 40(t4)
	ld a7, 1568(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1568(a3)
	ld a6, 48(t4)
	ld a7, 1576(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1576(a3)
	ld a6, 56(t4)
	ld a7, 1584(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1584(a3)
	ld a6, 64(t4)
	ld a7, 1592(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1592(a3)
	sd a5, 1600(a3)
	ld a4, 64(t5)
	addi a5, zero, 0
	ld a6, 0(t4)
	ld a7, 1536(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1536(a3)
	ld a6, 8(t4)
	ld a7, 1544(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1544(a3)
	ld a6, 16(t4)
	ld a7, 1552(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1552(a3)
	ld a6, 24(t4)
	ld a7, 1560(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1560(a3)
	ld a6, 32(t4)
	ld a7, 1568(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1568(a3)
	ld a6, 40(t4)
	ld a7, 1576(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1576(a3)
	ld a6, 48(t4)
	ld a7, 1584(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1584(a3)
	ld a6, 56(t4)
	ld a7, 1592(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1592(a3)
	ld a6, 64(t4)
	ld a7, 1600(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1600(a3)
	sd a5, 1608(a3)
	addi a5, zero, 0
	ld a7, 1536(a3)
	ld t0, 1544(a3)
	srli a7, a7, 9
	slli t0, t0, 55
	or a7, a7, t0
	ld a6, 1472(a3)
	add t0, a6, a7
	sltu t3, t0, a7
	add t0, t0, a5
	sltu a5, t0, a5
	add a5, a5, t3
	sd t0, 1472(a3)
	ld a7, 1544(a3)
	ld t0, 1552(a3)
	srli a7, a7, 9
	slli t0, t0, 55
	or a7, a7, t0
	ld a6, 1480(a3)
	add t0, a6, a7
	sltu t3, t0, a7
	add t0, t0, a5
	sltu a5, t0, a5
	add a5, a5, t3
	sd t0, 1480(a3)
	ld a7, 1552(a3)
	ld t0, 1560(a3)
	srli a7, a7, 9
	slli t0, t0, 55
	or a7, a7, t0
	ld a6, 1488(a3)
	add t0, a6, a7
	sltu t3, t0, a7
	add t0, t0, a5
	sltu a5, t0, a5
	add a5, a5, t3
	sd t0, 1488(a3)
	ld a7, 1560(a3)
	ld t0, 1568(a3)
	srli a7, a7, 9
	slli t0, t0, 55
	or a7, a7, t0
	ld a6, 1496(a3)
	add t0, a6, a7
	sltu t3, t0, a7
	add t0, t0, a5
	sltu a5, t0, a5
	add a5, a5, t3
	sd t0, 1496(a3)
	ld a7, 1568(a3)
	ld t0, 1576(a3)
	srli a7, a7, 9
	slli t0, t0, 55
	or a7, a7, t0
	ld a6, 1504(a3)
	add t0, a6, a7
	sltu t3, t0, a7
	add t0, t0, a5
	sltu a5, t0, a5
	add a5, a5, t3
	sd t0, 1504(a3)
	ld a7, 1576(a3)
	ld t0, 1584(a3)
	srli a7, a7, 9
	slli t0, t0, 55
	or a7, a7, t0
	ld a6, 1512(a3)
	add t0, a6, a7
	sltu t3, t0, a7
	add t0, t0, a5
	sltu a5, t0, a5
	add a5, a5, t3
	sd t0, 1512(a3)
	ld a7, 1584(a3)
	ld t0, 1592(a3)
	srli a7, a7, 9
	slli t0, t0, 55
	or a7, a7, t0
	ld a6, 1520(a3)
	add t0, a6, a7
	sltu t3, t0, a7
	add t0, t0, a5
	sltu a5, t0, a5
	add a5, a5, t3
	sd t0, 1520(a3)
	ld a7, 1592(a3)
	ld t0, 1600(a3)
	srli a7, a7, 9
	slli t0, t0, 55
	or a7, a7, t0
	ld a6, 1528(a3)
	add t0, a6, a7
	sltu t3, t0, a7
	add t0, t0, a5
	sltu a5, t0, a5
	add a5, a5, t3
	sd t0, 1528(a3)
	ld a7, 1600(a3)
	ld t0, 1608(a3)
	srli a7, a7, 9
	slli t0, t0, 55
	or a7, a7, t0
	ld a6, 1536(a3)
	andi a6, a6, 511
	add t0, a6, a7
	sltu t3, t0, a7
	add t0, t0, a5
	sltu a5, t0, a5
	add a5, a5, t3
	sd t0, 1536(a3)
	ld t0, 1536(a3)
	srli a6, t0, 9
	slli a5, a5, 55
	or a5, a5, a6
	andi t0, t0, 511
	sd t0, 1536(a3)
	ld t0, 1472(a3)
	add t0, t0, a5
	sltu a5, t0, a5
	sd t0, 1472(a3)
	ld t0, 1480(a3)
	add t0, t0, a5
	sltu a5, t0, a5
	sd t0, 1480(a3)
	ld t0, 1488(a3)
	add t0, t0, a5
	sltu a5, t0, a5
	sd t0, 1488(a3)
	ld t0, 1496(a3)
	add t0, t0, a5
	sltu a5, t0, a5
	sd t0, 1496(a3)
	ld t0, 1504(a3)
	add t0, t0, a5
	sltu a5, t0, a5
	sd t0, 1504(a3)
	ld t0, 1512(a3)
	add t0, t0, a5
	sltu a5, t0, a5
	sd t0, 1512(a3)
	ld t0, 1520(a3)
	add t0, t0, a5
	sltu a5, t0, a5
	sd t0, 1520(a3)
	ld t0, 1528(a3)
	add t0, t0, a5
	sltu a5, t0, a5
	sd t0, 1528(a3)
	ld t0, 1536(a3)
	add t0, t0, a5
	sltu a5, t0, a5
	sd t0, 1536(a3)
	addi a5, zero, 1
	ld t0, 1472(a3)
	add t0, t0, a5
	sltu a5, t0, a5
	ld t0, 1480(a3)
	add t0, t0, a5
	sltu a5, t0, a5
	ld t0, 1488(a3)
	add t0, t0, a5
	sltu a5, t0, a5
	ld t0, 1496(a3)
	add t0, t0, a5
	sltu a5, t0, a5
	ld t0, 1504(a3)
	add t0, t0, a5
	sltu a5, t0, a5
	ld t0, 1512(a3)
	add t0, t0, a5
	sltu a5, t0, a5
	ld t0, 1520(a3)
	add t0, t0, a5
	sltu a5, t0, a5
	ld t0, 1528(a3)
	add t0, t0, a5
	sltu a5, t0, a5
	ld t0, 1536(a3)
	add t0, t0, a5
	srli a5, t0, 9
	ld t0, 1472(a3)
	add t0, t0, a5
	sltu a5, t0, a5
	sd t0, 1472(a3)
	ld t0, 1480(a3)
	add t0, t0, a5
	sltu a5, t0, a5
	sd t0, 1480(a3)
	ld t0, 1488(a3)
	add t0, t0, a5
	sltu a5, t0, a5
	sd t0, 1488(a3)
	ld t0, 1496(a3)
	add t0, t0, a5
	sltu a5, t0, a5
	sd t0, 1496(a3)
	ld t0, 1504(a3)
	add t0, t0, a5
	sltu a5, t0, a5
	sd t0, 1504(a3)
	ld t0, 1512(a3)
	add t0, t0, a5
	sltu a5, t0, a5
	sd t0, 1512(a3)
	ld t0, 1520(a3)
	add t0, t0, a5
	sltu a5, t0, a5
	sd t0, 1520(a3)
	ld t0, 1528(a3)
	add t0, t0, a5
	sltu a5, t0, a5
	sd t0, 1528(a3)
	ld t0, 1536(a3)
	add t0, t0, a5
	sltu a5, t0, a5
	sd t0, 1536(a3)
	ld t0, 1536(a3)
	andi t0, t0, 511
	sd t0, 1536(a3)
	ld t0, 1472(a3)
	ld a6, 1480(a3)
	srli t0, t0, 55
	slli a6, a6, 9
	or t0, t0, a6
	sd t0, 0(t2)
	ld t0, 1480(a3)
	ld a6, 1488(a3)
	srli t0, t0, 55
	slli a6, a6, 9
	or t0, t0, a6
	sd t0, 8(t2)
	ld t0, 1488(a3)
	ld a6, 1496(a3)
	srli t0, t0, 55
	slli a6, a6, 9
	or t0, t0, a6
	sd t0, 16(t2)
	ld t0, 1496(a3)
	ld a6, 1504(a3)
	srli t0, t0, 55
	slli a6, a6, 9
	or t0, t0, a6
	sd t0, 24(t2)
	ld t0, 1504(a3)
	ld a6, 1512(a3)
	srli t0, t0, 55
	slli a6, a6, 9
	or t0, t0, a6
	sd t0, 32(t2)
	ld t0, 1512(a3)
	ld a6, 1520(a3)
	srli t0, t0, 55
	slli a6, a6, 9
	or t0, t0, a6
	sd t0, 40(t2)
	ld t0, 1520(a3)
	ld a6, 1528(a3)
	srli t0, t0, 55
	slli a6, a6, 9
	or t0, t0, a6
	sd t0, 48(t2)
	ld t0, 1528(a3)
	ld a6, 1536(a3)
	srli t0, t0, 55
	slli a6, a6, 9
	or t0, t0, a6
	ld a6, 1472(a3)
	slli a6, a6, 18
	or t0, t0, a6
	sd t0, 56(t2)
	ld t0, 1472(a3)
	srli t0, t0, 46
	andi t0, t0, 511
	sd t0, 64(t2)
	ret
	.option pop
