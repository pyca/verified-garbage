// The functions of `src/internal/vg_brainpoolp512r1_mul_mod_n.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_brainpoolp512r1_mul_mod_n:
	.option push
	.option arch, +m, +c
	add t2, a0, a1
	add t4, a0, a2
	add t5, a0, a3
	addi a3, a0, 2047
	addi a3, a3, 2047
	addi a3, a3, 2047
	addi a3, a3, 3
	lui a6, 743545
	addiw a6, a6, 1667
	slli a6, a6, 32
	lui a7, 641680
	addiw a7, a7, 105
	add a6, a6, a7
	sd a6, 1616(a3)
	lui a6, 121629
	addiw a6, a6, 897
	slli a6, a6, 32
	lui a7, 34270
	addiw a7, a7, -1315
	add a6, a6, a7
	sd a6, 1624(a3)
	lui a6, 268390
	addiw a6, a6, 281
	slli a6, a6, 32
	lui a7, 522945
	addiw a7, a7, 71
	add a6, a6, a7
	sd a6, 1632(a3)
	lui a6, 349158
	addiw a6, a6, -959
	slli a6, a6, 32
	lui a7, 314002
	addiw a7, a7, 1561
	add a6, a6, a7
	sd a6, 1640(a3)
	lui a6, 878138
	addiw a6, a6, -822
	slli a6, a6, 32
	lui a7, 459569
	addiw a7, a7, -1936
	add a6, a6, a7
	sd a6, 1648(a3)
	lui a6, 832265
	addiw a6, a6, -588
	slli a6, a6, 32
	lui a7, 736413
	addiw a7, a7, 526
	add a6, a6, a7
	sd a6, 1656(a3)
	lui a6, 261454
	addiw a6, a6, 1710
	slli a6, a6, 32
	lui a7, 212128
	addiw a7, a7, -1017
	add a6, a6, a7
	sd a6, 1664(a3)
	lui a6, 699866
	addiw a6, a6, -583
	slli a6, a6, 32
	lui a7, 900764
	addiw a7, a7, 1163
	add a6, a6, a7
	sd a6, 1672(a3)
	addi a7, zero, 0
	sd a7, 1536(a3)
	sd a7, 1544(a3)
	sd a7, 1552(a3)
	sd a7, 1560(a3)
	sd a7, 1568(a3)
	sd a7, 1576(a3)
	sd a7, 1584(a3)
	sd a7, 1592(a3)
	sd a7, 1600(a3)
	lui t6, 709781
	addiw t6, t6, 1055
	slli t6, t6, 32
	lui a7, 61879
	addiw a7, a7, 39
	add t6, t6, a7
	ld a4, 0(t5)
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
	ld a7, 1600(a3)
	add t0, a7, a5
	sltu t3, t0, a5
	sd t0, 1600(a3)
	sd t3, 1608(a3)
	ld a7, 1536(a3)
	mul a4, a7, t6
	ld a6, 1616(a3)
	mulhu a5, a4, a6
	addi t3, zero, 0
	sltu t3, t3, a7
	add a5, a5, t3
	ld a6, 1624(a3)
	ld a7, 1544(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1536(a3)
	ld a6, 1632(a3)
	ld a7, 1552(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1544(a3)
	ld a6, 1640(a3)
	ld a7, 1560(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1552(a3)
	ld a6, 1648(a3)
	ld a7, 1568(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1560(a3)
	ld a6, 1656(a3)
	ld a7, 1576(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1568(a3)
	ld a6, 1664(a3)
	ld a7, 1584(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1576(a3)
	ld a6, 1672(a3)
	ld a7, 1592(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1584(a3)
	ld a7, 1600(a3)
	add t0, a7, a5
	sltu t3, t0, a5
	sd t0, 1592(a3)
	ld a7, 1608(a3)
	add a7, a7, t3
	sd a7, 1600(a3)
	ld a4, 8(t5)
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
	ld a7, 1600(a3)
	add t0, a7, a5
	sltu t3, t0, a5
	sd t0, 1600(a3)
	sd t3, 1608(a3)
	ld a7, 1536(a3)
	mul a4, a7, t6
	ld a6, 1616(a3)
	mulhu a5, a4, a6
	addi t3, zero, 0
	sltu t3, t3, a7
	add a5, a5, t3
	ld a6, 1624(a3)
	ld a7, 1544(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1536(a3)
	ld a6, 1632(a3)
	ld a7, 1552(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1544(a3)
	ld a6, 1640(a3)
	ld a7, 1560(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1552(a3)
	ld a6, 1648(a3)
	ld a7, 1568(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1560(a3)
	ld a6, 1656(a3)
	ld a7, 1576(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1568(a3)
	ld a6, 1664(a3)
	ld a7, 1584(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1576(a3)
	ld a6, 1672(a3)
	ld a7, 1592(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1584(a3)
	ld a7, 1600(a3)
	add t0, a7, a5
	sltu t3, t0, a5
	sd t0, 1592(a3)
	ld a7, 1608(a3)
	add a7, a7, t3
	sd a7, 1600(a3)
	ld a4, 16(t5)
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
	ld a7, 1600(a3)
	add t0, a7, a5
	sltu t3, t0, a5
	sd t0, 1600(a3)
	sd t3, 1608(a3)
	ld a7, 1536(a3)
	mul a4, a7, t6
	ld a6, 1616(a3)
	mulhu a5, a4, a6
	addi t3, zero, 0
	sltu t3, t3, a7
	add a5, a5, t3
	ld a6, 1624(a3)
	ld a7, 1544(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1536(a3)
	ld a6, 1632(a3)
	ld a7, 1552(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1544(a3)
	ld a6, 1640(a3)
	ld a7, 1560(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1552(a3)
	ld a6, 1648(a3)
	ld a7, 1568(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1560(a3)
	ld a6, 1656(a3)
	ld a7, 1576(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1568(a3)
	ld a6, 1664(a3)
	ld a7, 1584(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1576(a3)
	ld a6, 1672(a3)
	ld a7, 1592(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1584(a3)
	ld a7, 1600(a3)
	add t0, a7, a5
	sltu t3, t0, a5
	sd t0, 1592(a3)
	ld a7, 1608(a3)
	add a7, a7, t3
	sd a7, 1600(a3)
	ld a4, 24(t5)
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
	ld a7, 1600(a3)
	add t0, a7, a5
	sltu t3, t0, a5
	sd t0, 1600(a3)
	sd t3, 1608(a3)
	ld a7, 1536(a3)
	mul a4, a7, t6
	ld a6, 1616(a3)
	mulhu a5, a4, a6
	addi t3, zero, 0
	sltu t3, t3, a7
	add a5, a5, t3
	ld a6, 1624(a3)
	ld a7, 1544(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1536(a3)
	ld a6, 1632(a3)
	ld a7, 1552(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1544(a3)
	ld a6, 1640(a3)
	ld a7, 1560(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1552(a3)
	ld a6, 1648(a3)
	ld a7, 1568(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1560(a3)
	ld a6, 1656(a3)
	ld a7, 1576(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1568(a3)
	ld a6, 1664(a3)
	ld a7, 1584(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1576(a3)
	ld a6, 1672(a3)
	ld a7, 1592(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1584(a3)
	ld a7, 1600(a3)
	add t0, a7, a5
	sltu t3, t0, a5
	sd t0, 1592(a3)
	ld a7, 1608(a3)
	add a7, a7, t3
	sd a7, 1600(a3)
	ld a4, 32(t5)
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
	ld a7, 1600(a3)
	add t0, a7, a5
	sltu t3, t0, a5
	sd t0, 1600(a3)
	sd t3, 1608(a3)
	ld a7, 1536(a3)
	mul a4, a7, t6
	ld a6, 1616(a3)
	mulhu a5, a4, a6
	addi t3, zero, 0
	sltu t3, t3, a7
	add a5, a5, t3
	ld a6, 1624(a3)
	ld a7, 1544(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1536(a3)
	ld a6, 1632(a3)
	ld a7, 1552(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1544(a3)
	ld a6, 1640(a3)
	ld a7, 1560(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1552(a3)
	ld a6, 1648(a3)
	ld a7, 1568(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1560(a3)
	ld a6, 1656(a3)
	ld a7, 1576(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1568(a3)
	ld a6, 1664(a3)
	ld a7, 1584(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1576(a3)
	ld a6, 1672(a3)
	ld a7, 1592(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1584(a3)
	ld a7, 1600(a3)
	add t0, a7, a5
	sltu t3, t0, a5
	sd t0, 1592(a3)
	ld a7, 1608(a3)
	add a7, a7, t3
	sd a7, 1600(a3)
	ld a4, 40(t5)
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
	ld a7, 1600(a3)
	add t0, a7, a5
	sltu t3, t0, a5
	sd t0, 1600(a3)
	sd t3, 1608(a3)
	ld a7, 1536(a3)
	mul a4, a7, t6
	ld a6, 1616(a3)
	mulhu a5, a4, a6
	addi t3, zero, 0
	sltu t3, t3, a7
	add a5, a5, t3
	ld a6, 1624(a3)
	ld a7, 1544(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1536(a3)
	ld a6, 1632(a3)
	ld a7, 1552(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1544(a3)
	ld a6, 1640(a3)
	ld a7, 1560(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1552(a3)
	ld a6, 1648(a3)
	ld a7, 1568(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1560(a3)
	ld a6, 1656(a3)
	ld a7, 1576(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1568(a3)
	ld a6, 1664(a3)
	ld a7, 1584(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1576(a3)
	ld a6, 1672(a3)
	ld a7, 1592(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1584(a3)
	ld a7, 1600(a3)
	add t0, a7, a5
	sltu t3, t0, a5
	sd t0, 1592(a3)
	ld a7, 1608(a3)
	add a7, a7, t3
	sd a7, 1600(a3)
	ld a4, 48(t5)
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
	ld a7, 1600(a3)
	add t0, a7, a5
	sltu t3, t0, a5
	sd t0, 1600(a3)
	sd t3, 1608(a3)
	ld a7, 1536(a3)
	mul a4, a7, t6
	ld a6, 1616(a3)
	mulhu a5, a4, a6
	addi t3, zero, 0
	sltu t3, t3, a7
	add a5, a5, t3
	ld a6, 1624(a3)
	ld a7, 1544(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1536(a3)
	ld a6, 1632(a3)
	ld a7, 1552(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1544(a3)
	ld a6, 1640(a3)
	ld a7, 1560(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1552(a3)
	ld a6, 1648(a3)
	ld a7, 1568(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1560(a3)
	ld a6, 1656(a3)
	ld a7, 1576(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1568(a3)
	ld a6, 1664(a3)
	ld a7, 1584(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1576(a3)
	ld a6, 1672(a3)
	ld a7, 1592(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1584(a3)
	ld a7, 1600(a3)
	add t0, a7, a5
	sltu t3, t0, a5
	sd t0, 1592(a3)
	ld a7, 1608(a3)
	add a7, a7, t3
	sd a7, 1600(a3)
	ld a4, 56(t5)
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
	ld a7, 1600(a3)
	add t0, a7, a5
	sltu t3, t0, a5
	sd t0, 1600(a3)
	sd t3, 1608(a3)
	ld a7, 1536(a3)
	mul a4, a7, t6
	ld a6, 1616(a3)
	mulhu a5, a4, a6
	addi t3, zero, 0
	sltu t3, t3, a7
	add a5, a5, t3
	ld a6, 1624(a3)
	ld a7, 1544(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1536(a3)
	ld a6, 1632(a3)
	ld a7, 1552(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1544(a3)
	ld a6, 1640(a3)
	ld a7, 1560(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1552(a3)
	ld a6, 1648(a3)
	ld a7, 1568(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1560(a3)
	ld a6, 1656(a3)
	ld a7, 1576(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1568(a3)
	ld a6, 1664(a3)
	ld a7, 1584(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1576(a3)
	ld a6, 1672(a3)
	ld a7, 1592(a3)
	mul t0, a6, a4
	mulhu a1, a6, a4
	add t0, t0, a7
	sltu t3, t0, a7
	add a1, a1, t3
	add t0, t0, a5
	sltu t3, t0, a5
	add a5, a1, t3
	sd t0, 1584(a3)
	ld a7, 1600(a3)
	add t0, a7, a5
	sltu t3, t0, a5
	sd t0, 1592(a3)
	ld a7, 1608(a3)
	add a7, a7, t3
	sd a7, 1600(a3)
	addi a5, zero, 0
	ld a7, 1536(a3)
	ld a6, 1616(a3)
	sltu t3, a7, a6
	sub t0, a7, a6
	sltu a1, t0, a5
	sub t0, t0, a5
	add a5, t3, a1
	sd t0, 1616(a3)
	ld a7, 1544(a3)
	ld a6, 1624(a3)
	sltu t3, a7, a6
	sub t0, a7, a6
	sltu a1, t0, a5
	sub t0, t0, a5
	add a5, t3, a1
	sd t0, 1624(a3)
	ld a7, 1552(a3)
	ld a6, 1632(a3)
	sltu t3, a7, a6
	sub t0, a7, a6
	sltu a1, t0, a5
	sub t0, t0, a5
	add a5, t3, a1
	sd t0, 1632(a3)
	ld a7, 1560(a3)
	ld a6, 1640(a3)
	sltu t3, a7, a6
	sub t0, a7, a6
	sltu a1, t0, a5
	sub t0, t0, a5
	add a5, t3, a1
	sd t0, 1640(a3)
	ld a7, 1568(a3)
	ld a6, 1648(a3)
	sltu t3, a7, a6
	sub t0, a7, a6
	sltu a1, t0, a5
	sub t0, t0, a5
	add a5, t3, a1
	sd t0, 1648(a3)
	ld a7, 1576(a3)
	ld a6, 1656(a3)
	sltu t3, a7, a6
	sub t0, a7, a6
	sltu a1, t0, a5
	sub t0, t0, a5
	add a5, t3, a1
	sd t0, 1656(a3)
	ld a7, 1584(a3)
	ld a6, 1664(a3)
	sltu t3, a7, a6
	sub t0, a7, a6
	sltu a1, t0, a5
	sub t0, t0, a5
	add a5, t3, a1
	sd t0, 1664(a3)
	ld a7, 1592(a3)
	ld a6, 1672(a3)
	sltu t3, a7, a6
	sub t0, a7, a6
	sltu a1, t0, a5
	sub t0, t0, a5
	add a5, t3, a1
	sd t0, 1672(a3)
	ld a7, 1600(a3)
	sub a7, a7, a5
	ld t0, 1616(a3)
	ld a6, 1536(a3)
	xor a6, a6, t0
	and a6, a6, a7
	xor t0, t0, a6
	sd t0, 0(t2)
	ld t0, 1624(a3)
	ld a6, 1544(a3)
	xor a6, a6, t0
	and a6, a6, a7
	xor t0, t0, a6
	sd t0, 8(t2)
	ld t0, 1632(a3)
	ld a6, 1552(a3)
	xor a6, a6, t0
	and a6, a6, a7
	xor t0, t0, a6
	sd t0, 16(t2)
	ld t0, 1640(a3)
	ld a6, 1560(a3)
	xor a6, a6, t0
	and a6, a6, a7
	xor t0, t0, a6
	sd t0, 24(t2)
	ld t0, 1648(a3)
	ld a6, 1568(a3)
	xor a6, a6, t0
	and a6, a6, a7
	xor t0, t0, a6
	sd t0, 32(t2)
	ld t0, 1656(a3)
	ld a6, 1576(a3)
	xor a6, a6, t0
	and a6, a6, a7
	xor t0, t0, a6
	sd t0, 40(t2)
	ld t0, 1664(a3)
	ld a6, 1584(a3)
	xor a6, a6, t0
	and a6, a6, a7
	xor t0, t0, a6
	sd t0, 48(t2)
	ld t0, 1672(a3)
	ld a6, 1592(a3)
	xor a6, a6, t0
	and a6, a6, a7
	xor t0, t0, a6
	sd t0, 56(t2)
	ret
	.option pop
