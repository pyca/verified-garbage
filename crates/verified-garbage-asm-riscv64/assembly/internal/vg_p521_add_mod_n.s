// The functions of `src/internal/vg_p521_add_mod_n.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p521_add_mod_n:
	.option push
	.option arch, +m, +c
	add t2, a0, a1
	add t4, a0, a2
	add t5, a0, a3
	addi a3, a0, 2047
	addi a3, a3, 2047
	addi a3, a3, 2047
	addi a3, a3, 3
	lui a6, 767739
	addiw a6, a6, 1823
	slli a6, a6, 32
	lui a7, 594822
	addiw a7, a7, 1033
	add a6, a6, a7
	sd a6, 1560(a3)
	lui a6, 244573
	addiw a6, a6, -1607
	slli a6, a6, 32
	lui a7, 563652
	addiw a7, a7, 1966
	add a6, a6, a7
	sd a6, 1568(a3)
	lui a6, 523456
	addiw a6, a6, 329
	slli a6, a6, 32
	lui a7, 1011866
	addiw a7, a7, 1488
	add a6, a6, a7
	sd a6, 1576(a3)
	lui a6, 333928
	addiw a6, a6, 1924
	slli a6, a6, 32
	lui a7, 783097
	addiw a7, a7, 1643
	add a6, a6, a7
	sd a6, 1584(a3)
	addi a6, zero, -6
	sd a6, 1592(a3)
	addi a6, zero, -1
	sd a6, 1600(a3)
	addi a6, zero, -1
	sd a6, 1608(a3)
	addi a6, zero, -1
	sd a6, 1616(a3)
	addi a6, zero, 511
	sd a6, 1624(a3)
	addi a5, zero, 0
	ld a6, 0(t4)
	ld a7, 0(t5)
	add t0, a6, a7
	sltu t3, t0, a7
	add t0, t0, a5
	sltu a5, t0, a5
	add a5, a5, t3
	sd t0, 1472(a3)
	ld a6, 8(t4)
	ld a7, 8(t5)
	add t0, a6, a7
	sltu t3, t0, a7
	add t0, t0, a5
	sltu a5, t0, a5
	add a5, a5, t3
	sd t0, 1480(a3)
	ld a6, 16(t4)
	ld a7, 16(t5)
	add t0, a6, a7
	sltu t3, t0, a7
	add t0, t0, a5
	sltu a5, t0, a5
	add a5, a5, t3
	sd t0, 1488(a3)
	ld a6, 24(t4)
	ld a7, 24(t5)
	add t0, a6, a7
	sltu t3, t0, a7
	add t0, t0, a5
	sltu a5, t0, a5
	add a5, a5, t3
	sd t0, 1496(a3)
	ld a6, 32(t4)
	ld a7, 32(t5)
	add t0, a6, a7
	sltu t3, t0, a7
	add t0, t0, a5
	sltu a5, t0, a5
	add a5, a5, t3
	sd t0, 1504(a3)
	ld a6, 40(t4)
	ld a7, 40(t5)
	add t0, a6, a7
	sltu t3, t0, a7
	add t0, t0, a5
	sltu a5, t0, a5
	add a5, a5, t3
	sd t0, 1512(a3)
	ld a6, 48(t4)
	ld a7, 48(t5)
	add t0, a6, a7
	sltu t3, t0, a7
	add t0, t0, a5
	sltu a5, t0, a5
	add a5, a5, t3
	sd t0, 1520(a3)
	ld a6, 56(t4)
	ld a7, 56(t5)
	add t0, a6, a7
	sltu t3, t0, a7
	add t0, t0, a5
	sltu a5, t0, a5
	add a5, a5, t3
	sd t0, 1528(a3)
	ld a6, 64(t4)
	ld a7, 64(t5)
	add t0, a6, a7
	sltu t3, t0, a7
	add t0, t0, a5
	sltu a5, t0, a5
	add a5, a5, t3
	sd t0, 1536(a3)
	sd a5, 1544(a3)
	addi a5, zero, 0
	ld a7, 1472(a3)
	ld a6, 1560(a3)
	sltu t3, a7, a6
	sub t0, a7, a6
	sltu a1, t0, a5
	sub t0, t0, a5
	add a5, t3, a1
	sd t0, 1560(a3)
	ld a7, 1480(a3)
	ld a6, 1568(a3)
	sltu t3, a7, a6
	sub t0, a7, a6
	sltu a1, t0, a5
	sub t0, t0, a5
	add a5, t3, a1
	sd t0, 1568(a3)
	ld a7, 1488(a3)
	ld a6, 1576(a3)
	sltu t3, a7, a6
	sub t0, a7, a6
	sltu a1, t0, a5
	sub t0, t0, a5
	add a5, t3, a1
	sd t0, 1576(a3)
	ld a7, 1496(a3)
	ld a6, 1584(a3)
	sltu t3, a7, a6
	sub t0, a7, a6
	sltu a1, t0, a5
	sub t0, t0, a5
	add a5, t3, a1
	sd t0, 1584(a3)
	ld a7, 1504(a3)
	ld a6, 1592(a3)
	sltu t3, a7, a6
	sub t0, a7, a6
	sltu a1, t0, a5
	sub t0, t0, a5
	add a5, t3, a1
	sd t0, 1592(a3)
	ld a7, 1512(a3)
	ld a6, 1600(a3)
	sltu t3, a7, a6
	sub t0, a7, a6
	sltu a1, t0, a5
	sub t0, t0, a5
	add a5, t3, a1
	sd t0, 1600(a3)
	ld a7, 1520(a3)
	ld a6, 1608(a3)
	sltu t3, a7, a6
	sub t0, a7, a6
	sltu a1, t0, a5
	sub t0, t0, a5
	add a5, t3, a1
	sd t0, 1608(a3)
	ld a7, 1528(a3)
	ld a6, 1616(a3)
	sltu t3, a7, a6
	sub t0, a7, a6
	sltu a1, t0, a5
	sub t0, t0, a5
	add a5, t3, a1
	sd t0, 1616(a3)
	ld a7, 1536(a3)
	ld a6, 1624(a3)
	sltu t3, a7, a6
	sub t0, a7, a6
	sltu a1, t0, a5
	sub t0, t0, a5
	add a5, t3, a1
	sd t0, 1624(a3)
	ld a7, 1544(a3)
	sub a7, a7, a5
	ld t0, 1560(a3)
	ld a6, 1472(a3)
	xor a6, a6, t0
	and a6, a6, a7
	xor t0, t0, a6
	sd t0, 0(t2)
	ld t0, 1568(a3)
	ld a6, 1480(a3)
	xor a6, a6, t0
	and a6, a6, a7
	xor t0, t0, a6
	sd t0, 8(t2)
	ld t0, 1576(a3)
	ld a6, 1488(a3)
	xor a6, a6, t0
	and a6, a6, a7
	xor t0, t0, a6
	sd t0, 16(t2)
	ld t0, 1584(a3)
	ld a6, 1496(a3)
	xor a6, a6, t0
	and a6, a6, a7
	xor t0, t0, a6
	sd t0, 24(t2)
	ld t0, 1592(a3)
	ld a6, 1504(a3)
	xor a6, a6, t0
	and a6, a6, a7
	xor t0, t0, a6
	sd t0, 32(t2)
	ld t0, 1600(a3)
	ld a6, 1512(a3)
	xor a6, a6, t0
	and a6, a6, a7
	xor t0, t0, a6
	sd t0, 40(t2)
	ld t0, 1608(a3)
	ld a6, 1520(a3)
	xor a6, a6, t0
	and a6, a6, a7
	xor t0, t0, a6
	sd t0, 48(t2)
	ld t0, 1616(a3)
	ld a6, 1528(a3)
	xor a6, a6, t0
	and a6, a6, a7
	xor t0, t0, a6
	sd t0, 56(t2)
	ld t0, 1624(a3)
	ld a6, 1536(a3)
	xor a6, a6, t0
	and a6, a6, a7
	xor t0, t0, a6
	sd t0, 64(t2)
	ret
	.option pop
