// The functions of `src/internal/vg_p224_add_mod_n.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p224_add_mod_n:
	.option push
	.option arch, +m, +c
	add t2, a0, a1
	add t4, a0, a2
	add t5, a0, a3
	addi a3, a0, 2047
	addi a3, a3, 1
	ld a1, 0(t4)
	ld t3, 8(t4)
	ld t6, 16(t4)
	ld a4, 24(t4)
	ld a5, 0(t5)
	ld a6, 8(t5)
	ld a7, 16(t5)
	ld t0, 24(t5)
	add a1, a1, a5
	sltu a2, a1, a5
	add t3, t3, a6
	sltu a5, t3, a6
	add t3, t3, a2
	sltu a2, t3, a2
	add a2, a2, a5
	add t4, t6, a7
	sltu a5, t4, a7
	add t4, t4, a2
	sltu a2, t4, a2
	add a2, a2, a5
	add t5, a4, t0
	sltu a5, t5, t0
	add t5, t5, a2
	sltu a2, t5, a2
	add a2, a2, a5
	lui t0, 967213
	addiw t0, t0, 1723
	slli t0, t0, 32
	lui a0, 670269
	addiw a0, a0, 1475
	add t0, t0, a0
	add t6, a1, t0
	sltu a7, t6, t0
	lui t0, 15
	addiw t0, t0, -1699
	slli t0, t0, 32
	lui a0, 128113
	addiw a0, a0, -63
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
	addiw t0, t0, -1
	slli t0, t0, 32
	lui a0, 0
	addiw a0, a0, 0
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
