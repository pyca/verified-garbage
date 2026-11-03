// The functions of `src/internal/vg_p224_sub_mod_n.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p224_sub_mod_n:
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
	sltu a2, a1, a5
	sub a1, a1, a5
	sltu a5, t3, a6
	sub t3, t3, a6
	sltu a0, t3, a2
	sub t3, t3, a2
	add a2, a5, a0
	sltu a5, t6, a7
	sub t4, t6, a7
	sltu a0, t4, a2
	sub t4, t4, a2
	add a2, a5, a0
	sltu a5, a4, t0
	sub t5, a4, t0
	sltu a0, t5, a2
	sub t5, t5, a2
	add a2, a5, a0
	addi t0, zero, 0
	sub t0, t0, a2
	lui t6, 81363
	addiw t6, t6, -1723
	slli t6, t6, 32
	lui a0, 378307
	addiw a0, a0, -1475
	add t6, t6, a0
	and t6, t6, t0
	add a1, a1, t6
	sltu a7, a1, t6
	sd a1, 0(t2)
	lui t6, 1048561
	addiw t6, t6, 1699
	slli t6, t6, 32
	lui a0, 920463
	addiw a0, a0, 62
	add t6, t6, a0
	and t6, t6, t0
	add t3, t3, t6
	sltu a0, t3, t6
	add t3, t3, a7
	sltu a7, t3, a7
	add a7, a7, a0
	sd t3, 8(t2)
	lui t6, 0
	addiw t6, t6, 0
	slli t6, t6, 32
	lui a0, 0
	addiw a0, a0, -1
	add t6, t6, a0
	and t6, t6, t0
	add t4, t4, t6
	sltu a0, t4, t6
	add t4, t4, a7
	sltu a7, t4, a7
	add a7, a7, a0
	sd t4, 16(t2)
	lui t6, 0
	addiw t6, t6, 1
	slli t6, t6, 32
	lui a0, 0
	addiw a0, a0, -1
	add t6, t6, a0
	and t6, t6, t0
	add t5, t5, t6
	sltu a0, t5, t6
	add t5, t5, a7
	sltu a7, t5, a7
	add a7, a7, a0
	sd t5, 24(t2)
	ret
	.option pop
