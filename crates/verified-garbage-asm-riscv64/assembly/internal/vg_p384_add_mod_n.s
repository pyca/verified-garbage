// The functions of `src/internal/vg_p384_add_mod_n.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p384_add_mod_n:
	.option push
	.option arch, +m, +c
	add t2, a0, a1
	add t4, a0, a2
	add t5, a0, a3
	addi a3, a0, 2047
	addi a3, a3, 1
	addi a0, t4, 0
	addi a7, t5, 0
	addi a2, zero, 0
	ld t5, 0(a0)
	ld a5, 0(a7)
	add t5, t5, a5
	sltu a6, t5, a5
	add t5, t5, a2
	sltu a2, t5, a2
	add a2, a2, a6
	ld t6, 8(a0)
	ld a5, 8(a7)
	add t6, t6, a5
	sltu a6, t6, a5
	add t6, t6, a2
	sltu a2, t6, a2
	add a2, a2, a6
	ld t3, 16(a0)
	ld a5, 16(a7)
	add t3, t3, a5
	sltu a6, t3, a5
	add t3, t3, a2
	sltu a2, t3, a2
	add a2, a2, a6
	ld t4, 24(a0)
	ld a5, 24(a7)
	add t4, t4, a5
	sltu a6, t4, a5
	add t4, t4, a2
	sltu a2, t4, a2
	add a2, a2, a6
	ld a1, 32(a0)
	ld a5, 32(a7)
	add a1, a1, a5
	sltu a6, a1, a5
	add a1, a1, a2
	sltu a2, a1, a2
	add a2, a2, a6
	ld a4, 40(a0)
	ld a5, 40(a7)
	add a4, a4, a5
	sltu a6, a4, a5
	add a4, a4, a2
	sltu a2, a4, a2
	add a2, a2, a6
	addi a7, zero, 0
	lui t0, 78142
	addiw t0, t0, 1685
	slli t0, t0, 32
	lui a6, 209837
	addiw a6, a6, 1677
	add t0, t0, a6
	add a5, t5, t0
	sltu a0, a5, t0
	add a5, a5, a7
	sltu a7, a5, a7
	add a7, a7, a0
	sd a5, 0(t2)
	lui t0, 687711
	addiw t0, t0, 590
	slli t0, t0, 32
	lui a6, 750838
	addiw a6, a6, -1915
	add t0, t0, a6
	add a5, t6, t0
	sltu a0, a5, t0
	add a5, a5, a7
	sltu a7, a5, a7
	add a7, a7, a0
	sd a5, 8(t2)
	lui t0, 231883
	addiw t0, t0, 638
	slli t0, t0, 32
	lui a6, 48269
	addiw a6, a6, 544
	add t0, t0, a6
	add a5, t3, t0
	sltu a0, a5, t0
	add a5, a5, a7
	sltu a7, a5, a7
	add a7, a7, a0
	sd a5, 16(t2)
	addi t0, zero, 0
	add a5, t4, t0
	sltu a0, a5, t0
	add a5, a5, a7
	sltu a7, a5, a7
	add a7, a7, a0
	sd a5, 24(t2)
	add a5, a1, t0
	sltu a0, a5, t0
	add a5, a5, a7
	sltu a7, a5, a7
	add a7, a7, a0
	sd a5, 32(t2)
	add a5, a4, t0
	sltu a0, a5, t0
	add a5, a5, a7
	sltu a7, a5, a7
	add a7, a7, a0
	sd a5, 40(t2)
	or a7, a7, a2
	addi t0, zero, 0
	sub t0, t0, a7
	ld a5, 0(t2)
	xor a5, a5, t5
	and a5, a5, t0
	xor a5, a5, t5
	sd a5, 0(t2)
	ld a5, 8(t2)
	xor a5, a5, t6
	and a5, a5, t0
	xor a5, a5, t6
	sd a5, 8(t2)
	ld a5, 16(t2)
	xor a5, a5, t3
	and a5, a5, t0
	xor a5, a5, t3
	sd a5, 16(t2)
	ld a5, 24(t2)
	xor a5, a5, t4
	and a5, a5, t0
	xor a5, a5, t4
	sd a5, 24(t2)
	ld a5, 32(t2)
	xor a5, a5, a1
	and a5, a5, t0
	xor a5, a5, a1
	sd a5, 32(t2)
	ld a5, 40(t2)
	xor a5, a5, a4
	and a5, a5, t0
	xor a5, a5, a4
	sd a5, 40(t2)
	ret
	.option pop
