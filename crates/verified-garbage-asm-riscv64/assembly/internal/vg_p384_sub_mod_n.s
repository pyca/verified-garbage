// The functions of `src/internal/vg_p384_sub_mod_n.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p384_sub_mod_n:
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
	sltu a6, t5, a5
	sub t5, t5, a5
	sltu t0, t5, a2
	sub t5, t5, a2
	add a2, a6, t0
	ld t6, 8(a0)
	ld a5, 8(a7)
	sltu a6, t6, a5
	sub t6, t6, a5
	sltu t0, t6, a2
	sub t6, t6, a2
	add a2, a6, t0
	ld t3, 16(a0)
	ld a5, 16(a7)
	sltu a6, t3, a5
	sub t3, t3, a5
	sltu t0, t3, a2
	sub t3, t3, a2
	add a2, a6, t0
	ld t4, 24(a0)
	ld a5, 24(a7)
	sltu a6, t4, a5
	sub t4, t4, a5
	sltu t0, t4, a2
	sub t4, t4, a2
	add a2, a6, t0
	ld a1, 32(a0)
	ld a5, 32(a7)
	sltu a6, a1, a5
	sub a1, a1, a5
	sltu t0, a1, a2
	sub a1, a1, a2
	add a2, a6, t0
	ld a4, 40(a0)
	ld a5, 40(a7)
	sltu a6, a4, a5
	sub a4, a4, a5
	sltu t0, a4, a2
	sub a4, a4, a2
	add a2, a6, t0
	addi t0, zero, 0
	sub t0, t0, a2
	addi a7, zero, 0
	lui a6, 970434
	addiw a6, a6, -1685
	slli a6, a6, 32
	lui a0, 838739
	addiw a0, a0, -1677
	add a6, a6, a0
	and a6, a6, t0
	add t5, t5, a6
	sltu a0, t5, a6
	add t5, t5, a7
	sltu a7, t5, a7
	add a7, a7, a0
	sd t5, 0(t2)
	lui a6, 360865
	addiw a6, a6, -590
	slli a6, a6, 32
	lui a0, 297738
	addiw a0, a0, 1914
	add a6, a6, a0
	and a6, a6, t0
	add t6, t6, a6
	sltu a0, t6, a6
	add t6, t6, a7
	sltu a7, t6, a7
	add a7, a7, a0
	sd t6, 8(t2)
	lui a6, 816693
	addiw a6, a6, -638
	slli a6, a6, 32
	lui a0, 1000307
	addiw a0, a0, -545
	add a6, a6, a0
	and a6, a6, t0
	add t3, t3, a6
	sltu a0, t3, a6
	add t3, t3, a7
	sltu a7, t3, a7
	add a7, a7, a0
	sd t3, 16(t2)
	addi a6, t0, 0
	add t4, t4, a6
	sltu a0, t4, a6
	add t4, t4, a7
	sltu a7, t4, a7
	add a7, a7, a0
	sd t4, 24(t2)
	addi a6, t0, 0
	add a1, a1, a6
	sltu a0, a1, a6
	add a1, a1, a7
	sltu a7, a1, a7
	add a7, a7, a0
	sd a1, 32(t2)
	addi a6, t0, 0
	add a4, a4, a6
	sltu a0, a4, a6
	add a4, a4, a7
	sltu a7, a4, a7
	add a7, a7, a0
	sd a4, 40(t2)
	ret
	.option pop
