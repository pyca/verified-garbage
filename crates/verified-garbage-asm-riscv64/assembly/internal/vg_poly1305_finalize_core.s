// The functions of `src/internal/vg_poly1305_finalize_core.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_poly1305_finalize_core:
	.option push
	.option arch, +m, +c
	andi t6, a1, 15
	ld a5, 24(a0)
	ld a6, 32(a0)
	lui a4, 65536
	addiw a4, a4, -4
	slli a4, a4, 32
	lui a1, 65536
	addiw a1, a1, -1
	slli a1, a1, 32
	srli a1, a1, 32
	or a4, a4, a1
	and a5, a5, a4
	andi a4, a4, -4
	and a6, a6, a4
	srli a7, a6, 2
	add a7, a7, a6
	ld t0, 0(a0)
	ld t1, 8(a0)
	ld t2, 16(a0)
	beqz t6, 20f
	addi t5, zero, 0
	addi t4, a0, 56
	add t4, t4, t6
	addi t3, zero, 16
	sub t3, t3, t6
22:
	sb t5, 0(t4)
	addi t4, t4, 1
	addi t3, t3, -1
	bnez t3, 22b
	addi t5, zero, 1
	addi t4, a0, 56
	add t4, t4, t6
	sb t5, 0(t4)
	lbu t3, 56(a0)
	lbu a4, 57(a0)
	slli a4, a4, 8
	or t3, t3, a4
	lbu a4, 58(a0)
	slli a4, a4, 16
	or t3, t3, a4
	lbu a4, 59(a0)
	slli a4, a4, 24
	or t3, t3, a4
	lbu a1, 60(a0)
	lbu a4, 61(a0)
	slli a4, a4, 8
	or a1, a1, a4
	lbu a4, 62(a0)
	slli a4, a4, 16
	or a1, a1, a4
	lbu a4, 63(a0)
	slli a4, a4, 24
	or a1, a1, a4
	slli a1, a1, 32
	or t3, t3, a1
	lbu t4, 64(a0)
	lbu a4, 65(a0)
	slli a4, a4, 8
	or t4, t4, a4
	lbu a4, 66(a0)
	slli a4, a4, 16
	or t4, t4, a4
	lbu a4, 67(a0)
	slli a4, a4, 24
	or t4, t4, a4
	lbu a1, 68(a0)
	lbu a4, 69(a0)
	slli a4, a4, 8
	or a1, a1, a4
	lbu a4, 70(a0)
	slli a4, a4, 16
	or a1, a1, a4
	lbu a4, 71(a0)
	slli a4, a4, 24
	or a1, a1, a4
	slli a1, a1, 32
	or t4, t4, a1
	add t0, t0, t3
	sltu t3, t0, t3
	add t1, t1, t4
	sltu t4, t1, t4
	add t1, t1, t3
	sltu t3, t1, t3
	add t2, t2, t4
	add t2, t2, t3
	mul t3, t0, a5
	mulhu t4, t0, a5
	mul t5, t0, a6
	mulhu t6, t0, a6
	mul a4, t1, a7
	mulhu a1, t1, a7
	add t3, t3, a4
	sltu a4, t3, a4
	add t4, t4, a1
	add t4, t4, a4
	mul a4, t1, a5
	mulhu a1, t1, a5
	add t5, t5, a4
	sltu a4, t5, a4
	add t6, t6, a1
	add t6, t6, a4
	mul a4, t2, a7
	add t5, t5, a4
	sltu a4, t5, a4
	add t6, t6, a4
	mul a1, t2, a5
	add t5, t5, t4
	sltu t4, t5, t4
	add t6, t6, a1
	add t6, t6, t4
	andi t2, t6, 3
	andi a4, t6, -4
	srli a1, t6, 2
	add a4, a4, a1
	add t0, t3, a4
	sltu a4, t0, a4
	add t1, t5, a4
	sltu a4, t1, a4
	add t2, t2, a4
	j 21f
20:
21:
	addi a4, zero, 5
	add t3, t0, a4
	sltu a4, t3, a4
	add t4, t1, a4
	sltu a4, t4, a4
	add t5, t2, a4
	srli a4, t5, 2
	addi a4, a4, -1
	andi t5, t5, 3
	xor a1, t0, t3
	and a1, a1, a4
	xor t0, t3, a1
	xor a1, t1, t4
	and a1, a1, a4
	xor t1, t4, a1
	xor a1, t2, t5
	and a1, a1, a4
	xor t2, t5, a1
	ld t3, 40(a0)
	ld t4, 48(a0)
	add t0, t0, t3
	sltu t3, t0, t3
	add t1, t1, t4
	add t1, t1, t3
	sb t0, 0(a2)
	srli a4, t0, 8
	sb a4, 1(a2)
	srli a4, t0, 16
	sb a4, 2(a2)
	srli a4, t0, 24
	sb a4, 3(a2)
	srli a4, t0, 32
	sb a4, 4(a2)
	srli a1, a4, 8
	sb a1, 5(a2)
	srli a1, a4, 16
	sb a1, 6(a2)
	srli a1, a4, 24
	sb a1, 7(a2)
	sb t1, 8(a2)
	srli a4, t1, 8
	sb a4, 9(a2)
	srli a4, t1, 16
	sb a4, 10(a2)
	srli a4, t1, 24
	sb a4, 11(a2)
	srli a4, t1, 32
	sb a4, 12(a2)
	srli a1, a4, 8
	sb a1, 13(a2)
	srli a1, a4, 16
	sb a1, 14(a2)
	srli a1, a4, 24
	sb a1, 15(a2)
	ret
	.option pop
