// The functions of `src/internal/vg_ed25519_scalar_reduce.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed25519_scalar_reduce:
	.option push
	.option arch, +m, +c
	addi a3, a2, 0
	addi a3, a3, 7
	andi a3, a3, -8
	addi t3, a1, 0
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	addi a7, zero, 0
	addi t4, zero, 64
	lui t5, 360742
	addiw t5, t5, 794
	slli t5, t5, 32
	lui t0, 380765
	addiw t0, t0, 1005
	slli t0, t0, 32
	srli t0, t0, 32
	or t5, t5, t0
	lui t6, 85488
	addiw t6, t6, -1570
	slli t6, t6, 32
	lui t0, 667514
	addiw t0, t0, -810
	slli t0, t0, 32
	srli t0, t0, 32
	or t6, t6, t0
20:
	addi t4, t4, -8
	add a1, t3, t4
	lbu a2, 0(a1)
	lbu t0, 1(a1)
	slli t0, t0, 8
	or a2, a2, t0
	lbu t0, 2(a1)
	slli t0, t0, 16
	or a2, a2, t0
	lbu t0, 3(a1)
	slli t0, t0, 24
	or a2, a2, t0
	lbu t1, 4(a1)
	lbu t0, 5(a1)
	slli t0, t0, 8
	or t1, t1, t0
	lbu t0, 6(a1)
	slli t0, t0, 16
	or t1, t1, t0
	lbu t0, 7(a1)
	slli t0, t0, 24
	or t1, t1, t0
	slli t1, t1, 32
	or a2, a2, t1
	srli t0, a6, 60
	slli t1, a7, 4
	or t0, t0, t1
	srli t1, a7, 60
	slli a7, a6, 4
	srli a7, a7, 4
	addi a6, a5, 0
	addi a5, a4, 0
	addi a4, a2, 0
	mul t2, t0, t5
	mulhu a1, t0, t5
	mul a2, t0, t6
	mulhu t0, t0, t6
	add a1, a1, a2
	sltu a2, a1, a2
	add t0, t0, a2
	mul a2, t1, t5
	add a1, a1, a2
	sltu a2, a1, a2
	add t0, t0, a2
	mul a2, t1, t6
	add t0, t0, a2
	sltu a2, a4, t2
	sub a4, a4, t2
	sltu t1, a5, a1
	sub a5, a5, a1
	sltu t2, a5, a2
	sub a5, a5, a2
	or a2, t1, t2
	sltu t1, a6, t0
	sub a6, a6, t0
	sltu t2, a6, a2
	sub a6, a6, a2
	or a2, t1, t2
	sltu t1, a7, a2
	sub a7, a7, a2
	addi t2, zero, 0
	sub t2, t2, t1
	and a1, t5, t2
	add a4, a4, a1
	sltu a1, a4, a1
	and a2, t6, t2
	add a5, a5, a1
	sltu a1, a5, a1
	add a5, a5, a2
	sltu a2, a5, a2
	or a1, a1, a2
	add a6, a6, a1
	sltu a1, a6, a1
	add a7, a7, a1
	slli t1, t1, 60
	add a7, a7, t1
	bnez t4, 20b
	sd a4, 160(a3)
	sd a5, 168(a3)
	sd a6, 176(a3)
	sd a7, 184(a3)
	lwu a4, 160(a3)
	sb a4, 0(a0)
	srli a5, a4, 8
	sb a5, 1(a0)
	srli a5, a4, 16
	sb a5, 2(a0)
	srli a5, a4, 24
	sb a5, 3(a0)
	lwu a4, 164(a3)
	sb a4, 4(a0)
	srli a5, a4, 8
	sb a5, 5(a0)
	srli a5, a4, 16
	sb a5, 6(a0)
	srli a5, a4, 24
	sb a5, 7(a0)
	lwu a4, 168(a3)
	sb a4, 8(a0)
	srli a5, a4, 8
	sb a5, 9(a0)
	srli a5, a4, 16
	sb a5, 10(a0)
	srli a5, a4, 24
	sb a5, 11(a0)
	lwu a4, 172(a3)
	sb a4, 12(a0)
	srli a5, a4, 8
	sb a5, 13(a0)
	srli a5, a4, 16
	sb a5, 14(a0)
	srli a5, a4, 24
	sb a5, 15(a0)
	lwu a4, 176(a3)
	sb a4, 16(a0)
	srli a5, a4, 8
	sb a5, 17(a0)
	srli a5, a4, 16
	sb a5, 18(a0)
	srli a5, a4, 24
	sb a5, 19(a0)
	lwu a4, 180(a3)
	sb a4, 20(a0)
	srli a5, a4, 8
	sb a5, 21(a0)
	srli a5, a4, 16
	sb a5, 22(a0)
	srli a5, a4, 24
	sb a5, 23(a0)
	lwu a4, 184(a3)
	sb a4, 24(a0)
	srli a5, a4, 8
	sb a5, 25(a0)
	srli a5, a4, 16
	sb a5, 26(a0)
	srli a5, a4, 24
	sb a5, 27(a0)
	lwu a4, 188(a3)
	sb a4, 28(a0)
	srli a5, a4, 8
	sb a5, 29(a0)
	srli a5, a4, 16
	sb a5, 30(a0)
	srli a5, a4, 24
	sb a5, 31(a0)
	ret
	.option pop
