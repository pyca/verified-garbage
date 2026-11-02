// The functions of `src/internal/vg_chacha20_block.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_chacha20_block:
	.option push
	.option arch, +m, +c
	addi t0, a1, 71
	andi t0, t0, -8
	sd s0, 0(t0)
	sd s1, 8(t0)
	sd s2, 16(t0)
	sd s3, 24(t0)
	sd s4, 32(t0)
	lwu t0, 0(a0)
	lwu t1, 4(a0)
	lwu t2, 8(a0)
	lwu t3, 12(a0)
	lwu t4, 16(a0)
	lwu t5, 20(a0)
	lwu t6, 24(a0)
	lwu a2, 28(a0)
	lwu a3, 32(a0)
	lwu a4, 36(a0)
	lwu a5, 40(a0)
	lwu a6, 44(a0)
	lwu a7, 48(a0)
	lwu s0, 52(a0)
	lwu s1, 56(a0)
	lwu s2, 60(a0)
	addi s4, zero, 10
20:
	add t0, t0, t4
	xor a7, a7, t0
	slliw s3, a7, 16
	srliw a7, a7, 16
	or a7, a7, s3
	add a3, a3, a7
	xor t4, t4, a3
	slliw s3, t4, 12
	srliw t4, t4, 20
	or t4, t4, s3
	add t0, t0, t4
	xor a7, a7, t0
	slliw s3, a7, 8
	srliw a7, a7, 24
	or a7, a7, s3
	add a3, a3, a7
	xor t4, t4, a3
	slliw s3, t4, 7
	srliw t4, t4, 25
	or t4, t4, s3
	add t1, t1, t5
	xor s0, s0, t1
	slliw s3, s0, 16
	srliw s0, s0, 16
	or s0, s0, s3
	add a4, a4, s0
	xor t5, t5, a4
	slliw s3, t5, 12
	srliw t5, t5, 20
	or t5, t5, s3
	add t1, t1, t5
	xor s0, s0, t1
	slliw s3, s0, 8
	srliw s0, s0, 24
	or s0, s0, s3
	add a4, a4, s0
	xor t5, t5, a4
	slliw s3, t5, 7
	srliw t5, t5, 25
	or t5, t5, s3
	add t2, t2, t6
	xor s1, s1, t2
	slliw s3, s1, 16
	srliw s1, s1, 16
	or s1, s1, s3
	add a5, a5, s1
	xor t6, t6, a5
	slliw s3, t6, 12
	srliw t6, t6, 20
	or t6, t6, s3
	add t2, t2, t6
	xor s1, s1, t2
	slliw s3, s1, 8
	srliw s1, s1, 24
	or s1, s1, s3
	add a5, a5, s1
	xor t6, t6, a5
	slliw s3, t6, 7
	srliw t6, t6, 25
	or t6, t6, s3
	add t3, t3, a2
	xor s2, s2, t3
	slliw s3, s2, 16
	srliw s2, s2, 16
	or s2, s2, s3
	add a6, a6, s2
	xor a2, a2, a6
	slliw s3, a2, 12
	srliw a2, a2, 20
	or a2, a2, s3
	add t3, t3, a2
	xor s2, s2, t3
	slliw s3, s2, 8
	srliw s2, s2, 24
	or s2, s2, s3
	add a6, a6, s2
	xor a2, a2, a6
	slliw s3, a2, 7
	srliw a2, a2, 25
	or a2, a2, s3
	add t0, t0, t5
	xor s2, s2, t0
	slliw s3, s2, 16
	srliw s2, s2, 16
	or s2, s2, s3
	add a5, a5, s2
	xor t5, t5, a5
	slliw s3, t5, 12
	srliw t5, t5, 20
	or t5, t5, s3
	add t0, t0, t5
	xor s2, s2, t0
	slliw s3, s2, 8
	srliw s2, s2, 24
	or s2, s2, s3
	add a5, a5, s2
	xor t5, t5, a5
	slliw s3, t5, 7
	srliw t5, t5, 25
	or t5, t5, s3
	add t1, t1, t6
	xor a7, a7, t1
	slliw s3, a7, 16
	srliw a7, a7, 16
	or a7, a7, s3
	add a6, a6, a7
	xor t6, t6, a6
	slliw s3, t6, 12
	srliw t6, t6, 20
	or t6, t6, s3
	add t1, t1, t6
	xor a7, a7, t1
	slliw s3, a7, 8
	srliw a7, a7, 24
	or a7, a7, s3
	add a6, a6, a7
	xor t6, t6, a6
	slliw s3, t6, 7
	srliw t6, t6, 25
	or t6, t6, s3
	add t2, t2, a2
	xor s0, s0, t2
	slliw s3, s0, 16
	srliw s0, s0, 16
	or s0, s0, s3
	add a3, a3, s0
	xor a2, a2, a3
	slliw s3, a2, 12
	srliw a2, a2, 20
	or a2, a2, s3
	add t2, t2, a2
	xor s0, s0, t2
	slliw s3, s0, 8
	srliw s0, s0, 24
	or s0, s0, s3
	add a3, a3, s0
	xor a2, a2, a3
	slliw s3, a2, 7
	srliw a2, a2, 25
	or a2, a2, s3
	add t3, t3, t4
	xor s1, s1, t3
	slliw s3, s1, 16
	srliw s1, s1, 16
	or s1, s1, s3
	add a4, a4, s1
	xor t4, t4, a4
	slliw s3, t4, 12
	srliw t4, t4, 20
	or t4, t4, s3
	add t3, t3, t4
	xor s1, s1, t3
	slliw s3, s1, 8
	srliw s1, s1, 24
	or s1, s1, s3
	add a4, a4, s1
	xor t4, t4, a4
	slliw s3, t4, 7
	srliw t4, t4, 25
	or t4, t4, s3
	addi s4, s4, -1
	bnez s4, 20b
	lwu s3, 0(a0)
	add t0, t0, s3
	sw t0, 0(a1)
	lwu s3, 4(a0)
	add t1, t1, s3
	sw t1, 4(a1)
	lwu s3, 8(a0)
	add t2, t2, s3
	sw t2, 8(a1)
	lwu s3, 12(a0)
	add t3, t3, s3
	sw t3, 12(a1)
	lwu s3, 16(a0)
	add t4, t4, s3
	sw t4, 16(a1)
	lwu s3, 20(a0)
	add t5, t5, s3
	sw t5, 20(a1)
	lwu s3, 24(a0)
	add t6, t6, s3
	sw t6, 24(a1)
	lwu s3, 28(a0)
	add a2, a2, s3
	sw a2, 28(a1)
	lwu s3, 32(a0)
	add a3, a3, s3
	sw a3, 32(a1)
	lwu s3, 36(a0)
	add a4, a4, s3
	sw a4, 36(a1)
	lwu s3, 40(a0)
	add a5, a5, s3
	sw a5, 40(a1)
	lwu s3, 44(a0)
	add a6, a6, s3
	sw a6, 44(a1)
	lwu s3, 48(a0)
	add a7, a7, s3
	sw a7, 48(a1)
	lwu s3, 52(a0)
	add s0, s0, s3
	sw s0, 52(a1)
	lwu s3, 56(a0)
	add s1, s1, s3
	sw s1, 56(a1)
	lwu s3, 60(a0)
	add s2, s2, s3
	sw s2, 60(a1)
	addi t0, a1, 71
	andi t0, t0, -8
	ld s0, 0(t0)
	ld s1, 8(t0)
	ld s2, 16(t0)
	ld s3, 24(t0)
	ld s4, 32(t0)
	ret
	.option pop
