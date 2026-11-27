// The functions of `src/internal/vg_scrypt_blockmix.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_scrypt_blockmix:
	.option push
	.option arch, +m, +c
	sd s0, 0(a3)
	sd s1, 8(a3)
	sd s2, 16(a3)
	sd s3, 24(a3)
	sd s4, 32(a3)
	sd s5, 40(a3)
	sd s6, 48(a3)
	sd s7, 56(a3)
	sd s8, 64(a3)
	sd s10, 72(a3)
	addi s8, a1, 0
	addi s5, a0, 0
	addi s6, a2, 0
	addi s10, a3, 0
	slli t1, a1, 6
	add s7, a2, t1
	slli t1, a1, 7
	add t0, a0, t1
	addi t0, t0, -64
	lwu a2, 0(t0)
	lwu a3, 4(t0)
	lwu a4, 8(t0)
	lwu a5, 12(t0)
	lwu a6, 16(t0)
	lwu a7, 20(t0)
	lwu t2, 24(t0)
	lwu t3, 28(t0)
	lwu t4, 32(t0)
	lwu t5, 36(t0)
	lwu t6, 40(t0)
	lwu s0, 44(t0)
	lwu s1, 48(t0)
	lwu s2, 52(t0)
	lwu s3, 56(t0)
	lwu s4, 60(t0)
20:
	lwu t0, 0(s5)
	xor a2, a2, t0
	sw a2, 0(s6)
	lwu t0, 4(s5)
	xor a3, a3, t0
	sw a3, 4(s6)
	lwu t0, 8(s5)
	xor a4, a4, t0
	sw a4, 8(s6)
	lwu t0, 12(s5)
	xor a5, a5, t0
	sw a5, 12(s6)
	lwu t0, 16(s5)
	xor a6, a6, t0
	sw a6, 16(s6)
	lwu t0, 20(s5)
	xor a7, a7, t0
	sw a7, 20(s6)
	lwu t0, 24(s5)
	xor t2, t2, t0
	sw t2, 24(s6)
	lwu t0, 28(s5)
	xor t3, t3, t0
	sw t3, 28(s6)
	lwu t0, 32(s5)
	xor t4, t4, t0
	sw t4, 32(s6)
	lwu t0, 36(s5)
	xor t5, t5, t0
	sw t5, 36(s6)
	lwu t0, 40(s5)
	xor t6, t6, t0
	sw t6, 40(s6)
	lwu t0, 44(s5)
	xor s0, s0, t0
	sw s0, 44(s6)
	lwu t0, 48(s5)
	xor s1, s1, t0
	sw s1, 48(s6)
	lwu t0, 52(s5)
	xor s2, s2, t0
	sw s2, 52(s6)
	lwu t0, 56(s5)
	xor s3, s3, t0
	sw s3, 56(s6)
	lwu t0, 60(s5)
	xor s4, s4, t0
	sw s4, 60(s6)
	addw t0, a2, s1
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor a6, a6, t1
	xor a6, a6, t0
	addw t0, a7, a3
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor t5, t5, t1
	xor t5, t5, t0
	addw t0, t6, t2
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor s3, s3, t1
	xor s3, s3, t0
	addw t0, s4, s0
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor a5, a5, t1
	xor a5, a5, t0
	addw t0, a6, a2
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t4, t4, t1
	xor t4, t4, t0
	addw t0, t5, a7
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor s2, s2, t1
	xor s2, s2, t0
	addw t0, s3, t6
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor a4, a4, t1
	xor a4, a4, t0
	addw t0, a5, s4
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t3, t3, t1
	xor t3, t3, t0
	addw t0, t4, a6
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor s1, s1, t1
	xor s1, s1, t0
	addw t0, s2, t5
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor a3, a3, t1
	xor a3, a3, t0
	addw t0, a4, s3
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor t2, t2, t1
	xor t2, t2, t0
	addw t0, t3, a5
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor s0, s0, t1
	xor s0, s0, t0
	addw t0, s1, t4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a2, a2, t1
	xor a2, a2, t0
	addw t0, a3, s2
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a7, a7, t1
	xor a7, a7, t0
	addw t0, t2, a4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor t6, t6, t1
	xor t6, t6, t0
	addw t0, s0, t3
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor s4, s4, t1
	xor s4, s4, t0
	addw t0, a2, a5
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor a3, a3, t1
	xor a3, a3, t0
	addw t0, a7, a6
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor t2, t2, t1
	xor t2, t2, t0
	addw t0, t6, t5
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor s0, s0, t1
	xor s0, s0, t0
	addw t0, s4, s3
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor s1, s1, t1
	xor s1, s1, t0
	addw t0, a3, a2
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor a4, a4, t1
	xor a4, a4, t0
	addw t0, t2, a7
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t3, t3, t1
	xor t3, t3, t0
	addw t0, s0, t6
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t4, t4, t1
	xor t4, t4, t0
	addw t0, s1, s4
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor s2, s2, t1
	xor s2, s2, t0
	addw t0, a4, a3
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor a5, a5, t1
	xor a5, a5, t0
	addw t0, t3, t2
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor a6, a6, t1
	xor a6, a6, t0
	addw t0, t4, s0
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor t5, t5, t1
	xor t5, t5, t0
	addw t0, s2, s1
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor s3, s3, t1
	xor s3, s3, t0
	addw t0, a5, a4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a2, a2, t1
	xor a2, a2, t0
	addw t0, a6, t3
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a7, a7, t1
	xor a7, a7, t0
	addw t0, t5, t4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor t6, t6, t1
	xor t6, t6, t0
	addw t0, s3, s2
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor s4, s4, t1
	xor s4, s4, t0
	addw t0, a2, s1
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor a6, a6, t1
	xor a6, a6, t0
	addw t0, a7, a3
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor t5, t5, t1
	xor t5, t5, t0
	addw t0, t6, t2
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor s3, s3, t1
	xor s3, s3, t0
	addw t0, s4, s0
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor a5, a5, t1
	xor a5, a5, t0
	addw t0, a6, a2
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t4, t4, t1
	xor t4, t4, t0
	addw t0, t5, a7
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor s2, s2, t1
	xor s2, s2, t0
	addw t0, s3, t6
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor a4, a4, t1
	xor a4, a4, t0
	addw t0, a5, s4
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t3, t3, t1
	xor t3, t3, t0
	addw t0, t4, a6
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor s1, s1, t1
	xor s1, s1, t0
	addw t0, s2, t5
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor a3, a3, t1
	xor a3, a3, t0
	addw t0, a4, s3
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor t2, t2, t1
	xor t2, t2, t0
	addw t0, t3, a5
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor s0, s0, t1
	xor s0, s0, t0
	addw t0, s1, t4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a2, a2, t1
	xor a2, a2, t0
	addw t0, a3, s2
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a7, a7, t1
	xor a7, a7, t0
	addw t0, t2, a4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor t6, t6, t1
	xor t6, t6, t0
	addw t0, s0, t3
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor s4, s4, t1
	xor s4, s4, t0
	addw t0, a2, a5
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor a3, a3, t1
	xor a3, a3, t0
	addw t0, a7, a6
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor t2, t2, t1
	xor t2, t2, t0
	addw t0, t6, t5
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor s0, s0, t1
	xor s0, s0, t0
	addw t0, s4, s3
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor s1, s1, t1
	xor s1, s1, t0
	addw t0, a3, a2
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor a4, a4, t1
	xor a4, a4, t0
	addw t0, t2, a7
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t3, t3, t1
	xor t3, t3, t0
	addw t0, s0, t6
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t4, t4, t1
	xor t4, t4, t0
	addw t0, s1, s4
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor s2, s2, t1
	xor s2, s2, t0
	addw t0, a4, a3
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor a5, a5, t1
	xor a5, a5, t0
	addw t0, t3, t2
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor a6, a6, t1
	xor a6, a6, t0
	addw t0, t4, s0
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor t5, t5, t1
	xor t5, t5, t0
	addw t0, s2, s1
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor s3, s3, t1
	xor s3, s3, t0
	addw t0, a5, a4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a2, a2, t1
	xor a2, a2, t0
	addw t0, a6, t3
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a7, a7, t1
	xor a7, a7, t0
	addw t0, t5, t4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor t6, t6, t1
	xor t6, t6, t0
	addw t0, s3, s2
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor s4, s4, t1
	xor s4, s4, t0
	addw t0, a2, s1
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor a6, a6, t1
	xor a6, a6, t0
	addw t0, a7, a3
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor t5, t5, t1
	xor t5, t5, t0
	addw t0, t6, t2
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor s3, s3, t1
	xor s3, s3, t0
	addw t0, s4, s0
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor a5, a5, t1
	xor a5, a5, t0
	addw t0, a6, a2
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t4, t4, t1
	xor t4, t4, t0
	addw t0, t5, a7
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor s2, s2, t1
	xor s2, s2, t0
	addw t0, s3, t6
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor a4, a4, t1
	xor a4, a4, t0
	addw t0, a5, s4
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t3, t3, t1
	xor t3, t3, t0
	addw t0, t4, a6
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor s1, s1, t1
	xor s1, s1, t0
	addw t0, s2, t5
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor a3, a3, t1
	xor a3, a3, t0
	addw t0, a4, s3
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor t2, t2, t1
	xor t2, t2, t0
	addw t0, t3, a5
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor s0, s0, t1
	xor s0, s0, t0
	addw t0, s1, t4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a2, a2, t1
	xor a2, a2, t0
	addw t0, a3, s2
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a7, a7, t1
	xor a7, a7, t0
	addw t0, t2, a4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor t6, t6, t1
	xor t6, t6, t0
	addw t0, s0, t3
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor s4, s4, t1
	xor s4, s4, t0
	addw t0, a2, a5
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor a3, a3, t1
	xor a3, a3, t0
	addw t0, a7, a6
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor t2, t2, t1
	xor t2, t2, t0
	addw t0, t6, t5
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor s0, s0, t1
	xor s0, s0, t0
	addw t0, s4, s3
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor s1, s1, t1
	xor s1, s1, t0
	addw t0, a3, a2
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor a4, a4, t1
	xor a4, a4, t0
	addw t0, t2, a7
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t3, t3, t1
	xor t3, t3, t0
	addw t0, s0, t6
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t4, t4, t1
	xor t4, t4, t0
	addw t0, s1, s4
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor s2, s2, t1
	xor s2, s2, t0
	addw t0, a4, a3
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor a5, a5, t1
	xor a5, a5, t0
	addw t0, t3, t2
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor a6, a6, t1
	xor a6, a6, t0
	addw t0, t4, s0
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor t5, t5, t1
	xor t5, t5, t0
	addw t0, s2, s1
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor s3, s3, t1
	xor s3, s3, t0
	addw t0, a5, a4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a2, a2, t1
	xor a2, a2, t0
	addw t0, a6, t3
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a7, a7, t1
	xor a7, a7, t0
	addw t0, t5, t4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor t6, t6, t1
	xor t6, t6, t0
	addw t0, s3, s2
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor s4, s4, t1
	xor s4, s4, t0
	addw t0, a2, s1
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor a6, a6, t1
	xor a6, a6, t0
	addw t0, a7, a3
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor t5, t5, t1
	xor t5, t5, t0
	addw t0, t6, t2
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor s3, s3, t1
	xor s3, s3, t0
	addw t0, s4, s0
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor a5, a5, t1
	xor a5, a5, t0
	addw t0, a6, a2
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t4, t4, t1
	xor t4, t4, t0
	addw t0, t5, a7
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor s2, s2, t1
	xor s2, s2, t0
	addw t0, s3, t6
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor a4, a4, t1
	xor a4, a4, t0
	addw t0, a5, s4
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t3, t3, t1
	xor t3, t3, t0
	addw t0, t4, a6
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor s1, s1, t1
	xor s1, s1, t0
	addw t0, s2, t5
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor a3, a3, t1
	xor a3, a3, t0
	addw t0, a4, s3
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor t2, t2, t1
	xor t2, t2, t0
	addw t0, t3, a5
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor s0, s0, t1
	xor s0, s0, t0
	addw t0, s1, t4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a2, a2, t1
	xor a2, a2, t0
	addw t0, a3, s2
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a7, a7, t1
	xor a7, a7, t0
	addw t0, t2, a4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor t6, t6, t1
	xor t6, t6, t0
	addw t0, s0, t3
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor s4, s4, t1
	xor s4, s4, t0
	addw t0, a2, a5
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor a3, a3, t1
	xor a3, a3, t0
	addw t0, a7, a6
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor t2, t2, t1
	xor t2, t2, t0
	addw t0, t6, t5
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor s0, s0, t1
	xor s0, s0, t0
	addw t0, s4, s3
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor s1, s1, t1
	xor s1, s1, t0
	addw t0, a3, a2
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor a4, a4, t1
	xor a4, a4, t0
	addw t0, t2, a7
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t3, t3, t1
	xor t3, t3, t0
	addw t0, s0, t6
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t4, t4, t1
	xor t4, t4, t0
	addw t0, s1, s4
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor s2, s2, t1
	xor s2, s2, t0
	addw t0, a4, a3
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor a5, a5, t1
	xor a5, a5, t0
	addw t0, t3, t2
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor a6, a6, t1
	xor a6, a6, t0
	addw t0, t4, s0
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor t5, t5, t1
	xor t5, t5, t0
	addw t0, s2, s1
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor s3, s3, t1
	xor s3, s3, t0
	addw t0, a5, a4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a2, a2, t1
	xor a2, a2, t0
	addw t0, a6, t3
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a7, a7, t1
	xor a7, a7, t0
	addw t0, t5, t4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor t6, t6, t1
	xor t6, t6, t0
	addw t0, s3, s2
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor s4, s4, t1
	xor s4, s4, t0
	lwu t0, 0(s6)
	addw a2, a2, t0
	sw a2, 0(s6)
	lwu t0, 4(s6)
	addw a3, a3, t0
	sw a3, 4(s6)
	lwu t0, 8(s6)
	addw a4, a4, t0
	sw a4, 8(s6)
	lwu t0, 12(s6)
	addw a5, a5, t0
	sw a5, 12(s6)
	lwu t0, 16(s6)
	addw a6, a6, t0
	sw a6, 16(s6)
	lwu t0, 20(s6)
	addw a7, a7, t0
	sw a7, 20(s6)
	lwu t0, 24(s6)
	addw t2, t2, t0
	sw t2, 24(s6)
	lwu t0, 28(s6)
	addw t3, t3, t0
	sw t3, 28(s6)
	lwu t0, 32(s6)
	addw t4, t4, t0
	sw t4, 32(s6)
	lwu t0, 36(s6)
	addw t5, t5, t0
	sw t5, 36(s6)
	lwu t0, 40(s6)
	addw t6, t6, t0
	sw t6, 40(s6)
	lwu t0, 44(s6)
	addw s0, s0, t0
	sw s0, 44(s6)
	lwu t0, 48(s6)
	addw s1, s1, t0
	sw s1, 48(s6)
	lwu t0, 52(s6)
	addw s2, s2, t0
	sw s2, 52(s6)
	lwu t0, 56(s6)
	addw s3, s3, t0
	sw s3, 56(s6)
	lwu t0, 60(s6)
	addw s4, s4, t0
	sw s4, 60(s6)
	addi s5, s5, 64
	lwu t0, 0(s5)
	xor a2, a2, t0
	sw a2, 0(s7)
	lwu t0, 4(s5)
	xor a3, a3, t0
	sw a3, 4(s7)
	lwu t0, 8(s5)
	xor a4, a4, t0
	sw a4, 8(s7)
	lwu t0, 12(s5)
	xor a5, a5, t0
	sw a5, 12(s7)
	lwu t0, 16(s5)
	xor a6, a6, t0
	sw a6, 16(s7)
	lwu t0, 20(s5)
	xor a7, a7, t0
	sw a7, 20(s7)
	lwu t0, 24(s5)
	xor t2, t2, t0
	sw t2, 24(s7)
	lwu t0, 28(s5)
	xor t3, t3, t0
	sw t3, 28(s7)
	lwu t0, 32(s5)
	xor t4, t4, t0
	sw t4, 32(s7)
	lwu t0, 36(s5)
	xor t5, t5, t0
	sw t5, 36(s7)
	lwu t0, 40(s5)
	xor t6, t6, t0
	sw t6, 40(s7)
	lwu t0, 44(s5)
	xor s0, s0, t0
	sw s0, 44(s7)
	lwu t0, 48(s5)
	xor s1, s1, t0
	sw s1, 48(s7)
	lwu t0, 52(s5)
	xor s2, s2, t0
	sw s2, 52(s7)
	lwu t0, 56(s5)
	xor s3, s3, t0
	sw s3, 56(s7)
	lwu t0, 60(s5)
	xor s4, s4, t0
	sw s4, 60(s7)
	addw t0, a2, s1
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor a6, a6, t1
	xor a6, a6, t0
	addw t0, a7, a3
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor t5, t5, t1
	xor t5, t5, t0
	addw t0, t6, t2
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor s3, s3, t1
	xor s3, s3, t0
	addw t0, s4, s0
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor a5, a5, t1
	xor a5, a5, t0
	addw t0, a6, a2
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t4, t4, t1
	xor t4, t4, t0
	addw t0, t5, a7
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor s2, s2, t1
	xor s2, s2, t0
	addw t0, s3, t6
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor a4, a4, t1
	xor a4, a4, t0
	addw t0, a5, s4
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t3, t3, t1
	xor t3, t3, t0
	addw t0, t4, a6
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor s1, s1, t1
	xor s1, s1, t0
	addw t0, s2, t5
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor a3, a3, t1
	xor a3, a3, t0
	addw t0, a4, s3
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor t2, t2, t1
	xor t2, t2, t0
	addw t0, t3, a5
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor s0, s0, t1
	xor s0, s0, t0
	addw t0, s1, t4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a2, a2, t1
	xor a2, a2, t0
	addw t0, a3, s2
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a7, a7, t1
	xor a7, a7, t0
	addw t0, t2, a4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor t6, t6, t1
	xor t6, t6, t0
	addw t0, s0, t3
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor s4, s4, t1
	xor s4, s4, t0
	addw t0, a2, a5
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor a3, a3, t1
	xor a3, a3, t0
	addw t0, a7, a6
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor t2, t2, t1
	xor t2, t2, t0
	addw t0, t6, t5
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor s0, s0, t1
	xor s0, s0, t0
	addw t0, s4, s3
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor s1, s1, t1
	xor s1, s1, t0
	addw t0, a3, a2
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor a4, a4, t1
	xor a4, a4, t0
	addw t0, t2, a7
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t3, t3, t1
	xor t3, t3, t0
	addw t0, s0, t6
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t4, t4, t1
	xor t4, t4, t0
	addw t0, s1, s4
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor s2, s2, t1
	xor s2, s2, t0
	addw t0, a4, a3
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor a5, a5, t1
	xor a5, a5, t0
	addw t0, t3, t2
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor a6, a6, t1
	xor a6, a6, t0
	addw t0, t4, s0
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor t5, t5, t1
	xor t5, t5, t0
	addw t0, s2, s1
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor s3, s3, t1
	xor s3, s3, t0
	addw t0, a5, a4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a2, a2, t1
	xor a2, a2, t0
	addw t0, a6, t3
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a7, a7, t1
	xor a7, a7, t0
	addw t0, t5, t4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor t6, t6, t1
	xor t6, t6, t0
	addw t0, s3, s2
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor s4, s4, t1
	xor s4, s4, t0
	addw t0, a2, s1
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor a6, a6, t1
	xor a6, a6, t0
	addw t0, a7, a3
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor t5, t5, t1
	xor t5, t5, t0
	addw t0, t6, t2
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor s3, s3, t1
	xor s3, s3, t0
	addw t0, s4, s0
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor a5, a5, t1
	xor a5, a5, t0
	addw t0, a6, a2
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t4, t4, t1
	xor t4, t4, t0
	addw t0, t5, a7
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor s2, s2, t1
	xor s2, s2, t0
	addw t0, s3, t6
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor a4, a4, t1
	xor a4, a4, t0
	addw t0, a5, s4
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t3, t3, t1
	xor t3, t3, t0
	addw t0, t4, a6
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor s1, s1, t1
	xor s1, s1, t0
	addw t0, s2, t5
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor a3, a3, t1
	xor a3, a3, t0
	addw t0, a4, s3
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor t2, t2, t1
	xor t2, t2, t0
	addw t0, t3, a5
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor s0, s0, t1
	xor s0, s0, t0
	addw t0, s1, t4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a2, a2, t1
	xor a2, a2, t0
	addw t0, a3, s2
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a7, a7, t1
	xor a7, a7, t0
	addw t0, t2, a4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor t6, t6, t1
	xor t6, t6, t0
	addw t0, s0, t3
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor s4, s4, t1
	xor s4, s4, t0
	addw t0, a2, a5
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor a3, a3, t1
	xor a3, a3, t0
	addw t0, a7, a6
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor t2, t2, t1
	xor t2, t2, t0
	addw t0, t6, t5
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor s0, s0, t1
	xor s0, s0, t0
	addw t0, s4, s3
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor s1, s1, t1
	xor s1, s1, t0
	addw t0, a3, a2
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor a4, a4, t1
	xor a4, a4, t0
	addw t0, t2, a7
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t3, t3, t1
	xor t3, t3, t0
	addw t0, s0, t6
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t4, t4, t1
	xor t4, t4, t0
	addw t0, s1, s4
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor s2, s2, t1
	xor s2, s2, t0
	addw t0, a4, a3
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor a5, a5, t1
	xor a5, a5, t0
	addw t0, t3, t2
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor a6, a6, t1
	xor a6, a6, t0
	addw t0, t4, s0
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor t5, t5, t1
	xor t5, t5, t0
	addw t0, s2, s1
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor s3, s3, t1
	xor s3, s3, t0
	addw t0, a5, a4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a2, a2, t1
	xor a2, a2, t0
	addw t0, a6, t3
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a7, a7, t1
	xor a7, a7, t0
	addw t0, t5, t4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor t6, t6, t1
	xor t6, t6, t0
	addw t0, s3, s2
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor s4, s4, t1
	xor s4, s4, t0
	addw t0, a2, s1
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor a6, a6, t1
	xor a6, a6, t0
	addw t0, a7, a3
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor t5, t5, t1
	xor t5, t5, t0
	addw t0, t6, t2
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor s3, s3, t1
	xor s3, s3, t0
	addw t0, s4, s0
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor a5, a5, t1
	xor a5, a5, t0
	addw t0, a6, a2
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t4, t4, t1
	xor t4, t4, t0
	addw t0, t5, a7
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor s2, s2, t1
	xor s2, s2, t0
	addw t0, s3, t6
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor a4, a4, t1
	xor a4, a4, t0
	addw t0, a5, s4
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t3, t3, t1
	xor t3, t3, t0
	addw t0, t4, a6
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor s1, s1, t1
	xor s1, s1, t0
	addw t0, s2, t5
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor a3, a3, t1
	xor a3, a3, t0
	addw t0, a4, s3
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor t2, t2, t1
	xor t2, t2, t0
	addw t0, t3, a5
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor s0, s0, t1
	xor s0, s0, t0
	addw t0, s1, t4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a2, a2, t1
	xor a2, a2, t0
	addw t0, a3, s2
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a7, a7, t1
	xor a7, a7, t0
	addw t0, t2, a4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor t6, t6, t1
	xor t6, t6, t0
	addw t0, s0, t3
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor s4, s4, t1
	xor s4, s4, t0
	addw t0, a2, a5
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor a3, a3, t1
	xor a3, a3, t0
	addw t0, a7, a6
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor t2, t2, t1
	xor t2, t2, t0
	addw t0, t6, t5
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor s0, s0, t1
	xor s0, s0, t0
	addw t0, s4, s3
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor s1, s1, t1
	xor s1, s1, t0
	addw t0, a3, a2
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor a4, a4, t1
	xor a4, a4, t0
	addw t0, t2, a7
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t3, t3, t1
	xor t3, t3, t0
	addw t0, s0, t6
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t4, t4, t1
	xor t4, t4, t0
	addw t0, s1, s4
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor s2, s2, t1
	xor s2, s2, t0
	addw t0, a4, a3
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor a5, a5, t1
	xor a5, a5, t0
	addw t0, t3, t2
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor a6, a6, t1
	xor a6, a6, t0
	addw t0, t4, s0
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor t5, t5, t1
	xor t5, t5, t0
	addw t0, s2, s1
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor s3, s3, t1
	xor s3, s3, t0
	addw t0, a5, a4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a2, a2, t1
	xor a2, a2, t0
	addw t0, a6, t3
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a7, a7, t1
	xor a7, a7, t0
	addw t0, t5, t4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor t6, t6, t1
	xor t6, t6, t0
	addw t0, s3, s2
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor s4, s4, t1
	xor s4, s4, t0
	addw t0, a2, s1
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor a6, a6, t1
	xor a6, a6, t0
	addw t0, a7, a3
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor t5, t5, t1
	xor t5, t5, t0
	addw t0, t6, t2
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor s3, s3, t1
	xor s3, s3, t0
	addw t0, s4, s0
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor a5, a5, t1
	xor a5, a5, t0
	addw t0, a6, a2
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t4, t4, t1
	xor t4, t4, t0
	addw t0, t5, a7
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor s2, s2, t1
	xor s2, s2, t0
	addw t0, s3, t6
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor a4, a4, t1
	xor a4, a4, t0
	addw t0, a5, s4
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t3, t3, t1
	xor t3, t3, t0
	addw t0, t4, a6
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor s1, s1, t1
	xor s1, s1, t0
	addw t0, s2, t5
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor a3, a3, t1
	xor a3, a3, t0
	addw t0, a4, s3
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor t2, t2, t1
	xor t2, t2, t0
	addw t0, t3, a5
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor s0, s0, t1
	xor s0, s0, t0
	addw t0, s1, t4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a2, a2, t1
	xor a2, a2, t0
	addw t0, a3, s2
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a7, a7, t1
	xor a7, a7, t0
	addw t0, t2, a4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor t6, t6, t1
	xor t6, t6, t0
	addw t0, s0, t3
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor s4, s4, t1
	xor s4, s4, t0
	addw t0, a2, a5
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor a3, a3, t1
	xor a3, a3, t0
	addw t0, a7, a6
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor t2, t2, t1
	xor t2, t2, t0
	addw t0, t6, t5
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor s0, s0, t1
	xor s0, s0, t0
	addw t0, s4, s3
	slliw t1, t0, 7
	srliw t0, t0, 25
	xor s1, s1, t1
	xor s1, s1, t0
	addw t0, a3, a2
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor a4, a4, t1
	xor a4, a4, t0
	addw t0, t2, a7
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t3, t3, t1
	xor t3, t3, t0
	addw t0, s0, t6
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor t4, t4, t1
	xor t4, t4, t0
	addw t0, s1, s4
	slliw t1, t0, 9
	srliw t0, t0, 23
	xor s2, s2, t1
	xor s2, s2, t0
	addw t0, a4, a3
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor a5, a5, t1
	xor a5, a5, t0
	addw t0, t3, t2
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor a6, a6, t1
	xor a6, a6, t0
	addw t0, t4, s0
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor t5, t5, t1
	xor t5, t5, t0
	addw t0, s2, s1
	slliw t1, t0, 13
	srliw t0, t0, 19
	xor s3, s3, t1
	xor s3, s3, t0
	addw t0, a5, a4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a2, a2, t1
	xor a2, a2, t0
	addw t0, a6, t3
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor a7, a7, t1
	xor a7, a7, t0
	addw t0, t5, t4
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor t6, t6, t1
	xor t6, t6, t0
	addw t0, s3, s2
	slliw t1, t0, 18
	srliw t0, t0, 14
	xor s4, s4, t1
	xor s4, s4, t0
	lwu t0, 0(s7)
	addw a2, a2, t0
	sw a2, 0(s7)
	lwu t0, 4(s7)
	addw a3, a3, t0
	sw a3, 4(s7)
	lwu t0, 8(s7)
	addw a4, a4, t0
	sw a4, 8(s7)
	lwu t0, 12(s7)
	addw a5, a5, t0
	sw a5, 12(s7)
	lwu t0, 16(s7)
	addw a6, a6, t0
	sw a6, 16(s7)
	lwu t0, 20(s7)
	addw a7, a7, t0
	sw a7, 20(s7)
	lwu t0, 24(s7)
	addw t2, t2, t0
	sw t2, 24(s7)
	lwu t0, 28(s7)
	addw t3, t3, t0
	sw t3, 28(s7)
	lwu t0, 32(s7)
	addw t4, t4, t0
	sw t4, 32(s7)
	lwu t0, 36(s7)
	addw t5, t5, t0
	sw t5, 36(s7)
	lwu t0, 40(s7)
	addw t6, t6, t0
	sw t6, 40(s7)
	lwu t0, 44(s7)
	addw s0, s0, t0
	sw s0, 44(s7)
	lwu t0, 48(s7)
	addw s1, s1, t0
	sw s1, 48(s7)
	lwu t0, 52(s7)
	addw s2, s2, t0
	sw s2, 52(s7)
	lwu t0, 56(s7)
	addw s3, s3, t0
	sw s3, 56(s7)
	lwu t0, 60(s7)
	addw s4, s4, t0
	sw s4, 60(s7)
	addi s5, s5, 64
	addi s6, s6, 64
	addi s7, s7, 64
	addi s8, s8, -1
	bnez s8, 20b
	ld s0, 0(s10)
	ld s1, 8(s10)
	ld s2, 16(s10)
	ld s3, 24(s10)
	ld s4, 32(s10)
	ld s5, 40(s10)
	ld s6, 48(s10)
	ld s7, 56(s10)
	ld s8, 64(s10)
	ld s10, 72(s10)
	ret
	.option pop
