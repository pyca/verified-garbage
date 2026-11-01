// The functions of `src/sha1.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha1_compress:
	.option push
	.option arch, +m, +c
	addi a3, a3, 7
	andi a3, a3, -8
	beqz a2, 20f
22:
	lbu t0, 0(a0)
	lbu t5, 1(a0)
	slli t5, t5, 8
	or t0, t0, t5
	lbu t5, 2(a0)
	slli t5, t5, 16
	or t0, t0, t5
	lbu t5, 3(a0)
	slli t5, t5, 24
	or t0, t0, t5
	lbu t1, 4(a0)
	lbu t5, 5(a0)
	slli t5, t5, 8
	or t1, t1, t5
	lbu t5, 6(a0)
	slli t5, t5, 16
	or t1, t1, t5
	lbu t5, 7(a0)
	slli t5, t5, 24
	or t1, t1, t5
	lbu t2, 8(a0)
	lbu t5, 9(a0)
	slli t5, t5, 8
	or t2, t2, t5
	lbu t5, 10(a0)
	slli t5, t5, 16
	or t2, t2, t5
	lbu t5, 11(a0)
	slli t5, t5, 24
	or t2, t2, t5
	lbu t3, 12(a0)
	lbu t5, 13(a0)
	slli t5, t5, 8
	or t3, t3, t5
	lbu t5, 14(a0)
	slli t5, t5, 16
	or t3, t3, t5
	lbu t5, 15(a0)
	slli t5, t5, 24
	or t3, t3, t5
	lbu t4, 16(a0)
	lbu t5, 17(a0)
	slli t5, t5, 8
	or t4, t4, t5
	lbu t5, 18(a0)
	slli t5, t5, 16
	or t4, t4, t5
	lbu t5, 19(a0)
	slli t5, t5, 24
	or t4, t4, t5
	slli t6, t0, 32
	or t0, t0, t6
	slli t6, t1, 32
	or t1, t1, t6
	lbu t5, 0(a1)
	slli t5, t5, 24
	lbu t6, 1(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 2(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 3(a1)
	or t5, t5, t6
	sw t5, 0(a3)
	lui a5, 370728
	addiw a5, a5, -1639
	add t4, t4, t5
	add t4, t4, a5
	xor t6, t2, t3
	and t6, t6, t1
	xor t6, t6, t3
	add t4, t4, t6
	srli t6, t0, 27
	add t4, t4, t6
	srli t1, t1, 2
	slli t4, t4, 32
	srli t6, t4, 32
	or t4, t4, t6
	lbu t5, 4(a1)
	slli t5, t5, 24
	lbu t6, 5(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 6(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 7(a1)
	or t5, t5, t6
	sw t5, 4(a3)
	add t3, t3, t5
	add t3, t3, a5
	xor t6, t1, t2
	and t6, t6, t0
	xor t6, t6, t2
	add t3, t3, t6
	srli t6, t4, 27
	add t3, t3, t6
	srli t0, t0, 2
	slli t3, t3, 32
	srli t6, t3, 32
	or t3, t3, t6
	lbu t5, 8(a1)
	slli t5, t5, 24
	lbu t6, 9(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 10(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 11(a1)
	or t5, t5, t6
	sw t5, 8(a3)
	add t2, t2, t5
	add t2, t2, a5
	xor t6, t0, t1
	and t6, t6, t4
	xor t6, t6, t1
	add t2, t2, t6
	srli t6, t3, 27
	add t2, t2, t6
	srli t4, t4, 2
	slli t2, t2, 32
	srli t6, t2, 32
	or t2, t2, t6
	lbu t5, 12(a1)
	slli t5, t5, 24
	lbu t6, 13(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 14(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 15(a1)
	or t5, t5, t6
	sw t5, 12(a3)
	add t1, t1, t5
	add t1, t1, a5
	xor t6, t4, t0
	and t6, t6, t3
	xor t6, t6, t0
	add t1, t1, t6
	srli t6, t2, 27
	add t1, t1, t6
	srli t3, t3, 2
	slli t1, t1, 32
	srli t6, t1, 32
	or t1, t1, t6
	lbu t5, 16(a1)
	slli t5, t5, 24
	lbu t6, 17(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 18(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 19(a1)
	or t5, t5, t6
	sw t5, 16(a3)
	add t0, t0, t5
	add t0, t0, a5
	xor t6, t3, t4
	and t6, t6, t2
	xor t6, t6, t4
	add t0, t0, t6
	srli t6, t1, 27
	add t0, t0, t6
	srli t2, t2, 2
	slli t0, t0, 32
	srli t6, t0, 32
	or t0, t0, t6
	lbu t5, 20(a1)
	slli t5, t5, 24
	lbu t6, 21(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 22(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 23(a1)
	or t5, t5, t6
	sw t5, 20(a3)
	add t4, t4, t5
	add t4, t4, a5
	xor t6, t2, t3
	and t6, t6, t1
	xor t6, t6, t3
	add t4, t4, t6
	srli t6, t0, 27
	add t4, t4, t6
	srli t1, t1, 2
	slli t4, t4, 32
	srli t6, t4, 32
	or t4, t4, t6
	lbu t5, 24(a1)
	slli t5, t5, 24
	lbu t6, 25(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 26(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 27(a1)
	or t5, t5, t6
	sw t5, 24(a3)
	add t3, t3, t5
	add t3, t3, a5
	xor t6, t1, t2
	and t6, t6, t0
	xor t6, t6, t2
	add t3, t3, t6
	srli t6, t4, 27
	add t3, t3, t6
	srli t0, t0, 2
	slli t3, t3, 32
	srli t6, t3, 32
	or t3, t3, t6
	lbu t5, 28(a1)
	slli t5, t5, 24
	lbu t6, 29(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 30(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 31(a1)
	or t5, t5, t6
	sw t5, 28(a3)
	add t2, t2, t5
	add t2, t2, a5
	xor t6, t0, t1
	and t6, t6, t4
	xor t6, t6, t1
	add t2, t2, t6
	srli t6, t3, 27
	add t2, t2, t6
	srli t4, t4, 2
	slli t2, t2, 32
	srli t6, t2, 32
	or t2, t2, t6
	lbu t5, 32(a1)
	slli t5, t5, 24
	lbu t6, 33(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 34(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 35(a1)
	or t5, t5, t6
	sw t5, 32(a3)
	add t1, t1, t5
	add t1, t1, a5
	xor t6, t4, t0
	and t6, t6, t3
	xor t6, t6, t0
	add t1, t1, t6
	srli t6, t2, 27
	add t1, t1, t6
	srli t3, t3, 2
	slli t1, t1, 32
	srli t6, t1, 32
	or t1, t1, t6
	lbu t5, 36(a1)
	slli t5, t5, 24
	lbu t6, 37(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 38(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 39(a1)
	or t5, t5, t6
	sw t5, 36(a3)
	add t0, t0, t5
	add t0, t0, a5
	xor t6, t3, t4
	and t6, t6, t2
	xor t6, t6, t4
	add t0, t0, t6
	srli t6, t1, 27
	add t0, t0, t6
	srli t2, t2, 2
	slli t0, t0, 32
	srli t6, t0, 32
	or t0, t0, t6
	lbu t5, 40(a1)
	slli t5, t5, 24
	lbu t6, 41(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 42(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 43(a1)
	or t5, t5, t6
	sw t5, 40(a3)
	add t4, t4, t5
	add t4, t4, a5
	xor t6, t2, t3
	and t6, t6, t1
	xor t6, t6, t3
	add t4, t4, t6
	srli t6, t0, 27
	add t4, t4, t6
	srli t1, t1, 2
	slli t4, t4, 32
	srli t6, t4, 32
	or t4, t4, t6
	lbu t5, 44(a1)
	slli t5, t5, 24
	lbu t6, 45(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 46(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 47(a1)
	or t5, t5, t6
	sw t5, 44(a3)
	add t3, t3, t5
	add t3, t3, a5
	xor t6, t1, t2
	and t6, t6, t0
	xor t6, t6, t2
	add t3, t3, t6
	srli t6, t4, 27
	add t3, t3, t6
	srli t0, t0, 2
	slli t3, t3, 32
	srli t6, t3, 32
	or t3, t3, t6
	lbu t5, 48(a1)
	slli t5, t5, 24
	lbu t6, 49(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 50(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 51(a1)
	or t5, t5, t6
	sw t5, 48(a3)
	add t2, t2, t5
	add t2, t2, a5
	xor t6, t0, t1
	and t6, t6, t4
	xor t6, t6, t1
	add t2, t2, t6
	srli t6, t3, 27
	add t2, t2, t6
	srli t4, t4, 2
	slli t2, t2, 32
	srli t6, t2, 32
	or t2, t2, t6
	lbu t5, 52(a1)
	slli t5, t5, 24
	lbu t6, 53(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 54(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 55(a1)
	or t5, t5, t6
	sw t5, 52(a3)
	add t1, t1, t5
	add t1, t1, a5
	xor t6, t4, t0
	and t6, t6, t3
	xor t6, t6, t0
	add t1, t1, t6
	srli t6, t2, 27
	add t1, t1, t6
	srli t3, t3, 2
	slli t1, t1, 32
	srli t6, t1, 32
	or t1, t1, t6
	lbu t5, 56(a1)
	slli t5, t5, 24
	lbu t6, 57(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 58(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 59(a1)
	or t5, t5, t6
	sw t5, 56(a3)
	add t0, t0, t5
	add t0, t0, a5
	xor t6, t3, t4
	and t6, t6, t2
	xor t6, t6, t4
	add t0, t0, t6
	srli t6, t1, 27
	add t0, t0, t6
	srli t2, t2, 2
	slli t0, t0, 32
	srli t6, t0, 32
	or t0, t0, t6
	lbu t5, 60(a1)
	slli t5, t5, 24
	lbu t6, 61(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 62(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 63(a1)
	or t5, t5, t6
	sw t5, 60(a3)
	add t4, t4, t5
	add t4, t4, a5
	xor t6, t2, t3
	and t6, t6, t1
	xor t6, t6, t3
	add t4, t4, t6
	srli t6, t0, 27
	add t4, t4, t6
	srli t1, t1, 2
	slli t4, t4, 32
	srli t6, t4, 32
	or t4, t4, t6
	lwu t5, 52(a3)
	lwu t6, 32(a3)
	xor t5, t5, t6
	lwu t6, 8(a3)
	xor t5, t5, t6
	lwu t6, 0(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 0(a3)
	add t3, t3, t5
	add t3, t3, a5
	xor t6, t1, t2
	and t6, t6, t0
	xor t6, t6, t2
	add t3, t3, t6
	srli t6, t4, 27
	add t3, t3, t6
	srli t0, t0, 2
	slli t3, t3, 32
	srli t6, t3, 32
	or t3, t3, t6
	lwu t5, 56(a3)
	lwu t6, 36(a3)
	xor t5, t5, t6
	lwu t6, 12(a3)
	xor t5, t5, t6
	lwu t6, 4(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 4(a3)
	add t2, t2, t5
	add t2, t2, a5
	xor t6, t0, t1
	and t6, t6, t4
	xor t6, t6, t1
	add t2, t2, t6
	srli t6, t3, 27
	add t2, t2, t6
	srli t4, t4, 2
	slli t2, t2, 32
	srli t6, t2, 32
	or t2, t2, t6
	lwu t5, 60(a3)
	lwu t6, 40(a3)
	xor t5, t5, t6
	lwu t6, 16(a3)
	xor t5, t5, t6
	lwu t6, 8(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 8(a3)
	add t1, t1, t5
	add t1, t1, a5
	xor t6, t4, t0
	and t6, t6, t3
	xor t6, t6, t0
	add t1, t1, t6
	srli t6, t2, 27
	add t1, t1, t6
	srli t3, t3, 2
	slli t1, t1, 32
	srli t6, t1, 32
	or t1, t1, t6
	lwu t5, 0(a3)
	lwu t6, 44(a3)
	xor t5, t5, t6
	lwu t6, 20(a3)
	xor t5, t5, t6
	lwu t6, 12(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 12(a3)
	add t0, t0, t5
	add t0, t0, a5
	xor t6, t3, t4
	and t6, t6, t2
	xor t6, t6, t4
	add t0, t0, t6
	srli t6, t1, 27
	add t0, t0, t6
	srli t2, t2, 2
	slli t0, t0, 32
	srli t6, t0, 32
	or t0, t0, t6
	lwu t5, 4(a3)
	lwu t6, 48(a3)
	xor t5, t5, t6
	lwu t6, 24(a3)
	xor t5, t5, t6
	lwu t6, 16(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 16(a3)
	lui a5, 454047
	addiw a5, a5, -1119
	add t4, t4, t5
	add t4, t4, a5
	xor t6, t1, t2
	xor t6, t6, t3
	add t4, t4, t6
	srli t6, t0, 27
	add t4, t4, t6
	srli t1, t1, 2
	slli t4, t4, 32
	srli t6, t4, 32
	or t4, t4, t6
	lwu t5, 8(a3)
	lwu t6, 52(a3)
	xor t5, t5, t6
	lwu t6, 28(a3)
	xor t5, t5, t6
	lwu t6, 20(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 20(a3)
	add t3, t3, t5
	add t3, t3, a5
	xor t6, t0, t1
	xor t6, t6, t2
	add t3, t3, t6
	srli t6, t4, 27
	add t3, t3, t6
	srli t0, t0, 2
	slli t3, t3, 32
	srli t6, t3, 32
	or t3, t3, t6
	lwu t5, 12(a3)
	lwu t6, 56(a3)
	xor t5, t5, t6
	lwu t6, 32(a3)
	xor t5, t5, t6
	lwu t6, 24(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 24(a3)
	add t2, t2, t5
	add t2, t2, a5
	xor t6, t4, t0
	xor t6, t6, t1
	add t2, t2, t6
	srli t6, t3, 27
	add t2, t2, t6
	srli t4, t4, 2
	slli t2, t2, 32
	srli t6, t2, 32
	or t2, t2, t6
	lwu t5, 16(a3)
	lwu t6, 60(a3)
	xor t5, t5, t6
	lwu t6, 36(a3)
	xor t5, t5, t6
	lwu t6, 28(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 28(a3)
	add t1, t1, t5
	add t1, t1, a5
	xor t6, t3, t4
	xor t6, t6, t0
	add t1, t1, t6
	srli t6, t2, 27
	add t1, t1, t6
	srli t3, t3, 2
	slli t1, t1, 32
	srli t6, t1, 32
	or t1, t1, t6
	lwu t5, 20(a3)
	lwu t6, 0(a3)
	xor t5, t5, t6
	lwu t6, 40(a3)
	xor t5, t5, t6
	lwu t6, 32(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 32(a3)
	add t0, t0, t5
	add t0, t0, a5
	xor t6, t2, t3
	xor t6, t6, t4
	add t0, t0, t6
	srli t6, t1, 27
	add t0, t0, t6
	srli t2, t2, 2
	slli t0, t0, 32
	srli t6, t0, 32
	or t0, t0, t6
	lwu t5, 24(a3)
	lwu t6, 4(a3)
	xor t5, t5, t6
	lwu t6, 44(a3)
	xor t5, t5, t6
	lwu t6, 36(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 36(a3)
	add t4, t4, t5
	add t4, t4, a5
	xor t6, t1, t2
	xor t6, t6, t3
	add t4, t4, t6
	srli t6, t0, 27
	add t4, t4, t6
	srli t1, t1, 2
	slli t4, t4, 32
	srli t6, t4, 32
	or t4, t4, t6
	lwu t5, 28(a3)
	lwu t6, 8(a3)
	xor t5, t5, t6
	lwu t6, 48(a3)
	xor t5, t5, t6
	lwu t6, 40(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 40(a3)
	add t3, t3, t5
	add t3, t3, a5
	xor t6, t0, t1
	xor t6, t6, t2
	add t3, t3, t6
	srli t6, t4, 27
	add t3, t3, t6
	srli t0, t0, 2
	slli t3, t3, 32
	srli t6, t3, 32
	or t3, t3, t6
	lwu t5, 32(a3)
	lwu t6, 12(a3)
	xor t5, t5, t6
	lwu t6, 52(a3)
	xor t5, t5, t6
	lwu t6, 44(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 44(a3)
	add t2, t2, t5
	add t2, t2, a5
	xor t6, t4, t0
	xor t6, t6, t1
	add t2, t2, t6
	srli t6, t3, 27
	add t2, t2, t6
	srli t4, t4, 2
	slli t2, t2, 32
	srli t6, t2, 32
	or t2, t2, t6
	lwu t5, 36(a3)
	lwu t6, 16(a3)
	xor t5, t5, t6
	lwu t6, 56(a3)
	xor t5, t5, t6
	lwu t6, 48(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 48(a3)
	add t1, t1, t5
	add t1, t1, a5
	xor t6, t3, t4
	xor t6, t6, t0
	add t1, t1, t6
	srli t6, t2, 27
	add t1, t1, t6
	srli t3, t3, 2
	slli t1, t1, 32
	srli t6, t1, 32
	or t1, t1, t6
	lwu t5, 40(a3)
	lwu t6, 20(a3)
	xor t5, t5, t6
	lwu t6, 60(a3)
	xor t5, t5, t6
	lwu t6, 52(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 52(a3)
	add t0, t0, t5
	add t0, t0, a5
	xor t6, t2, t3
	xor t6, t6, t4
	add t0, t0, t6
	srli t6, t1, 27
	add t0, t0, t6
	srli t2, t2, 2
	slli t0, t0, 32
	srli t6, t0, 32
	or t0, t0, t6
	lwu t5, 44(a3)
	lwu t6, 24(a3)
	xor t5, t5, t6
	lwu t6, 0(a3)
	xor t5, t5, t6
	lwu t6, 56(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 56(a3)
	add t4, t4, t5
	add t4, t4, a5
	xor t6, t1, t2
	xor t6, t6, t3
	add t4, t4, t6
	srli t6, t0, 27
	add t4, t4, t6
	srli t1, t1, 2
	slli t4, t4, 32
	srli t6, t4, 32
	or t4, t4, t6
	lwu t5, 48(a3)
	lwu t6, 28(a3)
	xor t5, t5, t6
	lwu t6, 4(a3)
	xor t5, t5, t6
	lwu t6, 60(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 60(a3)
	add t3, t3, t5
	add t3, t3, a5
	xor t6, t0, t1
	xor t6, t6, t2
	add t3, t3, t6
	srli t6, t4, 27
	add t3, t3, t6
	srli t0, t0, 2
	slli t3, t3, 32
	srli t6, t3, 32
	or t3, t3, t6
	lwu t5, 52(a3)
	lwu t6, 32(a3)
	xor t5, t5, t6
	lwu t6, 8(a3)
	xor t5, t5, t6
	lwu t6, 0(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 0(a3)
	add t2, t2, t5
	add t2, t2, a5
	xor t6, t4, t0
	xor t6, t6, t1
	add t2, t2, t6
	srli t6, t3, 27
	add t2, t2, t6
	srli t4, t4, 2
	slli t2, t2, 32
	srli t6, t2, 32
	or t2, t2, t6
	lwu t5, 56(a3)
	lwu t6, 36(a3)
	xor t5, t5, t6
	lwu t6, 12(a3)
	xor t5, t5, t6
	lwu t6, 4(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 4(a3)
	add t1, t1, t5
	add t1, t1, a5
	xor t6, t3, t4
	xor t6, t6, t0
	add t1, t1, t6
	srli t6, t2, 27
	add t1, t1, t6
	srli t3, t3, 2
	slli t1, t1, 32
	srli t6, t1, 32
	or t1, t1, t6
	lwu t5, 60(a3)
	lwu t6, 40(a3)
	xor t5, t5, t6
	lwu t6, 16(a3)
	xor t5, t5, t6
	lwu t6, 8(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 8(a3)
	add t0, t0, t5
	add t0, t0, a5
	xor t6, t2, t3
	xor t6, t6, t4
	add t0, t0, t6
	srli t6, t1, 27
	add t0, t0, t6
	srli t2, t2, 2
	slli t0, t0, 32
	srli t6, t0, 32
	or t0, t0, t6
	lwu t5, 0(a3)
	lwu t6, 44(a3)
	xor t5, t5, t6
	lwu t6, 20(a3)
	xor t5, t5, t6
	lwu t6, 12(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 12(a3)
	add t4, t4, t5
	add t4, t4, a5
	xor t6, t1, t2
	xor t6, t6, t3
	add t4, t4, t6
	srli t6, t0, 27
	add t4, t4, t6
	srli t1, t1, 2
	slli t4, t4, 32
	srli t6, t4, 32
	or t4, t4, t6
	lwu t5, 4(a3)
	lwu t6, 48(a3)
	xor t5, t5, t6
	lwu t6, 24(a3)
	xor t5, t5, t6
	lwu t6, 16(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 16(a3)
	add t3, t3, t5
	add t3, t3, a5
	xor t6, t0, t1
	xor t6, t6, t2
	add t3, t3, t6
	srli t6, t4, 27
	add t3, t3, t6
	srli t0, t0, 2
	slli t3, t3, 32
	srli t6, t3, 32
	or t3, t3, t6
	lwu t5, 8(a3)
	lwu t6, 52(a3)
	xor t5, t5, t6
	lwu t6, 28(a3)
	xor t5, t5, t6
	lwu t6, 20(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 20(a3)
	add t2, t2, t5
	add t2, t2, a5
	xor t6, t4, t0
	xor t6, t6, t1
	add t2, t2, t6
	srli t6, t3, 27
	add t2, t2, t6
	srli t4, t4, 2
	slli t2, t2, 32
	srli t6, t2, 32
	or t2, t2, t6
	lwu t5, 12(a3)
	lwu t6, 56(a3)
	xor t5, t5, t6
	lwu t6, 32(a3)
	xor t5, t5, t6
	lwu t6, 24(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 24(a3)
	add t1, t1, t5
	add t1, t1, a5
	xor t6, t3, t4
	xor t6, t6, t0
	add t1, t1, t6
	srli t6, t2, 27
	add t1, t1, t6
	srli t3, t3, 2
	slli t1, t1, 32
	srli t6, t1, 32
	or t1, t1, t6
	lwu t5, 16(a3)
	lwu t6, 60(a3)
	xor t5, t5, t6
	lwu t6, 36(a3)
	xor t5, t5, t6
	lwu t6, 28(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 28(a3)
	add t0, t0, t5
	add t0, t0, a5
	xor t6, t2, t3
	xor t6, t6, t4
	add t0, t0, t6
	srli t6, t1, 27
	add t0, t0, t6
	srli t2, t2, 2
	slli t0, t0, 32
	srli t6, t0, 32
	or t0, t0, t6
	lwu t5, 20(a3)
	lwu t6, 0(a3)
	xor t5, t5, t6
	lwu t6, 40(a3)
	xor t5, t5, t6
	lwu t6, 32(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 32(a3)
	lui a5, 586172
	addiw a5, a5, -804
	add t4, t4, t5
	add t4, t4, a5
	or t6, t1, t2
	and t6, t6, t3
	and a4, t1, t2
	or t6, t6, a4
	add t4, t4, t6
	srli t6, t0, 27
	add t4, t4, t6
	srli t1, t1, 2
	slli t4, t4, 32
	srli t6, t4, 32
	or t4, t4, t6
	lwu t5, 24(a3)
	lwu t6, 4(a3)
	xor t5, t5, t6
	lwu t6, 44(a3)
	xor t5, t5, t6
	lwu t6, 36(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 36(a3)
	add t3, t3, t5
	add t3, t3, a5
	or t6, t0, t1
	and t6, t6, t2
	and a4, t0, t1
	or t6, t6, a4
	add t3, t3, t6
	srli t6, t4, 27
	add t3, t3, t6
	srli t0, t0, 2
	slli t3, t3, 32
	srli t6, t3, 32
	or t3, t3, t6
	lwu t5, 28(a3)
	lwu t6, 8(a3)
	xor t5, t5, t6
	lwu t6, 48(a3)
	xor t5, t5, t6
	lwu t6, 40(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 40(a3)
	add t2, t2, t5
	add t2, t2, a5
	or t6, t4, t0
	and t6, t6, t1
	and a4, t4, t0
	or t6, t6, a4
	add t2, t2, t6
	srli t6, t3, 27
	add t2, t2, t6
	srli t4, t4, 2
	slli t2, t2, 32
	srli t6, t2, 32
	or t2, t2, t6
	lwu t5, 32(a3)
	lwu t6, 12(a3)
	xor t5, t5, t6
	lwu t6, 52(a3)
	xor t5, t5, t6
	lwu t6, 44(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 44(a3)
	add t1, t1, t5
	add t1, t1, a5
	or t6, t3, t4
	and t6, t6, t0
	and a4, t3, t4
	or t6, t6, a4
	add t1, t1, t6
	srli t6, t2, 27
	add t1, t1, t6
	srli t3, t3, 2
	slli t1, t1, 32
	srli t6, t1, 32
	or t1, t1, t6
	lwu t5, 36(a3)
	lwu t6, 16(a3)
	xor t5, t5, t6
	lwu t6, 56(a3)
	xor t5, t5, t6
	lwu t6, 48(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 48(a3)
	add t0, t0, t5
	add t0, t0, a5
	or t6, t2, t3
	and t6, t6, t4
	and a4, t2, t3
	or t6, t6, a4
	add t0, t0, t6
	srli t6, t1, 27
	add t0, t0, t6
	srli t2, t2, 2
	slli t0, t0, 32
	srli t6, t0, 32
	or t0, t0, t6
	lwu t5, 40(a3)
	lwu t6, 20(a3)
	xor t5, t5, t6
	lwu t6, 60(a3)
	xor t5, t5, t6
	lwu t6, 52(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 52(a3)
	add t4, t4, t5
	add t4, t4, a5
	or t6, t1, t2
	and t6, t6, t3
	and a4, t1, t2
	or t6, t6, a4
	add t4, t4, t6
	srli t6, t0, 27
	add t4, t4, t6
	srli t1, t1, 2
	slli t4, t4, 32
	srli t6, t4, 32
	or t4, t4, t6
	lwu t5, 44(a3)
	lwu t6, 24(a3)
	xor t5, t5, t6
	lwu t6, 0(a3)
	xor t5, t5, t6
	lwu t6, 56(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 56(a3)
	add t3, t3, t5
	add t3, t3, a5
	or t6, t0, t1
	and t6, t6, t2
	and a4, t0, t1
	or t6, t6, a4
	add t3, t3, t6
	srli t6, t4, 27
	add t3, t3, t6
	srli t0, t0, 2
	slli t3, t3, 32
	srli t6, t3, 32
	or t3, t3, t6
	lwu t5, 48(a3)
	lwu t6, 28(a3)
	xor t5, t5, t6
	lwu t6, 4(a3)
	xor t5, t5, t6
	lwu t6, 60(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 60(a3)
	add t2, t2, t5
	add t2, t2, a5
	or t6, t4, t0
	and t6, t6, t1
	and a4, t4, t0
	or t6, t6, a4
	add t2, t2, t6
	srli t6, t3, 27
	add t2, t2, t6
	srli t4, t4, 2
	slli t2, t2, 32
	srli t6, t2, 32
	or t2, t2, t6
	lwu t5, 52(a3)
	lwu t6, 32(a3)
	xor t5, t5, t6
	lwu t6, 8(a3)
	xor t5, t5, t6
	lwu t6, 0(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 0(a3)
	add t1, t1, t5
	add t1, t1, a5
	or t6, t3, t4
	and t6, t6, t0
	and a4, t3, t4
	or t6, t6, a4
	add t1, t1, t6
	srli t6, t2, 27
	add t1, t1, t6
	srli t3, t3, 2
	slli t1, t1, 32
	srli t6, t1, 32
	or t1, t1, t6
	lwu t5, 56(a3)
	lwu t6, 36(a3)
	xor t5, t5, t6
	lwu t6, 12(a3)
	xor t5, t5, t6
	lwu t6, 4(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 4(a3)
	add t0, t0, t5
	add t0, t0, a5
	or t6, t2, t3
	and t6, t6, t4
	and a4, t2, t3
	or t6, t6, a4
	add t0, t0, t6
	srli t6, t1, 27
	add t0, t0, t6
	srli t2, t2, 2
	slli t0, t0, 32
	srli t6, t0, 32
	or t0, t0, t6
	lwu t5, 60(a3)
	lwu t6, 40(a3)
	xor t5, t5, t6
	lwu t6, 16(a3)
	xor t5, t5, t6
	lwu t6, 8(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 8(a3)
	add t4, t4, t5
	add t4, t4, a5
	or t6, t1, t2
	and t6, t6, t3
	and a4, t1, t2
	or t6, t6, a4
	add t4, t4, t6
	srli t6, t0, 27
	add t4, t4, t6
	srli t1, t1, 2
	slli t4, t4, 32
	srli t6, t4, 32
	or t4, t4, t6
	lwu t5, 0(a3)
	lwu t6, 44(a3)
	xor t5, t5, t6
	lwu t6, 20(a3)
	xor t5, t5, t6
	lwu t6, 12(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 12(a3)
	add t3, t3, t5
	add t3, t3, a5
	or t6, t0, t1
	and t6, t6, t2
	and a4, t0, t1
	or t6, t6, a4
	add t3, t3, t6
	srli t6, t4, 27
	add t3, t3, t6
	srli t0, t0, 2
	slli t3, t3, 32
	srli t6, t3, 32
	or t3, t3, t6
	lwu t5, 4(a3)
	lwu t6, 48(a3)
	xor t5, t5, t6
	lwu t6, 24(a3)
	xor t5, t5, t6
	lwu t6, 16(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 16(a3)
	add t2, t2, t5
	add t2, t2, a5
	or t6, t4, t0
	and t6, t6, t1
	and a4, t4, t0
	or t6, t6, a4
	add t2, t2, t6
	srli t6, t3, 27
	add t2, t2, t6
	srli t4, t4, 2
	slli t2, t2, 32
	srli t6, t2, 32
	or t2, t2, t6
	lwu t5, 8(a3)
	lwu t6, 52(a3)
	xor t5, t5, t6
	lwu t6, 28(a3)
	xor t5, t5, t6
	lwu t6, 20(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 20(a3)
	add t1, t1, t5
	add t1, t1, a5
	or t6, t3, t4
	and t6, t6, t0
	and a4, t3, t4
	or t6, t6, a4
	add t1, t1, t6
	srli t6, t2, 27
	add t1, t1, t6
	srli t3, t3, 2
	slli t1, t1, 32
	srli t6, t1, 32
	or t1, t1, t6
	lwu t5, 12(a3)
	lwu t6, 56(a3)
	xor t5, t5, t6
	lwu t6, 32(a3)
	xor t5, t5, t6
	lwu t6, 24(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 24(a3)
	add t0, t0, t5
	add t0, t0, a5
	or t6, t2, t3
	and t6, t6, t4
	and a4, t2, t3
	or t6, t6, a4
	add t0, t0, t6
	srli t6, t1, 27
	add t0, t0, t6
	srli t2, t2, 2
	slli t0, t0, 32
	srli t6, t0, 32
	or t0, t0, t6
	lwu t5, 16(a3)
	lwu t6, 60(a3)
	xor t5, t5, t6
	lwu t6, 36(a3)
	xor t5, t5, t6
	lwu t6, 28(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 28(a3)
	add t4, t4, t5
	add t4, t4, a5
	or t6, t1, t2
	and t6, t6, t3
	and a4, t1, t2
	or t6, t6, a4
	add t4, t4, t6
	srli t6, t0, 27
	add t4, t4, t6
	srli t1, t1, 2
	slli t4, t4, 32
	srli t6, t4, 32
	or t4, t4, t6
	lwu t5, 20(a3)
	lwu t6, 0(a3)
	xor t5, t5, t6
	lwu t6, 40(a3)
	xor t5, t5, t6
	lwu t6, 32(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 32(a3)
	add t3, t3, t5
	add t3, t3, a5
	or t6, t0, t1
	and t6, t6, t2
	and a4, t0, t1
	or t6, t6, a4
	add t3, t3, t6
	srli t6, t4, 27
	add t3, t3, t6
	srli t0, t0, 2
	slli t3, t3, 32
	srli t6, t3, 32
	or t3, t3, t6
	lwu t5, 24(a3)
	lwu t6, 4(a3)
	xor t5, t5, t6
	lwu t6, 44(a3)
	xor t5, t5, t6
	lwu t6, 36(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 36(a3)
	add t2, t2, t5
	add t2, t2, a5
	or t6, t4, t0
	and t6, t6, t1
	and a4, t4, t0
	or t6, t6, a4
	add t2, t2, t6
	srli t6, t3, 27
	add t2, t2, t6
	srli t4, t4, 2
	slli t2, t2, 32
	srli t6, t2, 32
	or t2, t2, t6
	lwu t5, 28(a3)
	lwu t6, 8(a3)
	xor t5, t5, t6
	lwu t6, 48(a3)
	xor t5, t5, t6
	lwu t6, 40(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 40(a3)
	add t1, t1, t5
	add t1, t1, a5
	or t6, t3, t4
	and t6, t6, t0
	and a4, t3, t4
	or t6, t6, a4
	add t1, t1, t6
	srli t6, t2, 27
	add t1, t1, t6
	srli t3, t3, 2
	slli t1, t1, 32
	srli t6, t1, 32
	or t1, t1, t6
	lwu t5, 32(a3)
	lwu t6, 12(a3)
	xor t5, t5, t6
	lwu t6, 52(a3)
	xor t5, t5, t6
	lwu t6, 44(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 44(a3)
	add t0, t0, t5
	add t0, t0, a5
	or t6, t2, t3
	and t6, t6, t4
	and a4, t2, t3
	or t6, t6, a4
	add t0, t0, t6
	srli t6, t1, 27
	add t0, t0, t6
	srli t2, t2, 2
	slli t0, t0, 32
	srli t6, t0, 32
	or t0, t0, t6
	lwu t5, 36(a3)
	lwu t6, 16(a3)
	xor t5, t5, t6
	lwu t6, 56(a3)
	xor t5, t5, t6
	lwu t6, 48(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 48(a3)
	lui a5, 828972
	addiw a5, a5, 470
	add t4, t4, t5
	add t4, t4, a5
	xor t6, t1, t2
	xor t6, t6, t3
	add t4, t4, t6
	srli t6, t0, 27
	add t4, t4, t6
	srli t1, t1, 2
	slli t4, t4, 32
	srli t6, t4, 32
	or t4, t4, t6
	lwu t5, 40(a3)
	lwu t6, 20(a3)
	xor t5, t5, t6
	lwu t6, 60(a3)
	xor t5, t5, t6
	lwu t6, 52(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 52(a3)
	add t3, t3, t5
	add t3, t3, a5
	xor t6, t0, t1
	xor t6, t6, t2
	add t3, t3, t6
	srli t6, t4, 27
	add t3, t3, t6
	srli t0, t0, 2
	slli t3, t3, 32
	srli t6, t3, 32
	or t3, t3, t6
	lwu t5, 44(a3)
	lwu t6, 24(a3)
	xor t5, t5, t6
	lwu t6, 0(a3)
	xor t5, t5, t6
	lwu t6, 56(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 56(a3)
	add t2, t2, t5
	add t2, t2, a5
	xor t6, t4, t0
	xor t6, t6, t1
	add t2, t2, t6
	srli t6, t3, 27
	add t2, t2, t6
	srli t4, t4, 2
	slli t2, t2, 32
	srli t6, t2, 32
	or t2, t2, t6
	lwu t5, 48(a3)
	lwu t6, 28(a3)
	xor t5, t5, t6
	lwu t6, 4(a3)
	xor t5, t5, t6
	lwu t6, 60(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 60(a3)
	add t1, t1, t5
	add t1, t1, a5
	xor t6, t3, t4
	xor t6, t6, t0
	add t1, t1, t6
	srli t6, t2, 27
	add t1, t1, t6
	srli t3, t3, 2
	slli t1, t1, 32
	srli t6, t1, 32
	or t1, t1, t6
	lwu t5, 52(a3)
	lwu t6, 32(a3)
	xor t5, t5, t6
	lwu t6, 8(a3)
	xor t5, t5, t6
	lwu t6, 0(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 0(a3)
	add t0, t0, t5
	add t0, t0, a5
	xor t6, t2, t3
	xor t6, t6, t4
	add t0, t0, t6
	srli t6, t1, 27
	add t0, t0, t6
	srli t2, t2, 2
	slli t0, t0, 32
	srli t6, t0, 32
	or t0, t0, t6
	lwu t5, 56(a3)
	lwu t6, 36(a3)
	xor t5, t5, t6
	lwu t6, 12(a3)
	xor t5, t5, t6
	lwu t6, 4(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 4(a3)
	add t4, t4, t5
	add t4, t4, a5
	xor t6, t1, t2
	xor t6, t6, t3
	add t4, t4, t6
	srli t6, t0, 27
	add t4, t4, t6
	srli t1, t1, 2
	slli t4, t4, 32
	srli t6, t4, 32
	or t4, t4, t6
	lwu t5, 60(a3)
	lwu t6, 40(a3)
	xor t5, t5, t6
	lwu t6, 16(a3)
	xor t5, t5, t6
	lwu t6, 8(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 8(a3)
	add t3, t3, t5
	add t3, t3, a5
	xor t6, t0, t1
	xor t6, t6, t2
	add t3, t3, t6
	srli t6, t4, 27
	add t3, t3, t6
	srli t0, t0, 2
	slli t3, t3, 32
	srli t6, t3, 32
	or t3, t3, t6
	lwu t5, 0(a3)
	lwu t6, 44(a3)
	xor t5, t5, t6
	lwu t6, 20(a3)
	xor t5, t5, t6
	lwu t6, 12(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 12(a3)
	add t2, t2, t5
	add t2, t2, a5
	xor t6, t4, t0
	xor t6, t6, t1
	add t2, t2, t6
	srli t6, t3, 27
	add t2, t2, t6
	srli t4, t4, 2
	slli t2, t2, 32
	srli t6, t2, 32
	or t2, t2, t6
	lwu t5, 4(a3)
	lwu t6, 48(a3)
	xor t5, t5, t6
	lwu t6, 24(a3)
	xor t5, t5, t6
	lwu t6, 16(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 16(a3)
	add t1, t1, t5
	add t1, t1, a5
	xor t6, t3, t4
	xor t6, t6, t0
	add t1, t1, t6
	srli t6, t2, 27
	add t1, t1, t6
	srli t3, t3, 2
	slli t1, t1, 32
	srli t6, t1, 32
	or t1, t1, t6
	lwu t5, 8(a3)
	lwu t6, 52(a3)
	xor t5, t5, t6
	lwu t6, 28(a3)
	xor t5, t5, t6
	lwu t6, 20(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 20(a3)
	add t0, t0, t5
	add t0, t0, a5
	xor t6, t2, t3
	xor t6, t6, t4
	add t0, t0, t6
	srli t6, t1, 27
	add t0, t0, t6
	srli t2, t2, 2
	slli t0, t0, 32
	srli t6, t0, 32
	or t0, t0, t6
	lwu t5, 12(a3)
	lwu t6, 56(a3)
	xor t5, t5, t6
	lwu t6, 32(a3)
	xor t5, t5, t6
	lwu t6, 24(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 24(a3)
	add t4, t4, t5
	add t4, t4, a5
	xor t6, t1, t2
	xor t6, t6, t3
	add t4, t4, t6
	srli t6, t0, 27
	add t4, t4, t6
	srli t1, t1, 2
	slli t4, t4, 32
	srli t6, t4, 32
	or t4, t4, t6
	lwu t5, 16(a3)
	lwu t6, 60(a3)
	xor t5, t5, t6
	lwu t6, 36(a3)
	xor t5, t5, t6
	lwu t6, 28(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 28(a3)
	add t3, t3, t5
	add t3, t3, a5
	xor t6, t0, t1
	xor t6, t6, t2
	add t3, t3, t6
	srli t6, t4, 27
	add t3, t3, t6
	srli t0, t0, 2
	slli t3, t3, 32
	srli t6, t3, 32
	or t3, t3, t6
	lwu t5, 20(a3)
	lwu t6, 0(a3)
	xor t5, t5, t6
	lwu t6, 40(a3)
	xor t5, t5, t6
	lwu t6, 32(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 32(a3)
	add t2, t2, t5
	add t2, t2, a5
	xor t6, t4, t0
	xor t6, t6, t1
	add t2, t2, t6
	srli t6, t3, 27
	add t2, t2, t6
	srli t4, t4, 2
	slli t2, t2, 32
	srli t6, t2, 32
	or t2, t2, t6
	lwu t5, 24(a3)
	lwu t6, 4(a3)
	xor t5, t5, t6
	lwu t6, 44(a3)
	xor t5, t5, t6
	lwu t6, 36(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 36(a3)
	add t1, t1, t5
	add t1, t1, a5
	xor t6, t3, t4
	xor t6, t6, t0
	add t1, t1, t6
	srli t6, t2, 27
	add t1, t1, t6
	srli t3, t3, 2
	slli t1, t1, 32
	srli t6, t1, 32
	or t1, t1, t6
	lwu t5, 28(a3)
	lwu t6, 8(a3)
	xor t5, t5, t6
	lwu t6, 48(a3)
	xor t5, t5, t6
	lwu t6, 40(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 40(a3)
	add t0, t0, t5
	add t0, t0, a5
	xor t6, t2, t3
	xor t6, t6, t4
	add t0, t0, t6
	srli t6, t1, 27
	add t0, t0, t6
	srli t2, t2, 2
	slli t0, t0, 32
	srli t6, t0, 32
	or t0, t0, t6
	lwu t5, 32(a3)
	lwu t6, 12(a3)
	xor t5, t5, t6
	lwu t6, 52(a3)
	xor t5, t5, t6
	lwu t6, 44(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 44(a3)
	add t4, t4, t5
	add t4, t4, a5
	xor t6, t1, t2
	xor t6, t6, t3
	add t4, t4, t6
	srli t6, t0, 27
	add t4, t4, t6
	srli t1, t1, 2
	slli t4, t4, 32
	srli t6, t4, 32
	or t4, t4, t6
	lwu t5, 36(a3)
	lwu t6, 16(a3)
	xor t5, t5, t6
	lwu t6, 56(a3)
	xor t5, t5, t6
	lwu t6, 48(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 48(a3)
	add t3, t3, t5
	add t3, t3, a5
	xor t6, t0, t1
	xor t6, t6, t2
	add t3, t3, t6
	srli t6, t4, 27
	add t3, t3, t6
	srli t0, t0, 2
	slli t3, t3, 32
	srli t6, t3, 32
	or t3, t3, t6
	lwu t5, 40(a3)
	lwu t6, 20(a3)
	xor t5, t5, t6
	lwu t6, 60(a3)
	xor t5, t5, t6
	lwu t6, 52(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 52(a3)
	add t2, t2, t5
	add t2, t2, a5
	xor t6, t4, t0
	xor t6, t6, t1
	add t2, t2, t6
	srli t6, t3, 27
	add t2, t2, t6
	srli t4, t4, 2
	slli t2, t2, 32
	srli t6, t2, 32
	or t2, t2, t6
	lwu t5, 44(a3)
	lwu t6, 24(a3)
	xor t5, t5, t6
	lwu t6, 0(a3)
	xor t5, t5, t6
	lwu t6, 56(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 56(a3)
	add t1, t1, t5
	add t1, t1, a5
	xor t6, t3, t4
	xor t6, t6, t0
	add t1, t1, t6
	srli t6, t2, 27
	add t1, t1, t6
	srli t3, t3, 2
	slli t1, t1, 32
	srli t6, t1, 32
	or t1, t1, t6
	lwu t5, 48(a3)
	lwu t6, 28(a3)
	xor t5, t5, t6
	lwu t6, 4(a3)
	xor t5, t5, t6
	lwu t6, 60(a3)
	xor t5, t5, t6
	slliw t6, t5, 1
	srliw t5, t5, 31
	or t5, t5, t6
	sw t5, 60(a3)
	add t0, t0, t5
	add t0, t0, a5
	xor t6, t2, t3
	xor t6, t6, t4
	add t0, t0, t6
	srli t6, t1, 27
	add t0, t0, t6
	srli t2, t2, 2
	slli t0, t0, 32
	srli t6, t0, 32
	or t0, t0, t6
	lbu t5, 0(a0)
	lbu t6, 1(a0)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 2(a0)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 3(a0)
	slli t6, t6, 24
	or t5, t5, t6
	add t0, t0, t5
	sb t0, 0(a0)
	srli t5, t0, 8
	sb t5, 1(a0)
	srli t5, t0, 16
	sb t5, 2(a0)
	srli t5, t0, 24
	sb t5, 3(a0)
	lbu t5, 4(a0)
	lbu t6, 5(a0)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 6(a0)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 7(a0)
	slli t6, t6, 24
	or t5, t5, t6
	add t1, t1, t5
	sb t1, 4(a0)
	srli t5, t1, 8
	sb t5, 5(a0)
	srli t5, t1, 16
	sb t5, 6(a0)
	srli t5, t1, 24
	sb t5, 7(a0)
	lbu t5, 8(a0)
	lbu t6, 9(a0)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 10(a0)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 11(a0)
	slli t6, t6, 24
	or t5, t5, t6
	add t2, t2, t5
	sb t2, 8(a0)
	srli t5, t2, 8
	sb t5, 9(a0)
	srli t5, t2, 16
	sb t5, 10(a0)
	srli t5, t2, 24
	sb t5, 11(a0)
	lbu t5, 12(a0)
	lbu t6, 13(a0)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 14(a0)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 15(a0)
	slli t6, t6, 24
	or t5, t5, t6
	add t3, t3, t5
	sb t3, 12(a0)
	srli t5, t3, 8
	sb t5, 13(a0)
	srli t5, t3, 16
	sb t5, 14(a0)
	srli t5, t3, 24
	sb t5, 15(a0)
	lbu t5, 16(a0)
	lbu t6, 17(a0)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 18(a0)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 19(a0)
	slli t6, t6, 24
	or t5, t5, t6
	add t4, t4, t5
	sb t4, 16(a0)
	srli t5, t4, 8
	sb t5, 17(a0)
	srli t5, t4, 16
	sb t5, 18(a0)
	srli t5, t4, 24
	sb t5, 19(a0)
	addi a1, a1, 64
	addi a2, a2, -1
	bnez a2, 22b
	j 21f
20:
21:
	ret
	.option pop

vg_sha1_init:
	.option push
	.option arch, +m, +c
	lui t0, 422994
	addiw t0, t0, 769
	sb t0, 0(a0)
	srli t1, t0, 8
	sb t1, 1(a0)
	srli t1, t0, 16
	sb t1, 2(a0)
	srli t1, t0, 24
	sb t1, 3(a0)
	lui t0, 982235
	addiw t0, t0, -1143
	sb t0, 4(a0)
	srli t1, t0, 8
	sb t1, 5(a0)
	srli t1, t0, 16
	sb t1, 6(a0)
	srli t1, t0, 24
	sb t1, 7(a0)
	lui t0, 625582
	addiw t0, t0, -770
	sb t0, 8(a0)
	srli t1, t0, 8
	sb t1, 9(a0)
	srli t1, t0, 16
	sb t1, 10(a0)
	srli t1, t0, 24
	sb t1, 11(a0)
	lui t0, 66341
	addiw t0, t0, 1142
	sb t0, 12(a0)
	srli t1, t0, 8
	sb t1, 13(a0)
	srli t1, t0, 16
	sb t1, 14(a0)
	srli t1, t0, 24
	sb t1, 15(a0)
	lui t0, 802094
	addiw t0, t0, 496
	sb t0, 16(a0)
	srli t1, t0, 8
	sb t1, 17(a0)
	srli t1, t0, 16
	sb t1, 18(a0)
	srli t1, t0, 24
	sb t1, 19(a0)
	ret
	.option pop

vg_sha1_update:
	.option push
	.option arch, +m, +c
	addi sp, sp, -144
	addi t0, sp, 0
	sd ra, 80(t0)
	sd s1, 88(t0)
	sd s2, 96(t0)
	sd s3, 104(t0)
	sd s4, 112(t0)
	sd s5, 120(t0)
	sd s6, 128(t0)
	addi s1, a0, 0
	addi s2, t0, 0
	addi s3, a2, 0
	addi s4, a3, 0
	andi s5, a1, 63
	beqz s4, 20f
22:
	addi t0, zero, 0
	beqz s5, 23f
	addi t2, zero, 64
	sub t2, t2, s5
	srli t1, s4, 6
	beqz t1, 25f
	j 26f
25:
	add t1, s4, s5
	srli t1, t1, 6
	beqz t1, 27f
	j 28f
27:
	addi t2, s4, 0
28:
26:
	sub s4, s4, t2
29:
	lbu t1, 0(s3)
	add t3, s1, s5
	sb t1, 20(t3)
	addi s3, s3, 1
	addi s5, s5, 1
	addi t2, t2, -1
	bnez t2, 29b
	addi t1, s5, -64
	beqz t1, 210f
	j 211f
210:
	addi a1, s1, 20
	addi s5, zero, 0
	addi t0, zero, 1
211:
	j 24f
23:
	srli t1, s4, 6
	beqz t1, 212f
	addi a1, s3, 0
	addi s3, s3, 64
	addi s4, s4, -64
	addi t0, zero, 1
	j 213f
212:
	addi t2, zero, 64
	sub t2, t2, s5
	srli t1, s4, 6
	beqz t1, 214f
	j 215f
214:
	add t1, s4, s5
	srli t1, t1, 6
	beqz t1, 216f
	j 217f
216:
	addi t2, s4, 0
217:
215:
	sub s4, s4, t2
218:
	lbu t1, 0(s3)
	add t3, s1, s5
	sb t1, 20(t3)
	addi s3, s3, 1
	addi s5, s5, 1
	addi t2, t2, -1
	bnez t2, 218b
	addi t1, s5, -64
	beqz t1, 219f
	j 220f
219:
	addi a1, s1, 20
	addi s5, zero, 0
	addi t0, zero, 1
220:
213:
24:
	beqz t0, 221f
	addi a0, s1, 0
	addi a2, zero, 1
	addi a3, s2, 0
	call {vg_sha1_compress}
	j 222f
221:
222:
	bnez s4, 22b
	j 21f
20:
21:
	ld ra, 80(s2)
	ld s1, 88(s2)
	ld s3, 104(s2)
	ld s4, 112(s2)
	ld s5, 120(s2)
	ld s6, 128(s2)
	ld s2, 96(s2)
	addi sp, sp, 144
	ret
	.option pop

vg_sha1_finalize:
	.option push
	.option arch, +m, +c
	addi sp, sp, -144
	addi t0, sp, 0
	sd ra, 80(t0)
	sd s1, 88(t0)
	sd s2, 96(t0)
	sd s3, 104(t0)
	sd s4, 112(t0)
	sd s5, 120(t0)
	sd s6, 128(t0)
	addi s1, a0, 0
	addi s2, t0, 0
	addi s3, a2, 0
	addi s4, a1, 0
	andi s5, s4, 63
	addi t1, zero, 128
	add t3, s1, s5
	sb t1, 20(t3)
	addi s5, s5, 1
	addi s6, s5, 7
	srli s6, s6, 6
20:
	addi t2, zero, 64
	beqz s6, 21f
	j 22f
21:
	addi t2, zero, 56
22:
	addi t1, zero, 0
	sub t2, t2, s5
	beqz t2, 23f
25:
	add t3, s1, s5
	sb t1, 20(t3)
	addi s5, s5, 1
	addi t2, t2, -1
	bnez t2, 25b
	j 24f
23:
24:
	beqz s6, 26f
	j 27f
26:
	slli t1, s4, 3
	srli t3, t1, 56
	sb t3, 76(s1)
	srli t3, t1, 48
	sb t3, 77(s1)
	srli t3, t1, 40
	sb t3, 78(s1)
	srli t3, t1, 32
	sb t3, 79(s1)
	srli t3, t1, 24
	sb t3, 80(s1)
	srli t3, t1, 16
	sb t3, 81(s1)
	srli t3, t1, 8
	sb t3, 82(s1)
	srli t3, t1, 0
	sb t3, 83(s1)
27:
	addi a1, s1, 20
	addi a0, s1, 0
	addi a2, zero, 1
	addi a3, s2, 0
	call {vg_sha1_compress}
	addi s5, zero, 0
	addi s6, s6, -1
	beqz s6, 20b
	lbu t1, 0(s1)
	lbu t2, 1(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 2(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 3(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 0(s3)
	srli t2, t1, 16
	sb t2, 1(s3)
	srli t2, t1, 8
	sb t2, 2(s3)
	srli t2, t1, 0
	sb t2, 3(s3)
	lbu t1, 4(s1)
	lbu t2, 5(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 6(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 7(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 4(s3)
	srli t2, t1, 16
	sb t2, 5(s3)
	srli t2, t1, 8
	sb t2, 6(s3)
	srli t2, t1, 0
	sb t2, 7(s3)
	lbu t1, 8(s1)
	lbu t2, 9(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 10(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 11(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 8(s3)
	srli t2, t1, 16
	sb t2, 9(s3)
	srli t2, t1, 8
	sb t2, 10(s3)
	srli t2, t1, 0
	sb t2, 11(s3)
	lbu t1, 12(s1)
	lbu t2, 13(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 14(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 15(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 12(s3)
	srli t2, t1, 16
	sb t2, 13(s3)
	srli t2, t1, 8
	sb t2, 14(s3)
	srli t2, t1, 0
	sb t2, 15(s3)
	lbu t1, 16(s1)
	lbu t2, 17(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 18(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 19(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 16(s3)
	srli t2, t1, 16
	sb t2, 17(s3)
	srli t2, t1, 8
	sb t2, 18(s3)
	srli t2, t1, 0
	sb t2, 19(s3)
	ld ra, 80(s2)
	ld s1, 88(s2)
	ld s3, 104(s2)
	ld s4, 112(s2)
	ld s5, 120(s2)
	ld s6, 128(s2)
	ld s2, 96(s2)
	addi sp, sp, 144
	ret
	.option pop
