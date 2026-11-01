// The functions of `src/internal/vg_sha1_compress.rs` of `verified-garbage-asm-riscv64`, as text: generated from
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
