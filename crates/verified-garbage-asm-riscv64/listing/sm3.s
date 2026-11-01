// The functions of `src/sm3.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sm3_compress:
	.option push
	.option arch, +m, +c
	addi a3, a3, 7
	andi a3, a3, -8
	sd s0, 64(a3)
	beqz a2, 20f
22:
	lbu t0, 0(a0)
	lbu a5, 1(a0)
	slli a5, a5, 8
	or t0, t0, a5
	lbu a5, 2(a0)
	slli a5, a5, 16
	or t0, t0, a5
	lbu a5, 3(a0)
	slli a5, a5, 24
	or t0, t0, a5
	lbu t1, 4(a0)
	lbu a5, 5(a0)
	slli a5, a5, 8
	or t1, t1, a5
	lbu a5, 6(a0)
	slli a5, a5, 16
	or t1, t1, a5
	lbu a5, 7(a0)
	slli a5, a5, 24
	or t1, t1, a5
	lbu t2, 8(a0)
	lbu a5, 9(a0)
	slli a5, a5, 8
	or t2, t2, a5
	lbu a5, 10(a0)
	slli a5, a5, 16
	or t2, t2, a5
	lbu a5, 11(a0)
	slli a5, a5, 24
	or t2, t2, a5
	lbu t3, 12(a0)
	lbu a5, 13(a0)
	slli a5, a5, 8
	or t3, t3, a5
	lbu a5, 14(a0)
	slli a5, a5, 16
	or t3, t3, a5
	lbu a5, 15(a0)
	slli a5, a5, 24
	or t3, t3, a5
	lbu t4, 16(a0)
	lbu a5, 17(a0)
	slli a5, a5, 8
	or t4, t4, a5
	lbu a5, 18(a0)
	slli a5, a5, 16
	or t4, t4, a5
	lbu a5, 19(a0)
	slli a5, a5, 24
	or t4, t4, a5
	lbu t5, 20(a0)
	lbu a5, 21(a0)
	slli a5, a5, 8
	or t5, t5, a5
	lbu a5, 22(a0)
	slli a5, a5, 16
	or t5, t5, a5
	lbu a5, 23(a0)
	slli a5, a5, 24
	or t5, t5, a5
	lbu t6, 24(a0)
	lbu a5, 25(a0)
	slli a5, a5, 8
	or t6, t6, a5
	lbu a5, 26(a0)
	slli a5, a5, 16
	or t6, t6, a5
	lbu a5, 27(a0)
	slli a5, a5, 24
	or t6, t6, a5
	lbu a4, 28(a0)
	lbu a5, 29(a0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 30(a0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 31(a0)
	slli a5, a5, 24
	or a4, a4, a5
	lbu a5, 0(a1)
	slli a5, a5, 24
	lbu a6, 1(a1)
	slli a6, a6, 16
	or a5, a5, a6
	lbu a6, 2(a1)
	slli a6, a6, 8
	or a5, a5, a6
	lbu a6, 3(a1)
	or a5, a5, a6
	sw a5, 0(a3)
	lbu a5, 4(a1)
	slli a5, a5, 24
	lbu a6, 5(a1)
	slli a6, a6, 16
	or a5, a5, a6
	lbu a6, 6(a1)
	slli a6, a6, 8
	or a5, a5, a6
	lbu a6, 7(a1)
	or a5, a5, a6
	sw a5, 4(a3)
	lbu a5, 8(a1)
	slli a5, a5, 24
	lbu a6, 9(a1)
	slli a6, a6, 16
	or a5, a5, a6
	lbu a6, 10(a1)
	slli a6, a6, 8
	or a5, a5, a6
	lbu a6, 11(a1)
	or a5, a5, a6
	sw a5, 8(a3)
	lbu a5, 12(a1)
	slli a5, a5, 24
	lbu a6, 13(a1)
	slli a6, a6, 16
	or a5, a5, a6
	lbu a6, 14(a1)
	slli a6, a6, 8
	or a5, a5, a6
	lbu a6, 15(a1)
	or a5, a5, a6
	sw a5, 12(a3)
	lbu a5, 16(a1)
	slli a5, a5, 24
	lbu a6, 17(a1)
	slli a6, a6, 16
	or a5, a5, a6
	lbu a6, 18(a1)
	slli a6, a6, 8
	or a5, a5, a6
	lbu a6, 19(a1)
	or a5, a5, a6
	sw a5, 16(a3)
	slliw a6, t0, 12
	srliw a5, t0, 20
	or a5, a5, a6
	add a6, a5, t4
	lui a7, 498884
	addiw a7, a7, 1305
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add a4, a4, a6
	xor a5, a5, a6
	add t3, t3, a5
	lwu a7, 0(a3)
	add a4, a4, a7
	lwu s0, 16(a3)
	xor s0, a7, s0
	add t3, t3, s0
	xor a5, t0, t1
	xor a5, a5, t2
	add t3, t3, a5
	xor a5, t4, t5
	xor a5, a5, t6
	add a4, a4, a5
	slliw a5, t1, 9
	srliw t1, t1, 23
	or t1, t1, a5
	slliw a5, t5, 19
	srliw t5, t5, 13
	or t5, t5, a5
	slliw a6, a4, 9
	srliw a5, a4, 23
	or a5, a5, a6
	slliw a7, a4, 17
	srliw a6, a4, 15
	or a6, a6, a7
	xor a4, a4, a5
	xor a4, a4, a6
	lbu a5, 20(a1)
	slli a5, a5, 24
	lbu a6, 21(a1)
	slli a6, a6, 16
	or a5, a5, a6
	lbu a6, 22(a1)
	slli a6, a6, 8
	or a5, a5, a6
	lbu a6, 23(a1)
	or a5, a5, a6
	sw a5, 20(a3)
	slliw a6, t3, 12
	srliw a5, t3, 20
	or a5, a5, a6
	add a6, a5, a4
	lui a7, 997769
	addiw a7, a7, -1486
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add t6, t6, a6
	xor a5, a5, a6
	add t2, t2, a5
	lwu a7, 4(a3)
	add t6, t6, a7
	lwu s0, 20(a3)
	xor s0, a7, s0
	add t2, t2, s0
	xor a5, t3, t0
	xor a5, a5, t1
	add t2, t2, a5
	xor a5, a4, t4
	xor a5, a5, t5
	add t6, t6, a5
	slliw a5, t0, 9
	srliw t0, t0, 23
	or t0, t0, a5
	slliw a5, t4, 19
	srliw t4, t4, 13
	or t4, t4, a5
	slliw a6, t6, 9
	srliw a5, t6, 23
	or a5, a5, a6
	slliw a7, t6, 17
	srliw a6, t6, 15
	or a6, a6, a7
	xor t6, t6, a5
	xor t6, t6, a6
	lbu a5, 24(a1)
	slli a5, a5, 24
	lbu a6, 25(a1)
	slli a6, a6, 16
	or a5, a5, a6
	lbu a6, 26(a1)
	slli a6, a6, 8
	or a5, a5, a6
	lbu a6, 27(a1)
	or a5, a5, a6
	sw a5, 24(a3)
	slliw a6, t2, 12
	srliw a5, t2, 20
	or a5, a5, a6
	add a6, a5, t6
	lui a7, 946961
	addiw a7, a7, 1125
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add t5, t5, a6
	xor a5, a5, a6
	add t1, t1, a5
	lwu a7, 8(a3)
	add t5, t5, a7
	lwu s0, 24(a3)
	xor s0, a7, s0
	add t1, t1, s0
	xor a5, t2, t3
	xor a5, a5, t0
	add t1, t1, a5
	xor a5, t6, a4
	xor a5, a5, t4
	add t5, t5, a5
	slliw a5, t3, 9
	srliw t3, t3, 23
	or t3, t3, a5
	slliw a5, a4, 19
	srliw a4, a4, 13
	or a4, a4, a5
	slliw a6, t5, 9
	srliw a5, t5, 23
	or a5, a5, a6
	slliw a7, t5, 17
	srliw a6, t5, 15
	or a6, a6, a7
	xor t5, t5, a5
	xor t5, t5, a6
	lbu a5, 28(a1)
	slli a5, a5, 24
	lbu a6, 29(a1)
	slli a6, a6, 16
	or a5, a5, a6
	lbu a6, 30(a1)
	slli a6, a6, 8
	or a5, a5, a6
	lbu a6, 31(a1)
	or a5, a5, a6
	sw a5, 28(a3)
	slliw a6, t1, 12
	srliw a5, t1, 20
	or a5, a5, a6
	add a6, a5, t5
	lui a7, 845347
	addiw a7, a7, -1845
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add t4, t4, a6
	xor a5, a5, a6
	add t0, t0, a5
	lwu a7, 12(a3)
	add t4, t4, a7
	lwu s0, 28(a3)
	xor s0, a7, s0
	add t0, t0, s0
	xor a5, t1, t2
	xor a5, a5, t3
	add t0, t0, a5
	xor a5, t5, t6
	xor a5, a5, a4
	add t4, t4, a5
	slliw a5, t2, 9
	srliw t2, t2, 23
	or t2, t2, a5
	slliw a5, t6, 19
	srliw t6, t6, 13
	or t6, t6, a5
	slliw a6, t4, 9
	srliw a5, t4, 23
	or a5, a5, a6
	slliw a7, t4, 17
	srliw a6, t4, 15
	or a6, a6, a7
	xor t4, t4, a5
	xor t4, t4, a6
	lbu a5, 32(a1)
	slli a5, a5, 24
	lbu a6, 33(a1)
	slli a6, a6, 16
	or a5, a5, a6
	lbu a6, 34(a1)
	slli a6, a6, 8
	or a5, a5, a6
	lbu a6, 35(a1)
	or a5, a5, a6
	sw a5, 32(a3)
	slliw a6, t0, 12
	srliw a5, t0, 20
	or a5, a5, a6
	add a6, a5, t4
	lui a7, 642117
	addiw a7, a7, 407
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add a4, a4, a6
	xor a5, a5, a6
	add t3, t3, a5
	lwu a7, 16(a3)
	add a4, a4, a7
	lwu s0, 32(a3)
	xor s0, a7, s0
	add t3, t3, s0
	xor a5, t0, t1
	xor a5, a5, t2
	add t3, t3, a5
	xor a5, t4, t5
	xor a5, a5, t6
	add a4, a4, a5
	slliw a5, t1, 9
	srliw t1, t1, 23
	or t1, t1, a5
	slliw a5, t5, 19
	srliw t5, t5, 13
	or t5, t5, a5
	slliw a6, a4, 9
	srliw a5, a4, 23
	or a5, a5, a6
	slliw a7, a4, 17
	srliw a6, a4, 15
	or a6, a6, a7
	xor a4, a4, a5
	xor a4, a4, a6
	lbu a5, 36(a1)
	slli a5, a5, 24
	lbu a6, 37(a1)
	slli a6, a6, 16
	or a5, a5, a6
	lbu a6, 38(a1)
	slli a6, a6, 8
	or a5, a5, a6
	lbu a6, 39(a1)
	or a5, a5, a6
	sw a5, 36(a3)
	slliw a6, t3, 12
	srliw a5, t3, 20
	or a5, a5, a6
	add a6, a5, a4
	lui a7, 235658
	addiw a7, a7, 815
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add t6, t6, a6
	xor a5, a5, a6
	add t2, t2, a5
	lwu a7, 20(a3)
	add t6, t6, a7
	lwu s0, 36(a3)
	xor s0, a7, s0
	add t2, t2, s0
	xor a5, t3, t0
	xor a5, a5, t1
	add t2, t2, a5
	xor a5, a4, t4
	xor a5, a5, t5
	add t6, t6, a5
	slliw a5, t0, 9
	srliw t0, t0, 23
	or t0, t0, a5
	slliw a5, t4, 19
	srliw t4, t4, 13
	or t4, t4, a5
	slliw a6, t6, 9
	srliw a5, t6, 23
	or a5, a5, a6
	slliw a7, t6, 17
	srliw a6, t6, 15
	or a6, a6, a7
	xor t6, t6, a5
	xor t6, t6, a6
	lbu a5, 40(a1)
	slli a5, a5, 24
	lbu a6, 41(a1)
	slli a6, a6, 16
	or a5, a5, a6
	lbu a6, 42(a1)
	slli a6, a6, 8
	or a5, a5, a6
	lbu a6, 43(a1)
	or a5, a5, a6
	sw a5, 40(a3)
	slliw a6, t2, 12
	srliw a5, t2, 20
	or a5, a5, a6
	add a6, a5, t6
	lui a7, 471316
	addiw a7, a7, 1630
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add t5, t5, a6
	xor a5, a5, a6
	add t1, t1, a5
	lwu a7, 24(a3)
	add t5, t5, a7
	lwu s0, 40(a3)
	xor s0, a7, s0
	add t1, t1, s0
	xor a5, t2, t3
	xor a5, a5, t0
	add t1, t1, a5
	xor a5, t6, a4
	xor a5, a5, t4
	add t5, t5, a5
	slliw a5, t3, 9
	srliw t3, t3, 23
	or t3, t3, a5
	slliw a5, a4, 19
	srliw a4, a4, 13
	or a4, a4, a5
	slliw a6, t5, 9
	srliw a5, t5, 23
	or a5, a5, a6
	slliw a7, t5, 17
	srliw a6, t5, 15
	or a6, a6, a7
	xor t5, t5, a5
	xor t5, t5, a6
	lbu a5, 44(a1)
	slli a5, a5, 24
	lbu a6, 45(a1)
	slli a6, a6, 16
	or a5, a5, a6
	lbu a6, 46(a1)
	slli a6, a6, 8
	or a5, a5, a6
	lbu a6, 47(a1)
	or a5, a5, a6
	sw a5, 44(a3)
	slliw a6, t1, 12
	srliw a5, t1, 20
	or a5, a5, a6
	add a6, a5, t5
	lui a7, 942633
	addiw a7, a7, -836
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add t4, t4, a6
	xor a5, a5, a6
	add t0, t0, a5
	lwu a7, 28(a3)
	add t4, t4, a7
	lwu s0, 44(a3)
	xor s0, a7, s0
	add t0, t0, s0
	xor a5, t1, t2
	xor a5, a5, t3
	add t0, t0, a5
	xor a5, t5, t6
	xor a5, a5, a4
	add t4, t4, a5
	slliw a5, t2, 9
	srliw t2, t2, 23
	or t2, t2, a5
	slliw a5, t6, 19
	srliw t6, t6, 13
	or t6, t6, a5
	slliw a6, t4, 9
	srliw a5, t4, 23
	or a5, a5, a6
	slliw a7, t4, 17
	srliw a6, t4, 15
	or a6, a6, a7
	xor t4, t4, a5
	xor t4, t4, a6
	lbu a5, 48(a1)
	slli a5, a5, 24
	lbu a6, 49(a1)
	slli a6, a6, 16
	or a5, a5, a6
	lbu a6, 50(a1)
	slli a6, a6, 8
	or a5, a5, a6
	lbu a6, 51(a1)
	or a5, a5, a6
	sw a5, 48(a3)
	slliw a6, t0, 12
	srliw a5, t0, 20
	or a5, a5, a6
	add a6, a5, t4
	lui a7, 836690
	addiw a7, a7, -1671
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add a4, a4, a6
	xor a5, a5, a6
	add t3, t3, a5
	lwu a7, 32(a3)
	add a4, a4, a7
	lwu s0, 48(a3)
	xor s0, a7, s0
	add t3, t3, s0
	xor a5, t0, t1
	xor a5, a5, t2
	add t3, t3, a5
	xor a5, t4, t5
	xor a5, a5, t6
	add a4, a4, a5
	slliw a5, t1, 9
	srliw t1, t1, 23
	or t1, t1, a5
	slliw a5, t5, 19
	srliw t5, t5, 13
	or t5, t5, a5
	slliw a6, a4, 9
	srliw a5, a4, 23
	or a5, a5, a6
	slliw a7, a4, 17
	srliw a6, a4, 15
	or a6, a6, a7
	xor a4, a4, a5
	xor a4, a4, a6
	lbu a5, 52(a1)
	slli a5, a5, 24
	lbu a6, 53(a1)
	slli a6, a6, 16
	or a5, a5, a6
	lbu a6, 54(a1)
	slli a6, a6, 8
	or a5, a5, a6
	lbu a6, 55(a1)
	or a5, a5, a6
	sw a5, 52(a3)
	slliw a6, t3, 12
	srliw a5, t3, 20
	or a5, a5, a6
	add a6, a5, a4
	lui a7, 624803
	addiw a7, a7, 755
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add t6, t6, a6
	xor a5, a5, a6
	add t2, t2, a5
	lwu a7, 36(a3)
	add t6, t6, a7
	lwu s0, 52(a3)
	xor s0, a7, s0
	add t2, t2, s0
	xor a5, t3, t0
	xor a5, a5, t1
	add t2, t2, a5
	xor a5, a4, t4
	xor a5, a5, t5
	add t6, t6, a5
	slliw a5, t0, 9
	srliw t0, t0, 23
	or t0, t0, a5
	slliw a5, t4, 19
	srliw t4, t4, 13
	or t4, t4, a5
	slliw a6, t6, 9
	srliw a5, t6, 23
	or a5, a5, a6
	slliw a7, t6, 17
	srliw a6, t6, 15
	or a6, a6, a7
	xor t6, t6, a5
	xor t6, t6, a6
	lbu a5, 56(a1)
	slli a5, a5, 24
	lbu a6, 57(a1)
	slli a6, a6, 16
	or a5, a5, a6
	lbu a6, 58(a1)
	slli a6, a6, 8
	or a5, a5, a6
	lbu a6, 59(a1)
	or a5, a5, a6
	sw a5, 56(a3)
	slliw a6, t2, 12
	srliw a5, t2, 20
	or a5, a5, a6
	add a6, a5, t6
	lui a7, 201030
	addiw a7, a7, 1511
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add t5, t5, a6
	xor a5, a5, a6
	add t1, t1, a5
	lwu a7, 40(a3)
	add t5, t5, a7
	lwu s0, 56(a3)
	xor s0, a7, s0
	add t1, t1, s0
	xor a5, t2, t3
	xor a5, a5, t0
	add t1, t1, a5
	xor a5, t6, a4
	xor a5, a5, t4
	add t5, t5, a5
	slliw a5, t3, 9
	srliw t3, t3, 23
	or t3, t3, a5
	slliw a5, a4, 19
	srliw a4, a4, 13
	or a4, a4, a5
	slliw a6, t5, 9
	srliw a5, t5, 23
	or a5, a5, a6
	slliw a7, t5, 17
	srliw a6, t5, 15
	or a6, a6, a7
	xor t5, t5, a5
	xor t5, t5, a6
	lbu a5, 60(a1)
	slli a5, a5, 24
	lbu a6, 61(a1)
	slli a6, a6, 16
	or a5, a5, a6
	lbu a6, 62(a1)
	slli a6, a6, 8
	or a5, a5, a6
	lbu a6, 63(a1)
	or a5, a5, a6
	sw a5, 60(a3)
	slliw a6, t1, 12
	srliw a5, t1, 20
	or a5, a5, a6
	add a6, a5, t5
	lui a7, 402061
	addiw a7, a7, -1074
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add t4, t4, a6
	xor a5, a5, a6
	add t0, t0, a5
	lwu a7, 44(a3)
	add t4, t4, a7
	lwu s0, 60(a3)
	xor s0, a7, s0
	add t0, t0, s0
	xor a5, t1, t2
	xor a5, a5, t3
	add t0, t0, a5
	xor a5, t5, t6
	xor a5, a5, a4
	add t4, t4, a5
	slliw a5, t2, 9
	srliw t2, t2, 23
	or t2, t2, a5
	slliw a5, t6, 19
	srliw t6, t6, 13
	or t6, t6, a5
	slliw a6, t4, 9
	srliw a5, t4, 23
	or a5, a5, a6
	slliw a7, t4, 17
	srliw a6, t4, 15
	or a6, a6, a7
	xor t4, t4, a5
	xor t4, t4, a6
	lwu a5, 0(a3)
	lwu a6, 28(a3)
	xor a5, a5, a6
	lwu a6, 52(a3)
	slliw a7, a6, 15
	srliw a6, a6, 17
	or a6, a6, a7
	xor a5, a5, a6
	slliw a7, a5, 15
	srliw a6, a5, 17
	or a6, a6, a7
	slliw s0, a5, 23
	srliw a7, a5, 9
	or a7, a7, s0
	xor a5, a5, a6
	xor a5, a5, a7
	lwu a6, 12(a3)
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	xor a5, a5, a6
	lwu a6, 40(a3)
	xor a5, a5, a6
	sw a5, 0(a3)
	slliw a6, t0, 12
	srliw a5, t0, 20
	or a5, a5, a6
	add a6, a5, t4
	lui a7, 804121
	addiw a7, a7, 1948
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add a4, a4, a6
	xor a5, a5, a6
	add t3, t3, a5
	lwu a7, 48(a3)
	add a4, a4, a7
	lwu s0, 0(a3)
	xor s0, a7, s0
	add t3, t3, s0
	xor a5, t0, t1
	xor a5, a5, t2
	add t3, t3, a5
	xor a5, t4, t5
	xor a5, a5, t6
	add a4, a4, a5
	slliw a5, t1, 9
	srliw t1, t1, 23
	or t1, t1, a5
	slliw a5, t5, 19
	srliw t5, t5, 13
	or t5, t5, a5
	slliw a6, a4, 9
	srliw a5, a4, 23
	or a5, a5, a6
	slliw a7, a4, 17
	srliw a6, a4, 15
	or a6, a6, a7
	xor a4, a4, a5
	xor a4, a4, a6
	lwu a5, 4(a3)
	lwu a6, 32(a3)
	xor a5, a5, a6
	lwu a6, 56(a3)
	slliw a7, a6, 15
	srliw a6, a6, 17
	or a6, a6, a7
	xor a5, a5, a6
	slliw a7, a5, 15
	srliw a6, a5, 17
	or a6, a6, a7
	slliw s0, a5, 23
	srliw a7, a5, 9
	or a7, a7, s0
	xor a5, a5, a6
	xor a5, a5, a7
	lwu a6, 16(a3)
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	xor a5, a5, a6
	lwu a6, 44(a3)
	xor a5, a5, a6
	sw a5, 4(a3)
	slliw a6, t3, 12
	srliw a5, t3, 20
	or a5, a5, a6
	add a6, a5, a4
	lui a7, 559667
	addiw a7, a7, -199
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add t6, t6, a6
	xor a5, a5, a6
	add t2, t2, a5
	lwu a7, 52(a3)
	add t6, t6, a7
	lwu s0, 4(a3)
	xor s0, a7, s0
	add t2, t2, s0
	xor a5, t3, t0
	xor a5, a5, t1
	add t2, t2, a5
	xor a5, a4, t4
	xor a5, a5, t5
	add t6, t6, a5
	slliw a5, t0, 9
	srliw t0, t0, 23
	or t0, t0, a5
	slliw a5, t4, 19
	srliw t4, t4, 13
	or t4, t4, a5
	slliw a6, t6, 9
	srliw a5, t6, 23
	or a5, a5, a6
	slliw a7, t6, 17
	srliw a6, t6, 15
	or a6, a6, a7
	xor t6, t6, a5
	xor t6, t6, a6
	lwu a5, 8(a3)
	lwu a6, 36(a3)
	xor a5, a5, a6
	lwu a6, 60(a3)
	slliw a7, a6, 15
	srliw a6, a6, 17
	or a6, a6, a7
	xor a5, a5, a6
	slliw a7, a5, 15
	srliw a6, a5, 17
	or a6, a6, a7
	slliw s0, a5, 23
	srliw a7, a5, 9
	or a7, a7, s0
	xor a5, a5, a6
	xor a5, a5, a7
	lwu a6, 20(a3)
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	xor a5, a5, a6
	lwu a6, 48(a3)
	xor a5, a5, a6
	sw a5, 8(a3)
	slliw a6, t2, 12
	srliw a5, t2, 20
	or a5, a5, a6
	add a6, a5, t6
	lui a7, 70758
	addiw a7, a7, -397
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add t5, t5, a6
	xor a5, a5, a6
	add t1, t1, a5
	lwu a7, 56(a3)
	add t5, t5, a7
	lwu s0, 8(a3)
	xor s0, a7, s0
	add t1, t1, s0
	xor a5, t2, t3
	xor a5, a5, t0
	add t1, t1, a5
	xor a5, t6, a4
	xor a5, a5, t4
	add t5, t5, a5
	slliw a5, t3, 9
	srliw t3, t3, 23
	or t3, t3, a5
	slliw a5, a4, 19
	srliw a4, a4, 13
	or a4, a4, a5
	slliw a6, t5, 9
	srliw a5, t5, 23
	or a5, a5, a6
	slliw a7, t5, 17
	srliw a6, t5, 15
	or a6, a6, a7
	xor t5, t5, a5
	xor t5, t5, a6
	lwu a5, 12(a3)
	lwu a6, 40(a3)
	xor a5, a5, a6
	lwu a6, 0(a3)
	slliw a7, a6, 15
	srliw a6, a6, 17
	or a6, a6, a7
	xor a5, a5, a6
	slliw a7, a5, 15
	srliw a6, a5, 17
	or a6, a6, a7
	slliw s0, a5, 23
	srliw a7, a5, 9
	or a7, a7, s0
	xor a5, a5, a6
	xor a5, a5, a7
	lwu a6, 24(a3)
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	xor a5, a5, a6
	lwu a6, 52(a3)
	xor a5, a5, a6
	sw a5, 12(a3)
	slliw a6, t1, 12
	srliw a5, t1, 20
	or a5, a5, a6
	add a6, a5, t5
	lui a7, 141516
	addiw a7, a7, -794
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add t4, t4, a6
	xor a5, a5, a6
	add t0, t0, a5
	lwu a7, 60(a3)
	add t4, t4, a7
	lwu s0, 12(a3)
	xor s0, a7, s0
	add t0, t0, s0
	xor a5, t1, t2
	xor a5, a5, t3
	add t0, t0, a5
	xor a5, t5, t6
	xor a5, a5, a4
	add t4, t4, a5
	slliw a5, t2, 9
	srliw t2, t2, 23
	or t2, t2, a5
	slliw a5, t6, 19
	srliw t6, t6, 13
	or t6, t6, a5
	slliw a6, t4, 9
	srliw a5, t4, 23
	or a5, a5, a6
	slliw a7, t4, 17
	srliw a6, t4, 15
	or a6, a6, a7
	xor t4, t4, a5
	xor t4, t4, a6
	lwu a5, 16(a3)
	lwu a6, 44(a3)
	xor a5, a5, a6
	lwu a6, 4(a3)
	slliw a7, a6, 15
	srliw a6, a6, 17
	or a6, a6, a7
	xor a5, a5, a6
	slliw a7, a5, 15
	srliw a6, a5, 17
	or a6, a6, a7
	slliw s0, a5, 23
	srliw a7, a5, 9
	or a7, a7, s0
	xor a5, a5, a6
	xor a5, a5, a7
	lwu a6, 28(a3)
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	xor a5, a5, a6
	lwu a6, 56(a3)
	xor a5, a5, a6
	sw a5, 16(a3)
	slliw a6, t0, 12
	srliw a5, t0, 20
	or a5, a5, a6
	add a6, a5, t4
	lui a7, 645288
	addiw a7, a7, -1401
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add a4, a4, a6
	xor a5, a5, a6
	add t3, t3, a5
	lwu a7, 0(a3)
	add a4, a4, a7
	lwu s0, 16(a3)
	xor s0, a7, s0
	add t3, t3, s0
	or a5, t0, t1
	and a5, a5, t2
	and a6, t0, t1
	or a5, a5, a6
	add t3, t3, a5
	xor a5, t5, t6
	and a5, a5, t4
	xor a5, a5, t6
	add a4, a4, a5
	slliw a5, t1, 9
	srliw t1, t1, 23
	or t1, t1, a5
	slliw a5, t5, 19
	srliw t5, t5, 13
	or t5, t5, a5
	slliw a6, a4, 9
	srliw a5, a4, 23
	or a5, a5, a6
	slliw a7, a4, 17
	srliw a6, a4, 15
	or a6, a6, a7
	xor a4, a4, a5
	xor a4, a4, a6
	lwu a5, 20(a3)
	lwu a6, 48(a3)
	xor a5, a5, a6
	lwu a6, 8(a3)
	slliw a7, a6, 15
	srliw a6, a6, 17
	or a6, a6, a7
	xor a5, a5, a6
	slliw a7, a5, 15
	srliw a6, a5, 17
	or a6, a6, a7
	slliw s0, a5, 23
	srliw a7, a5, 9
	or a7, a7, s0
	xor a5, a5, a6
	xor a5, a5, a7
	lwu a6, 32(a3)
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	xor a5, a5, a6
	lwu a6, 60(a3)
	xor a5, a5, a6
	sw a5, 20(a3)
	slliw a6, t3, 12
	srliw a5, t3, 20
	or a5, a5, a6
	add a6, a5, a4
	lui a7, 241999
	addiw a7, a7, 1295
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add t6, t6, a6
	xor a5, a5, a6
	add t2, t2, a5
	lwu a7, 4(a3)
	add t6, t6, a7
	lwu s0, 20(a3)
	xor s0, a7, s0
	add t2, t2, s0
	or a5, t3, t0
	and a5, a5, t1
	and a6, t3, t0
	or a5, a5, a6
	add t2, t2, a5
	xor a5, t4, t5
	and a5, a5, a4
	xor a5, a5, t5
	add t6, t6, a5
	slliw a5, t0, 9
	srliw t0, t0, 23
	or t0, t0, a5
	slliw a5, t4, 19
	srliw t4, t4, 13
	or t4, t4, a5
	slliw a6, t6, 9
	srliw a5, t6, 23
	or a5, a5, a6
	slliw a7, t6, 17
	srliw a6, t6, 15
	or a6, a6, a7
	xor t6, t6, a5
	xor t6, t6, a6
	lwu a5, 24(a3)
	lwu a6, 52(a3)
	xor a5, a5, a6
	lwu a6, 12(a3)
	slliw a7, a6, 15
	srliw a6, a6, 17
	or a6, a6, a7
	xor a5, a5, a6
	slliw a7, a5, 15
	srliw a6, a5, 17
	or a6, a6, a7
	slliw s0, a5, 23
	srliw a7, a5, 9
	or a7, a7, s0
	xor a5, a5, a6
	xor a5, a5, a7
	lwu a6, 36(a3)
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	xor a5, a5, a6
	lwu a6, 0(a3)
	xor a5, a5, a6
	sw a5, 24(a3)
	slliw a6, t2, 12
	srliw a5, t2, 20
	or a5, a5, a6
	add a6, a5, t6
	lui a7, 483999
	addiw a7, a7, -1506
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add t5, t5, a6
	xor a5, a5, a6
	add t1, t1, a5
	lwu a7, 8(a3)
	add t5, t5, a7
	lwu s0, 24(a3)
	xor s0, a7, s0
	add t1, t1, s0
	or a5, t2, t3
	and a5, a5, t0
	and a6, t2, t3
	or a5, a5, a6
	add t1, t1, a5
	xor a5, a4, t4
	and a5, a5, t6
	xor a5, a5, t4
	add t5, t5, a5
	slliw a5, t3, 9
	srliw t3, t3, 23
	or t3, t3, a5
	slliw a5, a4, 19
	srliw a4, a4, 13
	or a4, a4, a5
	slliw a6, t5, 9
	srliw a5, t5, 23
	or a5, a5, a6
	slliw a7, t5, 17
	srliw a6, t5, 15
	or a6, a6, a7
	xor t5, t5, a5
	xor t5, t5, a6
	lwu a5, 28(a3)
	lwu a6, 56(a3)
	xor a5, a5, a6
	lwu a6, 16(a3)
	slliw a7, a6, 15
	srliw a6, a6, 17
	or a6, a6, a7
	xor a5, a5, a6
	slliw a7, a5, 15
	srliw a6, a5, 17
	or a6, a6, a7
	slliw s0, a5, 23
	srliw a7, a5, 9
	or a7, a7, s0
	xor a5, a5, a6
	xor a5, a5, a7
	lwu a6, 40(a3)
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	xor a5, a5, a6
	lwu a6, 4(a3)
	xor a5, a5, a6
	sw a5, 28(a3)
	slliw a6, t1, 12
	srliw a5, t1, 20
	or a5, a5, a6
	add a6, a5, t5
	lui a7, 967997
	addiw a7, a7, 1084
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add t4, t4, a6
	xor a5, a5, a6
	add t0, t0, a5
	lwu a7, 12(a3)
	add t4, t4, a7
	lwu s0, 28(a3)
	xor s0, a7, s0
	add t0, t0, s0
	or a5, t1, t2
	and a5, a5, t3
	and a6, t1, t2
	or a5, a5, a6
	add t0, t0, a5
	xor a5, t6, a4
	and a5, a5, t5
	xor a5, a5, a4
	add t4, t4, a5
	slliw a5, t2, 9
	srliw t2, t2, 23
	or t2, t2, a5
	slliw a5, t6, 19
	srliw t6, t6, 13
	or t6, t6, a5
	slliw a6, t4, 9
	srliw a5, t4, 23
	or a5, a5, a6
	slliw a7, t4, 17
	srliw a6, t4, 15
	or a6, a6, a7
	xor t4, t4, a5
	xor t4, t4, a6
	lwu a5, 32(a3)
	lwu a6, 60(a3)
	xor a5, a5, a6
	lwu a6, 20(a3)
	slliw a7, a6, 15
	srliw a6, a6, 17
	or a6, a6, a7
	xor a5, a5, a6
	slliw a7, a5, 15
	srliw a6, a5, 17
	or a6, a6, a7
	slliw s0, a5, 23
	srliw a7, a5, 9
	or a7, a7, s0
	xor a5, a5, a6
	xor a5, a5, a7
	lwu a6, 44(a3)
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	xor a5, a5, a6
	lwu a6, 8(a3)
	xor a5, a5, a6
	sw a5, 32(a3)
	slliw a6, t0, 12
	srliw a5, t0, 20
	or a5, a5, a6
	add a6, a5, t4
	lui a7, 887419
	addiw a7, a7, -1927
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add a4, a4, a6
	xor a5, a5, a6
	add t3, t3, a5
	lwu a7, 16(a3)
	add a4, a4, a7
	lwu s0, 32(a3)
	xor s0, a7, s0
	add t3, t3, s0
	or a5, t0, t1
	and a5, a5, t2
	and a6, t0, t1
	or a5, a5, a6
	add t3, t3, a5
	xor a5, t5, t6
	and a5, a5, t4
	xor a5, a5, t6
	add a4, a4, a5
	slliw a5, t1, 9
	srliw t1, t1, 23
	or t1, t1, a5
	slliw a5, t5, 19
	srliw t5, t5, 13
	or t5, t5, a5
	slliw a6, a4, 9
	srliw a5, a4, 23
	or a5, a5, a6
	slliw a7, a4, 17
	srliw a6, a4, 15
	or a6, a6, a7
	xor a4, a4, a5
	xor a4, a4, a6
	lwu a5, 36(a3)
	lwu a6, 0(a3)
	xor a5, a5, a6
	lwu a6, 24(a3)
	slliw a7, a6, 15
	srliw a6, a6, 17
	or a6, a6, a7
	xor a5, a5, a6
	slliw a7, a5, 15
	srliw a6, a5, 17
	or a6, a6, a7
	slliw s0, a5, 23
	srliw a7, a5, 9
	or a7, a7, s0
	xor a5, a5, a6
	xor a5, a5, a7
	lwu a6, 48(a3)
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	xor a5, a5, a6
	lwu a6, 12(a3)
	xor a5, a5, a6
	sw a5, 36(a3)
	slliw a6, t3, 12
	srliw a5, t3, 20
	or a5, a5, a6
	add a6, a5, a4
	lui a7, 726261
	addiw a7, a7, 243
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add t6, t6, a6
	xor a5, a5, a6
	add t2, t2, a5
	lwu a7, 20(a3)
	add t6, t6, a7
	lwu s0, 36(a3)
	xor s0, a7, s0
	add t2, t2, s0
	or a5, t3, t0
	and a5, a5, t1
	and a6, t3, t0
	or a5, a5, a6
	add t2, t2, a5
	xor a5, t4, t5
	and a5, a5, a4
	xor a5, a5, t5
	add t6, t6, a5
	slliw a5, t0, 9
	srliw t0, t0, 23
	or t0, t0, a5
	slliw a5, t4, 19
	srliw t4, t4, 13
	or t4, t4, a5
	slliw a6, t6, 9
	srliw a5, t6, 23
	or a5, a5, a6
	slliw a7, t6, 17
	srliw a6, t6, 15
	or a6, a6, a7
	xor t6, t6, a5
	xor t6, t6, a6
	lwu a5, 40(a3)
	lwu a6, 4(a3)
	xor a5, a5, a6
	lwu a6, 28(a3)
	slliw a7, a6, 15
	srliw a6, a6, 17
	or a6, a6, a7
	xor a5, a5, a6
	slliw a7, a5, 15
	srliw a6, a5, 17
	or a6, a6, a7
	slliw s0, a5, 23
	srliw a7, a5, 9
	or a7, a7, s0
	xor a5, a5, a6
	xor a5, a5, a7
	lwu a6, 52(a3)
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	xor a5, a5, a6
	lwu a6, 16(a3)
	xor a5, a5, a6
	sw a5, 40(a3)
	slliw a6, t2, 12
	srliw a5, t2, 20
	or a5, a5, a6
	add a6, a5, t6
	lui a7, 403946
	addiw a7, a7, 487
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add t5, t5, a6
	xor a5, a5, a6
	add t1, t1, a5
	lwu a7, 24(a3)
	add t5, t5, a7
	lwu s0, 40(a3)
	xor s0, a7, s0
	add t1, t1, s0
	or a5, t2, t3
	and a5, a5, t0
	and a6, t2, t3
	or a5, a5, a6
	add t1, t1, a5
	xor a5, a4, t4
	and a5, a5, t6
	xor a5, a5, t4
	add t5, t5, a5
	slliw a5, t3, 9
	srliw t3, t3, 23
	or t3, t3, a5
	slliw a5, a4, 19
	srliw a4, a4, 13
	or a4, a4, a5
	slliw a6, t5, 9
	srliw a5, t5, 23
	or a5, a5, a6
	slliw a7, t5, 17
	srliw a6, t5, 15
	or a6, a6, a7
	xor t5, t5, a5
	xor t5, t5, a6
	lwu a5, 44(a3)
	lwu a6, 8(a3)
	xor a5, a5, a6
	lwu a6, 32(a3)
	slliw a7, a6, 15
	srliw a6, a6, 17
	or a6, a6, a7
	xor a5, a5, a6
	slliw a7, a5, 15
	srliw a6, a5, 17
	or a6, a6, a7
	slliw s0, a5, 23
	srliw a7, a5, 9
	or a7, a7, s0
	xor a5, a5, a6
	xor a5, a5, a7
	lwu a6, 56(a3)
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	xor a5, a5, a6
	lwu a6, 20(a3)
	xor a5, a5, a6
	sw a5, 44(a3)
	slliw a6, t1, 12
	srliw a5, t1, 20
	or a5, a5, a6
	add a6, a5, t5
	lui a7, 807892
	addiw a7, a7, 974
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add t4, t4, a6
	xor a5, a5, a6
	add t0, t0, a5
	lwu a7, 28(a3)
	add t4, t4, a7
	lwu s0, 44(a3)
	xor s0, a7, s0
	add t0, t0, s0
	or a5, t1, t2
	and a5, a5, t3
	and a6, t1, t2
	or a5, a5, a6
	add t0, t0, a5
	xor a5, t6, a4
	and a5, a5, t5
	xor a5, a5, a4
	add t4, t4, a5
	slliw a5, t2, 9
	srliw t2, t2, 23
	or t2, t2, a5
	slliw a5, t6, 19
	srliw t6, t6, 13
	or t6, t6, a5
	slliw a6, t4, 9
	srliw a5, t4, 23
	or a5, a5, a6
	slliw a7, t4, 17
	srliw a6, t4, 15
	or a6, a6, a7
	xor t4, t4, a5
	xor t4, t4, a6
	lwu a5, 48(a3)
	lwu a6, 12(a3)
	xor a5, a5, a6
	lwu a6, 36(a3)
	slliw a7, a6, 15
	srliw a6, a6, 17
	or a6, a6, a7
	xor a5, a5, a6
	slliw a7, a5, 15
	srliw a6, a5, 17
	or a6, a6, a7
	slliw s0, a5, 23
	srliw a7, a5, 9
	or a7, a7, s0
	xor a5, a5, a6
	xor a5, a5, a7
	lwu a6, 60(a3)
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	xor a5, a5, a6
	lwu a6, 24(a3)
	xor a5, a5, a6
	sw a5, 48(a3)
	slliw a6, t0, 12
	srliw a5, t0, 20
	or a5, a5, a6
	add a6, a5, t4
	lui a7, 567208
	addiw a7, a7, 1949
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add a4, a4, a6
	xor a5, a5, a6
	add t3, t3, a5
	lwu a7, 32(a3)
	add a4, a4, a7
	lwu s0, 48(a3)
	xor s0, a7, s0
	add t3, t3, s0
	or a5, t0, t1
	and a5, a5, t2
	and a6, t0, t1
	or a5, a5, a6
	add t3, t3, a5
	xor a5, t5, t6
	and a5, a5, t4
	xor a5, a5, t6
	add a4, a4, a5
	slliw a5, t1, 9
	srliw t1, t1, 23
	or t1, t1, a5
	slliw a5, t5, 19
	srliw t5, t5, 13
	or t5, t5, a5
	slliw a6, a4, 9
	srliw a5, a4, 23
	or a5, a5, a6
	slliw a7, a4, 17
	srliw a6, a4, 15
	or a6, a6, a7
	xor a4, a4, a5
	xor a4, a4, a6
	lwu a5, 52(a3)
	lwu a6, 16(a3)
	xor a5, a5, a6
	lwu a6, 40(a3)
	slliw a7, a6, 15
	srliw a6, a6, 17
	or a6, a6, a7
	xor a5, a5, a6
	slliw a7, a5, 15
	srliw a6, a5, 17
	or a6, a6, a7
	slliw s0, a5, 23
	srliw a7, a5, 9
	or a7, a7, s0
	xor a5, a5, a6
	xor a5, a5, a7
	lwu a6, 0(a3)
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	xor a5, a5, a6
	lwu a6, 28(a3)
	xor a5, a5, a6
	sw a5, 52(a3)
	slliw a6, t3, 12
	srliw a5, t3, 20
	or a5, a5, a6
	add a6, a5, a4
	lui a7, 85841
	addiw a7, a7, -197
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add t6, t6, a6
	xor a5, a5, a6
	add t2, t2, a5
	lwu a7, 36(a3)
	add t6, t6, a7
	lwu s0, 52(a3)
	xor s0, a7, s0
	add t2, t2, s0
	or a5, t3, t0
	and a5, a5, t1
	and a6, t3, t0
	or a5, a5, a6
	add t2, t2, a5
	xor a5, t4, t5
	and a5, a5, a4
	xor a5, a5, t5
	add t6, t6, a5
	slliw a5, t0, 9
	srliw t0, t0, 23
	or t0, t0, a5
	slliw a5, t4, 19
	srliw t4, t4, 13
	or t4, t4, a5
	slliw a6, t6, 9
	srliw a5, t6, 23
	or a5, a5, a6
	slliw a7, t6, 17
	srliw a6, t6, 15
	or a6, a6, a7
	xor t6, t6, a5
	xor t6, t6, a6
	lwu a5, 56(a3)
	lwu a6, 20(a3)
	xor a5, a5, a6
	lwu a6, 44(a3)
	slliw a7, a6, 15
	srliw a6, a6, 17
	or a6, a6, a7
	xor a5, a5, a6
	slliw a7, a5, 15
	srliw a6, a5, 17
	or a6, a6, a7
	slliw s0, a5, 23
	srliw a7, a5, 9
	or a7, a7, s0
	xor a5, a5, a6
	xor a5, a5, a7
	lwu a6, 4(a3)
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	xor a5, a5, a6
	lwu a6, 32(a3)
	xor a5, a5, a6
	sw a5, 56(a3)
	slliw a6, t2, 12
	srliw a5, t2, 20
	or a5, a5, a6
	add a6, a5, t6
	lui a7, 171682
	addiw a7, a7, -394
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add t5, t5, a6
	xor a5, a5, a6
	add t1, t1, a5
	lwu a7, 40(a3)
	add t5, t5, a7
	lwu s0, 56(a3)
	xor s0, a7, s0
	add t1, t1, s0
	or a5, t2, t3
	and a5, a5, t0
	and a6, t2, t3
	or a5, a5, a6
	add t1, t1, a5
	xor a5, a4, t4
	and a5, a5, t6
	xor a5, a5, t4
	add t5, t5, a5
	slliw a5, t3, 9
	srliw t3, t3, 23
	or t3, t3, a5
	slliw a5, a4, 19
	srliw a4, a4, 13
	or a4, a4, a5
	slliw a6, t5, 9
	srliw a5, t5, 23
	or a5, a5, a6
	slliw a7, t5, 17
	srliw a6, t5, 15
	or a6, a6, a7
	xor t5, t5, a5
	xor t5, t5, a6
	lwu a5, 60(a3)
	lwu a6, 24(a3)
	xor a5, a5, a6
	lwu a6, 48(a3)
	slliw a7, a6, 15
	srliw a6, a6, 17
	or a6, a6, a7
	xor a5, a5, a6
	slliw a7, a5, 15
	srliw a6, a5, 17
	or a6, a6, a7
	slliw s0, a5, 23
	srliw a7, a5, 9
	or a7, a7, s0
	xor a5, a5, a6
	xor a5, a5, a7
	lwu a6, 8(a3)
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	xor a5, a5, a6
	lwu a6, 36(a3)
	xor a5, a5, a6
	sw a5, 60(a3)
	slliw a6, t1, 12
	srliw a5, t1, 20
	or a5, a5, a6
	add a6, a5, t5
	lui a7, 343364
	addiw a7, a7, -788
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add t4, t4, a6
	xor a5, a5, a6
	add t0, t0, a5
	lwu a7, 44(a3)
	add t4, t4, a7
	lwu s0, 60(a3)
	xor s0, a7, s0
	add t0, t0, s0
	or a5, t1, t2
	and a5, a5, t3
	and a6, t1, t2
	or a5, a5, a6
	add t0, t0, a5
	xor a5, t6, a4
	and a5, a5, t5
	xor a5, a5, a4
	add t4, t4, a5
	slliw a5, t2, 9
	srliw t2, t2, 23
	or t2, t2, a5
	slliw a5, t6, 19
	srliw t6, t6, 13
	or t6, t6, a5
	slliw a6, t4, 9
	srliw a5, t4, 23
	or a5, a5, a6
	slliw a7, t4, 17
	srliw a6, t4, 15
	or a6, a6, a7
	xor t4, t4, a5
	xor t4, t4, a6
	lwu a5, 0(a3)
	lwu a6, 28(a3)
	xor a5, a5, a6
	lwu a6, 52(a3)
	slliw a7, a6, 15
	srliw a6, a6, 17
	or a6, a6, a7
	xor a5, a5, a6
	slliw a7, a5, 15
	srliw a6, a5, 17
	or a6, a6, a7
	slliw s0, a5, 23
	srliw a7, a5, 9
	or a7, a7, s0
	xor a5, a5, a6
	xor a5, a5, a7
	lwu a6, 12(a3)
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	xor a5, a5, a6
	lwu a6, 40(a3)
	xor a5, a5, a6
	sw a5, 0(a3)
	slliw a6, t0, 12
	srliw a5, t0, 20
	or a5, a5, a6
	add a6, a5, t4
	lui a7, 686728
	addiw a7, a7, -1576
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add a4, a4, a6
	xor a5, a5, a6
	add t3, t3, a5
	lwu a7, 48(a3)
	add a4, a4, a7
	lwu s0, 0(a3)
	xor s0, a7, s0
	add t3, t3, s0
	or a5, t0, t1
	and a5, a5, t2
	and a6, t0, t1
	or a5, a5, a6
	add t3, t3, a5
	xor a5, t5, t6
	and a5, a5, t4
	xor a5, a5, t6
	add a4, a4, a5
	slliw a5, t1, 9
	srliw t1, t1, 23
	or t1, t1, a5
	slliw a5, t5, 19
	srliw t5, t5, 13
	or t5, t5, a5
	slliw a6, a4, 9
	srliw a5, a4, 23
	or a5, a5, a6
	slliw a7, a4, 17
	srliw a6, a4, 15
	or a6, a6, a7
	xor a4, a4, a5
	xor a4, a4, a6
	lwu a5, 4(a3)
	lwu a6, 32(a3)
	xor a5, a5, a6
	lwu a6, 56(a3)
	slliw a7, a6, 15
	srliw a6, a6, 17
	or a6, a6, a7
	xor a5, a5, a6
	slliw a7, a5, 15
	srliw a6, a5, 17
	or a6, a6, a7
	slliw s0, a5, 23
	srliw a7, a5, 9
	or a7, a7, s0
	xor a5, a5, a6
	xor a5, a5, a7
	lwu a6, 16(a3)
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	xor a5, a5, a6
	lwu a6, 44(a3)
	xor a5, a5, a6
	sw a5, 4(a3)
	slliw a6, t3, 12
	srliw a5, t3, 20
	or a5, a5, a6
	add a6, a5, a4
	lui a7, 324879
	addiw a7, a7, 945
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add t6, t6, a6
	xor a5, a5, a6
	add t2, t2, a5
	lwu a7, 52(a3)
	add t6, t6, a7
	lwu s0, 4(a3)
	xor s0, a7, s0
	add t2, t2, s0
	or a5, t3, t0
	and a5, a5, t1
	and a6, t3, t0
	or a5, a5, a6
	add t2, t2, a5
	xor a5, t4, t5
	and a5, a5, a4
	xor a5, a5, t5
	add t6, t6, a5
	slliw a5, t0, 9
	srliw t0, t0, 23
	or t0, t0, a5
	slliw a5, t4, 19
	srliw t4, t4, 13
	or t4, t4, a5
	slliw a6, t6, 9
	srliw a5, t6, 23
	or a5, a5, a6
	slliw a7, t6, 17
	srliw a6, t6, 15
	or a6, a6, a7
	xor t6, t6, a5
	xor t6, t6, a6
	lwu a5, 8(a3)
	lwu a6, 36(a3)
	xor a5, a5, a6
	lwu a6, 60(a3)
	slliw a7, a6, 15
	srliw a6, a6, 17
	or a6, a6, a7
	xor a5, a5, a6
	slliw a7, a5, 15
	srliw a6, a5, 17
	or a6, a6, a7
	slliw s0, a5, 23
	srliw a7, a5, 9
	or a7, a7, s0
	xor a5, a5, a6
	xor a5, a5, a7
	lwu a6, 20(a3)
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	xor a5, a5, a6
	lwu a6, 48(a3)
	xor a5, a5, a6
	sw a5, 8(a3)
	slliw a6, t2, 12
	srliw a5, t2, 20
	or a5, a5, a6
	add a6, a5, t6
	lui a7, 649758
	addiw a7, a7, 1890
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add t5, t5, a6
	xor a5, a5, a6
	add t1, t1, a5
	lwu a7, 56(a3)
	add t5, t5, a7
	lwu s0, 8(a3)
	xor s0, a7, s0
	add t1, t1, s0
	or a5, t2, t3
	and a5, a5, t0
	and a6, t2, t3
	or a5, a5, a6
	add t1, t1, a5
	xor a5, a4, t4
	and a5, a5, t6
	xor a5, a5, t4
	add t5, t5, a5
	slliw a5, t3, 9
	srliw t3, t3, 23
	or t3, t3, a5
	slliw a5, a4, 19
	srliw a4, a4, 13
	or a4, a4, a5
	slliw a6, t5, 9
	srliw a5, t5, 23
	or a5, a5, a6
	slliw a7, t5, 17
	srliw a6, t5, 15
	or a6, a6, a7
	xor t5, t5, a5
	xor t5, t5, a6
	lwu a5, 12(a3)
	lwu a6, 40(a3)
	xor a5, a5, a6
	lwu a6, 0(a3)
	slliw a7, a6, 15
	srliw a6, a6, 17
	or a6, a6, a7
	xor a5, a5, a6
	slliw a7, a5, 15
	srliw a6, a5, 17
	or a6, a6, a7
	slliw s0, a5, 23
	srliw a7, a5, 9
	or a7, a7, s0
	xor a5, a5, a6
	xor a5, a5, a7
	lwu a6, 24(a3)
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	xor a5, a5, a6
	lwu a6, 52(a3)
	xor a5, a5, a6
	sw a5, 12(a3)
	slliw a6, t1, 12
	srliw a5, t1, 20
	or a5, a5, a6
	add a6, a5, t5
	lui a7, 250941
	addiw a7, a7, -315
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add t4, t4, a6
	xor a5, a5, a6
	add t0, t0, a5
	lwu a7, 60(a3)
	add t4, t4, a7
	lwu s0, 12(a3)
	xor s0, a7, s0
	add t0, t0, s0
	or a5, t1, t2
	and a5, a5, t3
	and a6, t1, t2
	or a5, a5, a6
	add t0, t0, a5
	xor a5, t6, a4
	and a5, a5, t5
	xor a5, a5, a4
	add t4, t4, a5
	slliw a5, t2, 9
	srliw t2, t2, 23
	or t2, t2, a5
	slliw a5, t6, 19
	srliw t6, t6, 13
	or t6, t6, a5
	slliw a6, t4, 9
	srliw a5, t4, 23
	or a5, a5, a6
	slliw a7, t4, 17
	srliw a6, t4, 15
	or a6, a6, a7
	xor t4, t4, a5
	xor t4, t4, a6
	lwu a5, 16(a3)
	lwu a6, 44(a3)
	xor a5, a5, a6
	lwu a6, 4(a3)
	slliw a7, a6, 15
	srliw a6, a6, 17
	or a6, a6, a7
	xor a5, a5, a6
	slliw a7, a5, 15
	srliw a6, a5, 17
	or a6, a6, a7
	slliw s0, a5, 23
	srliw a7, a5, 9
	or a7, a7, s0
	xor a5, a5, a6
	xor a5, a5, a7
	lwu a6, 28(a3)
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	xor a5, a5, a6
	lwu a6, 56(a3)
	xor a5, a5, a6
	sw a5, 16(a3)
	slliw a6, t0, 12
	srliw a5, t0, 20
	or a5, a5, a6
	add a6, a5, t4
	lui a7, 501882
	addiw a7, a7, -630
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add a4, a4, a6
	xor a5, a5, a6
	add t3, t3, a5
	lwu a7, 0(a3)
	add a4, a4, a7
	lwu s0, 16(a3)
	xor s0, a7, s0
	add t3, t3, s0
	or a5, t0, t1
	and a5, a5, t2
	and a6, t0, t1
	or a5, a5, a6
	add t3, t3, a5
	xor a5, t5, t6
	and a5, a5, t4
	xor a5, a5, t6
	add a4, a4, a5
	slliw a5, t1, 9
	srliw t1, t1, 23
	or t1, t1, a5
	slliw a5, t5, 19
	srliw t5, t5, 13
	or t5, t5, a5
	slliw a6, a4, 9
	srliw a5, a4, 23
	or a5, a5, a6
	slliw a7, a4, 17
	srliw a6, a4, 15
	or a6, a6, a7
	xor a4, a4, a5
	xor a4, a4, a6
	lwu a5, 20(a3)
	lwu a6, 48(a3)
	xor a5, a5, a6
	lwu a6, 8(a3)
	slliw a7, a6, 15
	srliw a6, a6, 17
	or a6, a6, a7
	xor a5, a5, a6
	slliw a7, a5, 15
	srliw a6, a5, 17
	or a6, a6, a7
	slliw s0, a5, 23
	srliw a7, a5, 9
	or a7, a7, s0
	xor a5, a5, a6
	xor a5, a5, a7
	lwu a6, 32(a3)
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	xor a5, a5, a6
	lwu a6, 60(a3)
	xor a5, a5, a6
	sw a5, 20(a3)
	slliw a6, t3, 12
	srliw a5, t3, 20
	or a5, a5, a6
	add a6, a5, a4
	lui a7, 1003764
	addiw a7, a7, -1260
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add t6, t6, a6
	xor a5, a5, a6
	add t2, t2, a5
	lwu a7, 4(a3)
	add t6, t6, a7
	lwu s0, 20(a3)
	xor s0, a7, s0
	add t2, t2, s0
	or a5, t3, t0
	and a5, a5, t1
	and a6, t3, t0
	or a5, a5, a6
	add t2, t2, a5
	xor a5, t4, t5
	and a5, a5, a4
	xor a5, a5, t5
	add t6, t6, a5
	slliw a5, t0, 9
	srliw t0, t0, 23
	or t0, t0, a5
	slliw a5, t4, 19
	srliw t4, t4, 13
	or t4, t4, a5
	slliw a6, t6, 9
	srliw a5, t6, 23
	or a5, a5, a6
	slliw a7, t6, 17
	srliw a6, t6, 15
	or a6, a6, a7
	xor t6, t6, a5
	xor t6, t6, a6
	lwu a5, 24(a3)
	lwu a6, 52(a3)
	xor a5, a5, a6
	lwu a6, 12(a3)
	slliw a7, a6, 15
	srliw a6, a6, 17
	or a6, a6, a7
	xor a5, a5, a6
	slliw a7, a5, 15
	srliw a6, a5, 17
	or a6, a6, a7
	slliw s0, a5, 23
	srliw a7, a5, 9
	or a7, a7, s0
	xor a5, a5, a6
	xor a5, a5, a7
	lwu a6, 36(a3)
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	xor a5, a5, a6
	lwu a6, 0(a3)
	xor a5, a5, a6
	sw a5, 24(a3)
	slliw a6, t2, 12
	srliw a5, t2, 20
	or a5, a5, a6
	add a6, a5, t6
	lui a7, 958951
	addiw a7, a7, 1577
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add t5, t5, a6
	xor a5, a5, a6
	add t1, t1, a5
	lwu a7, 8(a3)
	add t5, t5, a7
	lwu s0, 24(a3)
	xor s0, a7, s0
	add t1, t1, s0
	or a5, t2, t3
	and a5, a5, t0
	and a6, t2, t3
	or a5, a5, a6
	add t1, t1, a5
	xor a5, a4, t4
	and a5, a5, t6
	xor a5, a5, t4
	add t5, t5, a5
	slliw a5, t3, 9
	srliw t3, t3, 23
	or t3, t3, a5
	slliw a5, a4, 19
	srliw a4, a4, 13
	or a4, a4, a5
	slliw a6, t5, 9
	srliw a5, t5, 23
	or a5, a5, a6
	slliw a7, t5, 17
	srliw a6, t5, 15
	or a6, a6, a7
	xor t5, t5, a5
	xor t5, t5, a6
	lwu a5, 28(a3)
	lwu a6, 56(a3)
	xor a5, a5, a6
	lwu a6, 16(a3)
	slliw a7, a6, 15
	srliw a6, a6, 17
	or a6, a6, a7
	xor a5, a5, a6
	slliw a7, a5, 15
	srliw a6, a5, 17
	or a6, a6, a7
	slliw s0, a5, 23
	srliw a7, a5, 9
	or a7, a7, s0
	xor a5, a5, a6
	xor a5, a5, a7
	lwu a6, 40(a3)
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	xor a5, a5, a6
	lwu a6, 4(a3)
	xor a5, a5, a6
	sw a5, 28(a3)
	slliw a6, t1, 12
	srliw a5, t1, 20
	or a5, a5, a6
	add a6, a5, t5
	lui a7, 869327
	addiw a7, a7, -941
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add t4, t4, a6
	xor a5, a5, a6
	add t0, t0, a5
	lwu a7, 12(a3)
	add t4, t4, a7
	lwu s0, 28(a3)
	xor s0, a7, s0
	add t0, t0, s0
	or a5, t1, t2
	and a5, a5, t3
	and a6, t1, t2
	or a5, a5, a6
	add t0, t0, a5
	xor a5, t6, a4
	and a5, a5, t5
	xor a5, a5, a4
	add t4, t4, a5
	slliw a5, t2, 9
	srliw t2, t2, 23
	or t2, t2, a5
	slliw a5, t6, 19
	srliw t6, t6, 13
	or t6, t6, a5
	slliw a6, t4, 9
	srliw a5, t4, 23
	or a5, a5, a6
	slliw a7, t4, 17
	srliw a6, t4, 15
	or a6, a6, a7
	xor t4, t4, a5
	xor t4, t4, a6
	lwu a5, 32(a3)
	lwu a6, 60(a3)
	xor a5, a5, a6
	lwu a6, 20(a3)
	slliw a7, a6, 15
	srliw a6, a6, 17
	or a6, a6, a7
	xor a5, a5, a6
	slliw a7, a5, 15
	srliw a6, a5, 17
	or a6, a6, a7
	slliw s0, a5, 23
	srliw a7, a5, 9
	or a7, a7, s0
	xor a5, a5, a6
	xor a5, a5, a7
	lwu a6, 44(a3)
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	xor a5, a5, a6
	lwu a6, 8(a3)
	xor a5, a5, a6
	sw a5, 32(a3)
	slliw a6, t0, 12
	srliw a5, t0, 20
	or a5, a5, a6
	add a6, a5, t4
	lui a7, 690078
	addiw a7, a7, -1881
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add a4, a4, a6
	xor a5, a5, a6
	add t3, t3, a5
	lwu a7, 16(a3)
	add a4, a4, a7
	lwu s0, 32(a3)
	xor s0, a7, s0
	add t3, t3, s0
	or a5, t0, t1
	and a5, a5, t2
	and a6, t0, t1
	or a5, a5, a6
	add t3, t3, a5
	xor a5, t5, t6
	and a5, a5, t4
	xor a5, a5, t6
	add a4, a4, a5
	slliw a5, t1, 9
	srliw t1, t1, 23
	or t1, t1, a5
	slliw a5, t5, 19
	srliw t5, t5, 13
	or t5, t5, a5
	slliw a6, a4, 9
	srliw a5, a4, 23
	or a5, a5, a6
	slliw a7, a4, 17
	srliw a6, a4, 15
	or a6, a6, a7
	xor a4, a4, a5
	xor a4, a4, a6
	lwu a5, 36(a3)
	lwu a6, 0(a3)
	xor a5, a5, a6
	lwu a6, 24(a3)
	slliw a7, a6, 15
	srliw a6, a6, 17
	or a6, a6, a7
	xor a5, a5, a6
	slliw a7, a5, 15
	srliw a6, a5, 17
	or a6, a6, a7
	slliw s0, a5, 23
	srliw a7, a5, 9
	or a7, a7, s0
	xor a5, a5, a6
	xor a5, a5, a7
	lwu a6, 48(a3)
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	xor a5, a5, a6
	lwu a6, 12(a3)
	xor a5, a5, a6
	sw a5, 36(a3)
	slliw a6, t3, 12
	srliw a5, t3, 20
	or a5, a5, a6
	add a6, a5, a4
	lui a7, 331579
	addiw a7, a7, 335
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add t6, t6, a6
	xor a5, a5, a6
	add t2, t2, a5
	lwu a7, 20(a3)
	add t6, t6, a7
	lwu s0, 36(a3)
	xor s0, a7, s0
	add t2, t2, s0
	or a5, t3, t0
	and a5, a5, t1
	and a6, t3, t0
	or a5, a5, a6
	add t2, t2, a5
	xor a5, t4, t5
	and a5, a5, a4
	xor a5, a5, t5
	add t6, t6, a5
	slliw a5, t0, 9
	srliw t0, t0, 23
	or t0, t0, a5
	slliw a5, t4, 19
	srliw t4, t4, 13
	or t4, t4, a5
	slliw a6, t6, 9
	srliw a5, t6, 23
	or a5, a5, a6
	slliw a7, t6, 17
	srliw a6, t6, 15
	or a6, a6, a7
	xor t6, t6, a5
	xor t6, t6, a6
	lwu a5, 40(a3)
	lwu a6, 4(a3)
	xor a5, a5, a6
	lwu a6, 28(a3)
	slliw a7, a6, 15
	srliw a6, a6, 17
	or a6, a6, a7
	xor a5, a5, a6
	slliw a7, a5, 15
	srliw a6, a5, 17
	or a6, a6, a7
	slliw s0, a5, 23
	srliw a7, a5, 9
	or a7, a7, s0
	xor a5, a5, a6
	xor a5, a5, a7
	lwu a6, 52(a3)
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	xor a5, a5, a6
	lwu a6, 16(a3)
	xor a5, a5, a6
	sw a5, 40(a3)
	slliw a6, t2, 12
	srliw a5, t2, 20
	or a5, a5, a6
	add a6, a5, t6
	lui a7, 663158
	addiw a7, a7, 670
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add t5, t5, a6
	xor a5, a5, a6
	add t1, t1, a5
	lwu a7, 24(a3)
	add t5, t5, a7
	lwu s0, 40(a3)
	xor s0, a7, s0
	add t1, t1, s0
	or a5, t2, t3
	and a5, a5, t0
	and a6, t2, t3
	or a5, a5, a6
	add t1, t1, a5
	xor a5, a4, t4
	and a5, a5, t6
	xor a5, a5, t4
	add t5, t5, a5
	slliw a5, t3, 9
	srliw t3, t3, 23
	or t3, t3, a5
	slliw a5, a4, 19
	srliw a4, a4, 13
	or a4, a4, a5
	slliw a6, t5, 9
	srliw a5, t5, 23
	or a5, a5, a6
	slliw a7, t5, 17
	srliw a6, t5, 15
	or a6, a6, a7
	xor t5, t5, a5
	xor t5, t5, a6
	lwu a5, 44(a3)
	lwu a6, 8(a3)
	xor a5, a5, a6
	lwu a6, 32(a3)
	slliw a7, a6, 15
	srliw a6, a6, 17
	or a6, a6, a7
	xor a5, a5, a6
	slliw a7, a5, 15
	srliw a6, a5, 17
	or a6, a6, a7
	slliw s0, a5, 23
	srliw a7, a5, 9
	or a7, a7, s0
	xor a5, a5, a6
	xor a5, a5, a7
	lwu a6, 56(a3)
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	xor a5, a5, a6
	lwu a6, 20(a3)
	xor a5, a5, a6
	sw a5, 44(a3)
	slliw a6, t1, 12
	srliw a5, t1, 20
	or a5, a5, a6
	add a6, a5, t5
	lui a7, 277740
	addiw a7, a7, 1341
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add t4, t4, a6
	xor a5, a5, a6
	add t0, t0, a5
	lwu a7, 28(a3)
	add t4, t4, a7
	lwu s0, 44(a3)
	xor s0, a7, s0
	add t0, t0, s0
	or a5, t1, t2
	and a5, a5, t3
	and a6, t1, t2
	or a5, a5, a6
	add t0, t0, a5
	xor a5, t6, a4
	and a5, a5, t5
	xor a5, a5, a4
	add t4, t4, a5
	slliw a5, t2, 9
	srliw t2, t2, 23
	or t2, t2, a5
	slliw a5, t6, 19
	srliw t6, t6, 13
	or t6, t6, a5
	slliw a6, t4, 9
	srliw a5, t4, 23
	or a5, a5, a6
	slliw a7, t4, 17
	srliw a6, t4, 15
	or a6, a6, a7
	xor t4, t4, a5
	xor t4, t4, a6
	lwu a5, 48(a3)
	lwu a6, 12(a3)
	xor a5, a5, a6
	lwu a6, 36(a3)
	slliw a7, a6, 15
	srliw a6, a6, 17
	or a6, a6, a7
	xor a5, a5, a6
	slliw a7, a5, 15
	srliw a6, a5, 17
	or a6, a6, a7
	slliw s0, a5, 23
	srliw a7, a5, 9
	or a7, a7, s0
	xor a5, a5, a6
	xor a5, a5, a7
	lwu a6, 60(a3)
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	xor a5, a5, a6
	lwu a6, 24(a3)
	xor a5, a5, a6
	sw a5, 48(a3)
	slliw a6, t0, 12
	srliw a5, t0, 20
	or a5, a5, a6
	add a6, a5, t4
	lui a7, 555481
	addiw a7, a7, -1414
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add a4, a4, a6
	xor a5, a5, a6
	add t3, t3, a5
	lwu a7, 32(a3)
	add a4, a4, a7
	lwu s0, 48(a3)
	xor s0, a7, s0
	add t3, t3, s0
	or a5, t0, t1
	and a5, a5, t2
	and a6, t0, t1
	or a5, a5, a6
	add t3, t3, a5
	xor a5, t5, t6
	and a5, a5, t4
	xor a5, a5, t6
	add a4, a4, a5
	slliw a5, t1, 9
	srliw t1, t1, 23
	or t1, t1, a5
	slliw a5, t5, 19
	srliw t5, t5, 13
	or t5, t5, a5
	slliw a6, a4, 9
	srliw a5, a4, 23
	or a5, a5, a6
	slliw a7, a4, 17
	srliw a6, a4, 15
	or a6, a6, a7
	xor a4, a4, a5
	xor a4, a4, a6
	lwu a5, 52(a3)
	lwu a6, 16(a3)
	xor a5, a5, a6
	lwu a6, 40(a3)
	slliw a7, a6, 15
	srliw a6, a6, 17
	or a6, a6, a7
	xor a5, a5, a6
	slliw a7, a5, 15
	srliw a6, a5, 17
	or a6, a6, a7
	slliw s0, a5, 23
	srliw a7, a5, 9
	or a7, a7, s0
	xor a5, a5, a6
	xor a5, a5, a7
	lwu a6, 0(a3)
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	xor a5, a5, a6
	lwu a6, 28(a3)
	xor a5, a5, a6
	sw a5, 52(a3)
	slliw a6, t3, 12
	srliw a5, t3, 20
	or a5, a5, a6
	add a6, a5, a4
	lui a7, 62385
	addiw a7, a7, 1269
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add t6, t6, a6
	xor a5, a5, a6
	add t2, t2, a5
	lwu a7, 36(a3)
	add t6, t6, a7
	lwu s0, 52(a3)
	xor s0, a7, s0
	add t2, t2, s0
	or a5, t3, t0
	and a5, a5, t1
	and a6, t3, t0
	or a5, a5, a6
	add t2, t2, a5
	xor a5, t4, t5
	and a5, a5, a4
	xor a5, a5, t5
	add t6, t6, a5
	slliw a5, t0, 9
	srliw t0, t0, 23
	or t0, t0, a5
	slliw a5, t4, 19
	srliw t4, t4, 13
	or t4, t4, a5
	slliw a6, t6, 9
	srliw a5, t6, 23
	or a5, a5, a6
	slliw a7, t6, 17
	srliw a6, t6, 15
	or a6, a6, a7
	xor t6, t6, a5
	xor t6, t6, a6
	lwu a5, 56(a3)
	lwu a6, 20(a3)
	xor a5, a5, a6
	lwu a6, 44(a3)
	slliw a7, a6, 15
	srliw a6, a6, 17
	or a6, a6, a7
	xor a5, a5, a6
	slliw a7, a5, 15
	srliw a6, a5, 17
	or a6, a6, a7
	slliw s0, a5, 23
	srliw a7, a5, 9
	or a7, a7, s0
	xor a5, a5, a6
	xor a5, a5, a7
	lwu a6, 4(a3)
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	xor a5, a5, a6
	lwu a6, 32(a3)
	xor a5, a5, a6
	sw a5, 56(a3)
	slliw a6, t2, 12
	srliw a5, t2, 20
	or a5, a5, a6
	add a6, a5, t6
	lui a7, 124771
	addiw a7, a7, -1558
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add t5, t5, a6
	xor a5, a5, a6
	add t1, t1, a5
	lwu a7, 40(a3)
	add t5, t5, a7
	lwu s0, 56(a3)
	xor s0, a7, s0
	add t1, t1, s0
	or a5, t2, t3
	and a5, a5, t0
	and a6, t2, t3
	or a5, a5, a6
	add t1, t1, a5
	xor a5, a4, t4
	and a5, a5, t6
	xor a5, a5, t4
	add t5, t5, a5
	slliw a5, t3, 9
	srliw t3, t3, 23
	or t3, t3, a5
	slliw a5, a4, 19
	srliw a4, a4, 13
	or a4, a4, a5
	slliw a6, t5, 9
	srliw a5, t5, 23
	or a5, a5, a6
	slliw a7, t5, 17
	srliw a6, t5, 15
	or a6, a6, a7
	xor t5, t5, a5
	xor t5, t5, a6
	lwu a5, 60(a3)
	lwu a6, 24(a3)
	xor a5, a5, a6
	lwu a6, 48(a3)
	slliw a7, a6, 15
	srliw a6, a6, 17
	or a6, a6, a7
	xor a5, a5, a6
	slliw a7, a5, 15
	srliw a6, a5, 17
	or a6, a6, a7
	slliw s0, a5, 23
	srliw a7, a5, 9
	or a7, a7, s0
	xor a5, a5, a6
	xor a5, a5, a7
	lwu a6, 8(a3)
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	xor a5, a5, a6
	lwu a6, 36(a3)
	xor a5, a5, a6
	sw a5, 60(a3)
	slliw a6, t1, 12
	srliw a5, t1, 20
	or a5, a5, a6
	add a6, a5, t5
	lui a7, 249541
	addiw a7, a7, 980
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add t4, t4, a6
	xor a5, a5, a6
	add t0, t0, a5
	lwu a7, 44(a3)
	add t4, t4, a7
	lwu s0, 60(a3)
	xor s0, a7, s0
	add t0, t0, s0
	or a5, t1, t2
	and a5, a5, t3
	and a6, t1, t2
	or a5, a5, a6
	add t0, t0, a5
	xor a5, t6, a4
	and a5, a5, t5
	xor a5, a5, a4
	add t4, t4, a5
	slliw a5, t2, 9
	srliw t2, t2, 23
	or t2, t2, a5
	slliw a5, t6, 19
	srliw t6, t6, 13
	or t6, t6, a5
	slliw a6, t4, 9
	srliw a5, t4, 23
	or a5, a5, a6
	slliw a7, t4, 17
	srliw a6, t4, 15
	or a6, a6, a7
	xor t4, t4, a5
	xor t4, t4, a6
	lwu a5, 0(a3)
	lwu a6, 28(a3)
	xor a5, a5, a6
	lwu a6, 52(a3)
	slliw a7, a6, 15
	srliw a6, a6, 17
	or a6, a6, a7
	xor a5, a5, a6
	slliw a7, a5, 15
	srliw a6, a5, 17
	or a6, a6, a7
	slliw s0, a5, 23
	srliw a7, a5, 9
	or a7, a7, s0
	xor a5, a5, a6
	xor a5, a5, a7
	lwu a6, 12(a3)
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	xor a5, a5, a6
	lwu a6, 40(a3)
	xor a5, a5, a6
	sw a5, 0(a3)
	slliw a6, t0, 12
	srliw a5, t0, 20
	or a5, a5, a6
	add a6, a5, t4
	lui a7, 499082
	addiw a7, a7, 1960
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add a4, a4, a6
	xor a5, a5, a6
	add t3, t3, a5
	lwu a7, 48(a3)
	add a4, a4, a7
	lwu s0, 0(a3)
	xor s0, a7, s0
	add t3, t3, s0
	or a5, t0, t1
	and a5, a5, t2
	and a6, t0, t1
	or a5, a5, a6
	add t3, t3, a5
	xor a5, t5, t6
	and a5, a5, t4
	xor a5, a5, t6
	add a4, a4, a5
	slliw a5, t1, 9
	srliw t1, t1, 23
	or t1, t1, a5
	slliw a5, t5, 19
	srliw t5, t5, 13
	or t5, t5, a5
	slliw a6, a4, 9
	srliw a5, a4, 23
	or a5, a5, a6
	slliw a7, a4, 17
	srliw a6, a4, 15
	or a6, a6, a7
	xor a4, a4, a5
	xor a4, a4, a6
	lwu a5, 4(a3)
	lwu a6, 32(a3)
	xor a5, a5, a6
	lwu a6, 56(a3)
	slliw a7, a6, 15
	srliw a6, a6, 17
	or a6, a6, a7
	xor a5, a5, a6
	slliw a7, a5, 15
	srliw a6, a5, 17
	or a6, a6, a7
	slliw s0, a5, 23
	srliw a7, a5, 9
	or a7, a7, s0
	xor a5, a5, a6
	xor a5, a5, a7
	lwu a6, 16(a3)
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	xor a5, a5, a6
	lwu a6, 44(a3)
	xor a5, a5, a6
	sw a5, 4(a3)
	slliw a6, t3, 12
	srliw a5, t3, 20
	or a5, a5, a6
	add a6, a5, a4
	lui a7, 998165
	addiw a7, a7, -176
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add t6, t6, a6
	xor a5, a5, a6
	add t2, t2, a5
	lwu a7, 52(a3)
	add t6, t6, a7
	lwu s0, 4(a3)
	xor s0, a7, s0
	add t2, t2, s0
	or a5, t3, t0
	and a5, a5, t1
	and a6, t3, t0
	or a5, a5, a6
	add t2, t2, a5
	xor a5, t4, t5
	and a5, a5, a4
	xor a5, a5, t5
	add t6, t6, a5
	slliw a5, t0, 9
	srliw t0, t0, 23
	or t0, t0, a5
	slliw a5, t4, 19
	srliw t4, t4, 13
	or t4, t4, a5
	slliw a6, t6, 9
	srliw a5, t6, 23
	or a5, a5, a6
	slliw a7, t6, 17
	srliw a6, t6, 15
	or a6, a6, a7
	xor t6, t6, a5
	xor t6, t6, a6
	lwu a5, 8(a3)
	lwu a6, 36(a3)
	xor a5, a5, a6
	lwu a6, 60(a3)
	slliw a7, a6, 15
	srliw a6, a6, 17
	or a6, a6, a7
	xor a5, a5, a6
	slliw a7, a5, 15
	srliw a6, a5, 17
	or a6, a6, a7
	slliw s0, a5, 23
	srliw a7, a5, 9
	or a7, a7, s0
	xor a5, a5, a6
	xor a5, a5, a7
	lwu a6, 20(a3)
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	xor a5, a5, a6
	lwu a6, 48(a3)
	xor a5, a5, a6
	sw a5, 8(a3)
	slliw a6, t2, 12
	srliw a5, t2, 20
	or a5, a5, a6
	add a6, a5, t6
	lui a7, 947754
	addiw a7, a7, -351
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add t5, t5, a6
	xor a5, a5, a6
	add t1, t1, a5
	lwu a7, 56(a3)
	add t5, t5, a7
	lwu s0, 8(a3)
	xor s0, a7, s0
	add t1, t1, s0
	or a5, t2, t3
	and a5, a5, t0
	and a6, t2, t3
	or a5, a5, a6
	add t1, t1, a5
	xor a5, a4, t4
	and a5, a5, t6
	xor a5, a5, t4
	add t5, t5, a5
	slliw a5, t3, 9
	srliw t3, t3, 23
	or t3, t3, a5
	slliw a5, a4, 19
	srliw a4, a4, 13
	or a4, a4, a5
	slliw a6, t5, 9
	srliw a5, t5, 23
	or a5, a5, a6
	slliw a7, t5, 17
	srliw a6, t5, 15
	or a6, a6, a7
	xor t5, t5, a5
	xor t5, t5, a6
	lwu a5, 12(a3)
	lwu a6, 40(a3)
	xor a5, a5, a6
	lwu a6, 0(a3)
	slliw a7, a6, 15
	srliw a6, a6, 17
	or a6, a6, a7
	xor a5, a5, a6
	slliw a7, a5, 15
	srliw a6, a5, 17
	or a6, a6, a7
	slliw s0, a5, 23
	srliw a7, a5, 9
	or a7, a7, s0
	xor a5, a5, a6
	xor a5, a5, a7
	lwu a6, 24(a3)
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	xor a5, a5, a6
	lwu a6, 52(a3)
	xor a5, a5, a6
	sw a5, 12(a3)
	slliw a6, t1, 12
	srliw a5, t1, 20
	or a5, a5, a6
	add a6, a5, t5
	lui a7, 846932
	addiw a7, a7, -701
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add t4, t4, a6
	xor a5, a5, a6
	add t0, t0, a5
	lwu a7, 60(a3)
	add t4, t4, a7
	lwu s0, 12(a3)
	xor s0, a7, s0
	add t0, t0, s0
	or a5, t1, t2
	and a5, a5, t3
	and a6, t1, t2
	or a5, a5, a6
	add t0, t0, a5
	xor a5, t6, a4
	and a5, a5, t5
	xor a5, a5, a4
	add t4, t4, a5
	slliw a5, t2, 9
	srliw t2, t2, 23
	or t2, t2, a5
	slliw a5, t6, 19
	srliw t6, t6, 13
	or t6, t6, a5
	slliw a6, t4, 9
	srliw a5, t4, 23
	or a5, a5, a6
	slliw a7, t4, 17
	srliw a6, t4, 15
	or a6, a6, a7
	xor t4, t4, a5
	xor t4, t4, a6
	lwu a5, 16(a3)
	lwu a6, 44(a3)
	xor a5, a5, a6
	lwu a6, 4(a3)
	slliw a7, a6, 15
	srliw a6, a6, 17
	or a6, a6, a7
	xor a5, a5, a6
	slliw a7, a5, 15
	srliw a6, a5, 17
	or a6, a6, a7
	slliw s0, a5, 23
	srliw a7, a5, 9
	or a7, a7, s0
	xor a5, a5, a6
	xor a5, a5, a7
	lwu a6, 28(a3)
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	xor a5, a5, a6
	lwu a6, 56(a3)
	xor a5, a5, a6
	sw a5, 16(a3)
	slliw a6, t0, 12
	srliw a5, t0, 20
	or a5, a5, a6
	add a6, a5, t4
	lui a7, 645288
	addiw a7, a7, -1401
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add a4, a4, a6
	xor a5, a5, a6
	add t3, t3, a5
	lwu a7, 0(a3)
	add a4, a4, a7
	lwu s0, 16(a3)
	xor s0, a7, s0
	add t3, t3, s0
	or a5, t0, t1
	and a5, a5, t2
	and a6, t0, t1
	or a5, a5, a6
	add t3, t3, a5
	xor a5, t5, t6
	and a5, a5, t4
	xor a5, a5, t6
	add a4, a4, a5
	slliw a5, t1, 9
	srliw t1, t1, 23
	or t1, t1, a5
	slliw a5, t5, 19
	srliw t5, t5, 13
	or t5, t5, a5
	slliw a6, a4, 9
	srliw a5, a4, 23
	or a5, a5, a6
	slliw a7, a4, 17
	srliw a6, a4, 15
	or a6, a6, a7
	xor a4, a4, a5
	xor a4, a4, a6
	lwu a5, 20(a3)
	lwu a6, 48(a3)
	xor a5, a5, a6
	lwu a6, 8(a3)
	slliw a7, a6, 15
	srliw a6, a6, 17
	or a6, a6, a7
	xor a5, a5, a6
	slliw a7, a5, 15
	srliw a6, a5, 17
	or a6, a6, a7
	slliw s0, a5, 23
	srliw a7, a5, 9
	or a7, a7, s0
	xor a5, a5, a6
	xor a5, a5, a7
	lwu a6, 32(a3)
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	xor a5, a5, a6
	lwu a6, 60(a3)
	xor a5, a5, a6
	sw a5, 20(a3)
	slliw a6, t3, 12
	srliw a5, t3, 20
	or a5, a5, a6
	add a6, a5, a4
	lui a7, 241999
	addiw a7, a7, 1295
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add t6, t6, a6
	xor a5, a5, a6
	add t2, t2, a5
	lwu a7, 4(a3)
	add t6, t6, a7
	lwu s0, 20(a3)
	xor s0, a7, s0
	add t2, t2, s0
	or a5, t3, t0
	and a5, a5, t1
	and a6, t3, t0
	or a5, a5, a6
	add t2, t2, a5
	xor a5, t4, t5
	and a5, a5, a4
	xor a5, a5, t5
	add t6, t6, a5
	slliw a5, t0, 9
	srliw t0, t0, 23
	or t0, t0, a5
	slliw a5, t4, 19
	srliw t4, t4, 13
	or t4, t4, a5
	slliw a6, t6, 9
	srliw a5, t6, 23
	or a5, a5, a6
	slliw a7, t6, 17
	srliw a6, t6, 15
	or a6, a6, a7
	xor t6, t6, a5
	xor t6, t6, a6
	lwu a5, 24(a3)
	lwu a6, 52(a3)
	xor a5, a5, a6
	lwu a6, 12(a3)
	slliw a7, a6, 15
	srliw a6, a6, 17
	or a6, a6, a7
	xor a5, a5, a6
	slliw a7, a5, 15
	srliw a6, a5, 17
	or a6, a6, a7
	slliw s0, a5, 23
	srliw a7, a5, 9
	or a7, a7, s0
	xor a5, a5, a6
	xor a5, a5, a7
	lwu a6, 36(a3)
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	xor a5, a5, a6
	lwu a6, 0(a3)
	xor a5, a5, a6
	sw a5, 24(a3)
	slliw a6, t2, 12
	srliw a5, t2, 20
	or a5, a5, a6
	add a6, a5, t6
	lui a7, 483999
	addiw a7, a7, -1506
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add t5, t5, a6
	xor a5, a5, a6
	add t1, t1, a5
	lwu a7, 8(a3)
	add t5, t5, a7
	lwu s0, 24(a3)
	xor s0, a7, s0
	add t1, t1, s0
	or a5, t2, t3
	and a5, a5, t0
	and a6, t2, t3
	or a5, a5, a6
	add t1, t1, a5
	xor a5, a4, t4
	and a5, a5, t6
	xor a5, a5, t4
	add t5, t5, a5
	slliw a5, t3, 9
	srliw t3, t3, 23
	or t3, t3, a5
	slliw a5, a4, 19
	srliw a4, a4, 13
	or a4, a4, a5
	slliw a6, t5, 9
	srliw a5, t5, 23
	or a5, a5, a6
	slliw a7, t5, 17
	srliw a6, t5, 15
	or a6, a6, a7
	xor t5, t5, a5
	xor t5, t5, a6
	lwu a5, 28(a3)
	lwu a6, 56(a3)
	xor a5, a5, a6
	lwu a6, 16(a3)
	slliw a7, a6, 15
	srliw a6, a6, 17
	or a6, a6, a7
	xor a5, a5, a6
	slliw a7, a5, 15
	srliw a6, a5, 17
	or a6, a6, a7
	slliw s0, a5, 23
	srliw a7, a5, 9
	or a7, a7, s0
	xor a5, a5, a6
	xor a5, a5, a7
	lwu a6, 40(a3)
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	xor a5, a5, a6
	lwu a6, 4(a3)
	xor a5, a5, a6
	sw a5, 28(a3)
	slliw a6, t1, 12
	srliw a5, t1, 20
	or a5, a5, a6
	add a6, a5, t5
	lui a7, 967997
	addiw a7, a7, 1084
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add t4, t4, a6
	xor a5, a5, a6
	add t0, t0, a5
	lwu a7, 12(a3)
	add t4, t4, a7
	lwu s0, 28(a3)
	xor s0, a7, s0
	add t0, t0, s0
	or a5, t1, t2
	and a5, a5, t3
	and a6, t1, t2
	or a5, a5, a6
	add t0, t0, a5
	xor a5, t6, a4
	and a5, a5, t5
	xor a5, a5, a4
	add t4, t4, a5
	slliw a5, t2, 9
	srliw t2, t2, 23
	or t2, t2, a5
	slliw a5, t6, 19
	srliw t6, t6, 13
	or t6, t6, a5
	slliw a6, t4, 9
	srliw a5, t4, 23
	or a5, a5, a6
	slliw a7, t4, 17
	srliw a6, t4, 15
	or a6, a6, a7
	xor t4, t4, a5
	xor t4, t4, a6
	lwu a5, 32(a3)
	lwu a6, 60(a3)
	xor a5, a5, a6
	lwu a6, 20(a3)
	slliw a7, a6, 15
	srliw a6, a6, 17
	or a6, a6, a7
	xor a5, a5, a6
	slliw a7, a5, 15
	srliw a6, a5, 17
	or a6, a6, a7
	slliw s0, a5, 23
	srliw a7, a5, 9
	or a7, a7, s0
	xor a5, a5, a6
	xor a5, a5, a7
	lwu a6, 44(a3)
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	xor a5, a5, a6
	lwu a6, 8(a3)
	xor a5, a5, a6
	sw a5, 32(a3)
	slliw a6, t0, 12
	srliw a5, t0, 20
	or a5, a5, a6
	add a6, a5, t4
	lui a7, 887419
	addiw a7, a7, -1927
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add a4, a4, a6
	xor a5, a5, a6
	add t3, t3, a5
	lwu a7, 16(a3)
	add a4, a4, a7
	lwu s0, 32(a3)
	xor s0, a7, s0
	add t3, t3, s0
	or a5, t0, t1
	and a5, a5, t2
	and a6, t0, t1
	or a5, a5, a6
	add t3, t3, a5
	xor a5, t5, t6
	and a5, a5, t4
	xor a5, a5, t6
	add a4, a4, a5
	slliw a5, t1, 9
	srliw t1, t1, 23
	or t1, t1, a5
	slliw a5, t5, 19
	srliw t5, t5, 13
	or t5, t5, a5
	slliw a6, a4, 9
	srliw a5, a4, 23
	or a5, a5, a6
	slliw a7, a4, 17
	srliw a6, a4, 15
	or a6, a6, a7
	xor a4, a4, a5
	xor a4, a4, a6
	lwu a5, 36(a3)
	lwu a6, 0(a3)
	xor a5, a5, a6
	lwu a6, 24(a3)
	slliw a7, a6, 15
	srliw a6, a6, 17
	or a6, a6, a7
	xor a5, a5, a6
	slliw a7, a5, 15
	srliw a6, a5, 17
	or a6, a6, a7
	slliw s0, a5, 23
	srliw a7, a5, 9
	or a7, a7, s0
	xor a5, a5, a6
	xor a5, a5, a7
	lwu a6, 48(a3)
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	xor a5, a5, a6
	lwu a6, 12(a3)
	xor a5, a5, a6
	sw a5, 36(a3)
	slliw a6, t3, 12
	srliw a5, t3, 20
	or a5, a5, a6
	add a6, a5, a4
	lui a7, 726261
	addiw a7, a7, 243
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add t6, t6, a6
	xor a5, a5, a6
	add t2, t2, a5
	lwu a7, 20(a3)
	add t6, t6, a7
	lwu s0, 36(a3)
	xor s0, a7, s0
	add t2, t2, s0
	or a5, t3, t0
	and a5, a5, t1
	and a6, t3, t0
	or a5, a5, a6
	add t2, t2, a5
	xor a5, t4, t5
	and a5, a5, a4
	xor a5, a5, t5
	add t6, t6, a5
	slliw a5, t0, 9
	srliw t0, t0, 23
	or t0, t0, a5
	slliw a5, t4, 19
	srliw t4, t4, 13
	or t4, t4, a5
	slliw a6, t6, 9
	srliw a5, t6, 23
	or a5, a5, a6
	slliw a7, t6, 17
	srliw a6, t6, 15
	or a6, a6, a7
	xor t6, t6, a5
	xor t6, t6, a6
	lwu a5, 40(a3)
	lwu a6, 4(a3)
	xor a5, a5, a6
	lwu a6, 28(a3)
	slliw a7, a6, 15
	srliw a6, a6, 17
	or a6, a6, a7
	xor a5, a5, a6
	slliw a7, a5, 15
	srliw a6, a5, 17
	or a6, a6, a7
	slliw s0, a5, 23
	srliw a7, a5, 9
	or a7, a7, s0
	xor a5, a5, a6
	xor a5, a5, a7
	lwu a6, 52(a3)
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	xor a5, a5, a6
	lwu a6, 16(a3)
	xor a5, a5, a6
	sw a5, 40(a3)
	slliw a6, t2, 12
	srliw a5, t2, 20
	or a5, a5, a6
	add a6, a5, t6
	lui a7, 403946
	addiw a7, a7, 487
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add t5, t5, a6
	xor a5, a5, a6
	add t1, t1, a5
	lwu a7, 24(a3)
	add t5, t5, a7
	lwu s0, 40(a3)
	xor s0, a7, s0
	add t1, t1, s0
	or a5, t2, t3
	and a5, a5, t0
	and a6, t2, t3
	or a5, a5, a6
	add t1, t1, a5
	xor a5, a4, t4
	and a5, a5, t6
	xor a5, a5, t4
	add t5, t5, a5
	slliw a5, t3, 9
	srliw t3, t3, 23
	or t3, t3, a5
	slliw a5, a4, 19
	srliw a4, a4, 13
	or a4, a4, a5
	slliw a6, t5, 9
	srliw a5, t5, 23
	or a5, a5, a6
	slliw a7, t5, 17
	srliw a6, t5, 15
	or a6, a6, a7
	xor t5, t5, a5
	xor t5, t5, a6
	lwu a5, 44(a3)
	lwu a6, 8(a3)
	xor a5, a5, a6
	lwu a6, 32(a3)
	slliw a7, a6, 15
	srliw a6, a6, 17
	or a6, a6, a7
	xor a5, a5, a6
	slliw a7, a5, 15
	srliw a6, a5, 17
	or a6, a6, a7
	slliw s0, a5, 23
	srliw a7, a5, 9
	or a7, a7, s0
	xor a5, a5, a6
	xor a5, a5, a7
	lwu a6, 56(a3)
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	xor a5, a5, a6
	lwu a6, 20(a3)
	xor a5, a5, a6
	sw a5, 44(a3)
	slliw a6, t1, 12
	srliw a5, t1, 20
	or a5, a5, a6
	add a6, a5, t5
	lui a7, 807892
	addiw a7, a7, 974
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add t4, t4, a6
	xor a5, a5, a6
	add t0, t0, a5
	lwu a7, 28(a3)
	add t4, t4, a7
	lwu s0, 44(a3)
	xor s0, a7, s0
	add t0, t0, s0
	or a5, t1, t2
	and a5, a5, t3
	and a6, t1, t2
	or a5, a5, a6
	add t0, t0, a5
	xor a5, t6, a4
	and a5, a5, t5
	xor a5, a5, a4
	add t4, t4, a5
	slliw a5, t2, 9
	srliw t2, t2, 23
	or t2, t2, a5
	slliw a5, t6, 19
	srliw t6, t6, 13
	or t6, t6, a5
	slliw a6, t4, 9
	srliw a5, t4, 23
	or a5, a5, a6
	slliw a7, t4, 17
	srliw a6, t4, 15
	or a6, a6, a7
	xor t4, t4, a5
	xor t4, t4, a6
	lwu a5, 48(a3)
	lwu a6, 12(a3)
	xor a5, a5, a6
	lwu a6, 36(a3)
	slliw a7, a6, 15
	srliw a6, a6, 17
	or a6, a6, a7
	xor a5, a5, a6
	slliw a7, a5, 15
	srliw a6, a5, 17
	or a6, a6, a7
	slliw s0, a5, 23
	srliw a7, a5, 9
	or a7, a7, s0
	xor a5, a5, a6
	xor a5, a5, a7
	lwu a6, 60(a3)
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	xor a5, a5, a6
	lwu a6, 24(a3)
	xor a5, a5, a6
	sw a5, 48(a3)
	slliw a6, t0, 12
	srliw a5, t0, 20
	or a5, a5, a6
	add a6, a5, t4
	lui a7, 567208
	addiw a7, a7, 1949
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add a4, a4, a6
	xor a5, a5, a6
	add t3, t3, a5
	lwu a7, 32(a3)
	add a4, a4, a7
	lwu s0, 48(a3)
	xor s0, a7, s0
	add t3, t3, s0
	or a5, t0, t1
	and a5, a5, t2
	and a6, t0, t1
	or a5, a5, a6
	add t3, t3, a5
	xor a5, t5, t6
	and a5, a5, t4
	xor a5, a5, t6
	add a4, a4, a5
	slliw a5, t1, 9
	srliw t1, t1, 23
	or t1, t1, a5
	slliw a5, t5, 19
	srliw t5, t5, 13
	or t5, t5, a5
	slliw a6, a4, 9
	srliw a5, a4, 23
	or a5, a5, a6
	slliw a7, a4, 17
	srliw a6, a4, 15
	or a6, a6, a7
	xor a4, a4, a5
	xor a4, a4, a6
	lwu a5, 52(a3)
	lwu a6, 16(a3)
	xor a5, a5, a6
	lwu a6, 40(a3)
	slliw a7, a6, 15
	srliw a6, a6, 17
	or a6, a6, a7
	xor a5, a5, a6
	slliw a7, a5, 15
	srliw a6, a5, 17
	or a6, a6, a7
	slliw s0, a5, 23
	srliw a7, a5, 9
	or a7, a7, s0
	xor a5, a5, a6
	xor a5, a5, a7
	lwu a6, 0(a3)
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	xor a5, a5, a6
	lwu a6, 28(a3)
	xor a5, a5, a6
	sw a5, 52(a3)
	slliw a6, t3, 12
	srliw a5, t3, 20
	or a5, a5, a6
	add a6, a5, a4
	lui a7, 85841
	addiw a7, a7, -197
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add t6, t6, a6
	xor a5, a5, a6
	add t2, t2, a5
	lwu a7, 36(a3)
	add t6, t6, a7
	lwu s0, 52(a3)
	xor s0, a7, s0
	add t2, t2, s0
	or a5, t3, t0
	and a5, a5, t1
	and a6, t3, t0
	or a5, a5, a6
	add t2, t2, a5
	xor a5, t4, t5
	and a5, a5, a4
	xor a5, a5, t5
	add t6, t6, a5
	slliw a5, t0, 9
	srliw t0, t0, 23
	or t0, t0, a5
	slliw a5, t4, 19
	srliw t4, t4, 13
	or t4, t4, a5
	slliw a6, t6, 9
	srliw a5, t6, 23
	or a5, a5, a6
	slliw a7, t6, 17
	srliw a6, t6, 15
	or a6, a6, a7
	xor t6, t6, a5
	xor t6, t6, a6
	lwu a5, 56(a3)
	lwu a6, 20(a3)
	xor a5, a5, a6
	lwu a6, 44(a3)
	slliw a7, a6, 15
	srliw a6, a6, 17
	or a6, a6, a7
	xor a5, a5, a6
	slliw a7, a5, 15
	srliw a6, a5, 17
	or a6, a6, a7
	slliw s0, a5, 23
	srliw a7, a5, 9
	or a7, a7, s0
	xor a5, a5, a6
	xor a5, a5, a7
	lwu a6, 4(a3)
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	xor a5, a5, a6
	lwu a6, 32(a3)
	xor a5, a5, a6
	sw a5, 56(a3)
	slliw a6, t2, 12
	srliw a5, t2, 20
	or a5, a5, a6
	add a6, a5, t6
	lui a7, 171682
	addiw a7, a7, -394
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add t5, t5, a6
	xor a5, a5, a6
	add t1, t1, a5
	lwu a7, 40(a3)
	add t5, t5, a7
	lwu s0, 56(a3)
	xor s0, a7, s0
	add t1, t1, s0
	or a5, t2, t3
	and a5, a5, t0
	and a6, t2, t3
	or a5, a5, a6
	add t1, t1, a5
	xor a5, a4, t4
	and a5, a5, t6
	xor a5, a5, t4
	add t5, t5, a5
	slliw a5, t3, 9
	srliw t3, t3, 23
	or t3, t3, a5
	slliw a5, a4, 19
	srliw a4, a4, 13
	or a4, a4, a5
	slliw a6, t5, 9
	srliw a5, t5, 23
	or a5, a5, a6
	slliw a7, t5, 17
	srliw a6, t5, 15
	or a6, a6, a7
	xor t5, t5, a5
	xor t5, t5, a6
	lwu a5, 60(a3)
	lwu a6, 24(a3)
	xor a5, a5, a6
	lwu a6, 48(a3)
	slliw a7, a6, 15
	srliw a6, a6, 17
	or a6, a6, a7
	xor a5, a5, a6
	slliw a7, a5, 15
	srliw a6, a5, 17
	or a6, a6, a7
	slliw s0, a5, 23
	srliw a7, a5, 9
	or a7, a7, s0
	xor a5, a5, a6
	xor a5, a5, a7
	lwu a6, 8(a3)
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	xor a5, a5, a6
	lwu a6, 36(a3)
	xor a5, a5, a6
	sw a5, 60(a3)
	slliw a6, t1, 12
	srliw a5, t1, 20
	or a5, a5, a6
	add a6, a5, t5
	lui a7, 343364
	addiw a7, a7, -788
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add t4, t4, a6
	xor a5, a5, a6
	add t0, t0, a5
	lwu a7, 44(a3)
	add t4, t4, a7
	lwu s0, 60(a3)
	xor s0, a7, s0
	add t0, t0, s0
	or a5, t1, t2
	and a5, a5, t3
	and a6, t1, t2
	or a5, a5, a6
	add t0, t0, a5
	xor a5, t6, a4
	and a5, a5, t5
	xor a5, a5, a4
	add t4, t4, a5
	slliw a5, t2, 9
	srliw t2, t2, 23
	or t2, t2, a5
	slliw a5, t6, 19
	srliw t6, t6, 13
	or t6, t6, a5
	slliw a6, t4, 9
	srliw a5, t4, 23
	or a5, a5, a6
	slliw a7, t4, 17
	srliw a6, t4, 15
	or a6, a6, a7
	xor t4, t4, a5
	xor t4, t4, a6
	lwu a5, 0(a3)
	lwu a6, 28(a3)
	xor a5, a5, a6
	lwu a6, 52(a3)
	slliw a7, a6, 15
	srliw a6, a6, 17
	or a6, a6, a7
	xor a5, a5, a6
	slliw a7, a5, 15
	srliw a6, a5, 17
	or a6, a6, a7
	slliw s0, a5, 23
	srliw a7, a5, 9
	or a7, a7, s0
	xor a5, a5, a6
	xor a5, a5, a7
	lwu a6, 12(a3)
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	xor a5, a5, a6
	lwu a6, 40(a3)
	xor a5, a5, a6
	sw a5, 0(a3)
	slliw a6, t0, 12
	srliw a5, t0, 20
	or a5, a5, a6
	add a6, a5, t4
	lui a7, 686728
	addiw a7, a7, -1576
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add a4, a4, a6
	xor a5, a5, a6
	add t3, t3, a5
	lwu a7, 48(a3)
	add a4, a4, a7
	lwu s0, 0(a3)
	xor s0, a7, s0
	add t3, t3, s0
	or a5, t0, t1
	and a5, a5, t2
	and a6, t0, t1
	or a5, a5, a6
	add t3, t3, a5
	xor a5, t5, t6
	and a5, a5, t4
	xor a5, a5, t6
	add a4, a4, a5
	slliw a5, t1, 9
	srliw t1, t1, 23
	or t1, t1, a5
	slliw a5, t5, 19
	srliw t5, t5, 13
	or t5, t5, a5
	slliw a6, a4, 9
	srliw a5, a4, 23
	or a5, a5, a6
	slliw a7, a4, 17
	srliw a6, a4, 15
	or a6, a6, a7
	xor a4, a4, a5
	xor a4, a4, a6
	lwu a5, 4(a3)
	lwu a6, 32(a3)
	xor a5, a5, a6
	lwu a6, 56(a3)
	slliw a7, a6, 15
	srliw a6, a6, 17
	or a6, a6, a7
	xor a5, a5, a6
	slliw a7, a5, 15
	srliw a6, a5, 17
	or a6, a6, a7
	slliw s0, a5, 23
	srliw a7, a5, 9
	or a7, a7, s0
	xor a5, a5, a6
	xor a5, a5, a7
	lwu a6, 16(a3)
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	xor a5, a5, a6
	lwu a6, 44(a3)
	xor a5, a5, a6
	sw a5, 4(a3)
	slliw a6, t3, 12
	srliw a5, t3, 20
	or a5, a5, a6
	add a6, a5, a4
	lui a7, 324879
	addiw a7, a7, 945
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add t6, t6, a6
	xor a5, a5, a6
	add t2, t2, a5
	lwu a7, 52(a3)
	add t6, t6, a7
	lwu s0, 4(a3)
	xor s0, a7, s0
	add t2, t2, s0
	or a5, t3, t0
	and a5, a5, t1
	and a6, t3, t0
	or a5, a5, a6
	add t2, t2, a5
	xor a5, t4, t5
	and a5, a5, a4
	xor a5, a5, t5
	add t6, t6, a5
	slliw a5, t0, 9
	srliw t0, t0, 23
	or t0, t0, a5
	slliw a5, t4, 19
	srliw t4, t4, 13
	or t4, t4, a5
	slliw a6, t6, 9
	srliw a5, t6, 23
	or a5, a5, a6
	slliw a7, t6, 17
	srliw a6, t6, 15
	or a6, a6, a7
	xor t6, t6, a5
	xor t6, t6, a6
	lwu a5, 8(a3)
	lwu a6, 36(a3)
	xor a5, a5, a6
	lwu a6, 60(a3)
	slliw a7, a6, 15
	srliw a6, a6, 17
	or a6, a6, a7
	xor a5, a5, a6
	slliw a7, a5, 15
	srliw a6, a5, 17
	or a6, a6, a7
	slliw s0, a5, 23
	srliw a7, a5, 9
	or a7, a7, s0
	xor a5, a5, a6
	xor a5, a5, a7
	lwu a6, 20(a3)
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	xor a5, a5, a6
	lwu a6, 48(a3)
	xor a5, a5, a6
	sw a5, 8(a3)
	slliw a6, t2, 12
	srliw a5, t2, 20
	or a5, a5, a6
	add a6, a5, t6
	lui a7, 649758
	addiw a7, a7, 1890
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add t5, t5, a6
	xor a5, a5, a6
	add t1, t1, a5
	lwu a7, 56(a3)
	add t5, t5, a7
	lwu s0, 8(a3)
	xor s0, a7, s0
	add t1, t1, s0
	or a5, t2, t3
	and a5, a5, t0
	and a6, t2, t3
	or a5, a5, a6
	add t1, t1, a5
	xor a5, a4, t4
	and a5, a5, t6
	xor a5, a5, t4
	add t5, t5, a5
	slliw a5, t3, 9
	srliw t3, t3, 23
	or t3, t3, a5
	slliw a5, a4, 19
	srliw a4, a4, 13
	or a4, a4, a5
	slliw a6, t5, 9
	srliw a5, t5, 23
	or a5, a5, a6
	slliw a7, t5, 17
	srliw a6, t5, 15
	or a6, a6, a7
	xor t5, t5, a5
	xor t5, t5, a6
	lwu a5, 12(a3)
	lwu a6, 40(a3)
	xor a5, a5, a6
	lwu a6, 0(a3)
	slliw a7, a6, 15
	srliw a6, a6, 17
	or a6, a6, a7
	xor a5, a5, a6
	slliw a7, a5, 15
	srliw a6, a5, 17
	or a6, a6, a7
	slliw s0, a5, 23
	srliw a7, a5, 9
	or a7, a7, s0
	xor a5, a5, a6
	xor a5, a5, a7
	lwu a6, 24(a3)
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	xor a5, a5, a6
	lwu a6, 52(a3)
	xor a5, a5, a6
	sw a5, 12(a3)
	slliw a6, t1, 12
	srliw a5, t1, 20
	or a5, a5, a6
	add a6, a5, t5
	lui a7, 250941
	addiw a7, a7, -315
	add a6, a6, a7
	slliw a7, a6, 7
	srliw a6, a6, 25
	or a6, a6, a7
	add t4, t4, a6
	xor a5, a5, a6
	add t0, t0, a5
	lwu a7, 60(a3)
	add t4, t4, a7
	lwu s0, 12(a3)
	xor s0, a7, s0
	add t0, t0, s0
	or a5, t1, t2
	and a5, a5, t3
	and a6, t1, t2
	or a5, a5, a6
	add t0, t0, a5
	xor a5, t6, a4
	and a5, a5, t5
	xor a5, a5, a4
	add t4, t4, a5
	slliw a5, t2, 9
	srliw t2, t2, 23
	or t2, t2, a5
	slliw a5, t6, 19
	srliw t6, t6, 13
	or t6, t6, a5
	slliw a6, t4, 9
	srliw a5, t4, 23
	or a5, a5, a6
	slliw a7, t4, 17
	srliw a6, t4, 15
	or a6, a6, a7
	xor t4, t4, a5
	xor t4, t4, a6
	lbu a5, 0(a0)
	lbu a6, 1(a0)
	slli a6, a6, 8
	or a5, a5, a6
	lbu a6, 2(a0)
	slli a6, a6, 16
	or a5, a5, a6
	lbu a6, 3(a0)
	slli a6, a6, 24
	or a5, a5, a6
	xor t0, t0, a5
	sb t0, 0(a0)
	srli a5, t0, 8
	sb a5, 1(a0)
	srli a5, t0, 16
	sb a5, 2(a0)
	srli a5, t0, 24
	sb a5, 3(a0)
	lbu a5, 4(a0)
	lbu a6, 5(a0)
	slli a6, a6, 8
	or a5, a5, a6
	lbu a6, 6(a0)
	slli a6, a6, 16
	or a5, a5, a6
	lbu a6, 7(a0)
	slli a6, a6, 24
	or a5, a5, a6
	xor t1, t1, a5
	sb t1, 4(a0)
	srli a5, t1, 8
	sb a5, 5(a0)
	srli a5, t1, 16
	sb a5, 6(a0)
	srli a5, t1, 24
	sb a5, 7(a0)
	lbu a5, 8(a0)
	lbu a6, 9(a0)
	slli a6, a6, 8
	or a5, a5, a6
	lbu a6, 10(a0)
	slli a6, a6, 16
	or a5, a5, a6
	lbu a6, 11(a0)
	slli a6, a6, 24
	or a5, a5, a6
	xor t2, t2, a5
	sb t2, 8(a0)
	srli a5, t2, 8
	sb a5, 9(a0)
	srli a5, t2, 16
	sb a5, 10(a0)
	srli a5, t2, 24
	sb a5, 11(a0)
	lbu a5, 12(a0)
	lbu a6, 13(a0)
	slli a6, a6, 8
	or a5, a5, a6
	lbu a6, 14(a0)
	slli a6, a6, 16
	or a5, a5, a6
	lbu a6, 15(a0)
	slli a6, a6, 24
	or a5, a5, a6
	xor t3, t3, a5
	sb t3, 12(a0)
	srli a5, t3, 8
	sb a5, 13(a0)
	srli a5, t3, 16
	sb a5, 14(a0)
	srli a5, t3, 24
	sb a5, 15(a0)
	lbu a5, 16(a0)
	lbu a6, 17(a0)
	slli a6, a6, 8
	or a5, a5, a6
	lbu a6, 18(a0)
	slli a6, a6, 16
	or a5, a5, a6
	lbu a6, 19(a0)
	slli a6, a6, 24
	or a5, a5, a6
	xor t4, t4, a5
	sb t4, 16(a0)
	srli a5, t4, 8
	sb a5, 17(a0)
	srli a5, t4, 16
	sb a5, 18(a0)
	srli a5, t4, 24
	sb a5, 19(a0)
	lbu a5, 20(a0)
	lbu a6, 21(a0)
	slli a6, a6, 8
	or a5, a5, a6
	lbu a6, 22(a0)
	slli a6, a6, 16
	or a5, a5, a6
	lbu a6, 23(a0)
	slli a6, a6, 24
	or a5, a5, a6
	xor t5, t5, a5
	sb t5, 20(a0)
	srli a5, t5, 8
	sb a5, 21(a0)
	srli a5, t5, 16
	sb a5, 22(a0)
	srli a5, t5, 24
	sb a5, 23(a0)
	lbu a5, 24(a0)
	lbu a6, 25(a0)
	slli a6, a6, 8
	or a5, a5, a6
	lbu a6, 26(a0)
	slli a6, a6, 16
	or a5, a5, a6
	lbu a6, 27(a0)
	slli a6, a6, 24
	or a5, a5, a6
	xor t6, t6, a5
	sb t6, 24(a0)
	srli a5, t6, 8
	sb a5, 25(a0)
	srli a5, t6, 16
	sb a5, 26(a0)
	srli a5, t6, 24
	sb a5, 27(a0)
	lbu a5, 28(a0)
	lbu a6, 29(a0)
	slli a6, a6, 8
	or a5, a5, a6
	lbu a6, 30(a0)
	slli a6, a6, 16
	or a5, a5, a6
	lbu a6, 31(a0)
	slli a6, a6, 24
	or a5, a5, a6
	xor a4, a4, a5
	sb a4, 28(a0)
	srli a5, a4, 8
	sb a5, 29(a0)
	srli a5, a4, 16
	sb a5, 30(a0)
	srli a5, a4, 24
	sb a5, 31(a0)
	addi a1, a1, 64
	addi a2, a2, -1
	bnez a2, 22b
	j 21f
20:
21:
	ld s0, 64(a3)
	ret
	.option pop

vg_sm3_init:
	.option push
	.option arch, +m, +c
	lui t0, 473089
	addiw t0, t0, 1647
	sb t0, 0(a0)
	srli t1, t0, 8
	sb t1, 1(a0)
	srli t1, t0, 16
	sb t1, 2(a0)
	srli t1, t0, 24
	sb t1, 3(a0)
	lui t0, 299339
	addiw t0, t0, 697
	sb t0, 4(a0)
	srli t1, t0, 8
	sb t1, 5(a0)
	srli t1, t0, 16
	sb t1, 6(a0)
	srli t1, t0, 24
	sb t1, 7(a0)
	lui t0, 94788
	addiw t0, t0, 727
	sb t0, 8(a0)
	srli t1, t0, 8
	sb t1, 9(a0)
	srli t1, t0, 16
	sb t1, 10(a0)
	srli t1, t0, 24
	sb t1, 11(a0)
	lui t0, 895136
	addiw t0, t0, 1536
	sb t0, 12(a0)
	srli t1, t0, 8
	sb t1, 13(a0)
	srli t1, t0, 16
	sb t1, 14(a0)
	srli t1, t0, 24
	sb t1, 15(a0)
	lui t0, 694003
	addiw t0, t0, 188
	sb t0, 16(a0)
	srli t1, t0, 8
	sb t1, 17(a0)
	srli t1, t0, 16
	sb t1, 18(a0)
	srli t1, t0, 24
	sb t1, 19(a0)
	lui t0, 90900
	addiw t0, t0, -1878
	sb t0, 20(a0)
	srli t1, t0, 8
	sb t1, 21(a0)
	srli t1, t0, 16
	sb t1, 22(a0)
	srli t1, t0, 24
	sb t1, 23(a0)
	lui t0, 932063
	addiw t0, t0, -435
	sb t0, 24(a0)
	srli t1, t0, 8
	sb t1, 25(a0)
	srli t1, t0, 16
	sb t1, 26(a0)
	srli t1, t0, 24
	sb t1, 27(a0)
	lui t0, 724913
	addiw t0, t0, -434
	sb t0, 28(a0)
	srli t1, t0, 8
	sb t1, 29(a0)
	srli t1, t0, 16
	sb t1, 30(a0)
	srli t1, t0, 24
	sb t1, 31(a0)
	ret
	.option pop

vg_sm3_update:
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
	sb t1, 32(t3)
	addi s3, s3, 1
	addi s5, s5, 1
	addi t2, t2, -1
	bnez t2, 29b
	addi t1, s5, -64
	beqz t1, 210f
	j 211f
210:
	addi a1, s1, 32
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
	sb t1, 32(t3)
	addi s3, s3, 1
	addi s5, s5, 1
	addi t2, t2, -1
	bnez t2, 218b
	addi t1, s5, -64
	beqz t1, 219f
	j 220f
219:
	addi a1, s1, 32
	addi s5, zero, 0
	addi t0, zero, 1
220:
213:
24:
	beqz t0, 221f
	addi a0, s1, 0
	addi a2, zero, 1
	addi a3, s2, 0
	call {vg_sm3_compress}
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

vg_sm3_finalize:
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
	sb t1, 32(t3)
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
	sb t1, 32(t3)
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
	sb t3, 88(s1)
	srli t3, t1, 48
	sb t3, 89(s1)
	srli t3, t1, 40
	sb t3, 90(s1)
	srli t3, t1, 32
	sb t3, 91(s1)
	srli t3, t1, 24
	sb t3, 92(s1)
	srli t3, t1, 16
	sb t3, 93(s1)
	srli t3, t1, 8
	sb t3, 94(s1)
	srli t3, t1, 0
	sb t3, 95(s1)
27:
	addi a1, s1, 32
	addi a0, s1, 0
	addi a2, zero, 1
	addi a3, s2, 0
	call {vg_sm3_compress}
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
	lbu t1, 20(s1)
	lbu t2, 21(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 22(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 23(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 20(s3)
	srli t2, t1, 16
	sb t2, 21(s3)
	srli t2, t1, 8
	sb t2, 22(s3)
	srli t2, t1, 0
	sb t2, 23(s3)
	lbu t1, 24(s1)
	lbu t2, 25(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 26(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 27(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 24(s3)
	srli t2, t1, 16
	sb t2, 25(s3)
	srli t2, t1, 8
	sb t2, 26(s3)
	srli t2, t1, 0
	sb t2, 27(s3)
	lbu t1, 28(s1)
	lbu t2, 29(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 30(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 31(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 28(s3)
	srli t2, t1, 16
	sb t2, 29(s3)
	srli t2, t1, 8
	sb t2, 30(s3)
	srli t2, t1, 0
	sb t2, 31(s3)
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
