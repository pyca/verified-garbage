// The functions of `src/ecdsa_brainpoolp384r1.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_brainpoolp384r1_verify:
	.option push
	.option arch, +m, +c
	addi sp, sp, -80
	addi a5, sp, 0
	addi t0, zero, 48
	bltu a2, t0, 20f
	lbu t1, 0(a1)
	sb t1, 0(a5)
	lbu t1, 1(a1)
	sb t1, 1(a5)
	lbu t1, 2(a1)
	sb t1, 2(a5)
	lbu t1, 3(a1)
	sb t1, 3(a5)
	lbu t1, 4(a1)
	sb t1, 4(a5)
	lbu t1, 5(a1)
	sb t1, 5(a5)
	lbu t1, 6(a1)
	sb t1, 6(a5)
	lbu t1, 7(a1)
	sb t1, 7(a5)
	lbu t1, 8(a1)
	sb t1, 8(a5)
	lbu t1, 9(a1)
	sb t1, 9(a5)
	lbu t1, 10(a1)
	sb t1, 10(a5)
	lbu t1, 11(a1)
	sb t1, 11(a5)
	lbu t1, 12(a1)
	sb t1, 12(a5)
	lbu t1, 13(a1)
	sb t1, 13(a5)
	lbu t1, 14(a1)
	sb t1, 14(a5)
	lbu t1, 15(a1)
	sb t1, 15(a5)
	lbu t1, 16(a1)
	sb t1, 16(a5)
	lbu t1, 17(a1)
	sb t1, 17(a5)
	lbu t1, 18(a1)
	sb t1, 18(a5)
	lbu t1, 19(a1)
	sb t1, 19(a5)
	lbu t1, 20(a1)
	sb t1, 20(a5)
	lbu t1, 21(a1)
	sb t1, 21(a5)
	lbu t1, 22(a1)
	sb t1, 22(a5)
	lbu t1, 23(a1)
	sb t1, 23(a5)
	lbu t1, 24(a1)
	sb t1, 24(a5)
	lbu t1, 25(a1)
	sb t1, 25(a5)
	lbu t1, 26(a1)
	sb t1, 26(a5)
	lbu t1, 27(a1)
	sb t1, 27(a5)
	lbu t1, 28(a1)
	sb t1, 28(a5)
	lbu t1, 29(a1)
	sb t1, 29(a5)
	lbu t1, 30(a1)
	sb t1, 30(a5)
	lbu t1, 31(a1)
	sb t1, 31(a5)
	lbu t1, 32(a1)
	sb t1, 32(a5)
	lbu t1, 33(a1)
	sb t1, 33(a5)
	lbu t1, 34(a1)
	sb t1, 34(a5)
	lbu t1, 35(a1)
	sb t1, 35(a5)
	lbu t1, 36(a1)
	sb t1, 36(a5)
	lbu t1, 37(a1)
	sb t1, 37(a5)
	lbu t1, 38(a1)
	sb t1, 38(a5)
	lbu t1, 39(a1)
	sb t1, 39(a5)
	lbu t1, 40(a1)
	sb t1, 40(a5)
	lbu t1, 41(a1)
	sb t1, 41(a5)
	lbu t1, 42(a1)
	sb t1, 42(a5)
	lbu t1, 43(a1)
	sb t1, 43(a5)
	lbu t1, 44(a1)
	sb t1, 44(a5)
	lbu t1, 45(a1)
	sb t1, 45(a5)
	lbu t1, 46(a1)
	sb t1, 46(a5)
	lbu t1, 47(a1)
	sb t1, 47(a5)
	j 21f
20:
	addi t1, zero, 0
	sb t1, 0(a5)
	addi t1, zero, 0
	sb t1, 1(a5)
	addi t1, zero, 0
	sb t1, 2(a5)
	addi t1, zero, 0
	sb t1, 3(a5)
	addi t1, zero, 0
	sb t1, 4(a5)
	addi t1, zero, 0
	sb t1, 5(a5)
	addi t1, zero, 0
	sb t1, 6(a5)
	addi t1, zero, 0
	sb t1, 7(a5)
	addi t1, zero, 0
	sb t1, 8(a5)
	addi t1, zero, 0
	sb t1, 9(a5)
	addi t1, zero, 0
	sb t1, 10(a5)
	addi t1, zero, 0
	sb t1, 11(a5)
	addi t1, zero, 0
	sb t1, 12(a5)
	addi t1, zero, 0
	sb t1, 13(a5)
	addi t1, zero, 0
	sb t1, 14(a5)
	addi t1, zero, 0
	sb t1, 15(a5)
	addi t1, zero, 0
	sb t1, 16(a5)
	addi t1, zero, 0
	sb t1, 17(a5)
	addi t1, zero, 0
	sb t1, 18(a5)
	addi t1, zero, 0
	sb t1, 19(a5)
	addi t1, zero, 0
	sb t1, 20(a5)
	addi t1, zero, 0
	sb t1, 21(a5)
	addi t1, zero, 0
	sb t1, 22(a5)
	addi t1, zero, 0
	sb t1, 23(a5)
	addi t1, zero, 0
	sb t1, 24(a5)
	addi t1, zero, 0
	sb t1, 25(a5)
	addi t1, zero, 0
	sb t1, 26(a5)
	addi t1, zero, 0
	sb t1, 27(a5)
	addi t1, zero, 0
	sb t1, 28(a5)
	addi t1, zero, 0
	sb t1, 29(a5)
	addi t1, zero, 0
	sb t1, 30(a5)
	addi t1, zero, 0
	sb t1, 31(a5)
	addi t1, zero, 0
	sb t1, 32(a5)
	addi t1, zero, 0
	sb t1, 33(a5)
	addi t1, zero, 0
	sb t1, 34(a5)
	addi t1, zero, 0
	sb t1, 35(a5)
	addi t1, zero, 0
	sb t1, 36(a5)
	addi t1, zero, 0
	sb t1, 37(a5)
	addi t1, zero, 0
	sb t1, 38(a5)
	addi t1, zero, 0
	sb t1, 39(a5)
	addi t1, zero, 0
	sb t1, 40(a5)
	addi t1, zero, 0
	sb t1, 41(a5)
	addi t1, zero, 0
	sb t1, 42(a5)
	addi t1, zero, 0
	sb t1, 43(a5)
	addi t1, zero, 0
	sb t1, 44(a5)
	addi t1, zero, 0
	sb t1, 45(a5)
	addi t1, zero, 0
	sb t1, 46(a5)
	addi t1, zero, 0
	sb t1, 47(a5)
	addi t1, zero, 0
	sb t1, 48(a5)
	addi t1, zero, 0
	sb t1, 49(a5)
	addi t1, zero, 0
	sb t1, 50(a5)
	addi t1, zero, 0
	sb t1, 51(a5)
	addi t1, zero, 0
	sb t1, 52(a5)
	addi t1, zero, 0
	sb t1, 53(a5)
	addi t1, zero, 0
	sb t1, 54(a5)
	addi t1, zero, 0
	sb t1, 55(a5)
	addi t1, zero, 0
	sb t1, 56(a5)
	addi t1, zero, 0
	sb t1, 57(a5)
	addi t1, zero, 0
	sb t1, 58(a5)
	addi t1, zero, 0
	sb t1, 59(a5)
	addi t1, zero, 0
	sb t1, 60(a5)
	addi t1, zero, 0
	sb t1, 61(a5)
	addi t1, zero, 0
	sb t1, 62(a5)
	addi t1, zero, 0
	sb t1, 63(a5)
	addi t1, zero, 0
	sb t1, 64(a5)
	addi t1, zero, 0
	sb t1, 65(a5)
	addi t1, zero, 0
	sb t1, 66(a5)
	addi t1, zero, 0
	sb t1, 67(a5)
	addi t1, zero, 0
	sb t1, 68(a5)
	addi t1, zero, 0
	sb t1, 69(a5)
	addi t1, zero, 0
	sb t1, 70(a5)
	addi t1, zero, 0
	sb t1, 71(a5)
	addi t2, a5, 48
	sub t2, t2, a2
	beqz a2, 22f
24:
	lbu t1, 0(a1)
	sb t1, 0(t2)
	addi a1, a1, 1
	addi t2, t2, 1
	addi a2, a2, -1
	bnez a2, 24b
	j 23f
22:
23:
21:
	addi a1, a5, 0
	addi a2, a3, 0
	addi a3, a4, 0
	sd s0, 0(a3)
	sd s1, 8(a3)
	sd s2, 16(a3)
	sd ra, 24(a3)
	sd s3, 32(a3)
	addi s0, a3, 0
	addi s3, a3, 0
	addi s2, a0, 0
	lbu t0, 1(a0)
	slli t0, t0, 8
	lbu t1, 2(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 3(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 4(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 5(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 6(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 7(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 8(a0)
	or t0, t0, t1
	sd t0, 1688(s0)
	lbu t0, 9(a0)
	slli t0, t0, 8
	lbu t1, 10(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 11(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 12(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 13(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 14(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 15(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 16(a0)
	or t0, t0, t1
	sd t0, 1680(s0)
	lbu t0, 17(a0)
	slli t0, t0, 8
	lbu t1, 18(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 19(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 20(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 21(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 22(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 23(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 24(a0)
	or t0, t0, t1
	sd t0, 1672(s0)
	lbu t0, 25(a0)
	slli t0, t0, 8
	lbu t1, 26(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 27(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 28(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 29(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 30(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 31(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 32(a0)
	or t0, t0, t1
	sd t0, 1664(s0)
	lbu t0, 33(a0)
	slli t0, t0, 8
	lbu t1, 34(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 35(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 36(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 37(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 38(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 39(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 40(a0)
	or t0, t0, t1
	sd t0, 1656(s0)
	lbu t0, 41(a0)
	slli t0, t0, 8
	lbu t1, 42(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 43(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 44(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 45(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 46(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 47(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 48(a0)
	or t0, t0, t1
	sd t0, 1648(s0)
	lbu t0, 49(a0)
	slli t0, t0, 8
	lbu t1, 50(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 51(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 52(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 53(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 54(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 55(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 56(a0)
	or t0, t0, t1
	sd t0, 1832(s0)
	lbu t0, 57(a0)
	slli t0, t0, 8
	lbu t1, 58(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 59(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 60(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 61(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 62(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 63(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 64(a0)
	or t0, t0, t1
	sd t0, 1824(s0)
	lbu t0, 65(a0)
	slli t0, t0, 8
	lbu t1, 66(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 67(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 68(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 69(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 70(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 71(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 72(a0)
	or t0, t0, t1
	sd t0, 1816(s0)
	lbu t0, 73(a0)
	slli t0, t0, 8
	lbu t1, 74(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 75(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 76(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 77(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 78(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 79(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 80(a0)
	or t0, t0, t1
	sd t0, 1808(s0)
	lbu t0, 81(a0)
	slli t0, t0, 8
	lbu t1, 82(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 83(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 84(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 85(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 86(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 87(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 88(a0)
	or t0, t0, t1
	sd t0, 1800(s0)
	lbu t0, 89(a0)
	slli t0, t0, 8
	lbu t1, 90(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 91(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 92(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 93(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 94(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 95(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 96(a0)
	or t0, t0, t1
	sd t0, 1792(s0)
	lbu t0, 0(a0)
	xori t0, t0, 4
	addi t0, t0, -1
	srli t0, t0, 63
	addi t1, zero, 0
	sub a7, t1, t0
	addi s0, s0, 2047
	sd a7, 129(s0)
	addi s0, s0, -2047
	lui t0, 554096
	addiw t0, t0, 19
	slli t0, t0, 32
	lui t1, 200831
	addiw t1, t1, -941
	add t0, t0, t1
	sd t0, 64(s0)
	lui t0, 707898
	addiw t0, t0, 1834
	slli t0, t0, 32
	lui t1, 590290
	addiw t1, t1, -1423
	add t0, t0, t1
	sd t0, 72(s0)
	lui t0, 76574
	addiw t0, t0, -1511
	slli t0, t0, 32
	lui t1, 523121
	addiw t1, t1, 291
	add t0, t0, t1
	sd t0, 80(s0)
	lui t0, 86775
	addiw t0, t0, 266
	slli t0, t0, 32
	lui t1, 972101
	addiw t1, t1, 1716
	add t0, t0, t1
	sd t0, 88(s0)
	lui t0, 62935
	addiw t0, t0, -130
	slli t0, t0, 32
	lui t1, 331364
	addiw t1, t1, 479
	add t0, t0, t1
	sd t0, 96(s0)
	lui t0, 576402
	addiw t0, t0, -381
	slli t0, t0, 32
	lui t1, 668551
	addiw t1, t1, -728
	add t0, t0, t1
	sd t0, 104(s0)
	lui t0, 243843
	addiw t0, t0, 515
	slli t0, t0, 32
	lui t1, 954438
	addiw t1, t1, 1381
	add t0, t0, t1
	sd t0, 112(s0)
	lui t0, 848811
	addiw t0, t0, 1711
	slli t0, t0, 32
	lui t1, 440316
	addiw t1, t1, 784
	add t0, t0, t1
	sd t0, 120(s0)
	lui t0, 127335
	addiw t0, t0, -403
	slli t0, t0, 32
	lui t1, 704578
	addiw t1, t1, 1447
	add t0, t0, t1
	sd t0, 128(s0)
	lui t0, 86775
	addiw t0, t0, 266
	slli t0, t0, 32
	lui t1, 972101
	addiw t1, t1, 1715
	add t0, t0, t1
	sd t0, 136(s0)
	lui t0, 62935
	addiw t0, t0, -130
	slli t0, t0, 32
	lui t1, 331364
	addiw t1, t1, 479
	add t0, t0, t1
	sd t0, 144(s0)
	lui t0, 576402
	addiw t0, t0, -381
	slli t0, t0, 32
	lui t1, 668551
	addiw t1, t1, -728
	add t0, t0, t1
	sd t0, 152(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 208(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 216(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 224(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 232(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 240(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 248(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 1
	add t0, t0, t1
	sd t0, 256(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 264(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 272(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 280(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 288(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 296(s0)
	lui t0, 494480
	addiw t0, t0, -19
	slli t0, t0, 32
	lui t1, 847745
	addiw t1, t1, 941
	add t0, t0, t1
	sd t0, 304(s0)
	lui t0, 340678
	addiw t0, t0, -1834
	slli t0, t0, 32
	lui t1, 458286
	addiw t1, t1, 1422
	add t0, t0, t1
	sd t0, 312(s0)
	lui t0, 972002
	addiw t0, t0, 1511
	slli t0, t0, 32
	lui t1, 525455
	addiw t1, t1, -292
	add t0, t0, t1
	sd t0, 320(s0)
	lui t0, 961801
	addiw t0, t0, -266
	slli t0, t0, 32
	lui t1, 76475
	addiw t1, t1, -1717
	add t0, t0, t1
	sd t0, 328(s0)
	lui t0, 985641
	addiw t0, t0, 130
	slli t0, t0, 32
	lui t1, 717212
	addiw t1, t1, -480
	add t0, t0, t1
	sd t0, 336(s0)
	lui t0, 472174
	addiw t0, t0, 381
	slli t0, t0, 32
	lui t1, 380025
	addiw t1, t1, 727
	add t0, t0, t1
	sd t0, 344(s0)
	lui t0, 897644
	addiw t0, t0, -1899
	slli t0, t0, 32
	lui t1, 288452
	addiw t1, t1, -871
	add t0, t0, t1
	sd t0, 352(s0)
	lui t0, 482687
	addiw t0, t0, 1023
	slli t0, t0, 32
	lui t1, 988539
	addiw t1, t1, 123
	add t0, t0, t1
	sd t0, 360(s0)
	lui t0, 603767
	addiw t0, t0, 442
	slli t0, t0, 32
	lui t1, 884497
	addiw t1, t1, -588
	add t0, t0, t1
	sd t0, 368(s0)
	lui t0, 950271
	addiw t0, t0, -1563
	slli t0, t0, 32
	lui t1, 218409
	addiw t1, t1, 884
	add t0, t0, t1
	sd t0, 376(s0)
	lui t0, 262313
	addiw t0, t0, -33
	slli t0, t0, 32
	lui t1, 273153
	addiw t1, t1, -928
	add t0, t0, t1
	sd t0, 384(s0)
	lui t0, 508728
	addiw t0, t0, 34
	slli t0, t0, 32
	lui t1, 667276
	addiw t1, t1, 209
	add t0, t0, t1
	sd t0, 392(s0)
	lui t0, 875696
	addiw t0, t0, -1621
	slli t0, t0, 32
	lui t1, 857387
	addiw t1, t1, 2036
	add t0, t0, t1
	sd t0, 400(s0)
	lui t0, 1006484
	addiw t0, t0, 47
	slli t0, t0, 32
	lui t1, 855825
	addiw t1, t1, 1335
	add t0, t0, t1
	sd t0, 408(s0)
	lui t0, 353971
	addiw t0, t0, -1486
	slli t0, t0, 32
	lui t1, 416468
	addiw t1, t1, -1174
	add t0, t0, t1
	sd t0, 416(s0)
	lui t0, 198979
	addiw t0, t0, 1902
	slli t0, t0, 32
	lui t1, 57658
	addiw t1, t1, 1494
	add t0, t0, t1
	sd t0, 424(s0)
	lui t0, 467913
	addiw t0, t0, 1031
	slli t0, t0, 32
	lui t1, 149523
	addiw t1, t1, -456
	add t0, t0, t1
	sd t0, 432(s0)
	lui t0, 274437
	addiw t0, t0, -402
	slli t0, t0, 32
	lui t1, 88498
	addiw t1, t1, 1750
	add t0, t0, t1
	sd t0, 440(s0)
	lui t0, 661662
	addiw t0, t0, -276
	slli t0, t0, 32
	lui t1, 869264
	addiw t1, t1, -1087
	add t0, t0, t1
	sd t0, 448(s0)
	lui t0, 421832
	addiw t0, t0, 233
	slli t0, t0, 32
	lui t1, 875144
	addiw t1, t1, 1727
	add t0, t0, t1
	sd t0, 456(s0)
	lui t0, 609336
	addiw t0, t0, -1814
	slli t0, t0, 32
	lui t1, 643587
	addiw t1, t1, -221
	add t0, t0, t1
	sd t0, 464(s0)
	lui t0, 26802
	addiw t0, t0, 1615
	slli t0, t0, 32
	lui t1, 1021378
	addiw t1, t1, 356
	add t0, t0, t1
	sd t0, 472(s0)
	lui t0, 642513
	addiw t0, t0, -560
	slli t0, t0, 32
	lui t1, 765136
	addiw t1, t1, 153
	add t0, t0, t1
	sd t0, 480(s0)
	lui t0, 544775
	addiw t0, t0, 1332
	slli t0, t0, 32
	lui t1, 560980
	addiw t1, t1, -63
	add t0, t0, t1
	sd t0, 488(s0)
	lui t0, 947083
	addiw t0, t0, 817
	slli t0, t0, 32
	lui t1, 56852
	addiw t1, t1, 165
	add t0, t0, t1
	sd t0, 496(s0)
	lui t0, 1007117
	addiw t0, t0, 583
	slli t0, t0, 32
	lui t1, 817559
	addiw t1, t1, -171
	add t0, t0, t1
	sd t0, 504(s0)
	lui t0, 1017905
	addiw t0, t0, -1628
	slli t0, t0, 32
	lui t1, 585843
	addiw t1, t1, 2044
	add t0, t0, t1
	sd t0, 512(s0)
	lui t0, 661515
	addiw t0, t0, -811
	slli t0, t0, 32
	lui t1, 874265
	addiw t1, t1, 535
	add t0, t0, t1
	sd t0, 520(s0)
	lui t0, 811362
	addiw t0, t0, 1382
	slli t0, t0, 32
	lui t1, 324126
	addiw t1, t1, -586
	add t0, t0, t1
	sd t0, 528(s0)
	lui t0, 184138
	addiw t0, t0, 98
	slli t0, t0, 32
	lui t1, 284823
	addiw t1, t1, -1867
	add t0, t0, t1
	sd t0, 536(s0)
	lui t0, 554096
	addiw t0, t0, 19
	slli t0, t0, 32
	lui t1, 200831
	addiw t1, t1, -943
	add t0, t0, t1
	sd t0, 640(s0)
	lui t0, 707898
	addiw t0, t0, 1834
	slli t0, t0, 32
	lui t1, 590290
	addiw t1, t1, -1423
	add t0, t0, t1
	sd t0, 648(s0)
	lui t0, 76574
	addiw t0, t0, -1511
	slli t0, t0, 32
	lui t1, 523121
	addiw t1, t1, 291
	add t0, t0, t1
	sd t0, 656(s0)
	lui t0, 86775
	addiw t0, t0, 266
	slli t0, t0, 32
	lui t1, 972101
	addiw t1, t1, 1716
	add t0, t0, t1
	sd t0, 664(s0)
	lui t0, 62935
	addiw t0, t0, -130
	slli t0, t0, 32
	lui t1, 331364
	addiw t1, t1, 479
	add t0, t0, t1
	sd t0, 672(s0)
	lui t0, 576402
	addiw t0, t0, -381
	slli t0, t0, 32
	lui t1, 668551
	addiw t1, t1, -728
	add t0, t0, t1
	sd t0, 680(s0)
	lui t0, 34767
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 265061
	addiw t1, t1, -1058
	add t0, t0, t1
	sd t0, 1936(s0)
	lui t0, 341288
	addiw t0, t0, 820
	slli t0, t0, 32
	lui t1, 251902
	addiw t1, t1, -1691
	add t0, t0, t1
	sd t0, 1944(s0)
	lui t0, 582288
	addiw t0, t0, -1635
	slli t0, t0, 32
	lui t1, 825665
	addiw t1, t1, -1895
	add t0, t0, t1
	sd t0, 1952(s0)
	lui t0, 401728
	addiw t0, t0, 402
	slli t0, t0, 32
	lui t1, 627085
	addiw t1, t1, 1455
	add t0, t0, t1
	sd t0, 1960(s0)
	lui t0, 875631
	addiw t0, t0, -196
	slli t0, t0, 32
	lui t1, 677856
	addiw t1, t1, 1324
	add t0, t0, t1
	sd t0, 1968(s0)
	lui t0, 224247
	addiw t0, t0, -1917
	slli t0, t0, 32
	lui t1, 96480
	addiw t1, t1, -1982
	add t0, t0, t1
	sd t0, 1976(s0)
	lui t0, 127072
	addiw t0, t0, -534
	slli t0, t0, 32
	lui t1, 3214
	addiw t1, t1, 365
	add t0, t0, t1
	sd t0, 1984(s0)
	lui t0, 221935
	addiw t0, t0, 1992
	slli t0, t0, 32
	lui t1, 132513
	addiw t1, t1, -29
	add t0, t0, t1
	sd t0, 1992(s0)
	lui t0, 842565
	addiw t0, t0, 1732
	slli t0, t0, 32
	lui t1, 1012247
	addiw t1, t1, -294
	add t0, t0, t1
	sd t0, 2000(s0)
	lui t0, 95252
	addiw t0, t0, -2008
	slli t0, t0, 32
	lui t1, 1042304
	addiw t1, t1, -296
	add t0, t0, t1
	sd t0, 2008(s0)
	lui t0, 176949
	addiw t0, t0, 1666
	slli t0, t0, 32
	lui t1, 859346
	addiw t1, t1, 1373
	add t0, t0, t1
	sd t0, 2016(s0)
	lui t0, 283613
	addiw t0, t0, -261
	slli t0, t0, 32
	lui t1, 951400
	addiw t1, t1, 1706
	add t0, t0, t1
	sd t0, 2024(s0)
	lbu t0, 0(a2)
	slli t0, t0, 8
	lbu t1, 1(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 2(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 3(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 4(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 5(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 6(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 7(a2)
	or t0, t0, t1
	sd t0, 584(s0)
	lbu t0, 8(a2)
	slli t0, t0, 8
	lbu t1, 9(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 10(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 11(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 12(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 13(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 14(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 15(a2)
	or t0, t0, t1
	sd t0, 576(s0)
	lbu t0, 16(a2)
	slli t0, t0, 8
	lbu t1, 17(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 18(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 19(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 20(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 21(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 22(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 23(a2)
	or t0, t0, t1
	sd t0, 568(s0)
	lbu t0, 24(a2)
	slli t0, t0, 8
	lbu t1, 25(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 26(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 27(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 28(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 29(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 30(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 31(a2)
	or t0, t0, t1
	sd t0, 560(s0)
	lbu t0, 32(a2)
	slli t0, t0, 8
	lbu t1, 33(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 34(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 35(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 36(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 37(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 38(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 39(a2)
	or t0, t0, t1
	sd t0, 552(s0)
	lbu t0, 40(a2)
	slli t0, t0, 8
	lbu t1, 41(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 42(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 43(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 44(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 45(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 46(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 47(a2)
	or t0, t0, t1
	sd t0, 544(s0)
	lbu t0, 48(a2)
	slli t0, t0, 8
	lbu t1, 49(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 50(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 51(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 52(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 53(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 54(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 55(a2)
	or t0, t0, t1
	sd t0, 632(s0)
	lbu t0, 56(a2)
	slli t0, t0, 8
	lbu t1, 57(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 58(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 59(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 60(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 61(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 62(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 63(a2)
	or t0, t0, t1
	sd t0, 624(s0)
	lbu t0, 64(a2)
	slli t0, t0, 8
	lbu t1, 65(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 66(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 67(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 68(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 69(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 70(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 71(a2)
	or t0, t0, t1
	sd t0, 616(s0)
	lbu t0, 72(a2)
	slli t0, t0, 8
	lbu t1, 73(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 74(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 75(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 76(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 77(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 78(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 79(a2)
	or t0, t0, t1
	sd t0, 608(s0)
	lbu t0, 80(a2)
	slli t0, t0, 8
	lbu t1, 81(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 82(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 83(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 84(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 85(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 86(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 87(a2)
	or t0, t0, t1
	sd t0, 600(s0)
	lbu t0, 88(a2)
	slli t0, t0, 8
	lbu t1, 89(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 90(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 91(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 92(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 93(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 94(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 95(a2)
	or t0, t0, t1
	sd t0, 592(s0)
	lbu t0, 0(a1)
	slli t0, t0, 8
	lbu t1, 1(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 2(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 3(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 4(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 5(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 6(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 7(a1)
	or t0, t0, t1
	sd t0, 1640(s0)
	lbu t0, 8(a1)
	slli t0, t0, 8
	lbu t1, 9(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 10(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 11(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 12(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 13(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 14(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 15(a1)
	or t0, t0, t1
	sd t0, 1632(s0)
	lbu t0, 16(a1)
	slli t0, t0, 8
	lbu t1, 17(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 18(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 19(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 20(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 21(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 22(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 23(a1)
	or t0, t0, t1
	sd t0, 1624(s0)
	lbu t0, 24(a1)
	slli t0, t0, 8
	lbu t1, 25(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 26(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 27(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 28(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 29(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 30(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 31(a1)
	or t0, t0, t1
	sd t0, 1616(s0)
	lbu t0, 32(a1)
	slli t0, t0, 8
	lbu t1, 33(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 34(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 35(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 36(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 37(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 38(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 39(a1)
	or t0, t0, t1
	sd t0, 1608(s0)
	lbu t0, 40(a1)
	slli t0, t0, 8
	lbu t1, 41(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 42(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 43(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 44(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 45(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 46(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 47(a1)
	or t0, t0, t1
	sd t0, 1600(s0)
	addi t5, zero, 0
	ld t3, 544(s0)
	ld t4, 112(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 552(s0)
	ld t4, 120(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 560(s0)
	ld t4, 128(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 568(s0)
	ld t4, 136(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 576(s0)
	ld t4, 144(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 584(s0)
	ld t4, 152(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t6, zero, 0
	sub a7, t6, t5
	addi t0, s0, 2047
	ld t0, 129(t0)
	and t0, t0, a7
	addi s0, s0, 2047
	sd t0, 129(s0)
	addi s0, s0, -2047
	addi t3, zero, 0
	ld t4, 544(s0)
	or t3, t3, t4
	ld t4, 552(s0)
	or t3, t3, t4
	ld t4, 560(s0)
	or t3, t3, t4
	ld t4, 568(s0)
	or t3, t3, t4
	ld t4, 576(s0)
	or t3, t3, t4
	ld t4, 584(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	xori a7, a7, -1
	addi t0, s0, 2047
	ld t0, 129(t0)
	and t0, t0, a7
	addi s0, s0, 2047
	sd t0, 129(s0)
	addi s0, s0, -2047
	addi t5, zero, 0
	ld t3, 592(s0)
	ld t4, 112(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 600(s0)
	ld t4, 120(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 608(s0)
	ld t4, 128(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 616(s0)
	ld t4, 136(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 624(s0)
	ld t4, 144(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 632(s0)
	ld t4, 152(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t6, zero, 0
	sub a7, t6, t5
	addi t0, s0, 2047
	ld t0, 129(t0)
	and t0, t0, a7
	addi s0, s0, 2047
	sd t0, 129(s0)
	addi s0, s0, -2047
	addi t3, zero, 0
	ld t4, 592(s0)
	or t3, t3, t4
	ld t4, 600(s0)
	or t3, t3, t4
	ld t4, 608(s0)
	or t3, t3, t4
	ld t4, 616(s0)
	or t3, t3, t4
	ld t4, 624(s0)
	or t3, t3, t4
	ld t4, 632(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	xori a7, a7, -1
	addi t0, s0, 2047
	ld t0, 129(t0)
	and t0, t0, a7
	addi s0, s0, 2047
	sd t0, 129(s0)
	addi s0, s0, -2047
	addi a0, s0, 0
	call {vg_brainpoolp384r1_check_point}
	addi s0, s3, 0
	lui t0, 705773
	addiw t0, t0, 931
	slli t0, t0, 32
	lui t1, 911218
	addiw t1, t1, -882
	add t0, t0, t1
	sd t0, 1744(s0)
	lui t0, 225893
	addiw t0, t0, -480
	slli t0, t0, 32
	lui t1, 193207
	addiw t1, t1, -1170
	add t0, t0, t1
	sd t0, 1752(s0)
	lui t0, 174376
	addiw t0, t0, -452
	slli t0, t0, 32
	lui t1, 622631
	addiw t1, t1, -1910
	add t0, t0, t1
	sd t0, 1760(s0)
	lui t0, 357543
	addiw t0, t0, 1227
	slli t0, t0, 32
	lui t1, 339317
	addiw t1, t1, -1793
	add t0, t0, t1
	sd t0, 1768(s0)
	lui t0, 587911
	addiw t0, t0, -567
	slli t0, t0, 32
	lui t1, 414054
	addiw t1, t1, -37
	add t0, t0, t1
	sd t0, 1776(s0)
	lui t0, 52873
	addiw t0, t0, 1050
	slli t0, t0, 32
	lui t1, 398569
	addiw t1, t1, 1986
	add t0, t0, t1
	sd t0, 1784(s0)
	lui t0, 804733
	addiw t0, t0, -515
	slli t0, t0, 32
	lui t1, 94138
	addiw t1, t1, -1381
	add t0, t0, t1
	sd t0, 1792(s0)
	lui t0, 199765
	addiw t0, t0, -1711
	slli t0, t0, 32
	lui t1, 608260
	addiw t1, t1, -785
	add t0, t0, t1
	sd t0, 1800(s0)
	lui t0, 921241
	addiw t0, t0, 403
	slli t0, t0, 32
	lui t1, 343998
	addiw t1, t1, -1448
	add t0, t0, t1
	sd t0, 1808(s0)
	lui t0, 961801
	addiw t0, t0, -266
	slli t0, t0, 32
	lui t1, 76475
	addiw t1, t1, -1716
	add t0, t0, t1
	sd t0, 1816(s0)
	lui t0, 985641
	addiw t0, t0, 130
	slli t0, t0, 32
	lui t1, 717212
	addiw t1, t1, -480
	add t0, t0, t1
	sd t0, 1824(s0)
	lui t0, 472174
	addiw t0, t0, 381
	slli t0, t0, 32
	lui t1, 380025
	addiw t1, t1, 727
	add t0, t0, t1
	sd t0, 1832(s0)
	lui t0, 243843
	addiw t0, t0, 515
	slli t0, t0, 32
	lui t1, 954438
	addiw t1, t1, 1379
	add t0, t0, t1
	sd t0, 1840(s0)
	lui t0, 848811
	addiw t0, t0, 1711
	slli t0, t0, 32
	lui t1, 440316
	addiw t1, t1, 784
	add t0, t0, t1
	sd t0, 1848(s0)
	lui t0, 127335
	addiw t0, t0, -403
	slli t0, t0, 32
	lui t1, 704578
	addiw t1, t1, 1447
	add t0, t0, t1
	sd t0, 1856(s0)
	lui t0, 86775
	addiw t0, t0, 266
	slli t0, t0, 32
	lui t1, 972101
	addiw t1, t1, 1715
	add t0, t0, t1
	sd t0, 1864(s0)
	lui t0, 62935
	addiw t0, t0, -130
	slli t0, t0, 32
	lui t1, 331364
	addiw t1, t1, 479
	add t0, t0, t1
	sd t0, 1872(s0)
	lui t0, 576402
	addiw t0, t0, -381
	slli t0, t0, 32
	lui t1, 668551
	addiw t1, t1, -728
	add t0, t0, t1
	sd t0, 1880(s0)
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 592
	addi a3, zero, 1744
	call {vg_brainpoolp384r1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 225
	addi a2, zero, 1024
	addi a3, zero, 1792
	call {vg_brainpoolp384r1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 609
	addi a2, zero, 2047
	addi a2, a2, 225
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_brainpoolp384r1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 273
	addi a2, zero, 2047
	addi a2, a2, 225
	addi a3, zero, 2047
	addi a3, a3, 609
	call {vg_brainpoolp384r1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 321
	addi a2, zero, 2047
	addi a2, a2, 273
	addi a3, zero, 2047
	addi a3, a3, 609
	call {vg_brainpoolp384r1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 369
	addi a2, zero, 2047
	addi a2, a2, 321
	addi a3, zero, 2047
	addi a3, a3, 609
	call {vg_brainpoolp384r1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 417
	addi a2, zero, 2047
	addi a2, a2, 369
	addi a3, zero, 2047
	addi a3, a3, 609
	call {vg_brainpoolp384r1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 465
	addi a2, zero, 2047
	addi a2, a2, 417
	addi a3, zero, 2047
	addi a3, a3, 609
	call {vg_brainpoolp384r1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 513
	addi a2, zero, 2047
	addi a2, a2, 465
	addi a3, zero, 2047
	addi a3, a3, 609
	call {vg_brainpoolp384r1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 561
	addi a2, zero, 2047
	addi a2, a2, 513
	addi a3, zero, 2047
	addi a3, a3, 609
	call {vg_brainpoolp384r1_mul_mod_n}
	addi t0, s0, 2047
	ld t0, 225(t0)
	sd t0, 1456(s0)
	addi t0, s0, 2047
	ld t0, 233(t0)
	sd t0, 1464(s0)
	addi t0, s0, 2047
	ld t0, 241(t0)
	sd t0, 1472(s0)
	addi t0, s0, 2047
	ld t0, 249(t0)
	sd t0, 1480(s0)
	addi t0, s0, 2047
	ld t0, 257(t0)
	sd t0, 1488(s0)
	addi t0, s0, 2047
	ld t0, 265(t0)
	sd t0, 1496(s0)
	addi s1, zero, 5
25:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 25b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 273
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 6
26:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 26b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 465
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 4
27:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 27b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 417
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 7
28:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 28b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 2
29:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 29b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 8
210:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 210b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 2
211:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 211b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 5
212:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 212b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 273
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 5
213:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 213b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 369
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 8
214:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 214b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 3
215:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 215b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 5
216:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 216b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 11
217:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 217b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 5
218:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 218b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 465
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 3
219:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 219b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 5
220:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 220b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 3
221:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 221b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 369
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 5
222:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 222b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 2
223:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 223b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 273
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 5
224:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 224b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 7
225:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 225b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 369
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 4
226:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 226b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 273
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 3
227:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 227b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 8
228:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 228b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 369
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 5
229:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 229b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 1
230:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 230b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 6
231:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 231b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 5
232:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 232b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 417
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 5
233:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 233b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 4
234:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 234b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 369
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 4
235:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 235b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 8
236:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 236b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 417
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 3
237:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 237b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 369
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 5
238:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 238b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 4
239:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 239b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 2
240:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 240b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 6
241:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 241b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 5
242:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 242b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 3
243:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 243b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 273
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 4
244:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 244b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 273
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 7
245:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 245b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 1
246:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 246b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 7
247:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 247b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 465
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 6
248:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 248b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 2
249:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 249b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 273
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 6
250:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 250b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 4
251:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 251b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 417
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 5
252:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 252b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 465
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 8
253:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 253b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 8
254:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 254b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 417
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 5
255:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 255b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 6
256:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 256b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 4
257:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 257b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 417
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 3
258:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 258b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 369
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 5
259:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 259b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 369
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 4
260:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 260b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 5
261:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 261b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 3
262:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 262b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 5
263:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 263b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 465
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 4
264:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 264b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 3
265:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 265b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 5
266:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 266b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 4
267:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 267b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 4
268:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 268b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 6
269:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 269b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 273
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 4
270:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 270b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 9
271:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 271b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 369
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 4
272:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 272b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 369
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 4
273:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 273b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 7
274:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 274b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 273
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 3
275:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 275b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 11
276:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 276b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 465
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 3
277:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 277b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 3
278:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 278b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 6
279:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 279b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 5
280:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 280b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 273
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 5
281:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 281b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 3
282:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 282b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 273
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 5
283:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 283b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 273
	call {vg_brainpoolp384r1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1600
	addi a3, zero, 1744
	call {vg_brainpoolp384r1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1072
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1648
	addi a2, zero, 1120
	addi a3, zero, 256
	call {vg_brainpoolp384r1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 544
	addi a3, zero, 1744
	call {vg_brainpoolp384r1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1120
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1216
	addi a3, zero, 256
	call {vg_brainpoolp384r1_mul_mod_n}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 208(s0)
	sd t0, 0(a6)
	ld t0, 216(s0)
	sd t0, 8(a6)
	ld t0, 224(s0)
	sd t0, 16(a6)
	ld t0, 232(s0)
	sd t0, 24(a6)
	ld t0, 240(s0)
	sd t0, 32(a6)
	ld t0, 248(s0)
	sd t0, 40(a6)
	ld t0, 304(s0)
	sd t0, 48(a6)
	ld t0, 312(s0)
	sd t0, 56(a6)
	ld t0, 320(s0)
	sd t0, 64(a6)
	ld t0, 328(s0)
	sd t0, 72(a6)
	ld t0, 336(s0)
	sd t0, 80(a6)
	ld t0, 344(s0)
	sd t0, 88(a6)
	ld t0, 208(s0)
	sd t0, 96(a6)
	ld t0, 216(s0)
	sd t0, 104(a6)
	ld t0, 224(s0)
	sd t0, 112(a6)
	ld t0, 232(s0)
	sd t0, 120(a6)
	ld t0, 240(s0)
	sd t0, 128(a6)
	ld t0, 248(s0)
	sd t0, 136(a6)
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 448(s0)
	sd t0, 576(a6)
	ld t0, 456(s0)
	sd t0, 584(a6)
	ld t0, 464(s0)
	sd t0, 592(a6)
	ld t0, 472(s0)
	sd t0, 600(a6)
	ld t0, 480(s0)
	sd t0, 608(a6)
	ld t0, 488(s0)
	sd t0, 616(a6)
	ld t0, 496(s0)
	sd t0, 624(a6)
	ld t0, 504(s0)
	sd t0, 632(a6)
	ld t0, 512(s0)
	sd t0, 640(a6)
	ld t0, 520(s0)
	sd t0, 648(a6)
	ld t0, 528(s0)
	sd t0, 656(a6)
	ld t0, 536(s0)
	sd t0, 664(a6)
	ld t0, 304(s0)
	sd t0, 672(a6)
	ld t0, 312(s0)
	sd t0, 680(a6)
	ld t0, 320(s0)
	sd t0, 688(a6)
	ld t0, 328(s0)
	sd t0, 696(a6)
	ld t0, 336(s0)
	sd t0, 704(a6)
	ld t0, 344(s0)
	sd t0, 712(a6)
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 1888(s0)
	sd t0, 144(a6)
	ld t0, 1896(s0)
	sd t0, 152(a6)
	ld t0, 1904(s0)
	sd t0, 160(a6)
	ld t0, 1912(s0)
	sd t0, 168(a6)
	ld t0, 1920(s0)
	sd t0, 176(a6)
	ld t0, 1928(s0)
	sd t0, 184(a6)
	addi t0, s0, 2047
	ld t0, 81(t0)
	sd t0, 192(a6)
	addi t0, s0, 2047
	ld t0, 89(t0)
	sd t0, 200(a6)
	addi t0, s0, 2047
	ld t0, 97(t0)
	sd t0, 208(a6)
	addi t0, s0, 2047
	ld t0, 105(t0)
	sd t0, 216(a6)
	addi t0, s0, 2047
	ld t0, 113(t0)
	sd t0, 224(a6)
	addi t0, s0, 2047
	ld t0, 121(t0)
	sd t0, 232(a6)
	ld t0, 304(s0)
	sd t0, 240(a6)
	ld t0, 312(s0)
	sd t0, 248(a6)
	ld t0, 320(s0)
	sd t0, 256(a6)
	ld t0, 328(s0)
	sd t0, 264(a6)
	ld t0, 336(s0)
	sd t0, 272(a6)
	ld t0, 344(s0)
	sd t0, 280(a6)
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 448
	addi a3, zero, 448
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 496
	addi a3, zero, 496
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 304
	addi a3, zero, 304
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 448
	addi a3, zero, 496
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 448
	addi a3, zero, 496
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1168
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 448
	addi a3, zero, 304
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 448
	addi a3, zero, 304
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 496
	addi a3, zero, 304
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 225
	addi a2, zero, 496
	addi a3, zero, 304
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 225
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 321
	addi a2, zero, 352
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 225
	addi a2, zero, 400
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 321
	addi a2, zero, 2047
	addi a2, a2, 225
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 225
	addi a2, zero, 1216
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 321
	addi a2, zero, 1216
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 273
	addi a2, zero, 2047
	addi a2, a2, 225
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1168
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 400
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1216
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 273
	addi a2, zero, 2047
	addi a2, a2, 273
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1408
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 225
	addi a2, zero, 1312
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 225
	addi a2, zero, 2047
	addi a2, a2, 225
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1312
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 321
	addi a2, zero, 1408
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 321
	addi a2, zero, 2047
	addi a2, a2, 321
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	addi t0, s0, 2047
	ld t0, 225(t0)
	sd t0, 1152(a6)
	addi t0, s0, 2047
	ld t0, 233(t0)
	sd t0, 1160(a6)
	addi t0, s0, 2047
	ld t0, 241(t0)
	sd t0, 1168(a6)
	addi t0, s0, 2047
	ld t0, 249(t0)
	sd t0, 1176(a6)
	addi t0, s0, 2047
	ld t0, 257(t0)
	sd t0, 1184(a6)
	addi t0, s0, 2047
	ld t0, 265(t0)
	sd t0, 1192(a6)
	addi t0, s0, 2047
	ld t0, 273(t0)
	sd t0, 1200(a6)
	addi t0, s0, 2047
	ld t0, 281(t0)
	sd t0, 1208(a6)
	addi t0, s0, 2047
	ld t0, 289(t0)
	sd t0, 1216(a6)
	addi t0, s0, 2047
	ld t0, 297(t0)
	sd t0, 1224(a6)
	addi t0, s0, 2047
	ld t0, 305(t0)
	sd t0, 1232(a6)
	addi t0, s0, 2047
	ld t0, 313(t0)
	sd t0, 1240(a6)
	addi t0, s0, 2047
	ld t0, 321(t0)
	sd t0, 1248(a6)
	addi t0, s0, 2047
	ld t0, 329(t0)
	sd t0, 1256(a6)
	addi t0, s0, 2047
	ld t0, 337(t0)
	sd t0, 1264(a6)
	addi t0, s0, 2047
	ld t0, 345(t0)
	sd t0, 1272(a6)
	addi t0, s0, 2047
	ld t0, 353(t0)
	sd t0, 1280(a6)
	addi t0, s0, 2047
	ld t0, 361(t0)
	sd t0, 1288(a6)
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 2047
	addi a2, a2, 225
	addi a3, zero, 448
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 2047
	addi a2, a2, 273
	addi a3, zero, 496
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 2047
	addi a2, a2, 321
	addi a3, zero, 304
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 2047
	addi a2, a2, 225
	addi a3, zero, 2047
	addi a3, a3, 273
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 448
	addi a3, zero, 496
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1168
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 2047
	addi a2, a2, 225
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 448
	addi a3, zero, 304
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 2047
	addi a2, a2, 273
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 369
	addi a2, zero, 496
	addi a3, zero, 304
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 2047
	addi a3, a3, 369
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 369
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 2047
	addi a3, a3, 369
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 465
	addi a2, zero, 352
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 369
	addi a2, zero, 400
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 465
	addi a2, zero, 2047
	addi a2, a2, 369
	addi a3, zero, 2047
	addi a3, a3, 465
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 369
	addi a2, zero, 1216
	addi a3, zero, 2047
	addi a3, a3, 465
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 465
	addi a2, zero, 1216
	addi a3, zero, 2047
	addi a3, a3, 465
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 417
	addi a2, zero, 2047
	addi a2, a2, 369
	addi a3, zero, 2047
	addi a3, a3, 465
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1168
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 400
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1216
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 417
	addi a2, zero, 2047
	addi a2, a2, 417
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1408
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 369
	addi a2, zero, 1312
	addi a3, zero, 2047
	addi a3, a3, 369
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 369
	addi a2, zero, 2047
	addi a2, a2, 369
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1312
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 465
	addi a2, zero, 1408
	addi a3, zero, 2047
	addi a3, a3, 465
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 465
	addi a2, zero, 2047
	addi a2, a2, 465
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	addi t0, s0, 2047
	ld t0, 369(t0)
	sd t0, 1728(a6)
	addi t0, s0, 2047
	ld t0, 377(t0)
	sd t0, 1736(a6)
	addi t0, s0, 2047
	ld t0, 385(t0)
	sd t0, 1744(a6)
	addi t0, s0, 2047
	ld t0, 393(t0)
	sd t0, 1752(a6)
	addi t0, s0, 2047
	ld t0, 401(t0)
	sd t0, 1760(a6)
	addi t0, s0, 2047
	ld t0, 409(t0)
	sd t0, 1768(a6)
	addi t0, s0, 2047
	ld t0, 417(t0)
	sd t0, 1776(a6)
	addi t0, s0, 2047
	ld t0, 425(t0)
	sd t0, 1784(a6)
	addi t0, s0, 2047
	ld t0, 433(t0)
	sd t0, 1792(a6)
	addi t0, s0, 2047
	ld t0, 441(t0)
	sd t0, 1800(a6)
	addi t0, s0, 2047
	ld t0, 449(t0)
	sd t0, 1808(a6)
	addi t0, s0, 2047
	ld t0, 457(t0)
	sd t0, 1816(a6)
	addi t0, s0, 2047
	ld t0, 465(t0)
	sd t0, 1824(a6)
	addi t0, s0, 2047
	ld t0, 473(t0)
	sd t0, 1832(a6)
	addi t0, s0, 2047
	ld t0, 481(t0)
	sd t0, 1840(a6)
	addi t0, s0, 2047
	ld t0, 489(t0)
	sd t0, 1848(a6)
	addi t0, s0, 2047
	ld t0, 497(t0)
	sd t0, 1856(a6)
	addi t0, s0, 2047
	ld t0, 505(t0)
	sd t0, 1864(a6)
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1888
	addi a3, zero, 1888
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 2047
	addi a2, a2, 81
	addi a3, zero, 2047
	addi a3, a3, 81
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 304
	addi a3, zero, 304
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1888
	addi a3, zero, 2047
	addi a3, a3, 81
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1888
	addi a3, zero, 2047
	addi a3, a3, 81
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1168
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1888
	addi a3, zero, 304
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1888
	addi a3, zero, 304
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 2047
	addi a2, a2, 81
	addi a3, zero, 304
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 513
	addi a2, zero, 2047
	addi a2, a2, 81
	addi a3, zero, 304
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 513
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 609
	addi a2, zero, 352
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 513
	addi a2, zero, 400
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 609
	addi a2, zero, 2047
	addi a2, a2, 513
	addi a3, zero, 2047
	addi a3, a3, 609
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 513
	addi a2, zero, 1216
	addi a3, zero, 2047
	addi a3, a3, 609
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 609
	addi a2, zero, 1216
	addi a3, zero, 2047
	addi a3, a3, 609
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 561
	addi a2, zero, 2047
	addi a2, a2, 513
	addi a3, zero, 2047
	addi a3, a3, 609
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1168
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 400
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1216
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 561
	addi a2, zero, 2047
	addi a2, a2, 561
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1408
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 513
	addi a2, zero, 1312
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 513
	addi a2, zero, 2047
	addi a2, a2, 513
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1312
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 609
	addi a2, zero, 1408
	addi a3, zero, 2047
	addi a3, a3, 609
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 609
	addi a2, zero, 2047
	addi a2, a2, 609
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	addi t0, s0, 2047
	ld t0, 513(t0)
	sd t0, 288(a6)
	addi t0, s0, 2047
	ld t0, 521(t0)
	sd t0, 296(a6)
	addi t0, s0, 2047
	ld t0, 529(t0)
	sd t0, 304(a6)
	addi t0, s0, 2047
	ld t0, 537(t0)
	sd t0, 312(a6)
	addi t0, s0, 2047
	ld t0, 545(t0)
	sd t0, 320(a6)
	addi t0, s0, 2047
	ld t0, 553(t0)
	sd t0, 328(a6)
	addi t0, s0, 2047
	ld t0, 561(t0)
	sd t0, 336(a6)
	addi t0, s0, 2047
	ld t0, 569(t0)
	sd t0, 344(a6)
	addi t0, s0, 2047
	ld t0, 577(t0)
	sd t0, 352(a6)
	addi t0, s0, 2047
	ld t0, 585(t0)
	sd t0, 360(a6)
	addi t0, s0, 2047
	ld t0, 593(t0)
	sd t0, 368(a6)
	addi t0, s0, 2047
	ld t0, 601(t0)
	sd t0, 376(a6)
	addi t0, s0, 2047
	ld t0, 609(t0)
	sd t0, 384(a6)
	addi t0, s0, 2047
	ld t0, 617(t0)
	sd t0, 392(a6)
	addi t0, s0, 2047
	ld t0, 625(t0)
	sd t0, 400(a6)
	addi t0, s0, 2047
	ld t0, 633(t0)
	sd t0, 408(a6)
	addi t0, s0, 2047
	ld t0, 641(t0)
	sd t0, 416(a6)
	addi t0, s0, 2047
	ld t0, 649(t0)
	sd t0, 424(a6)
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 2047
	addi a2, a2, 513
	addi a3, zero, 1888
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 2047
	addi a2, a2, 561
	addi a3, zero, 2047
	addi a3, a3, 81
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 2047
	addi a2, a2, 609
	addi a3, zero, 304
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 2047
	addi a2, a2, 513
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1888
	addi a3, zero, 2047
	addi a3, a3, 81
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1168
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 2047
	addi a2, a2, 513
	addi a3, zero, 2047
	addi a3, a3, 609
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1888
	addi a3, zero, 304
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 2047
	addi a2, a2, 561
	addi a3, zero, 2047
	addi a3, a3, 609
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 657
	addi a2, zero, 2047
	addi a2, a2, 81
	addi a3, zero, 304
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 2047
	addi a3, a3, 657
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 657
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 2047
	addi a3, a3, 657
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 753
	addi a2, zero, 352
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 657
	addi a2, zero, 400
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 753
	addi a2, zero, 2047
	addi a2, a2, 657
	addi a3, zero, 2047
	addi a3, a3, 753
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 657
	addi a2, zero, 1216
	addi a3, zero, 2047
	addi a3, a3, 753
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 753
	addi a2, zero, 1216
	addi a3, zero, 2047
	addi a3, a3, 753
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 705
	addi a2, zero, 2047
	addi a2, a2, 657
	addi a3, zero, 2047
	addi a3, a3, 753
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1168
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 400
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1216
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 705
	addi a2, zero, 2047
	addi a2, a2, 705
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1408
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 657
	addi a2, zero, 1312
	addi a3, zero, 2047
	addi a3, a3, 657
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 657
	addi a2, zero, 2047
	addi a2, a2, 657
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1312
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 753
	addi a2, zero, 1408
	addi a3, zero, 2047
	addi a3, a3, 753
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 753
	addi a2, zero, 2047
	addi a2, a2, 753
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	addi t0, s0, 2047
	ld t0, 657(t0)
	sd t0, 432(a6)
	addi t0, s0, 2047
	ld t0, 665(t0)
	sd t0, 440(a6)
	addi t0, s0, 2047
	ld t0, 673(t0)
	sd t0, 448(a6)
	addi t0, s0, 2047
	ld t0, 681(t0)
	sd t0, 456(a6)
	addi t0, s0, 2047
	ld t0, 689(t0)
	sd t0, 464(a6)
	addi t0, s0, 2047
	ld t0, 697(t0)
	sd t0, 472(a6)
	addi t0, s0, 2047
	ld t0, 705(t0)
	sd t0, 480(a6)
	addi t0, s0, 2047
	ld t0, 713(t0)
	sd t0, 488(a6)
	addi t0, s0, 2047
	ld t0, 721(t0)
	sd t0, 496(a6)
	addi t0, s0, 2047
	ld t0, 729(t0)
	sd t0, 504(a6)
	addi t0, s0, 2047
	ld t0, 737(t0)
	sd t0, 512(a6)
	addi t0, s0, 2047
	ld t0, 745(t0)
	sd t0, 520(a6)
	addi t0, s0, 2047
	ld t0, 753(t0)
	sd t0, 528(a6)
	addi t0, s0, 2047
	ld t0, 761(t0)
	sd t0, 536(a6)
	addi t0, s0, 2047
	ld t0, 769(t0)
	sd t0, 544(a6)
	addi t0, s0, 2047
	ld t0, 777(t0)
	sd t0, 552(a6)
	addi t0, s0, 2047
	ld t0, 785(t0)
	sd t0, 560(a6)
	addi t0, s0, 2047
	ld t0, 793(t0)
	sd t0, 568(a6)
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 448
	addi a3, zero, 1888
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 496
	addi a3, zero, 2047
	addi a3, a3, 81
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 304
	addi a3, zero, 304
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 448
	addi a3, zero, 496
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1888
	addi a3, zero, 2047
	addi a3, a3, 81
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1168
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 448
	addi a3, zero, 304
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1888
	addi a3, zero, 304
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 496
	addi a3, zero, 304
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 2047
	addi a2, a2, 81
	addi a3, zero, 304
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 352
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 400
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1024
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1216
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1216
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1024
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1168
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 400
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1216
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1072
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1408
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1312
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1312
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1408
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1120
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 1024(s0)
	sd t0, 720(a6)
	ld t0, 1032(s0)
	sd t0, 728(a6)
	ld t0, 1040(s0)
	sd t0, 736(a6)
	ld t0, 1048(s0)
	sd t0, 744(a6)
	ld t0, 1056(s0)
	sd t0, 752(a6)
	ld t0, 1064(s0)
	sd t0, 760(a6)
	ld t0, 1072(s0)
	sd t0, 768(a6)
	ld t0, 1080(s0)
	sd t0, 776(a6)
	ld t0, 1088(s0)
	sd t0, 784(a6)
	ld t0, 1096(s0)
	sd t0, 792(a6)
	ld t0, 1104(s0)
	sd t0, 800(a6)
	ld t0, 1112(s0)
	sd t0, 808(a6)
	ld t0, 1120(s0)
	sd t0, 816(a6)
	ld t0, 1128(s0)
	sd t0, 824(a6)
	ld t0, 1136(s0)
	sd t0, 832(a6)
	ld t0, 1144(s0)
	sd t0, 840(a6)
	ld t0, 1152(s0)
	sd t0, 848(a6)
	ld t0, 1160(s0)
	sd t0, 856(a6)
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 448
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 496
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 304
	addi a3, zero, 2047
	addi a3, a3, 609
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 448
	addi a3, zero, 496
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 2047
	addi a2, a2, 513
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1168
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 448
	addi a3, zero, 304
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 2047
	addi a2, a2, 513
	addi a3, zero, 2047
	addi a3, a3, 609
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 496
	addi a3, zero, 304
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 2047
	addi a2, a2, 561
	addi a3, zero, 2047
	addi a3, a3, 609
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 352
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 400
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1024
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1216
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1216
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1024
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1168
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 400
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1216
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1072
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1408
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1312
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1312
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1408
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1120
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 1024(s0)
	sd t0, 864(a6)
	ld t0, 1032(s0)
	sd t0, 872(a6)
	ld t0, 1040(s0)
	sd t0, 880(a6)
	ld t0, 1048(s0)
	sd t0, 888(a6)
	ld t0, 1056(s0)
	sd t0, 896(a6)
	ld t0, 1064(s0)
	sd t0, 904(a6)
	ld t0, 1072(s0)
	sd t0, 912(a6)
	ld t0, 1080(s0)
	sd t0, 920(a6)
	ld t0, 1088(s0)
	sd t0, 928(a6)
	ld t0, 1096(s0)
	sd t0, 936(a6)
	ld t0, 1104(s0)
	sd t0, 944(a6)
	ld t0, 1112(s0)
	sd t0, 952(a6)
	ld t0, 1120(s0)
	sd t0, 960(a6)
	ld t0, 1128(s0)
	sd t0, 968(a6)
	ld t0, 1136(s0)
	sd t0, 976(a6)
	ld t0, 1144(s0)
	sd t0, 984(a6)
	ld t0, 1152(s0)
	sd t0, 992(a6)
	ld t0, 1160(s0)
	sd t0, 1000(a6)
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 448
	addi a3, zero, 2047
	addi a3, a3, 657
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 496
	addi a3, zero, 2047
	addi a3, a3, 705
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 304
	addi a3, zero, 2047
	addi a3, a3, 753
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 448
	addi a3, zero, 496
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 2047
	addi a2, a2, 657
	addi a3, zero, 2047
	addi a3, a3, 705
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1168
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 448
	addi a3, zero, 304
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 2047
	addi a2, a2, 657
	addi a3, zero, 2047
	addi a3, a3, 753
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 496
	addi a3, zero, 304
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 2047
	addi a2, a2, 705
	addi a3, zero, 2047
	addi a3, a3, 753
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 352
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 400
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1024
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1216
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1216
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1024
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1168
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 400
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1216
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1072
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1408
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1312
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1312
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1408
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1120
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 1024(s0)
	sd t0, 1008(a6)
	ld t0, 1032(s0)
	sd t0, 1016(a6)
	ld t0, 1040(s0)
	sd t0, 1024(a6)
	ld t0, 1048(s0)
	sd t0, 1032(a6)
	ld t0, 1056(s0)
	sd t0, 1040(a6)
	ld t0, 1064(s0)
	sd t0, 1048(a6)
	ld t0, 1072(s0)
	sd t0, 1056(a6)
	ld t0, 1080(s0)
	sd t0, 1064(a6)
	ld t0, 1088(s0)
	sd t0, 1072(a6)
	ld t0, 1096(s0)
	sd t0, 1080(a6)
	ld t0, 1104(s0)
	sd t0, 1088(a6)
	ld t0, 1112(s0)
	sd t0, 1096(a6)
	ld t0, 1120(s0)
	sd t0, 1104(a6)
	ld t0, 1128(s0)
	sd t0, 1112(a6)
	ld t0, 1136(s0)
	sd t0, 1120(a6)
	ld t0, 1144(s0)
	sd t0, 1128(a6)
	ld t0, 1152(s0)
	sd t0, 1136(a6)
	ld t0, 1160(s0)
	sd t0, 1144(a6)
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 2047
	addi a2, a2, 225
	addi a3, zero, 1888
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 2047
	addi a2, a2, 273
	addi a3, zero, 2047
	addi a3, a3, 81
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 2047
	addi a2, a2, 321
	addi a3, zero, 304
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 2047
	addi a2, a2, 225
	addi a3, zero, 2047
	addi a3, a3, 273
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1888
	addi a3, zero, 2047
	addi a3, a3, 81
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1168
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 2047
	addi a2, a2, 225
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1888
	addi a3, zero, 304
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 2047
	addi a2, a2, 273
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 2047
	addi a2, a2, 81
	addi a3, zero, 304
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 352
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 400
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1024
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1216
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1216
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1024
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1168
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 400
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1216
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1072
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1408
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1312
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1312
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1408
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1120
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 1024(s0)
	sd t0, 1296(a6)
	ld t0, 1032(s0)
	sd t0, 1304(a6)
	ld t0, 1040(s0)
	sd t0, 1312(a6)
	ld t0, 1048(s0)
	sd t0, 1320(a6)
	ld t0, 1056(s0)
	sd t0, 1328(a6)
	ld t0, 1064(s0)
	sd t0, 1336(a6)
	ld t0, 1072(s0)
	sd t0, 1344(a6)
	ld t0, 1080(s0)
	sd t0, 1352(a6)
	ld t0, 1088(s0)
	sd t0, 1360(a6)
	ld t0, 1096(s0)
	sd t0, 1368(a6)
	ld t0, 1104(s0)
	sd t0, 1376(a6)
	ld t0, 1112(s0)
	sd t0, 1384(a6)
	ld t0, 1120(s0)
	sd t0, 1392(a6)
	ld t0, 1128(s0)
	sd t0, 1400(a6)
	ld t0, 1136(s0)
	sd t0, 1408(a6)
	ld t0, 1144(s0)
	sd t0, 1416(a6)
	ld t0, 1152(s0)
	sd t0, 1424(a6)
	ld t0, 1160(s0)
	sd t0, 1432(a6)
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 2047
	addi a2, a2, 225
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 2047
	addi a2, a2, 273
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 2047
	addi a2, a2, 321
	addi a3, zero, 2047
	addi a3, a3, 609
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 2047
	addi a2, a2, 225
	addi a3, zero, 2047
	addi a3, a3, 273
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 2047
	addi a2, a2, 513
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1168
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 2047
	addi a2, a2, 225
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 2047
	addi a2, a2, 513
	addi a3, zero, 2047
	addi a3, a3, 609
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 2047
	addi a2, a2, 273
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 2047
	addi a2, a2, 561
	addi a3, zero, 2047
	addi a3, a3, 609
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 352
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 400
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1024
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1216
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1216
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1024
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1168
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 400
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1216
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1072
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1408
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1312
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1312
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1408
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1120
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 1024(s0)
	sd t0, 1440(a6)
	ld t0, 1032(s0)
	sd t0, 1448(a6)
	ld t0, 1040(s0)
	sd t0, 1456(a6)
	ld t0, 1048(s0)
	sd t0, 1464(a6)
	ld t0, 1056(s0)
	sd t0, 1472(a6)
	ld t0, 1064(s0)
	sd t0, 1480(a6)
	ld t0, 1072(s0)
	sd t0, 1488(a6)
	ld t0, 1080(s0)
	sd t0, 1496(a6)
	ld t0, 1088(s0)
	sd t0, 1504(a6)
	ld t0, 1096(s0)
	sd t0, 1512(a6)
	ld t0, 1104(s0)
	sd t0, 1520(a6)
	ld t0, 1112(s0)
	sd t0, 1528(a6)
	ld t0, 1120(s0)
	sd t0, 1536(a6)
	ld t0, 1128(s0)
	sd t0, 1544(a6)
	ld t0, 1136(s0)
	sd t0, 1552(a6)
	ld t0, 1144(s0)
	sd t0, 1560(a6)
	ld t0, 1152(s0)
	sd t0, 1568(a6)
	ld t0, 1160(s0)
	sd t0, 1576(a6)
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 2047
	addi a2, a2, 225
	addi a3, zero, 2047
	addi a3, a3, 657
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 2047
	addi a2, a2, 273
	addi a3, zero, 2047
	addi a3, a3, 705
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 2047
	addi a2, a2, 321
	addi a3, zero, 2047
	addi a3, a3, 753
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 2047
	addi a2, a2, 225
	addi a3, zero, 2047
	addi a3, a3, 273
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 2047
	addi a2, a2, 657
	addi a3, zero, 2047
	addi a3, a3, 705
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1168
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 2047
	addi a2, a2, 225
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 2047
	addi a2, a2, 657
	addi a3, zero, 2047
	addi a3, a3, 753
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 2047
	addi a2, a2, 273
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 2047
	addi a2, a2, 705
	addi a3, zero, 2047
	addi a3, a3, 753
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 352
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 400
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1024
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1216
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1216
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1024
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1168
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 400
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1216
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1072
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1408
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1312
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1312
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1408
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1120
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 1024(s0)
	sd t0, 1584(a6)
	ld t0, 1032(s0)
	sd t0, 1592(a6)
	ld t0, 1040(s0)
	sd t0, 1600(a6)
	ld t0, 1048(s0)
	sd t0, 1608(a6)
	ld t0, 1056(s0)
	sd t0, 1616(a6)
	ld t0, 1064(s0)
	sd t0, 1624(a6)
	ld t0, 1072(s0)
	sd t0, 1632(a6)
	ld t0, 1080(s0)
	sd t0, 1640(a6)
	ld t0, 1088(s0)
	sd t0, 1648(a6)
	ld t0, 1096(s0)
	sd t0, 1656(a6)
	ld t0, 1104(s0)
	sd t0, 1664(a6)
	ld t0, 1112(s0)
	sd t0, 1672(a6)
	ld t0, 1120(s0)
	sd t0, 1680(a6)
	ld t0, 1128(s0)
	sd t0, 1688(a6)
	ld t0, 1136(s0)
	sd t0, 1696(a6)
	ld t0, 1144(s0)
	sd t0, 1704(a6)
	ld t0, 1152(s0)
	sd t0, 1712(a6)
	ld t0, 1160(s0)
	sd t0, 1720(a6)
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 2047
	addi a2, a2, 369
	addi a3, zero, 1888
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 2047
	addi a2, a2, 417
	addi a3, zero, 2047
	addi a3, a3, 81
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 2047
	addi a2, a2, 465
	addi a3, zero, 304
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 2047
	addi a2, a2, 369
	addi a3, zero, 2047
	addi a3, a3, 417
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1888
	addi a3, zero, 2047
	addi a3, a3, 81
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1168
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 2047
	addi a2, a2, 369
	addi a3, zero, 2047
	addi a3, a3, 465
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1888
	addi a3, zero, 304
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 2047
	addi a2, a2, 417
	addi a3, zero, 2047
	addi a3, a3, 465
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 2047
	addi a2, a2, 81
	addi a3, zero, 304
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 352
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 400
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1024
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1216
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1216
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1024
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1168
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 400
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1216
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1072
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1408
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1312
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1312
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1408
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1120
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 1024(s0)
	sd t0, 1872(a6)
	ld t0, 1032(s0)
	sd t0, 1880(a6)
	ld t0, 1040(s0)
	sd t0, 1888(a6)
	ld t0, 1048(s0)
	sd t0, 1896(a6)
	ld t0, 1056(s0)
	sd t0, 1904(a6)
	ld t0, 1064(s0)
	sd t0, 1912(a6)
	ld t0, 1072(s0)
	sd t0, 1920(a6)
	ld t0, 1080(s0)
	sd t0, 1928(a6)
	ld t0, 1088(s0)
	sd t0, 1936(a6)
	ld t0, 1096(s0)
	sd t0, 1944(a6)
	ld t0, 1104(s0)
	sd t0, 1952(a6)
	ld t0, 1112(s0)
	sd t0, 1960(a6)
	ld t0, 1120(s0)
	sd t0, 1968(a6)
	ld t0, 1128(s0)
	sd t0, 1976(a6)
	ld t0, 1136(s0)
	sd t0, 1984(a6)
	ld t0, 1144(s0)
	sd t0, 1992(a6)
	ld t0, 1152(s0)
	sd t0, 2000(a6)
	ld t0, 1160(s0)
	sd t0, 2008(a6)
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 2047
	addi a2, a2, 369
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 2047
	addi a2, a2, 417
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 2047
	addi a2, a2, 465
	addi a3, zero, 2047
	addi a3, a3, 609
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 2047
	addi a2, a2, 369
	addi a3, zero, 2047
	addi a3, a3, 417
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 2047
	addi a2, a2, 513
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1168
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 2047
	addi a2, a2, 369
	addi a3, zero, 2047
	addi a3, a3, 465
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 2047
	addi a2, a2, 513
	addi a3, zero, 2047
	addi a3, a3, 609
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 2047
	addi a2, a2, 417
	addi a3, zero, 2047
	addi a3, a3, 465
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 2047
	addi a2, a2, 561
	addi a3, zero, 2047
	addi a3, a3, 609
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 352
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 400
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1024
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1216
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1216
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1024
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1168
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 400
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1216
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1072
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1408
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1312
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1312
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1408
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1120
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 1024(s0)
	sd t0, 2016(a6)
	ld t0, 1032(s0)
	sd t0, 2024(a6)
	ld t0, 1040(s0)
	sd t0, 2032(a6)
	ld t0, 1048(s0)
	sd t0, 2040(a6)
	ld t0, 1056(s0)
	addi a6, a6, 2047
	sd t0, 1(a6)
	addi a6, a6, -2047
	ld t0, 1064(s0)
	addi a6, a6, 2047
	sd t0, 9(a6)
	addi a6, a6, -2047
	ld t0, 1072(s0)
	addi a6, a6, 2047
	sd t0, 17(a6)
	addi a6, a6, -2047
	ld t0, 1080(s0)
	addi a6, a6, 2047
	sd t0, 25(a6)
	addi a6, a6, -2047
	ld t0, 1088(s0)
	addi a6, a6, 2047
	sd t0, 33(a6)
	addi a6, a6, -2047
	ld t0, 1096(s0)
	addi a6, a6, 2047
	sd t0, 41(a6)
	addi a6, a6, -2047
	ld t0, 1104(s0)
	addi a6, a6, 2047
	sd t0, 49(a6)
	addi a6, a6, -2047
	ld t0, 1112(s0)
	addi a6, a6, 2047
	sd t0, 57(a6)
	addi a6, a6, -2047
	ld t0, 1120(s0)
	addi a6, a6, 2047
	sd t0, 65(a6)
	addi a6, a6, -2047
	ld t0, 1128(s0)
	addi a6, a6, 2047
	sd t0, 73(a6)
	addi a6, a6, -2047
	ld t0, 1136(s0)
	addi a6, a6, 2047
	sd t0, 81(a6)
	addi a6, a6, -2047
	ld t0, 1144(s0)
	addi a6, a6, 2047
	sd t0, 89(a6)
	addi a6, a6, -2047
	ld t0, 1152(s0)
	addi a6, a6, 2047
	sd t0, 97(a6)
	addi a6, a6, -2047
	ld t0, 1160(s0)
	addi a6, a6, 2047
	sd t0, 105(a6)
	addi a6, a6, -2047
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 2047
	addi a2, a2, 369
	addi a3, zero, 2047
	addi a3, a3, 657
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 2047
	addi a2, a2, 417
	addi a3, zero, 2047
	addi a3, a3, 705
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 2047
	addi a2, a2, 465
	addi a3, zero, 2047
	addi a3, a3, 753
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 2047
	addi a2, a2, 369
	addi a3, zero, 2047
	addi a3, a3, 417
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 2047
	addi a2, a2, 657
	addi a3, zero, 2047
	addi a3, a3, 705
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1168
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 2047
	addi a2, a2, 369
	addi a3, zero, 2047
	addi a3, a3, 465
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 2047
	addi a2, a2, 657
	addi a3, zero, 2047
	addi a3, a3, 753
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 2047
	addi a2, a2, 417
	addi a3, zero, 2047
	addi a3, a3, 465
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 2047
	addi a2, a2, 705
	addi a3, zero, 2047
	addi a3, a3, 753
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 352
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 400
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1024
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1216
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1216
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1024
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1168
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 400
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1216
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1072
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1408
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1312
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1312
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1408
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1120
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 1024(s0)
	addi a6, a6, 2047
	sd t0, 113(a6)
	addi a6, a6, -2047
	ld t0, 1032(s0)
	addi a6, a6, 2047
	sd t0, 121(a6)
	addi a6, a6, -2047
	ld t0, 1040(s0)
	addi a6, a6, 2047
	sd t0, 129(a6)
	addi a6, a6, -2047
	ld t0, 1048(s0)
	addi a6, a6, 2047
	sd t0, 137(a6)
	addi a6, a6, -2047
	ld t0, 1056(s0)
	addi a6, a6, 2047
	sd t0, 145(a6)
	addi a6, a6, -2047
	ld t0, 1064(s0)
	addi a6, a6, 2047
	sd t0, 153(a6)
	addi a6, a6, -2047
	ld t0, 1072(s0)
	addi a6, a6, 2047
	sd t0, 161(a6)
	addi a6, a6, -2047
	ld t0, 1080(s0)
	addi a6, a6, 2047
	sd t0, 169(a6)
	addi a6, a6, -2047
	ld t0, 1088(s0)
	addi a6, a6, 2047
	sd t0, 177(a6)
	addi a6, a6, -2047
	ld t0, 1096(s0)
	addi a6, a6, 2047
	sd t0, 185(a6)
	addi a6, a6, -2047
	ld t0, 1104(s0)
	addi a6, a6, 2047
	sd t0, 193(a6)
	addi a6, a6, -2047
	ld t0, 1112(s0)
	addi a6, a6, 2047
	sd t0, 201(a6)
	addi a6, a6, -2047
	ld t0, 1120(s0)
	addi a6, a6, 2047
	sd t0, 209(a6)
	addi a6, a6, -2047
	ld t0, 1128(s0)
	addi a6, a6, 2047
	sd t0, 217(a6)
	addi a6, a6, -2047
	ld t0, 1136(s0)
	addi a6, a6, 2047
	sd t0, 225(a6)
	addi a6, a6, -2047
	ld t0, 1144(s0)
	addi a6, a6, 2047
	sd t0, 233(a6)
	addi a6, a6, -2047
	ld t0, 1152(s0)
	addi a6, a6, 2047
	sd t0, 241(a6)
	addi a6, a6, -2047
	ld t0, 1160(s0)
	addi a6, a6, 2047
	sd t0, 249(a6)
	addi a6, a6, -2047
	ld t0, 208(s0)
	sd t0, 736(s0)
	ld t0, 216(s0)
	sd t0, 744(s0)
	ld t0, 224(s0)
	sd t0, 752(s0)
	ld t0, 232(s0)
	sd t0, 760(s0)
	ld t0, 240(s0)
	sd t0, 768(s0)
	ld t0, 248(s0)
	sd t0, 776(s0)
	ld t0, 304(s0)
	sd t0, 784(s0)
	ld t0, 312(s0)
	sd t0, 792(s0)
	ld t0, 320(s0)
	sd t0, 800(s0)
	ld t0, 328(s0)
	sd t0, 808(s0)
	ld t0, 336(s0)
	sd t0, 816(s0)
	ld t0, 344(s0)
	sd t0, 824(s0)
	ld t0, 208(s0)
	sd t0, 832(s0)
	ld t0, 216(s0)
	sd t0, 840(s0)
	ld t0, 224(s0)
	sd t0, 848(s0)
	ld t0, 232(s0)
	sd t0, 856(s0)
	ld t0, 240(s0)
	sd t0, 864(s0)
	ld t0, 248(s0)
	sd t0, 872(s0)
	addi s1, zero, 192
284:
	addi s1, s1, -1
	srli t1, s1, 5
	slli t1, t1, 3
	add t1, t1, s0
	ld t2, 1648(t1)
	ld t3, 1792(t1)
	slli t0, s1, 1
	srl t2, t2, t0
	srl t3, t3, t0
	andi t2, t2, 3
	andi t3, t3, 3
	slli t2, t2, 2
	or t2, t2, t3
	slli a1, t2, 63
	srai a1, a1, 63
	slli a2, t2, 62
	srai a2, a2, 63
	slli a3, t2, 61
	srai a3, a3, 63
	slli a4, t2, 60
	srai a4, a4, 63
	addi a0, s0, 2047
	addi a0, a0, 2047
	addi a0, a0, 2
	ld t0, 0(a0)
	ld t1, 144(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 288(a0)
	ld t2, 432(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 576(a0)
	ld t2, 720(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 864(a0)
	ld t3, 1008(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1152(a0)
	ld t2, 1296(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1440(a0)
	ld t3, 1584(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1728(a0)
	ld t3, 1872(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 2016(a0)
	addi t4, a0, 2047
	ld t4, 113(t4)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 801(s0)
	addi s0, s0, -2047
	ld t0, 8(a0)
	ld t1, 152(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 296(a0)
	ld t2, 440(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 584(a0)
	ld t2, 728(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 872(a0)
	ld t3, 1016(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1160(a0)
	ld t2, 1304(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1448(a0)
	ld t3, 1592(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1736(a0)
	ld t3, 1880(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 2024(a0)
	addi t4, a0, 2047
	ld t4, 121(t4)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 809(s0)
	addi s0, s0, -2047
	ld t0, 16(a0)
	ld t1, 160(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 304(a0)
	ld t2, 448(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 592(a0)
	ld t2, 736(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 880(a0)
	ld t3, 1024(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1168(a0)
	ld t2, 1312(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1456(a0)
	ld t3, 1600(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1744(a0)
	ld t3, 1888(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 2032(a0)
	addi t4, a0, 2047
	ld t4, 129(t4)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 817(s0)
	addi s0, s0, -2047
	ld t0, 24(a0)
	ld t1, 168(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 312(a0)
	ld t2, 456(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 600(a0)
	ld t2, 744(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 888(a0)
	ld t3, 1032(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1176(a0)
	ld t2, 1320(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1464(a0)
	ld t3, 1608(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1752(a0)
	ld t3, 1896(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 2040(a0)
	addi t4, a0, 2047
	ld t4, 137(t4)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 825(s0)
	addi s0, s0, -2047
	ld t0, 32(a0)
	ld t1, 176(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 320(a0)
	ld t2, 464(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 608(a0)
	ld t2, 752(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 896(a0)
	ld t3, 1040(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1184(a0)
	ld t2, 1328(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1472(a0)
	ld t3, 1616(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1760(a0)
	ld t3, 1904(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 1(t3)
	addi t4, a0, 2047
	ld t4, 145(t4)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 833(s0)
	addi s0, s0, -2047
	ld t0, 40(a0)
	ld t1, 184(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 328(a0)
	ld t2, 472(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 616(a0)
	ld t2, 760(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 904(a0)
	ld t3, 1048(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1192(a0)
	ld t2, 1336(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1480(a0)
	ld t3, 1624(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1768(a0)
	ld t3, 1912(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 9(t3)
	addi t4, a0, 2047
	ld t4, 153(t4)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 841(s0)
	addi s0, s0, -2047
	ld t0, 48(a0)
	ld t1, 192(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 336(a0)
	ld t2, 480(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 624(a0)
	ld t2, 768(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 912(a0)
	ld t3, 1056(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1200(a0)
	ld t2, 1344(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1488(a0)
	ld t3, 1632(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1776(a0)
	ld t3, 1920(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 17(t3)
	addi t4, a0, 2047
	ld t4, 161(t4)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 849(s0)
	addi s0, s0, -2047
	ld t0, 56(a0)
	ld t1, 200(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 344(a0)
	ld t2, 488(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 632(a0)
	ld t2, 776(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 920(a0)
	ld t3, 1064(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1208(a0)
	ld t2, 1352(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1496(a0)
	ld t3, 1640(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1784(a0)
	ld t3, 1928(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 25(t3)
	addi t4, a0, 2047
	ld t4, 169(t4)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 857(s0)
	addi s0, s0, -2047
	ld t0, 64(a0)
	ld t1, 208(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 352(a0)
	ld t2, 496(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 640(a0)
	ld t2, 784(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 928(a0)
	ld t3, 1072(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1216(a0)
	ld t2, 1360(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1504(a0)
	ld t3, 1648(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1792(a0)
	ld t3, 1936(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 33(t3)
	addi t4, a0, 2047
	ld t4, 177(t4)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 865(s0)
	addi s0, s0, -2047
	ld t0, 72(a0)
	ld t1, 216(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 360(a0)
	ld t2, 504(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 648(a0)
	ld t2, 792(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 936(a0)
	ld t3, 1080(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1224(a0)
	ld t2, 1368(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1512(a0)
	ld t3, 1656(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1800(a0)
	ld t3, 1944(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 41(t3)
	addi t4, a0, 2047
	ld t4, 185(t4)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 873(s0)
	addi s0, s0, -2047
	ld t0, 80(a0)
	ld t1, 224(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 368(a0)
	ld t2, 512(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 656(a0)
	ld t2, 800(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 944(a0)
	ld t3, 1088(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1232(a0)
	ld t2, 1376(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1520(a0)
	ld t3, 1664(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1808(a0)
	ld t3, 1952(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 49(t3)
	addi t4, a0, 2047
	ld t4, 193(t4)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 881(s0)
	addi s0, s0, -2047
	ld t0, 88(a0)
	ld t1, 232(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 376(a0)
	ld t2, 520(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 664(a0)
	ld t2, 808(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 952(a0)
	ld t3, 1096(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1240(a0)
	ld t2, 1384(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1528(a0)
	ld t3, 1672(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1816(a0)
	ld t3, 1960(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 57(t3)
	addi t4, a0, 2047
	ld t4, 201(t4)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 889(s0)
	addi s0, s0, -2047
	ld t0, 96(a0)
	ld t1, 240(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 384(a0)
	ld t2, 528(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 672(a0)
	ld t2, 816(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 960(a0)
	ld t3, 1104(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1248(a0)
	ld t2, 1392(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1536(a0)
	ld t3, 1680(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1824(a0)
	ld t3, 1968(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 65(t3)
	addi t4, a0, 2047
	ld t4, 209(t4)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 897(s0)
	addi s0, s0, -2047
	ld t0, 104(a0)
	ld t1, 248(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 392(a0)
	ld t2, 536(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 680(a0)
	ld t2, 824(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 968(a0)
	ld t3, 1112(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1256(a0)
	ld t2, 1400(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1544(a0)
	ld t3, 1688(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1832(a0)
	ld t3, 1976(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 73(t3)
	addi t4, a0, 2047
	ld t4, 217(t4)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 905(s0)
	addi s0, s0, -2047
	ld t0, 112(a0)
	ld t1, 256(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 400(a0)
	ld t2, 544(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 688(a0)
	ld t2, 832(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 976(a0)
	ld t3, 1120(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1264(a0)
	ld t2, 1408(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1552(a0)
	ld t3, 1696(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1840(a0)
	ld t3, 1984(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 81(t3)
	addi t4, a0, 2047
	ld t4, 225(t4)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 913(s0)
	addi s0, s0, -2047
	ld t0, 120(a0)
	ld t1, 264(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 408(a0)
	ld t2, 552(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 696(a0)
	ld t2, 840(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 984(a0)
	ld t3, 1128(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1272(a0)
	ld t2, 1416(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1560(a0)
	ld t3, 1704(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1848(a0)
	ld t3, 1992(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 89(t3)
	addi t4, a0, 2047
	ld t4, 233(t4)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 921(s0)
	addi s0, s0, -2047
	ld t0, 128(a0)
	ld t1, 272(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 416(a0)
	ld t2, 560(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 704(a0)
	ld t2, 848(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 992(a0)
	ld t3, 1136(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1280(a0)
	ld t2, 1424(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1568(a0)
	ld t3, 1712(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1856(a0)
	ld t3, 2000(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 97(t3)
	addi t4, a0, 2047
	ld t4, 241(t4)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 929(s0)
	addi s0, s0, -2047
	ld t0, 136(a0)
	ld t1, 280(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 424(a0)
	ld t2, 568(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 712(a0)
	ld t2, 856(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1000(a0)
	ld t3, 1144(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1288(a0)
	ld t2, 1432(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1576(a0)
	ld t3, 1720(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1864(a0)
	ld t3, 2008(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 105(t3)
	addi t4, a0, 2047
	ld t4, 249(t4)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 937(s0)
	addi s0, s0, -2047
	addi a0, s0, 0
	addi a1, zero, 880
	addi a2, zero, 736
	addi a3, zero, 832
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 832
	addi a3, zero, 832
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 928
	addi a2, zero, 784
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 976
	addi a2, zero, 832
	addi a3, zero, 208
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 880
	addi a3, zero, 880
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 928
	addi a3, zero, 928
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1216
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 880
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1312
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1312
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 976
	addi a3, zero, 976
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 352
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1168
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 928
	addi a3, zero, 976
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1120
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1360
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1312
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1312
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1312
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1360
	addi a3, zero, 1072
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1264
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1264
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1264
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1072
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1024
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1072
	addi a3, zero, 1072
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1216
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1024
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1312
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1312
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1120
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 352
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1168
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 976
	addi a2, zero, 1072
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 976
	addi a2, zero, 976
	addi a3, zero, 976
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 880
	addi a2, zero, 1360
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 880
	addi a2, zero, 880
	addi a3, zero, 1312
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 880
	addi a2, zero, 880
	addi a3, zero, 1312
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 928
	addi a2, zero, 1312
	addi a3, zero, 880
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 928
	addi a2, zero, 1360
	addi a3, zero, 928
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1264
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1264
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1264
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 928
	addi a2, zero, 928
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 880
	addi a3, zero, 976
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 976
	addi a3, zero, 976
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1168
	addi a3, zero, 976
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 928
	addi a3, zero, 208
	call {vg_brainpoolp384r1_add_mod_p}
	addi t3, zero, 0
	ld t4, 1120(s0)
	or t3, t3, t4
	ld t4, 1128(s0)
	or t3, t3, t4
	ld t4, 1136(s0)
	or t3, t3, t4
	ld t4, 1144(s0)
	or t3, t3, t4
	ld t4, 1152(s0)
	or t3, t3, t4
	ld t4, 1160(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	ld t0, 1072(s0)
	ld t1, 304(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1072(s0)
	ld t0, 1080(s0)
	ld t1, 312(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1080(s0)
	ld t0, 1088(s0)
	ld t1, 320(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1088(s0)
	ld t0, 1096(s0)
	ld t1, 328(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1096(s0)
	ld t0, 1104(s0)
	ld t1, 336(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1104(s0)
	ld t0, 1112(s0)
	ld t1, 344(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1112(s0)
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1024
	addi a3, zero, 2047
	addi a3, a3, 801
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1072
	addi a3, zero, 2047
	addi a3, a3, 849
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1120
	addi a3, zero, 2047
	addi a3, a3, 897
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1024
	addi a3, zero, 1072
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 2047
	addi a2, a2, 801
	addi a3, zero, 2047
	addi a3, a3, 849
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1168
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1024
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 2047
	addi a2, a2, 801
	addi a3, zero, 2047
	addi a3, a3, 897
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1072
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 736
	addi a2, zero, 2047
	addi a2, a2, 849
	addi a3, zero, 2047
	addi a3, a3, 897
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 736
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 736
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 736
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 832
	addi a2, zero, 352
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 736
	addi a2, zero, 400
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 832
	addi a2, zero, 736
	addi a3, zero, 832
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 736
	addi a2, zero, 1216
	addi a3, zero, 832
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 832
	addi a2, zero, 1216
	addi a3, zero, 832
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 784
	addi a2, zero, 736
	addi a3, zero, 832
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1168
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 400
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1216
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 784
	addi a2, zero, 784
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1408
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 736
	addi a2, zero, 1312
	addi a3, zero, 736
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 736
	addi a2, zero, 736
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1312
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 832
	addi a2, zero, 1408
	addi a3, zero, 832
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 832
	addi a2, zero, 832
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	bnez s1, 284b
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 225
	addi a2, zero, 832
	addi a3, zero, 304
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 609
	addi a2, zero, 2047
	addi a2, a2, 225
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 273
	addi a2, zero, 2047
	addi a2, a2, 225
	addi a3, zero, 2047
	addi a3, a3, 609
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 321
	addi a2, zero, 2047
	addi a2, a2, 273
	addi a3, zero, 2047
	addi a3, a3, 609
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 369
	addi a2, zero, 2047
	addi a2, a2, 321
	addi a3, zero, 2047
	addi a3, a3, 609
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 417
	addi a2, zero, 2047
	addi a2, a2, 369
	addi a3, zero, 2047
	addi a3, a3, 609
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 465
	addi a2, zero, 2047
	addi a2, a2, 417
	addi a3, zero, 2047
	addi a3, a3, 609
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 513
	addi a2, zero, 2047
	addi a2, a2, 465
	addi a3, zero, 2047
	addi a3, a3, 609
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 561
	addi a2, zero, 2047
	addi a2, a2, 513
	addi a3, zero, 2047
	addi a3, a3, 609
	call {vg_brainpoolp384r1_mul_mod_p}
	addi t0, s0, 2047
	ld t0, 225(t0)
	sd t0, 1456(s0)
	addi t0, s0, 2047
	ld t0, 233(t0)
	sd t0, 1464(s0)
	addi t0, s0, 2047
	ld t0, 241(t0)
	sd t0, 1472(s0)
	addi t0, s0, 2047
	ld t0, 249(t0)
	sd t0, 1480(s0)
	addi t0, s0, 2047
	ld t0, 257(t0)
	sd t0, 1488(s0)
	addi t0, s0, 2047
	ld t0, 265(t0)
	sd t0, 1496(s0)
	addi s1, zero, 5
285:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 285b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 273
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 6
286:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 286b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 465
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 4
287:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 287b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 417
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 7
288:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 288b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 2
289:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 289b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 8
290:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 290b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 2
291:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 291b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 5
292:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 292b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 273
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 5
293:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 293b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 369
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 8
294:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 294b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 3
295:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 295b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 5
296:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 296b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 11
297:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 297b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 5
298:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 298b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 465
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 3
299:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 299b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 5
2100:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2100b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 3
2101:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2101b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 369
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 5
2102:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2102b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 2
2103:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2103b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 273
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 5
2104:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2104b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 7
2105:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2105b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 369
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 4
2106:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2106b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 273
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 3
2107:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2107b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 8
2108:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2108b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 369
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 5
2109:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2109b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 1
2110:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2110b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 6
2111:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2111b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 5
2112:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2112b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 417
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 5
2113:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2113b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 4
2114:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2114b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 369
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 4
2115:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2115b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 8
2116:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2116b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 417
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 3
2117:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2117b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 369
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 5
2118:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2118b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 4
2119:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2119b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 2
2120:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2120b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 6
2121:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2121b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 5
2122:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2122b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 5
2123:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2123b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 9
2124:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2124b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 417
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 5
2125:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2125b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 465
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 6
2126:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2126b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 369
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 5
2127:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2127b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 6
2128:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2128b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 273
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 6
2129:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2129b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 465
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 4
2130:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2130b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 4
2131:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2131b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 4
2132:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2132b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 465
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 1
2133:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2133b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 4
2134:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2134b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 7
2135:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2135b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 417
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 6
2136:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2136b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 369
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 5
2137:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2137b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 465
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 6
2138:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2138b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 5
2139:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2139b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 369
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 5
2140:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2140b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 417
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 2
2141:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2141b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 273
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 5
2142:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2142b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 4
2143:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2143b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 273
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 3
2144:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2144b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 10
2145:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2145b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 369
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 2
2146:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2146b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 7
2147:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2147b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 5
2148:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2148b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 369
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 5
2149:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2149b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 273
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 7
2150:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2150b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 369
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 2
2151:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2151b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 6
2152:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2152b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 369
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 15
2153:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2153b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 417
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 4
2154:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2154b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 417
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 1
2155:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2155b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 4
2156:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2156b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 9
2157:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2157b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 4
2158:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2158b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 1
2159:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2159b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 6
2160:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2160b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 4
2161:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 2161b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 880
	addi a2, zero, 736
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 928
	addi a2, zero, 880
	addi a3, zero, 256
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 976
	addi a2, zero, 928
	addi a3, zero, 208
	call {vg_brainpoolp384r1_add_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 544
	addi a3, zero, 208
	call {vg_brainpoolp384r1_add_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 976
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_sub_mod_n}
	addi t3, zero, 0
	ld t4, 832(s0)
	or t3, t3, t4
	ld t4, 840(s0)
	or t3, t3, t4
	ld t4, 848(s0)
	or t3, t3, t4
	ld t4, 856(s0)
	or t3, t3, t4
	ld t4, 864(s0)
	or t3, t3, t4
	ld t4, 872(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	xori a7, a7, -1
	addi t0, s0, 2047
	ld t0, 129(t0)
	and t0, t0, a7
	addi s0, s0, 2047
	sd t0, 129(s0)
	addi s0, s0, -2047
	addi t3, zero, 0
	ld t4, 1072(s0)
	or t3, t3, t4
	ld t4, 1080(s0)
	or t3, t3, t4
	ld t4, 1088(s0)
	or t3, t3, t4
	ld t4, 1096(s0)
	or t3, t3, t4
	ld t4, 1104(s0)
	or t3, t3, t4
	ld t4, 1112(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	addi t0, s0, 2047
	ld t0, 129(t0)
	and t0, t0, a7
	addi s0, s0, 2047
	sd t0, 129(s0)
	addi s0, s0, -2047
	addi a0, s0, 2047
	ld a0, 129(a0)
	andi a0, a0, 1
	ld ra, 24(s0)
	ld s2, 16(s0)
	ld s1, 8(s0)
	ld s3, 32(s0)
	ld s0, 0(s0)
	addi sp, sp, 80
	ret
	.option pop

vg_ecdsa_brainpoolp384r1_sign:
	.option push
	.option arch, +m, +c
	addi sp, sp, -512
	addi t0, sp, 0
	sd ra, 0(t0)
	sd s0, 8(t0)
	sd s1, 16(t0)
	sd s2, 24(t0)
	sd s3, 32(t0)
	sd s4, 40(t0)
	sd s5, 48(t0)
	sd s6, 56(t0)
	sd s7, 64(t0)
	sd s8, 72(t0)
	sd s9, 80(t0)
	addi s1, t0, 0
	addi s2, a0, 0
	addi s3, a1, 0
	addi s4, a2, 0
	addi s0, a4, 0
	addi s6, a5, 0
	ld s7, 32(a5)
	ld s8, 40(a5)
	addi t0, zero, 0
	sd t0, 232(s1)
	sd t0, 240(s1)
	sd t0, 248(s1)
	sd t0, 256(s1)
	sd t0, 264(s1)
	sd t0, 272(s1)
	sd t0, 280(s1)
	sd t0, 288(s1)
	sd t0, 296(s1)
	addi t1, zero, 48
	sub t2, s7, t1
	srli t3, t2, 63
	addi t4, zero, 0
	sub t3, t4, t3
	and t2, t2, t3
	add a6, t1, t2
	addi a4, s4, 0
	addi a5, s1, 280
	sub a5, a5, a6
20:
	lbu t1, 0(a4)
	sb t1, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 20b
	lbu t0, 232(s1)
	slli t0, t0, 8
	lbu t1, 233(s1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 234(s1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 235(s1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 236(s1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 237(s1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 238(s1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 239(s1)
	or t0, t0, t1
	sd t0, 40(s0)
	lbu t0, 240(s1)
	slli t0, t0, 8
	lbu t1, 241(s1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 242(s1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 243(s1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 244(s1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 245(s1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 246(s1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 247(s1)
	or t0, t0, t1
	sd t0, 32(s0)
	lbu t0, 248(s1)
	slli t0, t0, 8
	lbu t1, 249(s1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 250(s1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 251(s1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 252(s1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 253(s1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 254(s1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 255(s1)
	or t0, t0, t1
	sd t0, 24(s0)
	lbu t0, 256(s1)
	slli t0, t0, 8
	lbu t1, 257(s1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 258(s1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 259(s1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 260(s1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 261(s1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 262(s1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 263(s1)
	or t0, t0, t1
	sd t0, 16(s0)
	lbu t0, 264(s1)
	slli t0, t0, 8
	lbu t1, 265(s1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 266(s1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 267(s1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 268(s1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 269(s1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 270(s1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 271(s1)
	or t0, t0, t1
	sd t0, 8(s0)
	lbu t0, 272(s1)
	slli t0, t0, 8
	lbu t1, 273(s1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 274(s1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 275(s1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 276(s1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 277(s1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 278(s1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 279(s1)
	or t0, t0, t1
	sd t0, 0(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 48(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 56(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 64(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 72(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 80(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 88(s0)
	addi a0, s0, 0
	addi a1, zero, 96
	addi a2, zero, 0
	addi a3, zero, 48
	call {vg_brainpoolp384r1_add_mod_n}
	addi a7, zero, -1
	ld t0, 136(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 304(s1)
	srli t1, t0, 48
	sb t1, 305(s1)
	srli t1, t0, 40
	sb t1, 306(s1)
	srli t1, t0, 32
	sb t1, 307(s1)
	srli t1, t0, 24
	sb t1, 308(s1)
	srli t1, t0, 16
	sb t1, 309(s1)
	srli t1, t0, 8
	sb t1, 310(s1)
	srli t1, t0, 0
	sb t1, 311(s1)
	ld t0, 128(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 312(s1)
	srli t1, t0, 48
	sb t1, 313(s1)
	srli t1, t0, 40
	sb t1, 314(s1)
	srli t1, t0, 32
	sb t1, 315(s1)
	srli t1, t0, 24
	sb t1, 316(s1)
	srli t1, t0, 16
	sb t1, 317(s1)
	srli t1, t0, 8
	sb t1, 318(s1)
	srli t1, t0, 0
	sb t1, 319(s1)
	ld t0, 120(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 320(s1)
	srli t1, t0, 48
	sb t1, 321(s1)
	srli t1, t0, 40
	sb t1, 322(s1)
	srli t1, t0, 32
	sb t1, 323(s1)
	srli t1, t0, 24
	sb t1, 324(s1)
	srli t1, t0, 16
	sb t1, 325(s1)
	srli t1, t0, 8
	sb t1, 326(s1)
	srli t1, t0, 0
	sb t1, 327(s1)
	ld t0, 112(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 328(s1)
	srli t1, t0, 48
	sb t1, 329(s1)
	srli t1, t0, 40
	sb t1, 330(s1)
	srli t1, t0, 32
	sb t1, 331(s1)
	srli t1, t0, 24
	sb t1, 332(s1)
	srli t1, t0, 16
	sb t1, 333(s1)
	srli t1, t0, 8
	sb t1, 334(s1)
	srli t1, t0, 0
	sb t1, 335(s1)
	ld t0, 104(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 336(s1)
	srli t1, t0, 48
	sb t1, 337(s1)
	srli t1, t0, 40
	sb t1, 338(s1)
	srli t1, t0, 32
	sb t1, 339(s1)
	srli t1, t0, 24
	sb t1, 340(s1)
	srli t1, t0, 16
	sb t1, 341(s1)
	srli t1, t0, 8
	sb t1, 342(s1)
	srli t1, t0, 0
	sb t1, 343(s1)
	ld t0, 96(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 344(s1)
	srli t1, t0, 48
	sb t1, 345(s1)
	srli t1, t0, 40
	sb t1, 346(s1)
	srli t1, t0, 32
	sb t1, 347(s1)
	srli t1, t0, 24
	sb t1, 348(s1)
	srli t1, t0, 16
	sb t1, 349(s1)
	srli t1, t0, 8
	sb t1, 350(s1)
	srli t1, t0, 0
	sb t1, 351(s1)
	addi t0, zero, 257
	slli t1, t0, 16
	or t0, t0, t1
	slli t1, t0, 32
	or t0, t0, t1
	addi t1, zero, 0
	sd t1, 96(s1)
	sd t0, 160(s1)
	sd t1, 104(s1)
	sd t0, 168(s1)
	sd t1, 112(s1)
	sd t0, 176(s1)
	sd t1, 120(s1)
	sd t0, 184(s1)
	sd t1, 128(s1)
	sd t0, 192(s1)
	sd t1, 136(s1)
	sd t0, 200(s1)
	sd t1, 144(s1)
	sd t0, 208(s1)
	sd t1, 152(s1)
	sd t0, 216(s1)
	add t0, s1, s7
	addi t1, zero, 0
	sb t1, 160(t0)
	addi a0, s0, 0
	addi a1, s0, 192
	addi a2, s1, 96
	addi a3, s7, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, s8, 0
	addi a2, s1, 160
	addi a3, s7, 1
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	add a1, s8, s7
	addi a1, a1, 1
	addi a2, s3, 0
	addi a3, zero, 48
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	add a1, s8, s7
	addi a1, a1, 49
	addi a2, s1, 304
	addi a3, zero, 48
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, s0, 192
	add a2, s8, s7
	addi a2, a2, 97
	addi a3, s1, 96
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, s0, 192
	addi a2, s1, 96
	addi a3, s7, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, s8, 0
	addi a2, s1, 160
	addi a3, s7, 0
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, s0, 192
	add a2, s8, s7
	addi a2, a2, 0
	addi a3, s1, 160
	ld t1, 16(s6)
	jalr ra, 0(t1)
	add t0, s1, s7
	addi t1, zero, 1
	sb t1, 160(t0)
	addi a0, s0, 0
	addi a1, s0, 192
	addi a2, s1, 96
	addi a3, s7, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, s8, 0
	addi a2, s1, 160
	addi a3, s7, 1
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	add a1, s8, s7
	addi a1, a1, 1
	addi a2, s3, 0
	addi a3, zero, 48
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	add a1, s8, s7
	addi a1, a1, 49
	addi a2, s1, 304
	addi a3, zero, 48
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, s0, 192
	add a2, s8, s7
	addi a2, a2, 97
	addi a3, s1, 96
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, s0, 192
	addi a2, s1, 96
	addi a3, s7, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, s8, 0
	addi a2, s1, 160
	addi a3, s7, 0
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, s0, 192
	add a2, s8, s7
	addi a2, a2, 0
	addi a3, s1, 160
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi s5, zero, 128
21:
	addi s9, zero, 0
22:
	addi a0, s0, 0
	addi a1, s0, 192
	addi a2, s1, 96
	addi a3, s7, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, s8, 0
	addi a2, s1, 160
	addi a3, s7, 0
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, s0, 192
	add a2, s8, s7
	addi a2, a2, 0
	addi a3, s1, 160
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a4, s1, 160
	addi a5, s1, 368
	add a5, a5, s9
	addi a6, s7, 0
23:
	lbu t1, 0(a4)
	sb t1, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 23b
	add s9, s9, s7
	addi t0, zero, 48
	sltu t6, s9, t0
	bnez t6, 22b
	addi a0, s2, 0
	addi a1, s3, 0
	addi a2, s1, 232
	addi a3, s1, 368
	addi a4, s0, 0
	call {vg_ecdsa_brainpoolp384r1_sign_k}
	addi s5, s5, -1
	andi t0, a0, 1
	addi t0, t0, -1
	and t6, t0, s5
	bnez t6, 24f
	addi t6, zero, 0
	j 25f
24:
	add t0, s1, s7
	addi t1, zero, 0
	sb t1, 160(t0)
	addi a0, s0, 0
	addi a1, s0, 192
	addi a2, s1, 96
	addi a3, s7, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, s8, 0
	addi a2, s1, 160
	addi a3, s7, 1
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, s0, 192
	add a2, s8, s7
	addi a2, a2, 1
	addi a3, s1, 96
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, s0, 192
	addi a2, s1, 96
	addi a3, s7, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, s8, 0
	addi a2, s1, 160
	addi a3, s7, 0
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, s0, 192
	add a2, s8, s7
	addi a2, a2, 0
	addi a3, s1, 160
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi t6, zero, 1
25:
	bnez t6, 21b
	addi t0, zero, 0
	sd t0, 96(s1)
	sd t0, 104(s1)
	sd t0, 112(s1)
	sd t0, 120(s1)
	sd t0, 128(s1)
	sd t0, 136(s1)
	sd t0, 144(s1)
	sd t0, 152(s1)
	sd t0, 160(s1)
	sd t0, 168(s1)
	sd t0, 176(s1)
	sd t0, 184(s1)
	sd t0, 192(s1)
	sd t0, 200(s1)
	sd t0, 208(s1)
	sd t0, 216(s1)
	sd t0, 224(s1)
	sd t0, 232(s1)
	sd t0, 240(s1)
	sd t0, 248(s1)
	sd t0, 256(s1)
	sd t0, 264(s1)
	sd t0, 272(s1)
	sd t0, 280(s1)
	sd t0, 288(s1)
	sd t0, 296(s1)
	sd t0, 304(s1)
	sd t0, 312(s1)
	sd t0, 320(s1)
	sd t0, 328(s1)
	sd t0, 336(s1)
	sd t0, 344(s1)
	sd t0, 352(s1)
	sd t0, 360(s1)
	sd t0, 368(s1)
	sd t0, 376(s1)
	sd t0, 384(s1)
	sd t0, 392(s1)
	sd t0, 400(s1)
	sd t0, 408(s1)
	sd t0, 416(s1)
	sd t0, 424(s1)
	sd t0, 432(s1)
	sd t0, 440(s1)
	sd t0, 448(s1)
	sd t0, 456(s1)
	sd t0, 464(s1)
	sd t0, 472(s1)
	sd t0, 480(s1)
	sd t0, 488(s1)
	sd t0, 496(s1)
	ld ra, 0(s1)
	ld s0, 8(s1)
	ld s2, 24(s1)
	ld s3, 32(s1)
	ld s4, 40(s1)
	ld s5, 48(s1)
	ld s6, 56(s1)
	ld s7, 64(s1)
	ld s8, 72(s1)
	ld s9, 80(s1)
	ld s1, 16(s1)
	addi sp, sp, 512
	ret
	.option pop
