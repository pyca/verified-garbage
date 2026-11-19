// The functions of `src/ecdsa_brainpoolp320r1.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_brainpoolp320r1_verify:
	.option push
	.option arch, +m, +c
	addi sp, sp, -80
	addi a5, sp, 0
	addi t0, zero, 40
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
	addi t2, a5, 40
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
	sd t0, 1416(s0)
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
	sd t0, 1408(s0)
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
	sd t0, 1400(s0)
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
	sd t0, 1392(s0)
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
	sd t0, 1384(s0)
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
	sd t0, 1536(s0)
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
	sd t0, 1528(s0)
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
	sd t0, 1520(s0)
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
	sd t0, 1512(s0)
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
	sd t0, 1504(s0)
	lbu t0, 0(a0)
	xori t0, t0, 4
	addi t0, t0, -1
	srli t0, t0, 63
	addi t1, zero, 0
	sub a7, t1, t0
	sd a7, 1824(s0)
	lui t0, 1035585
	addiw t0, t0, 690
	slli t0, t0, 32
	lui t1, 990003
	addiw t1, t1, -473
	add t0, t0, t1
	sd t0, 64(s0)
	lui t0, 325932
	addiw t0, t0, -1556
	slli t0, t0, 32
	lui t1, 493887
	addiw t1, t1, -984
	add t0, t0, t1
	sd t0, 72(s0)
	lui t0, 1022205
	addiw t0, t0, -89
	slli t0, t0, 32
	lui t1, 1011521
	addiw t1, t1, -529
	add t0, t0, t1
	sd t0, 80(s0)
	lui t0, 922568
	addiw t0, t0, -1953
	slli t0, t0, 32
	lui t1, 860190
	addiw t1, t1, 101
	add t0, t0, t1
	sd t0, 88(s0)
	lui t0, 865764
	addiw t0, t0, 1824
	slli t0, t0, 32
	lui t1, 224197
	addiw t1, t1, -73
	add t0, t0, t1
	sd t0, 96(s0)
	lui t0, 551189
	addiw t0, t0, 1371
	slli t0, t0, 32
	lui t1, 281689
	addiw t1, t1, 785
	add t0, t0, t1
	sd t0, 104(s0)
	lui t0, 185475
	addiw t0, t0, -312
	slli t0, t0, 32
	lui t1, 976998
	addiw t1, t1, -1815
	add t0, t0, t1
	sd t0, 112(s0)
	lui t0, 1022205
	addiw t0, t0, -90
	slli t0, t0, 32
	lui t1, 747761
	addiw t1, t1, 675
	add t0, t0, t1
	sd t0, 120(s0)
	lui t0, 922568
	addiw t0, t0, -1953
	slli t0, t0, 32
	lui t1, 860190
	addiw t1, t1, 101
	add t0, t0, t1
	sd t0, 128(s0)
	lui t0, 865764
	addiw t0, t0, 1824
	slli t0, t0, 32
	lui t1, 224197
	addiw t1, t1, -73
	add t0, t0, t1
	sd t0, 136(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 184(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 192(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 200(s0)
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
	addiw t1, t1, 1
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
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 256(s0)
	lui t0, 12991
	addiw t0, t0, -690
	slli t0, t0, 32
	lui t1, 58573
	addiw t1, t1, 473
	add t0, t0, t1
	sd t0, 264(s0)
	lui t0, 722644
	addiw t0, t0, 1556
	slli t0, t0, 32
	lui t1, 554689
	addiw t1, t1, 983
	add t0, t0, t1
	sd t0, 272(s0)
	lui t0, 26371
	addiw t0, t0, 89
	slli t0, t0, 32
	lui t1, 37055
	addiw t1, t1, 528
	add t0, t0, t1
	sd t0, 280(s0)
	lui t0, 126008
	addiw t0, t0, 1953
	slli t0, t0, 32
	lui t1, 188386
	addiw t1, t1, -102
	add t0, t0, t1
	sd t0, 288(s0)
	lui t0, 182812
	addiw t0, t0, -1824
	slli t0, t0, 32
	lui t1, 824379
	addiw t1, t1, 72
	add t0, t0, t1
	sd t0, 296(s0)
	lui t0, 133951
	addiw t0, t0, 635
	slli t0, t0, 32
	lui t1, 63251
	addiw t1, t1, 1442
	add t0, t0, t1
	sd t0, 304(s0)
	lui t0, 16199
	addiw t0, t0, -1426
	slli t0, t0, 32
	lui t1, 670766
	addiw t1, t1, -122
	add t0, t0, t1
	sd t0, 312(s0)
	lui t0, 660378
	addiw t0, t0, 994
	slli t0, t0, 32
	lui t1, 768395
	addiw t1, t1, 19
	add t0, t0, t1
	sd t0, 320(s0)
	lui t0, 238426
	addiw t0, t0, -1815
	slli t0, t0, 32
	lui t1, 843443
	addiw t1, t1, 1759
	add t0, t0, t1
	sd t0, 328(s0)
	lui t0, 288700
	addiw t0, t0, -1862
	slli t0, t0, 32
	lui t1, 846890
	addiw t1, t1, -666
	add t0, t0, t1
	sd t0, 336(s0)
	lui t0, 400942
	addiw t0, t0, 1414
	slli t0, t0, 32
	lui t1, 378611
	addiw t1, t1, 1280
	add t0, t0, t1
	sd t0, 344(s0)
	lui t0, 651436
	addiw t0, t0, -63
	slli t0, t0, 32
	lui t1, 460378
	addiw t1, t1, -1857
	add t0, t0, t1
	sd t0, 352(s0)
	lui t0, 351824
	addiw t0, t0, 1602
	slli t0, t0, 32
	lui t1, 873225
	addiw t1, t1, 268
	add t0, t0, t1
	sd t0, 360(s0)
	lui t0, 991086
	addiw t0, t0, 1177
	slli t0, t0, 32
	lui t1, 802100
	addiw t1, t1, 603
	add t0, t0, t1
	sd t0, 368(s0)
	lui t0, 77432
	addiw t0, t0, 286
	slli t0, t0, 32
	lui t1, 61958
	addiw t1, t1, -1335
	add t0, t0, t1
	sd t0, 376(s0)
	lui t0, 776486
	addiw t0, t0, -400
	slli t0, t0, 32
	lui t1, 382913
	addiw t1, t1, -1351
	add t0, t0, t1
	sd t0, 384(s0)
	lui t0, 976656
	addiw t0, t0, -347
	slli t0, t0, 32
	lui t1, 912591
	addiw t1, t1, 251
	add t0, t0, t1
	sd t0, 392(s0)
	lui t0, 459440
	addiw t0, t0, -976
	slli t0, t0, 32
	lui t1, 118745
	addiw t1, t1, 926
	add t0, t0, t1
	sd t0, 400(s0)
	lui t0, 353535
	addiw t0, t0, -508
	slli t0, t0, 32
	lui t1, 783650
	addiw t1, t1, 499
	add t0, t0, t1
	sd t0, 408(s0)
	lui t0, 280304
	addiw t0, t0, -1869
	slli t0, t0, 32
	lui t1, 269119
	addiw t1, t1, 1252
	add t0, t0, t1
	sd t0, 416(s0)
	lui t0, 344083
	addiw t0, t0, 1927
	slli t0, t0, 32
	lui t1, 294086
	addiw t1, t1, 332
	add t0, t0, t1
	sd t0, 424(s0)
	lui t0, 813048
	addiw t0, t0, 1544
	slli t0, t0, 32
	lui t1, 524782
	addiw t1, t1, 633
	add t0, t0, t1
	sd t0, 432(s0)
	lui t0, 344372
	addiw t0, t0, 855
	slli t0, t0, 32
	lui t1, 717809
	addiw t1, t1, -1033
	add t0, t0, t1
	sd t0, 440(s0)
	lui t0, 1029794
	addiw t0, t0, -1502
	slli t0, t0, 32
	lui t1, 532060
	addiw t1, t1, -391
	add t0, t0, t1
	sd t0, 448(s0)
	lui t0, 485801
	addiw t0, t0, 899
	slli t0, t0, 32
	lui t1, 776011
	addiw t1, t1, -1142
	add t0, t0, t1
	sd t0, 456(s0)
	lui t0, 1035585
	addiw t0, t0, 690
	slli t0, t0, 32
	lui t1, 990003
	addiw t1, t1, -475
	add t0, t0, t1
	sd t0, 544(s0)
	lui t0, 325932
	addiw t0, t0, -1556
	slli t0, t0, 32
	lui t1, 493887
	addiw t1, t1, -984
	add t0, t0, t1
	sd t0, 552(s0)
	lui t0, 1022205
	addiw t0, t0, -89
	slli t0, t0, 32
	lui t1, 1011521
	addiw t1, t1, -529
	add t0, t0, t1
	sd t0, 560(s0)
	lui t0, 922568
	addiw t0, t0, -1953
	slli t0, t0, 32
	lui t1, 860190
	addiw t1, t1, 101
	add t0, t0, t1
	sd t0, 568(s0)
	lui t0, 865764
	addiw t0, t0, 1824
	slli t0, t0, 32
	lui t1, 224197
	addiw t1, t1, -73
	add t0, t0, t1
	sd t0, 576(s0)
	lui t0, 627951
	addiw t0, t0, -1910
	slli t0, t0, 32
	lui t1, 476085
	addiw t1, t1, 761
	add t0, t0, t1
	sd t0, 1624(s0)
	lui t0, 795769
	addiw t0, t0, -1394
	slli t0, t0, 32
	lui t1, 591512
	addiw t1, t1, -1809
	add t0, t0, t1
	sd t0, 1632(s0)
	lui t0, 128201
	addiw t0, t0, -2017
	slli t0, t0, 32
	lui t1, 199771
	addiw t1, t1, 1654
	add t0, t0, t1
	sd t0, 1640(s0)
	lui t0, 345435
	addiw t0, t0, -1691
	slli t0, t0, 32
	lui t1, 942413
	addiw t1, t1, 1746
	add t0, t0, t1
	sd t0, 1648(s0)
	lui t0, 664988
	addiw t0, t0, -1462
	slli t0, t0, 32
	lui t1, 443097
	addiw t1, t1, 594
	add t0, t0, t1
	sd t0, 1656(s0)
	lui t0, 824038
	addiw t0, t0, -1799
	slli t0, t0, 32
	lui t1, 786206
	addiw t1, t1, -1254
	add t0, t0, t1
	sd t0, 1664(s0)
	lui t0, 84908
	addiw t0, t0, -1058
	slli t0, t0, 32
	lui t1, 133192
	addiw t1, t1, -1275
	add t0, t0, t1
	sd t0, 1672(s0)
	lui t0, 99694
	addiw t0, t0, 475
	slli t0, t0, 32
	lui t1, 615897
	addiw t1, t1, -263
	add t0, t0, t1
	sd t0, 1680(s0)
	lui t0, 595882
	addiw t0, t0, -910
	slli t0, t0, 32
	lui t1, 141776
	addiw t1, t1, 269
	add t0, t0, t1
	sd t0, 1688(s0)
	lui t0, 602987
	addiw t0, t0, -54
	slli t0, t0, 32
	lui t1, 170117
	addiw t1, t1, 872
	add t0, t0, t1
	sd t0, 1696(s0)
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
	sd t0, 496(s0)
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
	sd t0, 488(s0)
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
	sd t0, 480(s0)
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
	sd t0, 472(s0)
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
	sd t0, 464(s0)
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
	sd t0, 536(s0)
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
	sd t0, 528(s0)
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
	sd t0, 520(s0)
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
	sd t0, 512(s0)
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
	sd t0, 504(s0)
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
	sd t0, 1376(s0)
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
	sd t0, 1368(s0)
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
	sd t0, 1360(s0)
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
	sd t0, 1352(s0)
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
	sd t0, 1344(s0)
	addi t5, zero, 0
	ld t3, 464(s0)
	ld t4, 104(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 472(s0)
	ld t4, 112(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 480(s0)
	ld t4, 120(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 488(s0)
	ld t4, 128(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 496(s0)
	ld t4, 136(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t6, zero, 0
	sub a7, t6, t5
	ld t0, 1824(s0)
	and t0, t0, a7
	sd t0, 1824(s0)
	addi t3, zero, 0
	ld t4, 464(s0)
	or t3, t3, t4
	ld t4, 472(s0)
	or t3, t3, t4
	ld t4, 480(s0)
	or t3, t3, t4
	ld t4, 488(s0)
	or t3, t3, t4
	ld t4, 496(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	xori a7, a7, -1
	ld t0, 1824(s0)
	and t0, t0, a7
	sd t0, 1824(s0)
	addi t5, zero, 0
	ld t3, 504(s0)
	ld t4, 104(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 512(s0)
	ld t4, 112(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 520(s0)
	ld t4, 120(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 528(s0)
	ld t4, 128(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 536(s0)
	ld t4, 136(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t6, zero, 0
	sub a7, t6, t5
	ld t0, 1824(s0)
	and t0, t0, a7
	sd t0, 1824(s0)
	addi t3, zero, 0
	ld t4, 504(s0)
	or t3, t3, t4
	ld t4, 512(s0)
	or t3, t3, t4
	ld t4, 520(s0)
	or t3, t3, t4
	ld t4, 528(s0)
	or t3, t3, t4
	ld t4, 536(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	xori a7, a7, -1
	ld t0, 1824(s0)
	and t0, t0, a7
	sd t0, 1824(s0)
	addi a0, s0, 0
	call {vg_brainpoolp320r1_check_point}
	addi s0, s3, 0
	lui t0, 424403
	addiw t0, t0, -1569
	slli t0, t0, 32
	lui t1, 151870
	addiw t1, t1, 1229
	add t0, t0, t1
	sd t0, 1464(s0)
	lui t0, 597040
	addiw t0, t0, 28
	slli t0, t0, 32
	lui t1, 921111
	addiw t1, t1, -2043
	add t0, t0, t1
	sd t0, 1472(s0)
	lui t0, 551731
	addiw t0, t0, 189
	slli t0, t0, 32
	lui t1, 718956
	addiw t1, t1, 1033
	add t0, t0, t1
	sd t0, 1480(s0)
	lui t0, 930003
	addiw t0, t0, 1316
	slli t0, t0, 32
	lui t1, 321081
	addiw t1, t1, 254
	add t0, t0, t1
	sd t0, 1488(s0)
	lui t0, 204488
	addiw t0, t0, 1991
	slli t0, t0, 32
	lui t1, 204811
	addiw t1, t1, 335
	add t0, t0, t1
	sd t0, 1496(s0)
	lui t0, 497387
	addiw t0, t0, -1371
	slli t0, t0, 32
	lui t1, 766887
	addiw t1, t1, -785
	add t0, t0, t1
	sd t0, 1504(s0)
	lui t0, 863101
	addiw t0, t0, 312
	slli t0, t0, 32
	lui t1, 71578
	addiw t1, t1, 1814
	add t0, t0, t1
	sd t0, 1512(s0)
	lui t0, 26371
	addiw t0, t0, 90
	slli t0, t0, 32
	lui t1, 300815
	addiw t1, t1, -676
	add t0, t0, t1
	sd t0, 1520(s0)
	lui t0, 126008
	addiw t0, t0, 1953
	slli t0, t0, 32
	lui t1, 188386
	addiw t1, t1, -102
	add t0, t0, t1
	sd t0, 1528(s0)
	lui t0, 182812
	addiw t0, t0, -1824
	slli t0, t0, 32
	lui t1, 824379
	addiw t1, t1, 72
	add t0, t0, t1
	sd t0, 1536(s0)
	lui t0, 551189
	addiw t0, t0, 1371
	slli t0, t0, 32
	lui t1, 281689
	addiw t1, t1, 783
	add t0, t0, t1
	sd t0, 1544(s0)
	lui t0, 185475
	addiw t0, t0, -312
	slli t0, t0, 32
	lui t1, 976998
	addiw t1, t1, -1815
	add t0, t0, t1
	sd t0, 1552(s0)
	lui t0, 1022205
	addiw t0, t0, -90
	slli t0, t0, 32
	lui t1, 747761
	addiw t1, t1, 675
	add t0, t0, t1
	sd t0, 1560(s0)
	lui t0, 922568
	addiw t0, t0, -1953
	slli t0, t0, 32
	lui t1, 860190
	addiw t1, t1, 101
	add t0, t0, t1
	sd t0, 1568(s0)
	lui t0, 865764
	addiw t0, t0, 1824
	slli t0, t0, 32
	lui t1, 224197
	addiw t1, t1, -73
	add t0, t0, t1
	sd t0, 1576(s0)
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 504
	addi a3, zero, 1464
	call {vg_brainpoolp320r1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1904
	addi a2, zero, 864
	addi a3, zero, 1504
	call {vg_brainpoolp320r1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 177
	addi a2, zero, 1904
	addi a3, zero, 1904
	call {vg_brainpoolp320r1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1944
	addi a2, zero, 1904
	addi a3, zero, 2047
	addi a3, a3, 177
	call {vg_brainpoolp320r1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1984
	addi a2, zero, 1944
	addi a3, zero, 2047
	addi a3, a3, 177
	call {vg_brainpoolp320r1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 2024
	addi a2, zero, 1984
	addi a3, zero, 2047
	addi a3, a3, 177
	call {vg_brainpoolp320r1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 17
	addi a2, zero, 2024
	addi a3, zero, 2047
	addi a3, a3, 177
	call {vg_brainpoolp320r1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 57
	addi a2, zero, 2047
	addi a2, a2, 17
	addi a3, zero, 2047
	addi a3, a3, 177
	call {vg_brainpoolp320r1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 97
	addi a2, zero, 2047
	addi a2, a2, 57
	addi a3, zero, 2047
	addi a3, a3, 177
	call {vg_brainpoolp320r1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 137
	addi a2, zero, 2047
	addi a2, a2, 97
	addi a3, zero, 2047
	addi a3, a3, 177
	call {vg_brainpoolp320r1_mul_mod_n}
	addi t0, s0, 2047
	ld t0, 97(t0)
	sd t0, 1224(s0)
	addi t0, s0, 2047
	ld t0, 105(t0)
	sd t0, 1232(s0)
	addi t0, s0, 2047
	ld t0, 113(t0)
	sd t0, 1240(s0)
	addi t0, s0, 2047
	ld t0, 121(t0)
	sd t0, 1248(s0)
	addi t0, s0, 2047
	ld t0, 129(t0)
	sd t0, 1256(s0)
	addi s1, zero, 6
25:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 25b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 97
	call {vg_brainpoolp320r1_mul_mod_n}
	addi s1, zero, 5
26:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 26b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_mul_mod_n}
	addi s1, zero, 3
27:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 27b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1904
	call {vg_brainpoolp320r1_mul_mod_n}
	addi s1, zero, 6
28:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 28b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2024
	call {vg_brainpoolp320r1_mul_mod_n}
	addi s1, zero, 3
29:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 29b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1904
	call {vg_brainpoolp320r1_mul_mod_n}
	addi s1, zero, 11
210:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 210b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 97
	call {vg_brainpoolp320r1_mul_mod_n}
	addi s1, zero, 3
211:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 211b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1984
	call {vg_brainpoolp320r1_mul_mod_n}
	addi s1, zero, 5
212:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 212b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_mul_mod_n}
	addi s1, zero, 7
213:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 213b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 17
	call {vg_brainpoolp320r1_mul_mod_n}
	addi s1, zero, 4
214:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 214b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_mul_mod_n}
	addi s1, zero, 5
215:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 215b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 97
	call {vg_brainpoolp320r1_mul_mod_n}
	addi s1, zero, 4
216:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 216b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_mul_mod_n}
	addi s1, zero, 1
217:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 217b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1904
	call {vg_brainpoolp320r1_mul_mod_n}
	addi s1, zero, 8
218:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 218b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 17
	call {vg_brainpoolp320r1_mul_mod_n}
	addi s1, zero, 3
219:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 219b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2024
	call {vg_brainpoolp320r1_mul_mod_n}
	addi s1, zero, 7
220:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 220b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_mul_mod_n}
	addi s1, zero, 8
221:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 221b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 57
	call {vg_brainpoolp320r1_mul_mod_n}
	addi s1, zero, 4
222:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 222b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 97
	call {vg_brainpoolp320r1_mul_mod_n}
	addi s1, zero, 3
223:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 223b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1984
	call {vg_brainpoolp320r1_mul_mod_n}
	addi s1, zero, 3
224:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 224b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1904
	call {vg_brainpoolp320r1_mul_mod_n}
	addi s1, zero, 12
225:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 225b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_mul_mod_n}
	addi s1, zero, 8
226:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 226b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1944
	call {vg_brainpoolp320r1_mul_mod_n}
	addi s1, zero, 6
227:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 227b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 57
	call {vg_brainpoolp320r1_mul_mod_n}
	addi s1, zero, 4
228:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 228b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_mul_mod_n}
	addi s1, zero, 4
229:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 229b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1944
	call {vg_brainpoolp320r1_mul_mod_n}
	addi s1, zero, 7
230:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 230b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_mul_mod_n}
	addi s1, zero, 2
231:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 231b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1944
	call {vg_brainpoolp320r1_mul_mod_n}
	addi s1, zero, 6
232:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 232b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_mul_mod_n}
	addi s1, zero, 3
233:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 233b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1984
	call {vg_brainpoolp320r1_mul_mod_n}
	addi s1, zero, 6
234:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 234b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 57
	call {vg_brainpoolp320r1_mul_mod_n}
	addi s1, zero, 5
235:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 235b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 97
	call {vg_brainpoolp320r1_mul_mod_n}
	addi s1, zero, 3
236:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 236b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1984
	call {vg_brainpoolp320r1_mul_mod_n}
	addi s1, zero, 7
237:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 237b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_mul_mod_n}
	addi s1, zero, 7
238:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 238b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 17
	call {vg_brainpoolp320r1_mul_mod_n}
	addi s1, zero, 4
239:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 239b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1984
	call {vg_brainpoolp320r1_mul_mod_n}
	addi s1, zero, 5
240:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 240b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1944
	call {vg_brainpoolp320r1_mul_mod_n}
	addi s1, zero, 6
241:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 241b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 57
	call {vg_brainpoolp320r1_mul_mod_n}
	addi s1, zero, 4
242:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 242b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1984
	call {vg_brainpoolp320r1_mul_mod_n}
	addi s1, zero, 3
243:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 243b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1904
	call {vg_brainpoolp320r1_mul_mod_n}
	addi s1, zero, 9
244:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 244b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 57
	call {vg_brainpoolp320r1_mul_mod_n}
	addi s1, zero, 4
245:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 245b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 57
	call {vg_brainpoolp320r1_mul_mod_n}
	addi s1, zero, 7
246:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 246b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_mul_mod_n}
	addi s1, zero, 4
247:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 247b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 97
	call {vg_brainpoolp320r1_mul_mod_n}
	addi s1, zero, 4
248:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 248b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 97
	call {vg_brainpoolp320r1_mul_mod_n}
	addi s1, zero, 6
249:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 249b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1944
	call {vg_brainpoolp320r1_mul_mod_n}
	addi s1, zero, 6
250:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 250b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 57
	call {vg_brainpoolp320r1_mul_mod_n}
	addi s1, zero, 6
251:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 251b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2024
	call {vg_brainpoolp320r1_mul_mod_n}
	addi s1, zero, 5
252:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 252b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 17
	call {vg_brainpoolp320r1_mul_mod_n}
	addi s1, zero, 1
253:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 253b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1904
	call {vg_brainpoolp320r1_mul_mod_n}
	addi s1, zero, 8
254:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 254b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 97
	call {vg_brainpoolp320r1_mul_mod_n}
	addi s1, zero, 3
255:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 255b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1904
	call {vg_brainpoolp320r1_mul_mod_n}
	addi s1, zero, 6
256:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 256b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1984
	call {vg_brainpoolp320r1_mul_mod_n}
	addi s1, zero, 4
257:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 257b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1984
	call {vg_brainpoolp320r1_mul_mod_n}
	addi s1, zero, 4
258:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 258b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1984
	call {vg_brainpoolp320r1_mul_mod_n}
	addi s1, zero, 5
259:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 259b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 97
	call {vg_brainpoolp320r1_mul_mod_n}
	addi s1, zero, 3
260:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 260b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1984
	call {vg_brainpoolp320r1_mul_mod_n}
	addi s1, zero, 7
261:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 261b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 17
	call {vg_brainpoolp320r1_mul_mod_n}
	addi s1, zero, 1
262:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 262b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1904
	call {vg_brainpoolp320r1_mul_mod_n}
	addi s1, zero, 7
263:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 263b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 57
	call {vg_brainpoolp320r1_mul_mod_n}
	addi s1, zero, 6
264:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 264b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 17
	call {vg_brainpoolp320r1_mul_mod_n}
	addi s1, zero, 1
265:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 265b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1904
	call {vg_brainpoolp320r1_mul_mod_n}
	addi s1, zero, 8
266:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	bnez s1, 266b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 904
	addi a2, zero, 1344
	addi a3, zero, 1464
	call {vg_brainpoolp320r1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 904
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1384
	addi a2, zero, 944
	addi a3, zero, 224
	call {vg_brainpoolp320r1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 464
	addi a3, zero, 1464
	call {vg_brainpoolp320r1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 944
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1504
	addi a2, zero, 1024
	addi a3, zero, 224
	call {vg_brainpoolp320r1_mul_mod_n}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 184(s0)
	sd t0, 0(a6)
	ld t0, 192(s0)
	sd t0, 8(a6)
	ld t0, 200(s0)
	sd t0, 16(a6)
	ld t0, 208(s0)
	sd t0, 24(a6)
	ld t0, 216(s0)
	sd t0, 32(a6)
	ld t0, 264(s0)
	sd t0, 40(a6)
	ld t0, 272(s0)
	sd t0, 48(a6)
	ld t0, 280(s0)
	sd t0, 56(a6)
	ld t0, 288(s0)
	sd t0, 64(a6)
	ld t0, 296(s0)
	sd t0, 72(a6)
	ld t0, 184(s0)
	sd t0, 80(a6)
	ld t0, 192(s0)
	sd t0, 88(a6)
	ld t0, 200(s0)
	sd t0, 96(a6)
	ld t0, 208(s0)
	sd t0, 104(a6)
	ld t0, 216(s0)
	sd t0, 112(a6)
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 384(s0)
	sd t0, 480(a6)
	ld t0, 392(s0)
	sd t0, 488(a6)
	ld t0, 400(s0)
	sd t0, 496(a6)
	ld t0, 408(s0)
	sd t0, 504(a6)
	ld t0, 416(s0)
	sd t0, 512(a6)
	ld t0, 424(s0)
	sd t0, 520(a6)
	ld t0, 432(s0)
	sd t0, 528(a6)
	ld t0, 440(s0)
	sd t0, 536(a6)
	ld t0, 448(s0)
	sd t0, 544(a6)
	ld t0, 456(s0)
	sd t0, 552(a6)
	ld t0, 264(s0)
	sd t0, 560(a6)
	ld t0, 272(s0)
	sd t0, 568(a6)
	ld t0, 280(s0)
	sd t0, 576(a6)
	ld t0, 288(s0)
	sd t0, 584(a6)
	ld t0, 296(s0)
	sd t0, 592(a6)
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 1584(s0)
	sd t0, 120(a6)
	ld t0, 1592(s0)
	sd t0, 128(a6)
	ld t0, 1600(s0)
	sd t0, 136(a6)
	ld t0, 1608(s0)
	sd t0, 144(a6)
	ld t0, 1616(s0)
	sd t0, 152(a6)
	ld t0, 1784(s0)
	sd t0, 160(a6)
	ld t0, 1792(s0)
	sd t0, 168(a6)
	ld t0, 1800(s0)
	sd t0, 176(a6)
	ld t0, 1808(s0)
	sd t0, 184(a6)
	ld t0, 1816(s0)
	sd t0, 192(a6)
	ld t0, 264(s0)
	sd t0, 200(a6)
	ld t0, 272(s0)
	sd t0, 208(a6)
	ld t0, 280(s0)
	sd t0, 216(a6)
	ld t0, 288(s0)
	sd t0, 224(a6)
	ld t0, 296(s0)
	sd t0, 232(a6)
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 384
	addi a3, zero, 384
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 424
	addi a3, zero, 424
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 264
	addi a3, zero, 264
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 384
	addi a3, zero, 424
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 384
	addi a3, zero, 424
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 984
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 384
	addi a3, zero, 264
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 384
	addi a3, zero, 264
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 984
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 424
	addi a3, zero, 264
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1904
	addi a2, zero, 424
	addi a3, zero, 264
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 1904
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1904
	addi a2, zero, 1024
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 1904
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1984
	addi a2, zero, 304
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1904
	addi a2, zero, 344
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1984
	addi a2, zero, 1904
	addi a3, zero, 1984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1904
	addi a2, zero, 1024
	addi a3, zero, 1984
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1984
	addi a2, zero, 1024
	addi a3, zero, 1984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1944
	addi a2, zero, 1904
	addi a3, zero, 1984
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 984
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 304
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 344
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 984
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 304
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1024
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1944
	addi a2, zero, 1944
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1184
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1904
	addi a2, zero, 1104
	addi a3, zero, 1904
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1904
	addi a2, zero, 1904
	addi a3, zero, 984
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1104
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1984
	addi a2, zero, 1184
	addi a3, zero, 1984
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1984
	addi a2, zero, 1984
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 1904(s0)
	sd t0, 960(a6)
	ld t0, 1912(s0)
	sd t0, 968(a6)
	ld t0, 1920(s0)
	sd t0, 976(a6)
	ld t0, 1928(s0)
	sd t0, 984(a6)
	ld t0, 1936(s0)
	sd t0, 992(a6)
	ld t0, 1944(s0)
	sd t0, 1000(a6)
	ld t0, 1952(s0)
	sd t0, 1008(a6)
	ld t0, 1960(s0)
	sd t0, 1016(a6)
	ld t0, 1968(s0)
	sd t0, 1024(a6)
	ld t0, 1976(s0)
	sd t0, 1032(a6)
	ld t0, 1984(s0)
	sd t0, 1040(a6)
	ld t0, 1992(s0)
	sd t0, 1048(a6)
	ld t0, 2000(s0)
	sd t0, 1056(a6)
	ld t0, 2008(s0)
	sd t0, 1064(a6)
	ld t0, 2016(s0)
	sd t0, 1072(a6)
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1904
	addi a3, zero, 384
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1944
	addi a3, zero, 424
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 1984
	addi a3, zero, 264
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1904
	addi a3, zero, 1944
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 384
	addi a3, zero, 424
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 984
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1904
	addi a3, zero, 1984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 384
	addi a3, zero, 264
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 984
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1944
	addi a3, zero, 1984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2024
	addi a2, zero, 424
	addi a3, zero, 264
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 2024
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2024
	addi a2, zero, 1024
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 2024
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 57
	addi a2, zero, 304
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2024
	addi a2, zero, 344
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 57
	addi a2, zero, 2024
	addi a3, zero, 2047
	addi a3, a3, 57
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2024
	addi a2, zero, 1024
	addi a3, zero, 2047
	addi a3, a3, 57
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 57
	addi a2, zero, 1024
	addi a3, zero, 2047
	addi a3, a3, 57
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 17
	addi a2, zero, 2024
	addi a3, zero, 2047
	addi a3, a3, 57
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 984
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 304
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 344
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 984
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 304
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1024
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 17
	addi a2, zero, 2047
	addi a2, a2, 17
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1184
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2024
	addi a2, zero, 1104
	addi a3, zero, 2024
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2024
	addi a2, zero, 2024
	addi a3, zero, 984
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1104
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 57
	addi a2, zero, 1184
	addi a3, zero, 2047
	addi a3, a3, 57
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 57
	addi a2, zero, 2047
	addi a2, a2, 57
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 2024(s0)
	sd t0, 1440(a6)
	ld t0, 2032(s0)
	sd t0, 1448(a6)
	ld t0, 2040(s0)
	sd t0, 1456(a6)
	addi t0, s0, 2047
	ld t0, 1(t0)
	sd t0, 1464(a6)
	addi t0, s0, 2047
	ld t0, 9(t0)
	sd t0, 1472(a6)
	addi t0, s0, 2047
	ld t0, 17(t0)
	sd t0, 1480(a6)
	addi t0, s0, 2047
	ld t0, 25(t0)
	sd t0, 1488(a6)
	addi t0, s0, 2047
	ld t0, 33(t0)
	sd t0, 1496(a6)
	addi t0, s0, 2047
	ld t0, 41(t0)
	sd t0, 1504(a6)
	addi t0, s0, 2047
	ld t0, 49(t0)
	sd t0, 1512(a6)
	addi t0, s0, 2047
	ld t0, 57(t0)
	sd t0, 1520(a6)
	addi t0, s0, 2047
	ld t0, 65(t0)
	sd t0, 1528(a6)
	addi t0, s0, 2047
	ld t0, 73(t0)
	sd t0, 1536(a6)
	addi t0, s0, 2047
	ld t0, 81(t0)
	sd t0, 1544(a6)
	addi t0, s0, 2047
	ld t0, 89(t0)
	sd t0, 1552(a6)
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1584
	addi a3, zero, 1584
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1784
	addi a3, zero, 1784
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 264
	addi a3, zero, 264
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1584
	addi a3, zero, 1784
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1584
	addi a3, zero, 1784
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 984
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1584
	addi a3, zero, 264
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1584
	addi a3, zero, 264
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 984
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1784
	addi a3, zero, 264
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 97
	addi a2, zero, 1784
	addi a3, zero, 264
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 2047
	addi a3, a3, 97
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 97
	addi a2, zero, 1024
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 2047
	addi a3, a3, 97
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 177
	addi a2, zero, 304
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 97
	addi a2, zero, 344
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 177
	addi a2, zero, 2047
	addi a2, a2, 97
	addi a3, zero, 2047
	addi a3, a3, 177
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 97
	addi a2, zero, 1024
	addi a3, zero, 2047
	addi a3, a3, 177
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 177
	addi a2, zero, 1024
	addi a3, zero, 2047
	addi a3, a3, 177
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 137
	addi a2, zero, 2047
	addi a2, a2, 97
	addi a3, zero, 2047
	addi a3, a3, 177
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 984
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 304
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 344
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 984
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 304
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1024
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 137
	addi a2, zero, 2047
	addi a2, a2, 137
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1184
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 97
	addi a2, zero, 1104
	addi a3, zero, 2047
	addi a3, a3, 97
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 97
	addi a2, zero, 2047
	addi a2, a2, 97
	addi a3, zero, 984
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1104
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 177
	addi a2, zero, 1184
	addi a3, zero, 2047
	addi a3, a3, 177
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 177
	addi a2, zero, 2047
	addi a2, a2, 177
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	addi t0, s0, 2047
	ld t0, 97(t0)
	sd t0, 240(a6)
	addi t0, s0, 2047
	ld t0, 105(t0)
	sd t0, 248(a6)
	addi t0, s0, 2047
	ld t0, 113(t0)
	sd t0, 256(a6)
	addi t0, s0, 2047
	ld t0, 121(t0)
	sd t0, 264(a6)
	addi t0, s0, 2047
	ld t0, 129(t0)
	sd t0, 272(a6)
	addi t0, s0, 2047
	ld t0, 137(t0)
	sd t0, 280(a6)
	addi t0, s0, 2047
	ld t0, 145(t0)
	sd t0, 288(a6)
	addi t0, s0, 2047
	ld t0, 153(t0)
	sd t0, 296(a6)
	addi t0, s0, 2047
	ld t0, 161(t0)
	sd t0, 304(a6)
	addi t0, s0, 2047
	ld t0, 169(t0)
	sd t0, 312(a6)
	addi t0, s0, 2047
	ld t0, 177(t0)
	sd t0, 320(a6)
	addi t0, s0, 2047
	ld t0, 185(t0)
	sd t0, 328(a6)
	addi t0, s0, 2047
	ld t0, 193(t0)
	sd t0, 336(a6)
	addi t0, s0, 2047
	ld t0, 201(t0)
	sd t0, 344(a6)
	addi t0, s0, 2047
	ld t0, 209(t0)
	sd t0, 352(a6)
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 2047
	addi a2, a2, 97
	addi a3, zero, 1584
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 2047
	addi a2, a2, 137
	addi a3, zero, 1784
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 2047
	addi a2, a2, 177
	addi a3, zero, 264
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 2047
	addi a2, a2, 97
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1584
	addi a3, zero, 1784
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 984
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 2047
	addi a2, a2, 97
	addi a3, zero, 2047
	addi a3, a3, 177
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1584
	addi a3, zero, 264
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 984
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 2047
	addi a2, a2, 137
	addi a3, zero, 2047
	addi a3, a3, 177
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 217
	addi a2, zero, 1784
	addi a3, zero, 264
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 2047
	addi a3, a3, 217
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 217
	addi a2, zero, 1024
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 2047
	addi a3, a3, 217
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 297
	addi a2, zero, 304
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 217
	addi a2, zero, 344
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 297
	addi a2, zero, 2047
	addi a2, a2, 217
	addi a3, zero, 2047
	addi a3, a3, 297
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 217
	addi a2, zero, 1024
	addi a3, zero, 2047
	addi a3, a3, 297
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 297
	addi a2, zero, 1024
	addi a3, zero, 2047
	addi a3, a3, 297
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 257
	addi a2, zero, 2047
	addi a2, a2, 217
	addi a3, zero, 2047
	addi a3, a3, 297
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 984
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 304
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 344
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 984
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 304
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1024
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 257
	addi a2, zero, 2047
	addi a2, a2, 257
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1184
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 217
	addi a2, zero, 1104
	addi a3, zero, 2047
	addi a3, a3, 217
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 217
	addi a2, zero, 2047
	addi a2, a2, 217
	addi a3, zero, 984
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1104
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 297
	addi a2, zero, 1184
	addi a3, zero, 2047
	addi a3, a3, 297
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 297
	addi a2, zero, 2047
	addi a2, a2, 297
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	addi t0, s0, 2047
	ld t0, 217(t0)
	sd t0, 360(a6)
	addi t0, s0, 2047
	ld t0, 225(t0)
	sd t0, 368(a6)
	addi t0, s0, 2047
	ld t0, 233(t0)
	sd t0, 376(a6)
	addi t0, s0, 2047
	ld t0, 241(t0)
	sd t0, 384(a6)
	addi t0, s0, 2047
	ld t0, 249(t0)
	sd t0, 392(a6)
	addi t0, s0, 2047
	ld t0, 257(t0)
	sd t0, 400(a6)
	addi t0, s0, 2047
	ld t0, 265(t0)
	sd t0, 408(a6)
	addi t0, s0, 2047
	ld t0, 273(t0)
	sd t0, 416(a6)
	addi t0, s0, 2047
	ld t0, 281(t0)
	sd t0, 424(a6)
	addi t0, s0, 2047
	ld t0, 289(t0)
	sd t0, 432(a6)
	addi t0, s0, 2047
	ld t0, 297(t0)
	sd t0, 440(a6)
	addi t0, s0, 2047
	ld t0, 305(t0)
	sd t0, 448(a6)
	addi t0, s0, 2047
	ld t0, 313(t0)
	sd t0, 456(a6)
	addi t0, s0, 2047
	ld t0, 321(t0)
	sd t0, 464(a6)
	addi t0, s0, 2047
	ld t0, 329(t0)
	sd t0, 472(a6)
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 384
	addi a3, zero, 1584
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 424
	addi a3, zero, 1784
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 264
	addi a3, zero, 264
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 384
	addi a3, zero, 424
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1584
	addi a3, zero, 1784
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 984
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 384
	addi a3, zero, 264
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1584
	addi a3, zero, 264
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 984
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 424
	addi a3, zero, 264
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1784
	addi a3, zero, 264
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 864
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1024
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 864
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 304
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 344
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 864
	addi a3, zero, 944
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1024
	addi a3, zero, 944
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 1024
	addi a3, zero, 944
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 904
	addi a2, zero, 864
	addi a3, zero, 944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 984
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 304
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 344
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 984
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 304
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1024
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 904
	addi a2, zero, 904
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1184
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1104
	addi a3, zero, 864
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 864
	addi a3, zero, 984
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1104
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 1184
	addi a3, zero, 944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 944
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 864(s0)
	sd t0, 600(a6)
	ld t0, 872(s0)
	sd t0, 608(a6)
	ld t0, 880(s0)
	sd t0, 616(a6)
	ld t0, 888(s0)
	sd t0, 624(a6)
	ld t0, 896(s0)
	sd t0, 632(a6)
	ld t0, 904(s0)
	sd t0, 640(a6)
	ld t0, 912(s0)
	sd t0, 648(a6)
	ld t0, 920(s0)
	sd t0, 656(a6)
	ld t0, 928(s0)
	sd t0, 664(a6)
	ld t0, 936(s0)
	sd t0, 672(a6)
	ld t0, 944(s0)
	sd t0, 680(a6)
	ld t0, 952(s0)
	sd t0, 688(a6)
	ld t0, 960(s0)
	sd t0, 696(a6)
	ld t0, 968(s0)
	sd t0, 704(a6)
	ld t0, 976(s0)
	sd t0, 712(a6)
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 384
	addi a3, zero, 2047
	addi a3, a3, 97
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 424
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 264
	addi a3, zero, 2047
	addi a3, a3, 177
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 384
	addi a3, zero, 424
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 2047
	addi a2, a2, 97
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 984
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 384
	addi a3, zero, 264
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 2047
	addi a2, a2, 97
	addi a3, zero, 2047
	addi a3, a3, 177
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 984
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 424
	addi a3, zero, 264
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 2047
	addi a2, a2, 137
	addi a3, zero, 2047
	addi a3, a3, 177
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 864
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1024
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 864
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 304
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 344
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 864
	addi a3, zero, 944
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1024
	addi a3, zero, 944
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 1024
	addi a3, zero, 944
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 904
	addi a2, zero, 864
	addi a3, zero, 944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 984
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 304
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 344
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 984
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 304
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1024
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 904
	addi a2, zero, 904
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1184
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1104
	addi a3, zero, 864
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 864
	addi a3, zero, 984
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1104
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 1184
	addi a3, zero, 944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 944
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 864(s0)
	sd t0, 720(a6)
	ld t0, 872(s0)
	sd t0, 728(a6)
	ld t0, 880(s0)
	sd t0, 736(a6)
	ld t0, 888(s0)
	sd t0, 744(a6)
	ld t0, 896(s0)
	sd t0, 752(a6)
	ld t0, 904(s0)
	sd t0, 760(a6)
	ld t0, 912(s0)
	sd t0, 768(a6)
	ld t0, 920(s0)
	sd t0, 776(a6)
	ld t0, 928(s0)
	sd t0, 784(a6)
	ld t0, 936(s0)
	sd t0, 792(a6)
	ld t0, 944(s0)
	sd t0, 800(a6)
	ld t0, 952(s0)
	sd t0, 808(a6)
	ld t0, 960(s0)
	sd t0, 816(a6)
	ld t0, 968(s0)
	sd t0, 824(a6)
	ld t0, 976(s0)
	sd t0, 832(a6)
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 384
	addi a3, zero, 2047
	addi a3, a3, 217
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 424
	addi a3, zero, 2047
	addi a3, a3, 257
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 264
	addi a3, zero, 2047
	addi a3, a3, 297
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 384
	addi a3, zero, 424
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 2047
	addi a2, a2, 217
	addi a3, zero, 2047
	addi a3, a3, 257
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 984
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 384
	addi a3, zero, 264
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 2047
	addi a2, a2, 217
	addi a3, zero, 2047
	addi a3, a3, 297
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 984
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 424
	addi a3, zero, 264
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 2047
	addi a2, a2, 257
	addi a3, zero, 2047
	addi a3, a3, 297
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 864
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1024
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 864
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 304
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 344
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 864
	addi a3, zero, 944
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1024
	addi a3, zero, 944
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 1024
	addi a3, zero, 944
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 904
	addi a2, zero, 864
	addi a3, zero, 944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 984
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 304
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 344
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 984
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 304
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1024
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 904
	addi a2, zero, 904
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1184
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1104
	addi a3, zero, 864
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 864
	addi a3, zero, 984
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1104
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 1184
	addi a3, zero, 944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 944
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 864(s0)
	sd t0, 840(a6)
	ld t0, 872(s0)
	sd t0, 848(a6)
	ld t0, 880(s0)
	sd t0, 856(a6)
	ld t0, 888(s0)
	sd t0, 864(a6)
	ld t0, 896(s0)
	sd t0, 872(a6)
	ld t0, 904(s0)
	sd t0, 880(a6)
	ld t0, 912(s0)
	sd t0, 888(a6)
	ld t0, 920(s0)
	sd t0, 896(a6)
	ld t0, 928(s0)
	sd t0, 904(a6)
	ld t0, 936(s0)
	sd t0, 912(a6)
	ld t0, 944(s0)
	sd t0, 920(a6)
	ld t0, 952(s0)
	sd t0, 928(a6)
	ld t0, 960(s0)
	sd t0, 936(a6)
	ld t0, 968(s0)
	sd t0, 944(a6)
	ld t0, 976(s0)
	sd t0, 952(a6)
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1904
	addi a3, zero, 1584
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1944
	addi a3, zero, 1784
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 1984
	addi a3, zero, 264
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1904
	addi a3, zero, 1944
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1584
	addi a3, zero, 1784
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 984
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1904
	addi a3, zero, 1984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1584
	addi a3, zero, 264
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 984
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1944
	addi a3, zero, 1984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1784
	addi a3, zero, 264
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 864
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1024
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 864
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 304
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 344
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 864
	addi a3, zero, 944
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1024
	addi a3, zero, 944
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 1024
	addi a3, zero, 944
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 904
	addi a2, zero, 864
	addi a3, zero, 944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 984
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 304
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 344
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 984
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 304
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1024
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 904
	addi a2, zero, 904
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1184
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1104
	addi a3, zero, 864
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 864
	addi a3, zero, 984
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1104
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 1184
	addi a3, zero, 944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 944
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 864(s0)
	sd t0, 1080(a6)
	ld t0, 872(s0)
	sd t0, 1088(a6)
	ld t0, 880(s0)
	sd t0, 1096(a6)
	ld t0, 888(s0)
	sd t0, 1104(a6)
	ld t0, 896(s0)
	sd t0, 1112(a6)
	ld t0, 904(s0)
	sd t0, 1120(a6)
	ld t0, 912(s0)
	sd t0, 1128(a6)
	ld t0, 920(s0)
	sd t0, 1136(a6)
	ld t0, 928(s0)
	sd t0, 1144(a6)
	ld t0, 936(s0)
	sd t0, 1152(a6)
	ld t0, 944(s0)
	sd t0, 1160(a6)
	ld t0, 952(s0)
	sd t0, 1168(a6)
	ld t0, 960(s0)
	sd t0, 1176(a6)
	ld t0, 968(s0)
	sd t0, 1184(a6)
	ld t0, 976(s0)
	sd t0, 1192(a6)
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1904
	addi a3, zero, 2047
	addi a3, a3, 97
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1944
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 1984
	addi a3, zero, 2047
	addi a3, a3, 177
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1904
	addi a3, zero, 1944
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 2047
	addi a2, a2, 97
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 984
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1904
	addi a3, zero, 1984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 2047
	addi a2, a2, 97
	addi a3, zero, 2047
	addi a3, a3, 177
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 984
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1944
	addi a3, zero, 1984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 2047
	addi a2, a2, 137
	addi a3, zero, 2047
	addi a3, a3, 177
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 864
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1024
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 864
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 304
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 344
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 864
	addi a3, zero, 944
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1024
	addi a3, zero, 944
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 1024
	addi a3, zero, 944
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 904
	addi a2, zero, 864
	addi a3, zero, 944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 984
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 304
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 344
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 984
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 304
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1024
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 904
	addi a2, zero, 904
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1184
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1104
	addi a3, zero, 864
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 864
	addi a3, zero, 984
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1104
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 1184
	addi a3, zero, 944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 944
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 864(s0)
	sd t0, 1200(a6)
	ld t0, 872(s0)
	sd t0, 1208(a6)
	ld t0, 880(s0)
	sd t0, 1216(a6)
	ld t0, 888(s0)
	sd t0, 1224(a6)
	ld t0, 896(s0)
	sd t0, 1232(a6)
	ld t0, 904(s0)
	sd t0, 1240(a6)
	ld t0, 912(s0)
	sd t0, 1248(a6)
	ld t0, 920(s0)
	sd t0, 1256(a6)
	ld t0, 928(s0)
	sd t0, 1264(a6)
	ld t0, 936(s0)
	sd t0, 1272(a6)
	ld t0, 944(s0)
	sd t0, 1280(a6)
	ld t0, 952(s0)
	sd t0, 1288(a6)
	ld t0, 960(s0)
	sd t0, 1296(a6)
	ld t0, 968(s0)
	sd t0, 1304(a6)
	ld t0, 976(s0)
	sd t0, 1312(a6)
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1904
	addi a3, zero, 2047
	addi a3, a3, 217
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1944
	addi a3, zero, 2047
	addi a3, a3, 257
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 1984
	addi a3, zero, 2047
	addi a3, a3, 297
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1904
	addi a3, zero, 1944
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 2047
	addi a2, a2, 217
	addi a3, zero, 2047
	addi a3, a3, 257
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 984
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1904
	addi a3, zero, 1984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 2047
	addi a2, a2, 217
	addi a3, zero, 2047
	addi a3, a3, 297
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 984
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1944
	addi a3, zero, 1984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 2047
	addi a2, a2, 257
	addi a3, zero, 2047
	addi a3, a3, 297
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 864
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1024
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 864
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 304
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 344
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 864
	addi a3, zero, 944
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1024
	addi a3, zero, 944
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 1024
	addi a3, zero, 944
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 904
	addi a2, zero, 864
	addi a3, zero, 944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 984
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 304
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 344
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 984
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 304
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1024
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 904
	addi a2, zero, 904
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1184
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1104
	addi a3, zero, 864
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 864
	addi a3, zero, 984
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1104
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 1184
	addi a3, zero, 944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 944
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 864(s0)
	sd t0, 1320(a6)
	ld t0, 872(s0)
	sd t0, 1328(a6)
	ld t0, 880(s0)
	sd t0, 1336(a6)
	ld t0, 888(s0)
	sd t0, 1344(a6)
	ld t0, 896(s0)
	sd t0, 1352(a6)
	ld t0, 904(s0)
	sd t0, 1360(a6)
	ld t0, 912(s0)
	sd t0, 1368(a6)
	ld t0, 920(s0)
	sd t0, 1376(a6)
	ld t0, 928(s0)
	sd t0, 1384(a6)
	ld t0, 936(s0)
	sd t0, 1392(a6)
	ld t0, 944(s0)
	sd t0, 1400(a6)
	ld t0, 952(s0)
	sd t0, 1408(a6)
	ld t0, 960(s0)
	sd t0, 1416(a6)
	ld t0, 968(s0)
	sd t0, 1424(a6)
	ld t0, 976(s0)
	sd t0, 1432(a6)
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 2024
	addi a3, zero, 1584
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 2047
	addi a2, a2, 17
	addi a3, zero, 1784
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 2047
	addi a2, a2, 57
	addi a3, zero, 264
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 2024
	addi a3, zero, 2047
	addi a3, a3, 17
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1584
	addi a3, zero, 1784
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 984
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 2024
	addi a3, zero, 2047
	addi a3, a3, 57
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1584
	addi a3, zero, 264
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 984
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 2047
	addi a2, a2, 17
	addi a3, zero, 2047
	addi a3, a3, 57
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1784
	addi a3, zero, 264
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 864
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1024
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 864
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 304
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 344
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 864
	addi a3, zero, 944
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1024
	addi a3, zero, 944
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 1024
	addi a3, zero, 944
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 904
	addi a2, zero, 864
	addi a3, zero, 944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 984
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 304
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 344
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 984
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 304
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1024
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 904
	addi a2, zero, 904
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1184
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1104
	addi a3, zero, 864
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 864
	addi a3, zero, 984
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1104
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 1184
	addi a3, zero, 944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 944
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 864(s0)
	sd t0, 1560(a6)
	ld t0, 872(s0)
	sd t0, 1568(a6)
	ld t0, 880(s0)
	sd t0, 1576(a6)
	ld t0, 888(s0)
	sd t0, 1584(a6)
	ld t0, 896(s0)
	sd t0, 1592(a6)
	ld t0, 904(s0)
	sd t0, 1600(a6)
	ld t0, 912(s0)
	sd t0, 1608(a6)
	ld t0, 920(s0)
	sd t0, 1616(a6)
	ld t0, 928(s0)
	sd t0, 1624(a6)
	ld t0, 936(s0)
	sd t0, 1632(a6)
	ld t0, 944(s0)
	sd t0, 1640(a6)
	ld t0, 952(s0)
	sd t0, 1648(a6)
	ld t0, 960(s0)
	sd t0, 1656(a6)
	ld t0, 968(s0)
	sd t0, 1664(a6)
	ld t0, 976(s0)
	sd t0, 1672(a6)
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 2024
	addi a3, zero, 2047
	addi a3, a3, 97
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 2047
	addi a2, a2, 17
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 2047
	addi a2, a2, 57
	addi a3, zero, 2047
	addi a3, a3, 177
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 2024
	addi a3, zero, 2047
	addi a3, a3, 17
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 2047
	addi a2, a2, 97
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 984
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 2024
	addi a3, zero, 2047
	addi a3, a3, 57
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 2047
	addi a2, a2, 97
	addi a3, zero, 2047
	addi a3, a3, 177
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 984
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 2047
	addi a2, a2, 17
	addi a3, zero, 2047
	addi a3, a3, 57
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 2047
	addi a2, a2, 137
	addi a3, zero, 2047
	addi a3, a3, 177
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 864
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1024
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 864
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 304
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 344
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 864
	addi a3, zero, 944
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1024
	addi a3, zero, 944
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 1024
	addi a3, zero, 944
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 904
	addi a2, zero, 864
	addi a3, zero, 944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 984
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 304
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 344
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 984
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 304
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1024
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 904
	addi a2, zero, 904
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1184
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1104
	addi a3, zero, 864
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 864
	addi a3, zero, 984
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1104
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 1184
	addi a3, zero, 944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 944
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 864(s0)
	sd t0, 1680(a6)
	ld t0, 872(s0)
	sd t0, 1688(a6)
	ld t0, 880(s0)
	sd t0, 1696(a6)
	ld t0, 888(s0)
	sd t0, 1704(a6)
	ld t0, 896(s0)
	sd t0, 1712(a6)
	ld t0, 904(s0)
	sd t0, 1720(a6)
	ld t0, 912(s0)
	sd t0, 1728(a6)
	ld t0, 920(s0)
	sd t0, 1736(a6)
	ld t0, 928(s0)
	sd t0, 1744(a6)
	ld t0, 936(s0)
	sd t0, 1752(a6)
	ld t0, 944(s0)
	sd t0, 1760(a6)
	ld t0, 952(s0)
	sd t0, 1768(a6)
	ld t0, 960(s0)
	sd t0, 1776(a6)
	ld t0, 968(s0)
	sd t0, 1784(a6)
	ld t0, 976(s0)
	sd t0, 1792(a6)
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 2024
	addi a3, zero, 2047
	addi a3, a3, 217
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 2047
	addi a2, a2, 17
	addi a3, zero, 2047
	addi a3, a3, 257
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 2047
	addi a2, a2, 57
	addi a3, zero, 2047
	addi a3, a3, 297
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 2024
	addi a3, zero, 2047
	addi a3, a3, 17
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 2047
	addi a2, a2, 217
	addi a3, zero, 2047
	addi a3, a3, 257
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 984
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 2024
	addi a3, zero, 2047
	addi a3, a3, 57
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 2047
	addi a2, a2, 217
	addi a3, zero, 2047
	addi a3, a3, 297
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 984
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 2047
	addi a2, a2, 17
	addi a3, zero, 2047
	addi a3, a3, 57
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 2047
	addi a2, a2, 257
	addi a3, zero, 2047
	addi a3, a3, 297
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 864
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1024
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 864
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 304
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 344
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 864
	addi a3, zero, 944
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1024
	addi a3, zero, 944
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 1024
	addi a3, zero, 944
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 904
	addi a2, zero, 864
	addi a3, zero, 944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 984
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 304
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 344
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 984
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 304
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1024
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 904
	addi a2, zero, 904
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1184
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1104
	addi a3, zero, 864
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 864
	addi a3, zero, 984
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1104
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 1184
	addi a3, zero, 944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 944
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 864(s0)
	sd t0, 1800(a6)
	ld t0, 872(s0)
	sd t0, 1808(a6)
	ld t0, 880(s0)
	sd t0, 1816(a6)
	ld t0, 888(s0)
	sd t0, 1824(a6)
	ld t0, 896(s0)
	sd t0, 1832(a6)
	ld t0, 904(s0)
	sd t0, 1840(a6)
	ld t0, 912(s0)
	sd t0, 1848(a6)
	ld t0, 920(s0)
	sd t0, 1856(a6)
	ld t0, 928(s0)
	sd t0, 1864(a6)
	ld t0, 936(s0)
	sd t0, 1872(a6)
	ld t0, 944(s0)
	sd t0, 1880(a6)
	ld t0, 952(s0)
	sd t0, 1888(a6)
	ld t0, 960(s0)
	sd t0, 1896(a6)
	ld t0, 968(s0)
	sd t0, 1904(a6)
	ld t0, 976(s0)
	sd t0, 1912(a6)
	ld t0, 184(s0)
	sd t0, 624(s0)
	ld t0, 192(s0)
	sd t0, 632(s0)
	ld t0, 200(s0)
	sd t0, 640(s0)
	ld t0, 208(s0)
	sd t0, 648(s0)
	ld t0, 216(s0)
	sd t0, 656(s0)
	ld t0, 264(s0)
	sd t0, 664(s0)
	ld t0, 272(s0)
	sd t0, 672(s0)
	ld t0, 280(s0)
	sd t0, 680(s0)
	ld t0, 288(s0)
	sd t0, 688(s0)
	ld t0, 296(s0)
	sd t0, 696(s0)
	ld t0, 184(s0)
	sd t0, 704(s0)
	ld t0, 192(s0)
	sd t0, 712(s0)
	ld t0, 200(s0)
	sd t0, 720(s0)
	ld t0, 208(s0)
	sd t0, 728(s0)
	ld t0, 216(s0)
	sd t0, 736(s0)
	addi s1, zero, 160
267:
	addi s1, s1, -1
	srli t1, s1, 5
	slli t1, t1, 3
	add t1, t1, s0
	ld t2, 1384(t1)
	ld t3, 1504(t1)
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
	ld t1, 120(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 240(a0)
	ld t2, 360(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 480(a0)
	ld t2, 600(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 720(a0)
	ld t3, 840(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 960(a0)
	ld t2, 1080(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1200(a0)
	ld t3, 1320(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1440(a0)
	ld t3, 1560(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1680(a0)
	ld t4, 1800(a0)
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
	sd t0, 337(s0)
	addi s0, s0, -2047
	ld t0, 8(a0)
	ld t1, 128(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 248(a0)
	ld t2, 368(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 488(a0)
	ld t2, 608(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 728(a0)
	ld t3, 848(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 968(a0)
	ld t2, 1088(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1208(a0)
	ld t3, 1328(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1448(a0)
	ld t3, 1568(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1688(a0)
	ld t4, 1808(a0)
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
	sd t0, 345(s0)
	addi s0, s0, -2047
	ld t0, 16(a0)
	ld t1, 136(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 256(a0)
	ld t2, 376(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 496(a0)
	ld t2, 616(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 736(a0)
	ld t3, 856(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 976(a0)
	ld t2, 1096(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1216(a0)
	ld t3, 1336(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1456(a0)
	ld t3, 1576(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1696(a0)
	ld t4, 1816(a0)
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
	sd t0, 353(s0)
	addi s0, s0, -2047
	ld t0, 24(a0)
	ld t1, 144(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 264(a0)
	ld t2, 384(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 504(a0)
	ld t2, 624(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 744(a0)
	ld t3, 864(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 984(a0)
	ld t2, 1104(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1224(a0)
	ld t3, 1344(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1464(a0)
	ld t3, 1584(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1704(a0)
	ld t4, 1824(a0)
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
	sd t0, 361(s0)
	addi s0, s0, -2047
	ld t0, 32(a0)
	ld t1, 152(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 272(a0)
	ld t2, 392(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 512(a0)
	ld t2, 632(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 752(a0)
	ld t3, 872(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 992(a0)
	ld t2, 1112(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1232(a0)
	ld t3, 1352(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1472(a0)
	ld t3, 1592(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1712(a0)
	ld t4, 1832(a0)
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
	sd t0, 369(s0)
	addi s0, s0, -2047
	ld t0, 40(a0)
	ld t1, 160(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 280(a0)
	ld t2, 400(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 520(a0)
	ld t2, 640(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 760(a0)
	ld t3, 880(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1000(a0)
	ld t2, 1120(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1240(a0)
	ld t3, 1360(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1480(a0)
	ld t3, 1600(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1720(a0)
	ld t4, 1840(a0)
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
	sd t0, 377(s0)
	addi s0, s0, -2047
	ld t0, 48(a0)
	ld t1, 168(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 288(a0)
	ld t2, 408(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 528(a0)
	ld t2, 648(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 768(a0)
	ld t3, 888(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1008(a0)
	ld t2, 1128(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1248(a0)
	ld t3, 1368(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1488(a0)
	ld t3, 1608(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1728(a0)
	ld t4, 1848(a0)
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
	sd t0, 385(s0)
	addi s0, s0, -2047
	ld t0, 56(a0)
	ld t1, 176(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 296(a0)
	ld t2, 416(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 536(a0)
	ld t2, 656(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 776(a0)
	ld t3, 896(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1016(a0)
	ld t2, 1136(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1256(a0)
	ld t3, 1376(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1496(a0)
	ld t3, 1616(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1736(a0)
	ld t4, 1856(a0)
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
	sd t0, 393(s0)
	addi s0, s0, -2047
	ld t0, 64(a0)
	ld t1, 184(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 304(a0)
	ld t2, 424(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 544(a0)
	ld t2, 664(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 784(a0)
	ld t3, 904(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1024(a0)
	ld t2, 1144(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1264(a0)
	ld t3, 1384(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1504(a0)
	ld t3, 1624(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1744(a0)
	ld t4, 1864(a0)
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
	sd t0, 401(s0)
	addi s0, s0, -2047
	ld t0, 72(a0)
	ld t1, 192(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 312(a0)
	ld t2, 432(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 552(a0)
	ld t2, 672(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 792(a0)
	ld t3, 912(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1032(a0)
	ld t2, 1152(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1272(a0)
	ld t3, 1392(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1512(a0)
	ld t3, 1632(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1752(a0)
	ld t4, 1872(a0)
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
	sd t0, 409(s0)
	addi s0, s0, -2047
	ld t0, 80(a0)
	ld t1, 200(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 320(a0)
	ld t2, 440(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 560(a0)
	ld t2, 680(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 800(a0)
	ld t3, 920(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1040(a0)
	ld t2, 1160(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1280(a0)
	ld t3, 1400(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1520(a0)
	ld t3, 1640(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1760(a0)
	ld t4, 1880(a0)
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
	sd t0, 417(s0)
	addi s0, s0, -2047
	ld t0, 88(a0)
	ld t1, 208(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 328(a0)
	ld t2, 448(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 568(a0)
	ld t2, 688(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 808(a0)
	ld t3, 928(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1048(a0)
	ld t2, 1168(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1288(a0)
	ld t3, 1408(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1528(a0)
	ld t3, 1648(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1768(a0)
	ld t4, 1888(a0)
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
	sd t0, 425(s0)
	addi s0, s0, -2047
	ld t0, 96(a0)
	ld t1, 216(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 336(a0)
	ld t2, 456(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 576(a0)
	ld t2, 696(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 816(a0)
	ld t3, 936(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1056(a0)
	ld t2, 1176(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1296(a0)
	ld t3, 1416(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1536(a0)
	ld t3, 1656(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1776(a0)
	ld t4, 1896(a0)
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
	sd t0, 433(s0)
	addi s0, s0, -2047
	ld t0, 104(a0)
	ld t1, 224(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 344(a0)
	ld t2, 464(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 584(a0)
	ld t2, 704(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 824(a0)
	ld t3, 944(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1064(a0)
	ld t2, 1184(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1304(a0)
	ld t3, 1424(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1544(a0)
	ld t3, 1664(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1784(a0)
	ld t4, 1904(a0)
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
	sd t0, 441(s0)
	addi s0, s0, -2047
	ld t0, 112(a0)
	ld t1, 232(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 352(a0)
	ld t2, 472(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 592(a0)
	ld t2, 712(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 832(a0)
	ld t3, 952(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1072(a0)
	ld t2, 1192(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1312(a0)
	ld t3, 1432(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1552(a0)
	ld t3, 1672(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1792(a0)
	ld t4, 1912(a0)
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
	sd t0, 449(s0)
	addi s0, s0, -2047
	addi a0, s0, 0
	addi a1, zero, 744
	addi a2, zero, 624
	addi a3, zero, 704
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 704
	addi a3, zero, 704
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 784
	addi a2, zero, 664
	addi a3, zero, 984
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 824
	addi a2, zero, 704
	addi a3, zero, 184
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 744
	addi a3, zero, 744
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 784
	addi a3, zero, 784
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 1024
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 744
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1104
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 984
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1104
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 824
	addi a3, zero, 824
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 304
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 984
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 784
	addi a3, zero, 824
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 944
	addi a3, zero, 944
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1144
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 864
	addi a3, zero, 1104
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 864
	addi a3, zero, 1104
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 904
	addi a2, zero, 1104
	addi a3, zero, 864
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 904
	addi a2, zero, 1144
	addi a3, zero, 904
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 1064
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 1064
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 1064
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 904
	addi a2, zero, 904
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 864
	addi a3, zero, 864
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 904
	addi a3, zero, 904
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 1024
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 864
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1104
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 984
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1104
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 944
	addi a3, zero, 944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 304
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 984
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 824
	addi a2, zero, 904
	addi a3, zero, 944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 824
	addi a2, zero, 824
	addi a3, zero, 824
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 744
	addi a2, zero, 1144
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 744
	addi a2, zero, 744
	addi a3, zero, 1104
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 744
	addi a2, zero, 744
	addi a3, zero, 1104
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 784
	addi a2, zero, 1104
	addi a3, zero, 744
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 784
	addi a2, zero, 1144
	addi a3, zero, 784
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 1064
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 1064
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 1064
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 784
	addi a2, zero, 784
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 744
	addi a3, zero, 824
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 824
	addi a3, zero, 824
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 984
	addi a3, zero, 824
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 904
	addi a2, zero, 784
	addi a3, zero, 184
	call {vg_brainpoolp320r1_add_mod_p}
	addi t3, zero, 0
	ld t4, 944(s0)
	or t3, t3, t4
	ld t4, 952(s0)
	or t3, t3, t4
	ld t4, 960(s0)
	or t3, t3, t4
	ld t4, 968(s0)
	or t3, t3, t4
	ld t4, 976(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	ld t0, 904(s0)
	ld t1, 264(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 904(s0)
	ld t0, 912(s0)
	ld t1, 272(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 912(s0)
	ld t0, 920(s0)
	ld t1, 280(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 920(s0)
	ld t0, 928(s0)
	ld t1, 288(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 928(s0)
	ld t0, 936(s0)
	ld t1, 296(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 936(s0)
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 864
	addi a3, zero, 2047
	addi a3, a3, 337
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 904
	addi a3, zero, 2047
	addi a3, a3, 377
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 944
	addi a3, zero, 2047
	addi a3, a3, 417
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 864
	addi a3, zero, 904
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 2047
	addi a2, a2, 337
	addi a3, zero, 2047
	addi a3, a3, 377
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 984
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 864
	addi a3, zero, 944
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 2047
	addi a2, a2, 337
	addi a3, zero, 2047
	addi a3, a3, 417
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 984
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 904
	addi a3, zero, 944
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 624
	addi a2, zero, 2047
	addi a2, a2, 377
	addi a3, zero, 2047
	addi a3, a3, 417
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 624
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 624
	addi a2, zero, 1024
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 624
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 704
	addi a2, zero, 304
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 624
	addi a2, zero, 344
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 704
	addi a2, zero, 624
	addi a3, zero, 704
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 624
	addi a2, zero, 1024
	addi a3, zero, 704
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 704
	addi a2, zero, 1024
	addi a3, zero, 704
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 664
	addi a2, zero, 624
	addi a3, zero, 704
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 984
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 304
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 344
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 984
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 304
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1024
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 664
	addi a2, zero, 664
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1184
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 624
	addi a2, zero, 1104
	addi a3, zero, 624
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 624
	addi a2, zero, 624
	addi a3, zero, 984
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1104
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 704
	addi a2, zero, 1184
	addi a3, zero, 704
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 704
	addi a2, zero, 704
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	bnez s1, 267b
	addi a0, s0, 0
	addi a1, zero, 1904
	addi a2, zero, 704
	addi a3, zero, 264
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 177
	addi a2, zero, 1904
	addi a3, zero, 1904
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1944
	addi a2, zero, 1904
	addi a3, zero, 2047
	addi a3, a3, 177
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1984
	addi a2, zero, 1944
	addi a3, zero, 2047
	addi a3, a3, 177
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2024
	addi a2, zero, 1984
	addi a3, zero, 2047
	addi a3, a3, 177
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 17
	addi a2, zero, 2024
	addi a3, zero, 2047
	addi a3, a3, 177
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 57
	addi a2, zero, 2047
	addi a2, a2, 17
	addi a3, zero, 2047
	addi a3, a3, 177
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 97
	addi a2, zero, 2047
	addi a2, a2, 57
	addi a3, zero, 2047
	addi a3, a3, 177
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 137
	addi a2, zero, 2047
	addi a2, a2, 97
	addi a3, zero, 2047
	addi a3, a3, 177
	call {vg_brainpoolp320r1_mul_mod_p}
	addi t0, s0, 2047
	ld t0, 97(t0)
	sd t0, 1224(s0)
	addi t0, s0, 2047
	ld t0, 105(t0)
	sd t0, 1232(s0)
	addi t0, s0, 2047
	ld t0, 113(t0)
	sd t0, 1240(s0)
	addi t0, s0, 2047
	ld t0, 121(t0)
	sd t0, 1248(s0)
	addi t0, s0, 2047
	ld t0, 129(t0)
	sd t0, 1256(s0)
	addi s1, zero, 6
268:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 268b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 97
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 5
269:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 269b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 3
270:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 270b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1904
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 6
271:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 271b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2024
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 3
272:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 272b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1904
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 11
273:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 273b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 97
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 3
274:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 274b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1984
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 5
275:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 275b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 7
276:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 276b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 17
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 4
277:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 277b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 5
278:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 278b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 97
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 4
279:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 279b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 1
280:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 280b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1904
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 8
281:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 281b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 17
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 3
282:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 282b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2024
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 7
283:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 283b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 8
284:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 284b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 57
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 4
285:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 285b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 97
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 3
286:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 286b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1984
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 3
287:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 287b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1904
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 12
288:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 288b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 8
289:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 289b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 6
290:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 290b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 57
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 4
291:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 291b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 4
292:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 292b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 7
293:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 293b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 2
294:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 294b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 6
295:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 295b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 3
296:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 296b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1984
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 6
297:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 297b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 97
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 3
298:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 298b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2024
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 5
299:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 299b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 97
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 3
2100:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 2100b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2024
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 2
2101:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 2101b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1904
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 10
2102:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 2102b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 97
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 3
2103:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 2103b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2024
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 5
2104:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 2104b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 5
2105:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 2105b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 17
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 4
2106:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 2106b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 6
2107:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 2107b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 17
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 5
2108:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 2108b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 57
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 4
2109:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 2109b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 17
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 3
2110:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 2110b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2024
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 3
2111:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 2111b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 7
2112:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 2112b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 7
2113:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 2113b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 17
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 6
2114:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 2114b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 4
2115:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 2115b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 57
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 7
2116:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 2116b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1984
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 7
2117:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 2117b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 2
2118:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 2118b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 6
2119:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 2119b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 97
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 2
2120:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 2120b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1904
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 9
2121:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 2121b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 17
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 5
2122:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 2122b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 57
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 7
2123:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 2123b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 1
2124:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 2124b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1904
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 7
2125:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 2125b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 97
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 4
2126:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 2126b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 17
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 4
2127:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 2127b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 17
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 4
2128:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 2128b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2024
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 7
2129:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 2129b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 17
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 2
2130:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 2130b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1904
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 744
	addi a2, zero, 624
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 784
	addi a2, zero, 744
	addi a3, zero, 224
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 824
	addi a2, zero, 784
	addi a3, zero, 184
	call {vg_brainpoolp320r1_add_mod_n}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 464
	addi a3, zero, 184
	call {vg_brainpoolp320r1_add_mod_n}
	addi a0, s0, 0
	addi a1, zero, 904
	addi a2, zero, 824
	addi a3, zero, 864
	call {vg_brainpoolp320r1_sub_mod_n}
	addi t3, zero, 0
	ld t4, 704(s0)
	or t3, t3, t4
	ld t4, 712(s0)
	or t3, t3, t4
	ld t4, 720(s0)
	or t3, t3, t4
	ld t4, 728(s0)
	or t3, t3, t4
	ld t4, 736(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	xori a7, a7, -1
	ld t0, 1824(s0)
	and t0, t0, a7
	sd t0, 1824(s0)
	addi t3, zero, 0
	ld t4, 904(s0)
	or t3, t3, t4
	ld t4, 912(s0)
	or t3, t3, t4
	ld t4, 920(s0)
	or t3, t3, t4
	ld t4, 928(s0)
	or t3, t3, t4
	ld t4, 936(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	ld t0, 1824(s0)
	and t0, t0, a7
	sd t0, 1824(s0)
	ld a0, 1824(s0)
	andi a0, a0, 1
	ld ra, 24(s0)
	ld s2, 16(s0)
	ld s1, 8(s0)
	ld s3, 32(s0)
	ld s0, 0(s0)
	addi sp, sp, 80
	addi t0, zero, 0
	addi sp, sp, -80
	addi t1, sp, 0
	sd t0, 0(t1)
	sd t0, 8(t1)
	sd t0, 16(t1)
	sd t0, 24(t1)
	sd t0, 32(t1)
	sd t0, 40(t1)
	sd t0, 48(t1)
	sd t0, 56(t1)
	sd t0, 64(t1)
	sd t0, 72(t1)
	addi sp, sp, 80
	slli a0, a0, 32
	srli a0, a0, 32
	addi a1, zero, 0
	addi a2, zero, 0
	addi a3, zero, 0
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	addi a7, zero, 0
	addi t0, zero, 0
	addi t1, zero, 0
	addi t2, zero, 0
	addi t3, zero, 0
	addi t4, zero, 0
	addi t5, zero, 0
	addi t6, zero, 0
	ret
	.option pop

vg_ecdsa_brainpoolp320r1_sign:
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
	addi t1, zero, 40
	sub t2, s7, t1
	srli t3, t2, 63
	addi t4, zero, 0
	sub t3, t4, t3
	and t2, t2, t3
	add a6, t1, t2
	addi a4, s4, 0
	addi a5, s1, 272
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
	sd t0, 32(s0)
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
	sd t0, 24(s0)
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
	sd t0, 16(s0)
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
	sd t0, 8(s0)
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
	sd t0, 0(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 40(s0)
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
	addi a0, s0, 0
	addi a1, zero, 80
	addi a2, zero, 0
	addi a3, zero, 40
	call {vg_brainpoolp320r1_add_mod_n}
	addi a7, zero, -1
	ld t0, 112(s0)
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
	ld t0, 104(s0)
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
	ld t0, 96(s0)
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
	ld t0, 88(s0)
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
	ld t0, 80(s0)
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
	addi a3, zero, 40
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	add a1, s8, s7
	addi a1, a1, 41
	addi a2, s1, 304
	addi a3, zero, 40
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, s0, 192
	add a2, s8, s7
	addi a2, a2, 81
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
	addi a3, zero, 40
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	add a1, s8, s7
	addi a1, a1, 41
	addi a2, s1, 304
	addi a3, zero, 40
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, s0, 192
	add a2, s8, s7
	addi a2, a2, 81
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
	addi t0, zero, 40
	sltu t6, s9, t0
	bnez t6, 22b
	addi a0, s2, 0
	addi a1, s3, 0
	addi a2, s1, 232
	addi a3, s1, 368
	addi a4, s0, 0
	call {vg_ecdsa_brainpoolp320r1_sign_k}
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
	addi t0, zero, 0
	addi sp, sp, -1024
	addi t1, sp, 0
	sd t0, 0(t1)
	sd t0, 8(t1)
	sd t0, 16(t1)
	sd t0, 24(t1)
	sd t0, 32(t1)
	sd t0, 40(t1)
	sd t0, 48(t1)
	sd t0, 56(t1)
	sd t0, 64(t1)
	sd t0, 72(t1)
	sd t0, 80(t1)
	sd t0, 88(t1)
	sd t0, 96(t1)
	sd t0, 104(t1)
	sd t0, 112(t1)
	sd t0, 120(t1)
	sd t0, 128(t1)
	sd t0, 136(t1)
	sd t0, 144(t1)
	sd t0, 152(t1)
	sd t0, 160(t1)
	sd t0, 168(t1)
	sd t0, 176(t1)
	sd t0, 184(t1)
	sd t0, 192(t1)
	sd t0, 200(t1)
	sd t0, 208(t1)
	sd t0, 216(t1)
	sd t0, 224(t1)
	sd t0, 232(t1)
	sd t0, 240(t1)
	sd t0, 248(t1)
	sd t0, 256(t1)
	sd t0, 264(t1)
	sd t0, 272(t1)
	sd t0, 280(t1)
	sd t0, 288(t1)
	sd t0, 296(t1)
	sd t0, 304(t1)
	sd t0, 312(t1)
	sd t0, 320(t1)
	sd t0, 328(t1)
	sd t0, 336(t1)
	sd t0, 344(t1)
	sd t0, 352(t1)
	sd t0, 360(t1)
	sd t0, 368(t1)
	sd t0, 376(t1)
	sd t0, 384(t1)
	sd t0, 392(t1)
	sd t0, 400(t1)
	sd t0, 408(t1)
	sd t0, 416(t1)
	sd t0, 424(t1)
	sd t0, 432(t1)
	sd t0, 440(t1)
	sd t0, 448(t1)
	sd t0, 456(t1)
	sd t0, 464(t1)
	sd t0, 472(t1)
	sd t0, 480(t1)
	sd t0, 488(t1)
	sd t0, 496(t1)
	sd t0, 504(t1)
	sd t0, 512(t1)
	sd t0, 520(t1)
	sd t0, 528(t1)
	sd t0, 536(t1)
	sd t0, 544(t1)
	sd t0, 552(t1)
	sd t0, 560(t1)
	sd t0, 568(t1)
	sd t0, 576(t1)
	sd t0, 584(t1)
	sd t0, 592(t1)
	sd t0, 600(t1)
	sd t0, 608(t1)
	sd t0, 616(t1)
	sd t0, 624(t1)
	sd t0, 632(t1)
	sd t0, 640(t1)
	sd t0, 648(t1)
	sd t0, 656(t1)
	sd t0, 664(t1)
	sd t0, 672(t1)
	sd t0, 680(t1)
	sd t0, 688(t1)
	sd t0, 696(t1)
	sd t0, 704(t1)
	sd t0, 712(t1)
	sd t0, 720(t1)
	sd t0, 728(t1)
	sd t0, 736(t1)
	sd t0, 744(t1)
	sd t0, 752(t1)
	sd t0, 760(t1)
	sd t0, 768(t1)
	sd t0, 776(t1)
	sd t0, 784(t1)
	sd t0, 792(t1)
	sd t0, 800(t1)
	sd t0, 808(t1)
	sd t0, 816(t1)
	sd t0, 824(t1)
	sd t0, 832(t1)
	sd t0, 840(t1)
	sd t0, 848(t1)
	sd t0, 856(t1)
	sd t0, 864(t1)
	sd t0, 872(t1)
	sd t0, 880(t1)
	sd t0, 888(t1)
	sd t0, 896(t1)
	sd t0, 904(t1)
	sd t0, 912(t1)
	sd t0, 920(t1)
	sd t0, 928(t1)
	sd t0, 936(t1)
	sd t0, 944(t1)
	sd t0, 952(t1)
	sd t0, 960(t1)
	sd t0, 968(t1)
	sd t0, 976(t1)
	sd t0, 984(t1)
	sd t0, 992(t1)
	sd t0, 1000(t1)
	sd t0, 1008(t1)
	sd t0, 1016(t1)
	addi sp, sp, 1024
	slli a0, a0, 32
	srli a0, a0, 32
	addi a1, zero, 0
	addi a2, zero, 0
	addi a3, zero, 0
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	addi a7, zero, 0
	addi t0, zero, 0
	addi t1, zero, 0
	addi t2, zero, 0
	addi t3, zero, 0
	addi t4, zero, 0
	addi t5, zero, 0
	addi t6, zero, 0
	ret
	.option pop
