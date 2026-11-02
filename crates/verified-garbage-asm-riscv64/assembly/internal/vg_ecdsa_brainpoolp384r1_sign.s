// The functions of `src/internal/vg_ecdsa_brainpoolp384r1_sign.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_brainpoolp384r1_sign:
	.option push
	.option arch, +m, +c
	sd s0, 0(a4)
	sd s1, 8(a4)
	sd s2, 16(a4)
	sd ra, 24(a4)
	sd s3, 32(a4)
	addi s0, a4, 0
	addi s3, a4, 0
	addi s2, a0, 0
	lbu t0, 0(a3)
	slli t0, t0, 8
	lbu t1, 1(a3)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 2(a3)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 3(a3)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 4(a3)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 5(a3)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 6(a3)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 7(a3)
	or t0, t0, t1
	sd t0, 1592(s0)
	lbu t0, 8(a3)
	slli t0, t0, 8
	lbu t1, 9(a3)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 10(a3)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 11(a3)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 12(a3)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 13(a3)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 14(a3)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 15(a3)
	or t0, t0, t1
	sd t0, 1584(s0)
	lbu t0, 16(a3)
	slli t0, t0, 8
	lbu t1, 17(a3)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 18(a3)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 19(a3)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 20(a3)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 21(a3)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 22(a3)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 23(a3)
	or t0, t0, t1
	sd t0, 1576(s0)
	lbu t0, 24(a3)
	slli t0, t0, 8
	lbu t1, 25(a3)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 26(a3)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 27(a3)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 28(a3)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 29(a3)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 30(a3)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 31(a3)
	or t0, t0, t1
	sd t0, 1568(s0)
	lbu t0, 32(a3)
	slli t0, t0, 8
	lbu t1, 33(a3)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 34(a3)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 35(a3)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 36(a3)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 37(a3)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 38(a3)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 39(a3)
	or t0, t0, t1
	sd t0, 1560(s0)
	lbu t0, 40(a3)
	slli t0, t0, 8
	lbu t1, 41(a3)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 42(a3)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 43(a3)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 44(a3)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 45(a3)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 46(a3)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 47(a3)
	or t0, t0, t1
	sd t0, 1552(s0)
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
	sd t0, 1688(s0)
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
	sd t0, 1680(s0)
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
	sd t0, 1672(s0)
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
	sd t0, 1664(s0)
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
	sd t0, 1656(s0)
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
	sd t0, 1648(s0)
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
	sd t0, 1736(s0)
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
	sd t0, 1728(s0)
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
	sd t0, 1720(s0)
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
	sd t0, 1712(s0)
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
	sd t0, 1704(s0)
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
	sd t0, 1696(s0)
	addi t0, zero, 0
	addi t0, t0, -1
	addi s0, s0, 2047
	sd t0, 129(s0)
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
	addi t5, zero, 0
	ld t3, 1648(s0)
	ld t4, 112(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1656(s0)
	ld t4, 120(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1664(s0)
	ld t4, 128(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1672(s0)
	ld t4, 136(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1680(s0)
	ld t4, 144(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1688(s0)
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
	ld t4, 1648(s0)
	or t3, t3, t4
	ld t4, 1656(s0)
	or t3, t3, t4
	ld t4, 1664(s0)
	or t3, t3, t4
	ld t4, 1672(s0)
	or t3, t3, t4
	ld t4, 1680(s0)
	or t3, t3, t4
	ld t4, 1688(s0)
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
	ld t0, 448(s0)
	sd t0, 736(s0)
	ld t0, 456(s0)
	sd t0, 744(s0)
	ld t0, 464(s0)
	sd t0, 752(s0)
	ld t0, 472(s0)
	sd t0, 760(s0)
	ld t0, 480(s0)
	sd t0, 768(s0)
	ld t0, 488(s0)
	sd t0, 776(s0)
	ld t0, 496(s0)
	sd t0, 784(s0)
	ld t0, 504(s0)
	sd t0, 792(s0)
	ld t0, 512(s0)
	sd t0, 800(s0)
	ld t0, 520(s0)
	sd t0, 808(s0)
	ld t0, 528(s0)
	sd t0, 816(s0)
	ld t0, 536(s0)
	sd t0, 824(s0)
	addi t5, zero, 0
	ld t3, 1552(s0)
	ld t4, 112(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1560(s0)
	ld t4, 120(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1568(s0)
	ld t4, 128(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1576(s0)
	ld t4, 136(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1584(s0)
	ld t4, 144(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1592(s0)
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
	ld t4, 1552(s0)
	or t3, t3, t4
	ld t4, 1560(s0)
	or t3, t3, t4
	ld t4, 1568(s0)
	or t3, t3, t4
	ld t4, 1576(s0)
	or t3, t3, t4
	ld t4, 1584(s0)
	or t3, t3, t4
	ld t4, 1592(s0)
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
	call {vg_brainpoolp384r1_mul}
	addi s0, s3, 0
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
20:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 20b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 273
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 6
21:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 21b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 465
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 4
22:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 22b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 417
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 7
23:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 23b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 2
24:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 24b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 8
25:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 25b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 2
26:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 26b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 5
27:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 27b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 273
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 5
28:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 28b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 369
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 8
29:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 29b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 3
210:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 210b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 5
211:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 211b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 11
212:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 212b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 5
213:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 213b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 465
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 3
214:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 214b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 5
215:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 215b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 3
216:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 216b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 369
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 5
217:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 217b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 2
218:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 218b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 273
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 5
219:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 219b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 7
220:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 220b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 369
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 4
221:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 221b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 273
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 3
222:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 222b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 8
223:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 223b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 369
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 5
224:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 224b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 1
225:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 225b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 6
226:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 226b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 5
227:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 227b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 417
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 5
228:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 228b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 4
229:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 229b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 369
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 4
230:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 230b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 8
231:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 231b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 417
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 3
232:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 232b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 369
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 5
233:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 233b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 4
234:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 234b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 2
235:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 235b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 6
236:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 236b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 5
237:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 237b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 5
238:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 238b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 9
239:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 239b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 417
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 5
240:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 240b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 465
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 6
241:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 241b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 369
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 5
242:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 242b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 6
243:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 243b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 273
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 6
244:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 244b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 465
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 4
245:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 245b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 4
246:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 246b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 4
247:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 247b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 465
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 1
248:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 248b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 4
249:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 249b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 7
250:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 250b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 417
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 6
251:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 251b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 369
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 5
252:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 252b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 465
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 6
253:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 253b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 5
254:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 254b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 369
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 5
255:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 255b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 417
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 2
256:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 256b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 273
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 5
257:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 257b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 4
258:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 258b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 273
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 3
259:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 259b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 10
260:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 260b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 369
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 2
261:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 261b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 7
262:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 262b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 5
263:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 263b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 369
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 5
264:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 264b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 273
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 7
265:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 265b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 369
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 2
266:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 266b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 6
267:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 267b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 369
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 15
268:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 268b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 417
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 4
269:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 269b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 417
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 1
270:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 270b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 4
271:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 271b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 9
272:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 272b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 4
273:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 273b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 1
274:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 274b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 6
275:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 275b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_brainpoolp384r1_mul_mod_p}
	addi s1, zero, 4
276:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	bnez s1, 276b
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
	addi a2, zero, 1552
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
	addi a3, a3, 273
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 6
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
	addi a3, a3, 465
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 4
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
	addi a3, a3, 417
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 7
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
	addi a3, a3, 561
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 2
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
	addi a3, a3, 225
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 8
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
	addi a3, a3, 321
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 2
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
	addi a3, a3, 225
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 5
284:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 284b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 273
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 5
285:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 285b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 369
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 8
286:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 286b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 3
287:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 287b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 5
288:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 288b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 11
289:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 289b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 5
290:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 290b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 465
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 3
291:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 291b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 5
292:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 292b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 3
293:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 293b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 369
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 5
294:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 294b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 2
295:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 295b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 273
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 5
296:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 296b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 7
297:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 297b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 369
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 4
298:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 298b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 273
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 3
299:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 299b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 8
2100:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 2100b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 369
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 5
2101:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 2101b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 1
2102:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 2102b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 6
2103:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 2103b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 5
2104:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 2104b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 417
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 5
2105:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 2105b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 4
2106:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 2106b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 369
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 4
2107:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 2107b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 8
2108:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 2108b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 417
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 3
2109:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 2109b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 369
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 5
2110:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 2110b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 4
2111:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 2111b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 2
2112:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 2112b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 6
2113:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 2113b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 5
2114:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 2114b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 3
2115:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 2115b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 273
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 4
2116:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 2116b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 273
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 7
2117:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 2117b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 1
2118:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 2118b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 7
2119:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 2119b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 465
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 6
2120:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 2120b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 2
2121:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 2121b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 273
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 6
2122:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 2122b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 4
2123:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 2123b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 417
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 5
2124:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 2124b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 465
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 8
2125:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 2125b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 8
2126:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 2126b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 417
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 5
2127:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 2127b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 6
2128:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 2128b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 4
2129:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 2129b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 417
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 3
2130:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 2130b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 369
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 5
2131:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 2131b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 369
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 4
2132:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 2132b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 5
2133:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 2133b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 3
2134:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 2134b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 5
2135:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 2135b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 465
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 4
2136:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 2136b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 3
2137:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 2137b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 5
2138:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 2138b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 4
2139:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 2139b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 4
2140:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 2140b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 6
2141:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 2141b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 273
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 4
2142:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 2142b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 9
2143:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 2143b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 369
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 4
2144:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 2144b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 369
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 4
2145:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 2145b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 7
2146:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 2146b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 273
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 3
2147:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 2147b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 11
2148:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 2148b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 465
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 3
2149:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 2149b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 3
2150:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 2150b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 6
2151:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 2151b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 5
2152:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 2152b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 273
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 5
2153:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 2153b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 3
2154:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 2154b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 273
	call {vg_brainpoolp384r1_mul_mod_n}
	addi s1, zero, 5
2155:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_n}
	bnez s1, 2155b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 273
	call {vg_brainpoolp384r1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1696
	addi a3, zero, 1744
	call {vg_brainpoolp384r1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 976
	addi a3, zero, 1744
	call {vg_brainpoolp384r1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1648
	addi a3, zero, 1744
	call {vg_brainpoolp384r1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1120
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1072
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_add_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1456
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1312
	addi a3, zero, 256
	call {vg_brainpoolp384r1_mul_mod_n}
	addi t3, zero, 0
	ld t4, 976(s0)
	or t3, t3, t4
	ld t4, 984(s0)
	or t3, t3, t4
	ld t4, 992(s0)
	or t3, t3, t4
	ld t4, 1000(s0)
	or t3, t3, t4
	ld t4, 1008(s0)
	or t3, t3, t4
	ld t4, 1016(s0)
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
	ld t4, 1360(s0)
	or t3, t3, t4
	ld t4, 1368(s0)
	or t3, t3, t4
	ld t4, 1376(s0)
	or t3, t3, t4
	ld t4, 1384(s0)
	or t3, t3, t4
	ld t4, 1392(s0)
	or t3, t3, t4
	ld t4, 1400(s0)
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
	addi a7, s0, 2047
	ld a7, 129(a7)
	ld t0, 1016(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 0(s2)
	srli t1, t0, 48
	sb t1, 1(s2)
	srli t1, t0, 40
	sb t1, 2(s2)
	srli t1, t0, 32
	sb t1, 3(s2)
	srli t1, t0, 24
	sb t1, 4(s2)
	srli t1, t0, 16
	sb t1, 5(s2)
	srli t1, t0, 8
	sb t1, 6(s2)
	srli t1, t0, 0
	sb t1, 7(s2)
	ld t0, 1008(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 8(s2)
	srli t1, t0, 48
	sb t1, 9(s2)
	srli t1, t0, 40
	sb t1, 10(s2)
	srli t1, t0, 32
	sb t1, 11(s2)
	srli t1, t0, 24
	sb t1, 12(s2)
	srli t1, t0, 16
	sb t1, 13(s2)
	srli t1, t0, 8
	sb t1, 14(s2)
	srli t1, t0, 0
	sb t1, 15(s2)
	ld t0, 1000(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 16(s2)
	srli t1, t0, 48
	sb t1, 17(s2)
	srli t1, t0, 40
	sb t1, 18(s2)
	srli t1, t0, 32
	sb t1, 19(s2)
	srli t1, t0, 24
	sb t1, 20(s2)
	srli t1, t0, 16
	sb t1, 21(s2)
	srli t1, t0, 8
	sb t1, 22(s2)
	srli t1, t0, 0
	sb t1, 23(s2)
	ld t0, 992(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 24(s2)
	srli t1, t0, 48
	sb t1, 25(s2)
	srli t1, t0, 40
	sb t1, 26(s2)
	srli t1, t0, 32
	sb t1, 27(s2)
	srli t1, t0, 24
	sb t1, 28(s2)
	srli t1, t0, 16
	sb t1, 29(s2)
	srli t1, t0, 8
	sb t1, 30(s2)
	srli t1, t0, 0
	sb t1, 31(s2)
	ld t0, 984(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 32(s2)
	srli t1, t0, 48
	sb t1, 33(s2)
	srli t1, t0, 40
	sb t1, 34(s2)
	srli t1, t0, 32
	sb t1, 35(s2)
	srli t1, t0, 24
	sb t1, 36(s2)
	srli t1, t0, 16
	sb t1, 37(s2)
	srli t1, t0, 8
	sb t1, 38(s2)
	srli t1, t0, 0
	sb t1, 39(s2)
	ld t0, 976(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 40(s2)
	srli t1, t0, 48
	sb t1, 41(s2)
	srli t1, t0, 40
	sb t1, 42(s2)
	srli t1, t0, 32
	sb t1, 43(s2)
	srli t1, t0, 24
	sb t1, 44(s2)
	srli t1, t0, 16
	sb t1, 45(s2)
	srli t1, t0, 8
	sb t1, 46(s2)
	srli t1, t0, 0
	sb t1, 47(s2)
	ld t0, 1400(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 48(s2)
	srli t1, t0, 48
	sb t1, 49(s2)
	srli t1, t0, 40
	sb t1, 50(s2)
	srli t1, t0, 32
	sb t1, 51(s2)
	srli t1, t0, 24
	sb t1, 52(s2)
	srli t1, t0, 16
	sb t1, 53(s2)
	srli t1, t0, 8
	sb t1, 54(s2)
	srli t1, t0, 0
	sb t1, 55(s2)
	ld t0, 1392(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 56(s2)
	srli t1, t0, 48
	sb t1, 57(s2)
	srli t1, t0, 40
	sb t1, 58(s2)
	srli t1, t0, 32
	sb t1, 59(s2)
	srli t1, t0, 24
	sb t1, 60(s2)
	srli t1, t0, 16
	sb t1, 61(s2)
	srli t1, t0, 8
	sb t1, 62(s2)
	srli t1, t0, 0
	sb t1, 63(s2)
	ld t0, 1384(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 64(s2)
	srli t1, t0, 48
	sb t1, 65(s2)
	srli t1, t0, 40
	sb t1, 66(s2)
	srli t1, t0, 32
	sb t1, 67(s2)
	srli t1, t0, 24
	sb t1, 68(s2)
	srli t1, t0, 16
	sb t1, 69(s2)
	srli t1, t0, 8
	sb t1, 70(s2)
	srli t1, t0, 0
	sb t1, 71(s2)
	ld t0, 1376(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 72(s2)
	srli t1, t0, 48
	sb t1, 73(s2)
	srli t1, t0, 40
	sb t1, 74(s2)
	srli t1, t0, 32
	sb t1, 75(s2)
	srli t1, t0, 24
	sb t1, 76(s2)
	srli t1, t0, 16
	sb t1, 77(s2)
	srli t1, t0, 8
	sb t1, 78(s2)
	srli t1, t0, 0
	sb t1, 79(s2)
	ld t0, 1368(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 80(s2)
	srli t1, t0, 48
	sb t1, 81(s2)
	srli t1, t0, 40
	sb t1, 82(s2)
	srli t1, t0, 32
	sb t1, 83(s2)
	srli t1, t0, 24
	sb t1, 84(s2)
	srli t1, t0, 16
	sb t1, 85(s2)
	srli t1, t0, 8
	sb t1, 86(s2)
	srli t1, t0, 0
	sb t1, 87(s2)
	ld t0, 1360(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 88(s2)
	srli t1, t0, 48
	sb t1, 89(s2)
	srli t1, t0, 40
	sb t1, 90(s2)
	srli t1, t0, 32
	sb t1, 91(s2)
	srli t1, t0, 24
	sb t1, 92(s2)
	srli t1, t0, 16
	sb t1, 93(s2)
	srli t1, t0, 8
	sb t1, 94(s2)
	srli t1, t0, 0
	sb t1, 95(s2)
	addi a0, s0, 2047
	ld a0, 129(a0)
	andi a0, a0, 1
	ld ra, 24(s0)
	ld s2, 16(s0)
	ld s1, 8(s0)
	ld s3, 32(s0)
	ld s0, 0(s0)
	ret
	.option pop
