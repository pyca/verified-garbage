// The functions of `src/ec_brainpoolp384r1_compressed.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ec_brainpoolp384r1_compress_public_key:
	.option push
	.option arch, +m, +c
	sd s0, 0(a2)
	sd s1, 8(a2)
	sd s2, 16(a2)
	sd ra, 24(a2)
	sd s3, 32(a2)
	addi s0, a2, 0
	addi s3, a2, 0
	addi s2, a0, 0
	lbu t0, 1(a1)
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
	slli t0, t0, 8
	lbu t1, 8(a1)
	or t0, t0, t1
	sd t0, 1688(s0)
	lbu t0, 9(a1)
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
	slli t0, t0, 8
	lbu t1, 16(a1)
	or t0, t0, t1
	sd t0, 1680(s0)
	lbu t0, 17(a1)
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
	slli t0, t0, 8
	lbu t1, 24(a1)
	or t0, t0, t1
	sd t0, 1672(s0)
	lbu t0, 25(a1)
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
	slli t0, t0, 8
	lbu t1, 32(a1)
	or t0, t0, t1
	sd t0, 1664(s0)
	lbu t0, 33(a1)
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
	slli t0, t0, 8
	lbu t1, 40(a1)
	or t0, t0, t1
	sd t0, 1656(s0)
	lbu t0, 41(a1)
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
	slli t0, t0, 8
	lbu t1, 48(a1)
	or t0, t0, t1
	sd t0, 1648(s0)
	lbu t0, 49(a1)
	slli t0, t0, 8
	lbu t1, 50(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 51(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 52(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 53(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 54(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 55(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 56(a1)
	or t0, t0, t1
	sd t0, 1832(s0)
	lbu t0, 57(a1)
	slli t0, t0, 8
	lbu t1, 58(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 59(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 60(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 61(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 62(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 63(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 64(a1)
	or t0, t0, t1
	sd t0, 1824(s0)
	lbu t0, 65(a1)
	slli t0, t0, 8
	lbu t1, 66(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 67(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 68(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 69(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 70(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 71(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 72(a1)
	or t0, t0, t1
	sd t0, 1816(s0)
	lbu t0, 73(a1)
	slli t0, t0, 8
	lbu t1, 74(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 75(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 76(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 77(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 78(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 79(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 80(a1)
	or t0, t0, t1
	sd t0, 1808(s0)
	lbu t0, 81(a1)
	slli t0, t0, 8
	lbu t1, 82(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 83(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 84(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 85(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 86(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 87(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 88(a1)
	or t0, t0, t1
	sd t0, 1800(s0)
	lbu t0, 89(a1)
	slli t0, t0, 8
	lbu t1, 90(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 91(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 92(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 93(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 94(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 95(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 96(a1)
	or t0, t0, t1
	sd t0, 1792(s0)
	lbu t0, 0(a1)
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
	addi a0, s0, 0
	call {vg_brainpoolp384r1_check_point}
	addi s0, s3, 0
	addi a7, s0, 2047
	ld a7, 129(a7)
	ld t0, 1792(s0)
	andi t0, t0, 1
	addi t0, t0, 2
	and t0, t0, a7
	sb t0, 0(s2)
	ld t0, 1688(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 1(s2)
	srli t1, t0, 48
	sb t1, 2(s2)
	srli t1, t0, 40
	sb t1, 3(s2)
	srli t1, t0, 32
	sb t1, 4(s2)
	srli t1, t0, 24
	sb t1, 5(s2)
	srli t1, t0, 16
	sb t1, 6(s2)
	srli t1, t0, 8
	sb t1, 7(s2)
	srli t1, t0, 0
	sb t1, 8(s2)
	ld t0, 1680(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 9(s2)
	srli t1, t0, 48
	sb t1, 10(s2)
	srli t1, t0, 40
	sb t1, 11(s2)
	srli t1, t0, 32
	sb t1, 12(s2)
	srli t1, t0, 24
	sb t1, 13(s2)
	srli t1, t0, 16
	sb t1, 14(s2)
	srli t1, t0, 8
	sb t1, 15(s2)
	srli t1, t0, 0
	sb t1, 16(s2)
	ld t0, 1672(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 17(s2)
	srli t1, t0, 48
	sb t1, 18(s2)
	srli t1, t0, 40
	sb t1, 19(s2)
	srli t1, t0, 32
	sb t1, 20(s2)
	srli t1, t0, 24
	sb t1, 21(s2)
	srli t1, t0, 16
	sb t1, 22(s2)
	srli t1, t0, 8
	sb t1, 23(s2)
	srli t1, t0, 0
	sb t1, 24(s2)
	ld t0, 1664(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 25(s2)
	srli t1, t0, 48
	sb t1, 26(s2)
	srli t1, t0, 40
	sb t1, 27(s2)
	srli t1, t0, 32
	sb t1, 28(s2)
	srli t1, t0, 24
	sb t1, 29(s2)
	srli t1, t0, 16
	sb t1, 30(s2)
	srli t1, t0, 8
	sb t1, 31(s2)
	srli t1, t0, 0
	sb t1, 32(s2)
	ld t0, 1656(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 33(s2)
	srli t1, t0, 48
	sb t1, 34(s2)
	srli t1, t0, 40
	sb t1, 35(s2)
	srli t1, t0, 32
	sb t1, 36(s2)
	srli t1, t0, 24
	sb t1, 37(s2)
	srli t1, t0, 16
	sb t1, 38(s2)
	srli t1, t0, 8
	sb t1, 39(s2)
	srli t1, t0, 0
	sb t1, 40(s2)
	ld t0, 1648(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 41(s2)
	srli t1, t0, 48
	sb t1, 42(s2)
	srli t1, t0, 40
	sb t1, 43(s2)
	srli t1, t0, 32
	sb t1, 44(s2)
	srli t1, t0, 24
	sb t1, 45(s2)
	srli t1, t0, 16
	sb t1, 46(s2)
	srli t1, t0, 8
	sb t1, 47(s2)
	srli t1, t0, 0
	sb t1, 48(s2)
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

vg_ec_brainpoolp384r1_decompress_public_key:
	.option push
	.option arch, +m, +c
	sd s0, 0(a2)
	sd s1, 8(a2)
	sd s2, 16(a2)
	sd ra, 24(a2)
	sd s3, 32(a2)
	addi s0, a2, 0
	addi s3, a2, 0
	addi s2, a0, 0
	lbu t0, 1(a1)
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
	slli t0, t0, 8
	lbu t1, 8(a1)
	or t0, t0, t1
	sd t0, 1688(s0)
	lbu t0, 9(a1)
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
	slli t0, t0, 8
	lbu t1, 16(a1)
	or t0, t0, t1
	sd t0, 1680(s0)
	lbu t0, 17(a1)
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
	slli t0, t0, 8
	lbu t1, 24(a1)
	or t0, t0, t1
	sd t0, 1672(s0)
	lbu t0, 25(a1)
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
	slli t0, t0, 8
	lbu t1, 32(a1)
	or t0, t0, t1
	sd t0, 1664(s0)
	lbu t0, 33(a1)
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
	slli t0, t0, 8
	lbu t1, 40(a1)
	or t0, t0, t1
	sd t0, 1656(s0)
	lbu t0, 41(a1)
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
	slli t0, t0, 8
	lbu t1, 48(a1)
	or t0, t0, t1
	sd t0, 1648(s0)
	lbu t0, 0(a1)
	andi t0, t0, 1
	sd t0, 544(s0)
	lbu t0, 0(a1)
	xori t0, t0, 2
	srli t0, t0, 1
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
	lui t0, 400668
	addiw t0, t0, 5
	slli t0, t0, 32
	lui t1, 836640
	addiw t1, t1, -1259
	add t0, t0, t1
	sd t0, 592(s0)
	lui t0, 963407
	addiw t0, t0, -1590
	slli t0, t0, 32
	lui t1, 409716
	addiw t1, t1, 1692
	add t0, t0, t1
	sd t0, 600(s0)
	lui t0, 19143
	addiw t0, t0, 1670
	slli t0, t0, 32
	lui t1, 392924
	addiw t1, t1, 1096
	add t0, t0, t1
	sd t0, 608(s0)
	lui t0, 808126
	addiw t0, t0, -958
	slli t0, t0, 32
	lui t1, 505169
	addiw t1, t1, 1453
	add t0, t0, t1
	sd t0, 616(s0)
	lui t0, 15734
	addiw t0, t0, -1056
	slli t0, t0, 32
	lui t1, 607129
	addiw t1, t1, 119
	add t0, t0, t1
	sd t0, 624(s0)
	lui t0, 144100
	addiw t0, t0, 1953
	slli t0, t0, 32
	lui t1, 691426
	addiw t1, t1, -1206
	add t0, t0, t1
	sd t0, 632(s0)
	addi t5, zero, 0
	ld t3, 1648(s0)
	ld t4, 64(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1656(s0)
	ld t4, 72(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1664(s0)
	ld t4, 80(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1672(s0)
	ld t4, 88(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1680(s0)
	ld t4, 96(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1688(s0)
	ld t4, 104(s0)
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
	addi a0, s0, 0
	addi a1, zero, 1696
	addi a2, zero, 1648
	addi a3, zero, 1936
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1696
	addi a3, zero, 1696
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1168
	addi a3, zero, 1696
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 352
	addi a3, zero, 1696
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1168
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1168
	addi a3, zero, 1984
	call {vg_brainpoolp384r1_add_mod_p}
	ld t0, 304(s0)
	sd t0, 1456(s0)
	ld t0, 312(s0)
	sd t0, 1464(s0)
	ld t0, 320(s0)
	sd t0, 1472(s0)
	ld t0, 328(s0)
	sd t0, 1480(s0)
	ld t0, 336(s0)
	sd t0, 1488(s0)
	ld t0, 344(s0)
	sd t0, 1496(s0)
	addi s1, zero, 384
20:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1504
	addi a2, zero, 1168
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	srli t0, s1, 6
	slli t0, t0, 3
	add t0, t0, s0
	ld t1, 592(t0)
	srl t1, t1, s1
	andi t1, t1, 1
	addi t2, zero, 0
	sub a7, t2, t1
	ld t0, 1456(s0)
	ld t1, 1504(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1456(s0)
	ld t0, 1464(s0)
	ld t1, 1512(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1464(s0)
	ld t0, 1472(s0)
	ld t1, 1520(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1472(s0)
	ld t0, 1480(s0)
	ld t1, 1528(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1480(s0)
	ld t0, 1488(s0)
	ld t1, 1536(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1488(s0)
	ld t0, 1496(s0)
	ld t1, 1544(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1496(s0)
	bnez s1, 20b
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1264
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 976
	addi a2, zero, 1456
	addi a3, zero, 256
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 208
	addi a3, zero, 976
	call {vg_brainpoolp384r1_sub_mod_p}
	addi t3, zero, 0
	ld t4, 1312(s0)
	or t3, t3, t4
	ld t4, 1320(s0)
	or t3, t3, t4
	ld t4, 1328(s0)
	or t3, t3, t4
	ld t4, 1336(s0)
	or t3, t3, t4
	ld t4, 1344(s0)
	or t3, t3, t4
	ld t4, 1352(s0)
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
	ld t0, 976(s0)
	ld t1, 544(s0)
	xor t0, t0, t1
	andi t0, t0, 1
	addi t1, zero, 0
	sub a7, t1, t0
	ld t0, 976(s0)
	ld t1, 1024(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1072(s0)
	ld t0, 984(s0)
	ld t1, 1032(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1080(s0)
	ld t0, 992(s0)
	ld t1, 1040(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1088(s0)
	ld t0, 1000(s0)
	ld t1, 1048(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1096(s0)
	ld t0, 1008(s0)
	ld t1, 1056(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1104(s0)
	ld t0, 1016(s0)
	ld t1, 1064(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1112(s0)
	ld t0, 1072(s0)
	ld t1, 544(s0)
	xor t0, t0, t1
	andi t0, t0, 1
	addi a7, t0, -1
	addi t0, s0, 2047
	ld t0, 129(t0)
	and t0, t0, a7
	addi s0, s0, 2047
	sd t0, 129(s0)
	addi s0, s0, -2047
	addi a7, s0, 2047
	ld a7, 129(a7)
	addi t0, zero, 4
	and t0, t0, a7
	sb t0, 0(s2)
	ld t0, 1688(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 1(s2)
	srli t1, t0, 48
	sb t1, 2(s2)
	srli t1, t0, 40
	sb t1, 3(s2)
	srli t1, t0, 32
	sb t1, 4(s2)
	srli t1, t0, 24
	sb t1, 5(s2)
	srli t1, t0, 16
	sb t1, 6(s2)
	srli t1, t0, 8
	sb t1, 7(s2)
	srli t1, t0, 0
	sb t1, 8(s2)
	ld t0, 1680(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 9(s2)
	srli t1, t0, 48
	sb t1, 10(s2)
	srli t1, t0, 40
	sb t1, 11(s2)
	srli t1, t0, 32
	sb t1, 12(s2)
	srli t1, t0, 24
	sb t1, 13(s2)
	srli t1, t0, 16
	sb t1, 14(s2)
	srli t1, t0, 8
	sb t1, 15(s2)
	srli t1, t0, 0
	sb t1, 16(s2)
	ld t0, 1672(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 17(s2)
	srli t1, t0, 48
	sb t1, 18(s2)
	srli t1, t0, 40
	sb t1, 19(s2)
	srli t1, t0, 32
	sb t1, 20(s2)
	srli t1, t0, 24
	sb t1, 21(s2)
	srli t1, t0, 16
	sb t1, 22(s2)
	srli t1, t0, 8
	sb t1, 23(s2)
	srli t1, t0, 0
	sb t1, 24(s2)
	ld t0, 1664(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 25(s2)
	srli t1, t0, 48
	sb t1, 26(s2)
	srli t1, t0, 40
	sb t1, 27(s2)
	srli t1, t0, 32
	sb t1, 28(s2)
	srli t1, t0, 24
	sb t1, 29(s2)
	srli t1, t0, 16
	sb t1, 30(s2)
	srli t1, t0, 8
	sb t1, 31(s2)
	srli t1, t0, 0
	sb t1, 32(s2)
	ld t0, 1656(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 33(s2)
	srli t1, t0, 48
	sb t1, 34(s2)
	srli t1, t0, 40
	sb t1, 35(s2)
	srli t1, t0, 32
	sb t1, 36(s2)
	srli t1, t0, 24
	sb t1, 37(s2)
	srli t1, t0, 16
	sb t1, 38(s2)
	srli t1, t0, 8
	sb t1, 39(s2)
	srli t1, t0, 0
	sb t1, 40(s2)
	ld t0, 1648(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 41(s2)
	srli t1, t0, 48
	sb t1, 42(s2)
	srli t1, t0, 40
	sb t1, 43(s2)
	srli t1, t0, 32
	sb t1, 44(s2)
	srli t1, t0, 24
	sb t1, 45(s2)
	srli t1, t0, 16
	sb t1, 46(s2)
	srli t1, t0, 8
	sb t1, 47(s2)
	srli t1, t0, 0
	sb t1, 48(s2)
	ld t0, 1112(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 49(s2)
	srli t1, t0, 48
	sb t1, 50(s2)
	srli t1, t0, 40
	sb t1, 51(s2)
	srli t1, t0, 32
	sb t1, 52(s2)
	srli t1, t0, 24
	sb t1, 53(s2)
	srli t1, t0, 16
	sb t1, 54(s2)
	srli t1, t0, 8
	sb t1, 55(s2)
	srli t1, t0, 0
	sb t1, 56(s2)
	ld t0, 1104(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 57(s2)
	srli t1, t0, 48
	sb t1, 58(s2)
	srli t1, t0, 40
	sb t1, 59(s2)
	srli t1, t0, 32
	sb t1, 60(s2)
	srli t1, t0, 24
	sb t1, 61(s2)
	srli t1, t0, 16
	sb t1, 62(s2)
	srli t1, t0, 8
	sb t1, 63(s2)
	srli t1, t0, 0
	sb t1, 64(s2)
	ld t0, 1096(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 65(s2)
	srli t1, t0, 48
	sb t1, 66(s2)
	srli t1, t0, 40
	sb t1, 67(s2)
	srli t1, t0, 32
	sb t1, 68(s2)
	srli t1, t0, 24
	sb t1, 69(s2)
	srli t1, t0, 16
	sb t1, 70(s2)
	srli t1, t0, 8
	sb t1, 71(s2)
	srli t1, t0, 0
	sb t1, 72(s2)
	ld t0, 1088(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 73(s2)
	srli t1, t0, 48
	sb t1, 74(s2)
	srli t1, t0, 40
	sb t1, 75(s2)
	srli t1, t0, 32
	sb t1, 76(s2)
	srli t1, t0, 24
	sb t1, 77(s2)
	srli t1, t0, 16
	sb t1, 78(s2)
	srli t1, t0, 8
	sb t1, 79(s2)
	srli t1, t0, 0
	sb t1, 80(s2)
	ld t0, 1080(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 81(s2)
	srli t1, t0, 48
	sb t1, 82(s2)
	srli t1, t0, 40
	sb t1, 83(s2)
	srli t1, t0, 32
	sb t1, 84(s2)
	srli t1, t0, 24
	sb t1, 85(s2)
	srli t1, t0, 16
	sb t1, 86(s2)
	srli t1, t0, 8
	sb t1, 87(s2)
	srli t1, t0, 0
	sb t1, 88(s2)
	ld t0, 1072(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 89(s2)
	srli t1, t0, 48
	sb t1, 90(s2)
	srli t1, t0, 40
	sb t1, 91(s2)
	srli t1, t0, 32
	sb t1, 92(s2)
	srli t1, t0, 24
	sb t1, 93(s2)
	srli t1, t0, 16
	sb t1, 94(s2)
	srli t1, t0, 8
	sb t1, 95(s2)
	srli t1, t0, 0
	sb t1, 96(s2)
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
