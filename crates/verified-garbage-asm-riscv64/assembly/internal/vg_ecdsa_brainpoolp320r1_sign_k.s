// The functions of `src/internal/vg_ecdsa_brainpoolp320r1_sign_k.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_brainpoolp320r1_sign_k:
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
	sd t0, 1336(s0)
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
	sd t0, 1328(s0)
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
	sd t0, 1320(s0)
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
	sd t0, 1312(s0)
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
	sd t0, 1304(s0)
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
	sd t0, 1416(s0)
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
	sd t0, 1408(s0)
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
	sd t0, 1400(s0)
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
	sd t0, 1392(s0)
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
	sd t0, 1384(s0)
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
	sd t0, 1456(s0)
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
	sd t0, 1448(s0)
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
	sd t0, 1440(s0)
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
	sd t0, 1432(s0)
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
	sd t0, 1424(s0)
	addi t0, zero, 0
	addi t0, t0, -1
	sd t0, 1824(s0)
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
	addi t5, zero, 0
	ld t3, 1384(s0)
	ld t4, 104(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1392(s0)
	ld t4, 112(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1400(s0)
	ld t4, 120(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1408(s0)
	ld t4, 128(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1416(s0)
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
	ld t4, 1384(s0)
	or t3, t3, t4
	ld t4, 1392(s0)
	or t3, t3, t4
	ld t4, 1400(s0)
	or t3, t3, t4
	ld t4, 1408(s0)
	or t3, t3, t4
	ld t4, 1416(s0)
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
	ld t0, 384(s0)
	sd t0, 624(s0)
	ld t0, 392(s0)
	sd t0, 632(s0)
	ld t0, 400(s0)
	sd t0, 640(s0)
	ld t0, 408(s0)
	sd t0, 648(s0)
	ld t0, 416(s0)
	sd t0, 656(s0)
	ld t0, 424(s0)
	sd t0, 664(s0)
	ld t0, 432(s0)
	sd t0, 672(s0)
	ld t0, 440(s0)
	sd t0, 680(s0)
	ld t0, 448(s0)
	sd t0, 688(s0)
	ld t0, 456(s0)
	sd t0, 696(s0)
	addi t5, zero, 0
	ld t3, 1304(s0)
	ld t4, 104(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1312(s0)
	ld t4, 112(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1320(s0)
	ld t4, 120(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1328(s0)
	ld t4, 128(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1336(s0)
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
	ld t4, 1304(s0)
	or t3, t3, t4
	ld t4, 1312(s0)
	or t3, t3, t4
	ld t4, 1320(s0)
	or t3, t3, t4
	ld t4, 1328(s0)
	or t3, t3, t4
	ld t4, 1336(s0)
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
	call {vg_brainpoolp320r1_mul}
	addi s0, s3, 0
	call {vg_brainpoolp320r1_inv_mod_p}
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
	addi a2, zero, 1304
	addi a3, zero, 1464
	call {vg_brainpoolp320r1_mul_mod_n}
	call {vg_brainpoolp320r1_inv_mod_n}
	addi a0, s0, 0
	addi a1, zero, 904
	addi a2, zero, 1424
	addi a3, zero, 1464
	call {vg_brainpoolp320r1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 824
	addi a3, zero, 1464
	call {vg_brainpoolp320r1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1384
	addi a3, zero, 1464
	call {vg_brainpoolp320r1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 944
	addi a3, zero, 984
	call {vg_brainpoolp320r1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 904
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_add_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1224
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1104
	addi a3, zero, 224
	call {vg_brainpoolp320r1_mul_mod_n}
	addi t3, zero, 0
	ld t4, 824(s0)
	or t3, t3, t4
	ld t4, 832(s0)
	or t3, t3, t4
	ld t4, 840(s0)
	or t3, t3, t4
	ld t4, 848(s0)
	or t3, t3, t4
	ld t4, 856(s0)
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
	ld t4, 1144(s0)
	or t3, t3, t4
	ld t4, 1152(s0)
	or t3, t3, t4
	ld t4, 1160(s0)
	or t3, t3, t4
	ld t4, 1168(s0)
	or t3, t3, t4
	ld t4, 1176(s0)
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
	ld a7, 1824(s0)
	ld t0, 856(s0)
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
	ld t0, 848(s0)
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
	ld t0, 840(s0)
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
	ld t0, 832(s0)
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
	ld t0, 824(s0)
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
	ld t0, 1176(s0)
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
	ld t0, 1168(s0)
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
	ld t0, 1160(s0)
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
	ld t0, 1152(s0)
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
	ld t0, 1144(s0)
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
	ld a0, 1824(s0)
	andi a0, a0, 1
	ld ra, 24(s0)
	ld s2, 16(s0)
	ld s1, 8(s0)
	ld s3, 32(s0)
	ld s0, 0(s0)
	ret
	.option pop
