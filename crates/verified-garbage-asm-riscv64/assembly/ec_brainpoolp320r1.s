// The functions of `src/ec_brainpoolp320r1.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ec_brainpoolp320r1_public_key:
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
	sd t0, 1336(s0)
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
	sd t0, 1328(s0)
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
	sd t0, 1320(s0)
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
	sd t0, 1312(s0)
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
	sd t0, 1304(s0)
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
20:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 20b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 97
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 5
21:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 21b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 3
22:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 22b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1904
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 6
23:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 23b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2024
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 3
24:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 24b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1904
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 11
25:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 25b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 97
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 3
26:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 26b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1984
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 5
27:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 27b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 7
28:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 28b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 17
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 4
29:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 29b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 5
210:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 210b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 97
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 4
211:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 211b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 1
212:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 212b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1904
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 8
213:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 213b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 17
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 3
214:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 214b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2024
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 7
215:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 215b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 8
216:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 216b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 57
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 4
217:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 217b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 97
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 3
218:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 218b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1984
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 3
219:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 219b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1904
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 12
220:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 220b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 8
221:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 221b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 6
222:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 222b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 57
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 4
223:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 223b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 4
224:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 224b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 7
225:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 225b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 2
226:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 226b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 6
227:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 227b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 3
228:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 228b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1984
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 6
229:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 229b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 97
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 3
230:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 230b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2024
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 5
231:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 231b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 97
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 3
232:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 232b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2024
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 2
233:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 233b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1904
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 10
234:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 234b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 97
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 3
235:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 235b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2024
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 5
236:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 236b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 5
237:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 237b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 17
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 4
238:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 238b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 6
239:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 239b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 17
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 5
240:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 240b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 57
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 4
241:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 241b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 17
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 3
242:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 242b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2024
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 3
243:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 243b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 7
244:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 244b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 7
245:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 245b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 17
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 6
246:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 246b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 4
247:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 247b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 57
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 7
248:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 248b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1984
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 7
249:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 249b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 2
250:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 250b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 6
251:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 251b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 97
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 2
252:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 252b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1904
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 9
253:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 253b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 17
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 5
254:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 254b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 57
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 7
255:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 255b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 1
256:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 256b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1904
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 7
257:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 257b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 97
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 4
258:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 258b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 17
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 4
259:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 259b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 17
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 4
260:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 260b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2024
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 7
261:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 261b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 17
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 2
262:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 262b
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
	addi a2, zero, 664
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 824
	addi a3, zero, 224
	call {vg_brainpoolp320r1_mul_mod_p}
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
	ld a7, 1824(s0)
	addi t0, zero, 4
	and t0, t0, a7
	sb t0, 0(s2)
	ld t0, 816(s0)
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
	ld t0, 808(s0)
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
	ld t0, 800(s0)
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
	ld t0, 792(s0)
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
	ld t0, 784(s0)
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
	ld t0, 896(s0)
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
	ld t0, 888(s0)
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
	ld t0, 880(s0)
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
	ld t0, 872(s0)
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
	ld t0, 864(s0)
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
	ld a0, 1824(s0)
	andi a0, a0, 1
	ld ra, 24(s0)
	ld s2, 16(s0)
	ld s1, 8(s0)
	ld s3, 32(s0)
	ld s0, 0(s0)
	addi t0, zero, 0
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
