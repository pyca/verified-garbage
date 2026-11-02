// The functions of `src/ec_brainpoolp256r1_compressed.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ec_brainpoolp256r1_compress_public_key:
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
	sd t0, 1144(s0)
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
	sd t0, 1136(s0)
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
	sd t0, 1128(s0)
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
	sd t0, 1120(s0)
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
	sd t0, 1240(s0)
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
	sd t0, 1232(s0)
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
	sd t0, 1224(s0)
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
	sd t0, 1216(s0)
	lbu t0, 0(a1)
	xori t0, t0, 4
	addi t0, t0, -1
	srli t0, t0, 63
	addi t1, zero, 0
	sub a7, t1, t0
	sd a7, 1472(s0)
	lui t0, 131381
	addiw t0, t0, -2019
	slli t0, t0, 32
	lui t1, 128741
	addiw t1, t1, 887
	add t0, t0, t1
	sd t0, 64(s0)
	lui t0, 451519
	addiw t0, t0, 1572
	slli t0, t0, 32
	lui t1, 873058
	addiw t1, t1, 40
	add t0, t0, t1
	sd t0, 72(s0)
	lui t0, 255585
	addiw t0, t0, -1391
	slli t0, t0, 32
	lui t1, 645177
	addiw t1, t1, -654
	add t0, t0, t1
	sd t0, 80(s0)
	lui t0, 696245
	addiw t0, t0, 2012
	slli t0, t0, 32
	lui t1, 663275
	addiw t1, t1, -1604
	add t0, t0, t1
	sd t0, 88(s0)
	lui t0, 590305
	addiw t0, t0, -381
	slli t0, t0, 32
	lui t1, 619653
	addiw t1, t1, 1703
	add t0, t0, t1
	sd t0, 96(s0)
	lui t0, 574360
	addiw t0, t0, -1372
	slli t0, t0, 32
	lui t1, 742938
	addiw t1, t1, 1783
	add t0, t0, t1
	sd t0, 104(s0)
	lui t0, 255585
	addiw t0, t0, -1391
	slli t0, t0, 32
	lui t1, 645177
	addiw t1, t1, -655
	add t0, t0, t1
	sd t0, 112(s0)
	lui t0, 696245
	addiw t0, t0, 2012
	slli t0, t0, 32
	lui t1, 663275
	addiw t1, t1, -1604
	add t0, t0, t1
	sd t0, 120(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 160(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 168(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 176(s0)
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
	addiw t1, t1, 1
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
	lui t0, 917195
	addiw t0, t0, 2019
	slli t0, t0, 32
	lui t1, 919835
	addiw t1, t1, -887
	add t0, t0, t1
	sd t0, 224(s0)
	lui t0, 597057
	addiw t0, t0, -1572
	slli t0, t0, 32
	lui t1, 175518
	addiw t1, t1, -41
	add t0, t0, t1
	sd t0, 232(s0)
	lui t0, 792991
	addiw t0, t0, 1391
	slli t0, t0, 32
	lui t1, 403399
	addiw t1, t1, 653
	add t0, t0, t1
	sd t0, 240(s0)
	lui t0, 352331
	addiw t0, t0, -2012
	slli t0, t0, 32
	lui t1, 385301
	addiw t1, t1, 1603
	add t0, t0, t1
	sd t0, 248(s0)
	lui t0, 875801
	addiw t0, t0, -289
	slli t0, t0, 32
	lui t1, 431766
	addiw t1, t1, 609
	add t0, t0, t1
	sd t0, 256(s0)
	lui t0, 682002
	addiw t0, t0, 1010
	slli t0, t0, 32
	lui t1, 793889
	addiw t1, t1, -924
	add t0, t0, t1
	sd t0, 264(s0)
	lui t0, 614082
	addiw t0, t0, -418
	slli t0, t0, 32
	lui t1, 407941
	addiw t1, t1, 1390
	add t0, t0, t1
	sd t0, 272(s0)
	lui t0, 124007
	addiw t0, t0, 1708
	slli t0, t0, 32
	lui t1, 878188
	addiw t1, t1, -1001
	add t0, t0, t1
	sd t0, 280(s0)
	lui t0, 71535
	addiw t0, t0, -1960
	slli t0, t0, 32
	lui t1, 271406
	addiw t1, t1, -1459
	add t0, t0, t1
	sd t0, 288(s0)
	lui t0, 132254
	addiw t0, t0, -291
	slli t0, t0, 32
	lui t1, 413524
	addiw t1, t1, -501
	add t0, t0, t1
	sd t0, 296(s0)
	lui t0, 189949
	addiw t0, t0, -1606
	slli t0, t0, 32
	lui t1, 32140
	addiw t1, t1, -629
	add t0, t0, t1
	sd t0, 304(s0)
	lui t0, 272878
	addiw t0, t0, 99
	slli t0, t0, 32
	lui t1, 868022
	addiw t1, t1, -1093
	add t0, t0, t1
	sd t0, 312(s0)
	lui t0, 162830
	addiw t0, t0, -1747
	slli t0, t0, 32
	lui t1, 217597
	addiw t1, t1, 268
	add t0, t0, t1
	sd t0, 320(s0)
	lui t0, 527845
	addiw t0, t0, -613
	slli t0, t0, 32
	lui t1, 759759
	addiw t1, t1, 778
	add t0, t0, t1
	sd t0, 328(s0)
	lui t0, 459971
	addiw t0, t0, 285
	slli t0, t0, 32
	lui t1, 440467
	addiw t1, t1, -1325
	add t0, t0, t1
	sd t0, 336(s0)
	lui t0, 582135
	addiw t0, t0, 1659
	slli t0, t0, 32
	lui t1, 647450
	addiw t1, t1, -1057
	add t0, t0, t1
	sd t0, 344(s0)
	lui t0, 632063
	addiw t0, t0, -1719
	slli t0, t0, 32
	lui t1, 657688
	addiw t1, t1, -1513
	add t0, t0, t1
	sd t0, 352(s0)
	lui t0, 680335
	addiw t0, t0, 602
	slli t0, t0, 32
	lui t1, 842064
	addiw t1, t1, 354
	add t0, t0, t1
	sd t0, 360(s0)
	lui t0, 94175
	addiw t0, t0, 1769
	slli t0, t0, 32
	lui t1, 916441
	addiw t1, t1, -1277
	add t0, t0, t1
	sd t0, 368(s0)
	lui t0, 85688
	addiw t0, t0, -1850
	slli t0, t0, 32
	lui t1, 9963
	addiw t1, t1, 162
	add t0, t0, t1
	sd t0, 376(s0)
	lui t0, 131381
	addiw t0, t0, -2019
	slli t0, t0, 32
	lui t1, 128741
	addiw t1, t1, 885
	add t0, t0, t1
	sd t0, 448(s0)
	lui t0, 451519
	addiw t0, t0, 1572
	slli t0, t0, 32
	lui t1, 873058
	addiw t1, t1, 40
	add t0, t0, t1
	sd t0, 456(s0)
	lui t0, 255585
	addiw t0, t0, -1391
	slli t0, t0, 32
	lui t1, 645177
	addiw t1, t1, -654
	add t0, t0, t1
	sd t0, 464(s0)
	lui t0, 696245
	addiw t0, t0, 2012
	slli t0, t0, 32
	lui t1, 663275
	addiw t1, t1, -1604
	add t0, t0, t1
	sd t0, 472(s0)
	lui t0, 577518
	addiw t0, t0, -132
	slli t0, t0, 32
	lui t1, 681062
	addiw t1, t1, -1172
	add t0, t0, t1
	sd t0, 1312(s0)
	lui t0, 380133
	addiw t0, t0, -986
	slli t0, t0, 32
	lui t1, 398549
	addiw t1, t1, -179
	add t0, t0, t1
	sd t0, 1320(s0)
	lui t0, 663246
	addiw t0, t0, -1331
	slli t0, t0, 32
	lui t1, 438701
	addiw t1, t1, -2041
	add t0, t0, t1
	sd t0, 1328(s0)
	lui t0, 291195
	addiw t0, t0, -1502
	slli t0, t0, 32
	lui t1, 940376
	addiw t1, t1, -88
	add t0, t0, t1
	sd t0, 1336(s0)
	lui t0, 23845
	addiw t0, t0, -653
	slli t0, t0, 32
	lui t1, 789519
	addiw t1, t1, 879
	add t0, t0, t1
	sd t0, 1344(s0)
	lui t0, 44085
	addiw t0, t0, -1462
	slli t0, t0, 32
	lui t1, 836892
	addiw t1, t1, -167
	add t0, t0, t1
	sd t0, 1352(s0)
	lui t0, 412842
	addiw t0, t0, -1901
	slli t0, t0, 32
	lui t1, 360239
	addiw t1, t1, -1575
	add t0, t0, t1
	sd t0, 1360(s0)
	lui t0, 90959
	addiw t0, t0, 1398
	slli t0, t0, 32
	lui t1, 289341
	addiw t1, t1, -1730
	add t0, t0, t1
	sd t0, 1368(s0)
	addi a0, s0, 0
	call {vg_brainpoolp256r1_check_point}
	addi s0, s3, 0
	ld a7, 1472(s0)
	ld t0, 1216(s0)
	andi t0, t0, 1
	addi t0, t0, 2
	and t0, t0, a7
	sb t0, 0(s2)
	ld t0, 1144(s0)
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
	ld t0, 1136(s0)
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
	ld t0, 1128(s0)
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
	ld t0, 1120(s0)
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
	ld a0, 1472(s0)
	andi a0, a0, 1
	ld ra, 24(s0)
	ld s2, 16(s0)
	ld s1, 8(s0)
	ld s3, 32(s0)
	ld s0, 0(s0)
	ret
	.option pop

vg_ec_brainpoolp256r1_decompress_public_key:
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
	sd t0, 1144(s0)
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
	sd t0, 1136(s0)
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
	sd t0, 1128(s0)
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
	sd t0, 1120(s0)
	lbu t0, 0(a1)
	andi t0, t0, 1
	sd t0, 384(s0)
	lbu t0, 0(a1)
	xori t0, t0, 2
	srli t0, t0, 1
	addi t0, t0, -1
	srli t0, t0, 63
	addi t1, zero, 0
	sub a7, t1, t0
	sd a7, 1472(s0)
	lui t0, 131381
	addiw t0, t0, -2019
	slli t0, t0, 32
	lui t1, 128741
	addiw t1, t1, 887
	add t0, t0, t1
	sd t0, 64(s0)
	lui t0, 451519
	addiw t0, t0, 1572
	slli t0, t0, 32
	lui t1, 873058
	addiw t1, t1, 40
	add t0, t0, t1
	sd t0, 72(s0)
	lui t0, 255585
	addiw t0, t0, -1391
	slli t0, t0, 32
	lui t1, 645177
	addiw t1, t1, -654
	add t0, t0, t1
	sd t0, 80(s0)
	lui t0, 696245
	addiw t0, t0, 2012
	slli t0, t0, 32
	lui t1, 663275
	addiw t1, t1, -1604
	add t0, t0, t1
	sd t0, 88(s0)
	lui t0, 590305
	addiw t0, t0, -381
	slli t0, t0, 32
	lui t1, 619653
	addiw t1, t1, 1703
	add t0, t0, t1
	sd t0, 96(s0)
	lui t0, 574360
	addiw t0, t0, -1372
	slli t0, t0, 32
	lui t1, 742938
	addiw t1, t1, 1783
	add t0, t0, t1
	sd t0, 104(s0)
	lui t0, 255585
	addiw t0, t0, -1391
	slli t0, t0, 32
	lui t1, 645177
	addiw t1, t1, -655
	add t0, t0, t1
	sd t0, 112(s0)
	lui t0, 696245
	addiw t0, t0, 2012
	slli t0, t0, 32
	lui t1, 663275
	addiw t1, t1, -1604
	add t0, t0, t1
	sd t0, 120(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 160(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 168(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 176(s0)
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
	addiw t1, t1, 1
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
	lui t0, 917195
	addiw t0, t0, 2019
	slli t0, t0, 32
	lui t1, 919835
	addiw t1, t1, -887
	add t0, t0, t1
	sd t0, 224(s0)
	lui t0, 597057
	addiw t0, t0, -1572
	slli t0, t0, 32
	lui t1, 175518
	addiw t1, t1, -41
	add t0, t0, t1
	sd t0, 232(s0)
	lui t0, 792991
	addiw t0, t0, 1391
	slli t0, t0, 32
	lui t1, 403399
	addiw t1, t1, 653
	add t0, t0, t1
	sd t0, 240(s0)
	lui t0, 352331
	addiw t0, t0, -2012
	slli t0, t0, 32
	lui t1, 385301
	addiw t1, t1, 1603
	add t0, t0, t1
	sd t0, 248(s0)
	lui t0, 875801
	addiw t0, t0, -289
	slli t0, t0, 32
	lui t1, 431766
	addiw t1, t1, 609
	add t0, t0, t1
	sd t0, 256(s0)
	lui t0, 682002
	addiw t0, t0, 1010
	slli t0, t0, 32
	lui t1, 793889
	addiw t1, t1, -924
	add t0, t0, t1
	sd t0, 264(s0)
	lui t0, 614082
	addiw t0, t0, -418
	slli t0, t0, 32
	lui t1, 407941
	addiw t1, t1, 1390
	add t0, t0, t1
	sd t0, 272(s0)
	lui t0, 124007
	addiw t0, t0, 1708
	slli t0, t0, 32
	lui t1, 878188
	addiw t1, t1, -1001
	add t0, t0, t1
	sd t0, 280(s0)
	lui t0, 71535
	addiw t0, t0, -1960
	slli t0, t0, 32
	lui t1, 271406
	addiw t1, t1, -1459
	add t0, t0, t1
	sd t0, 288(s0)
	lui t0, 132254
	addiw t0, t0, -291
	slli t0, t0, 32
	lui t1, 413524
	addiw t1, t1, -501
	add t0, t0, t1
	sd t0, 296(s0)
	lui t0, 189949
	addiw t0, t0, -1606
	slli t0, t0, 32
	lui t1, 32140
	addiw t1, t1, -629
	add t0, t0, t1
	sd t0, 304(s0)
	lui t0, 272878
	addiw t0, t0, 99
	slli t0, t0, 32
	lui t1, 868022
	addiw t1, t1, -1093
	add t0, t0, t1
	sd t0, 312(s0)
	lui t0, 162830
	addiw t0, t0, -1747
	slli t0, t0, 32
	lui t1, 217597
	addiw t1, t1, 268
	add t0, t0, t1
	sd t0, 320(s0)
	lui t0, 527845
	addiw t0, t0, -613
	slli t0, t0, 32
	lui t1, 759759
	addiw t1, t1, 778
	add t0, t0, t1
	sd t0, 328(s0)
	lui t0, 459971
	addiw t0, t0, 285
	slli t0, t0, 32
	lui t1, 440467
	addiw t1, t1, -1325
	add t0, t0, t1
	sd t0, 336(s0)
	lui t0, 582135
	addiw t0, t0, 1659
	slli t0, t0, 32
	lui t1, 647450
	addiw t1, t1, -1057
	add t0, t0, t1
	sd t0, 344(s0)
	lui t0, 632063
	addiw t0, t0, -1719
	slli t0, t0, 32
	lui t1, 657688
	addiw t1, t1, -1513
	add t0, t0, t1
	sd t0, 352(s0)
	lui t0, 680335
	addiw t0, t0, 602
	slli t0, t0, 32
	lui t1, 842064
	addiw t1, t1, 354
	add t0, t0, t1
	sd t0, 360(s0)
	lui t0, 94175
	addiw t0, t0, 1769
	slli t0, t0, 32
	lui t1, 916441
	addiw t1, t1, -1277
	add t0, t0, t1
	sd t0, 368(s0)
	lui t0, 85688
	addiw t0, t0, -1850
	slli t0, t0, 32
	lui t1, 9963
	addiw t1, t1, 162
	add t0, t0, t1
	sd t0, 376(s0)
	lui t0, 131381
	addiw t0, t0, -2019
	slli t0, t0, 32
	lui t1, 128741
	addiw t1, t1, 885
	add t0, t0, t1
	sd t0, 448(s0)
	lui t0, 451519
	addiw t0, t0, 1572
	slli t0, t0, 32
	lui t1, 873058
	addiw t1, t1, 40
	add t0, t0, t1
	sd t0, 456(s0)
	lui t0, 255585
	addiw t0, t0, -1391
	slli t0, t0, 32
	lui t1, 645177
	addiw t1, t1, -654
	add t0, t0, t1
	sd t0, 464(s0)
	lui t0, 696245
	addiw t0, t0, 2012
	slli t0, t0, 32
	lui t1, 663275
	addiw t1, t1, -1604
	add t0, t0, t1
	sd t0, 472(s0)
	lui t0, 577518
	addiw t0, t0, -132
	slli t0, t0, 32
	lui t1, 681062
	addiw t1, t1, -1172
	add t0, t0, t1
	sd t0, 1312(s0)
	lui t0, 380133
	addiw t0, t0, -986
	slli t0, t0, 32
	lui t1, 398549
	addiw t1, t1, -179
	add t0, t0, t1
	sd t0, 1320(s0)
	lui t0, 663246
	addiw t0, t0, -1331
	slli t0, t0, 32
	lui t1, 438701
	addiw t1, t1, -2041
	add t0, t0, t1
	sd t0, 1328(s0)
	lui t0, 291195
	addiw t0, t0, -1502
	slli t0, t0, 32
	lui t1, 940376
	addiw t1, t1, -88
	add t0, t0, t1
	sd t0, 1336(s0)
	lui t0, 23845
	addiw t0, t0, -653
	slli t0, t0, 32
	lui t1, 789519
	addiw t1, t1, 879
	add t0, t0, t1
	sd t0, 1344(s0)
	lui t0, 44085
	addiw t0, t0, -1462
	slli t0, t0, 32
	lui t1, 836892
	addiw t1, t1, -167
	add t0, t0, t1
	sd t0, 1352(s0)
	lui t0, 412842
	addiw t0, t0, -1901
	slli t0, t0, 32
	lui t1, 360239
	addiw t1, t1, -1575
	add t0, t0, t1
	sd t0, 1360(s0)
	lui t0, 90959
	addiw t0, t0, 1398
	slli t0, t0, 32
	lui t1, 289341
	addiw t1, t1, -1730
	add t0, t0, t1
	sd t0, 1368(s0)
	lui t0, 32845
	addiw t0, t0, 519
	slli t0, t0, 32
	lui t1, 294329
	addiw t1, t1, 1246
	add t0, t0, t1
	sd t0, 416(s0)
	lui t0, 637168
	addiw t0, t0, -631
	slli t0, t0, 32
	lui t1, 1004697
	addiw t1, t1, -2038
	add t0, t0, t1
	sd t0, 424(s0)
	lui t0, 63896
	addiw t0, t0, 676
	slli t0, t0, 32
	lui t1, 161294
	addiw t1, t1, 860
	add t0, t0, t1
	sd t0, 432(s0)
	lui t0, 174061
	addiw t0, t0, 1527
	slli t0, t0, 32
	lui t1, 952251
	addiw t1, t1, -1425
	add t0, t0, t1
	sd t0, 440(s0)
	addi t5, zero, 0
	ld t3, 1120(s0)
	ld t4, 64(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1128(s0)
	ld t4, 72(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1136(s0)
	ld t4, 80(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1144(s0)
	ld t4, 88(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t6, zero, 0
	sub a7, t6, t5
	ld t0, 1472(s0)
	and t0, t0, a7
	sd t0, 1472(s0)
	addi a0, s0, 0
	addi a1, zero, 1152
	addi a2, zero, 1120
	addi a3, zero, 1312
	call {vg_brainpoolp256r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 800
	addi a2, zero, 1152
	addi a3, zero, 1152
	call {vg_brainpoolp256r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 800
	addi a2, zero, 800
	addi a3, zero, 1152
	call {vg_brainpoolp256r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 832
	addi a2, zero, 256
	addi a3, zero, 1152
	call {vg_brainpoolp256r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 800
	addi a2, zero, 800
	addi a3, zero, 832
	call {vg_brainpoolp256r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 800
	addi a2, zero, 800
	addi a3, zero, 1344
	call {vg_brainpoolp256r1_add_mod_p}
	ld t0, 224(s0)
	sd t0, 992(s0)
	ld t0, 232(s0)
	sd t0, 1000(s0)
	ld t0, 240(s0)
	sd t0, 1008(s0)
	ld t0, 248(s0)
	sd t0, 1016(s0)
	addi s1, zero, 256
20:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_brainpoolp256r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 800
	addi a3, zero, 992
	call {vg_brainpoolp256r1_mul_mod_p}
	srli t0, s1, 6
	slli t0, t0, 3
	add t0, t0, s0
	ld t1, 416(t0)
	srl t1, t1, s1
	andi t1, t1, 1
	addi t2, zero, 0
	sub a7, t2, t1
	ld t0, 992(s0)
	ld t1, 1024(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 992(s0)
	ld t0, 1000(s0)
	ld t1, 1032(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1000(s0)
	ld t0, 1008(s0)
	ld t1, 1040(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1008(s0)
	ld t0, 1016(s0)
	ld t1, 1048(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1016(s0)
	bnez s1, 20b
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_brainpoolp256r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 896
	addi a2, zero, 864
	addi a3, zero, 800
	call {vg_brainpoolp256r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 672
	addi a2, zero, 992
	addi a3, zero, 192
	call {vg_brainpoolp256r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 704
	addi a2, zero, 160
	addi a3, zero, 672
	call {vg_brainpoolp256r1_sub_mod_p}
	addi t3, zero, 0
	ld t4, 896(s0)
	or t3, t3, t4
	ld t4, 904(s0)
	or t3, t3, t4
	ld t4, 912(s0)
	or t3, t3, t4
	ld t4, 920(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	ld t0, 1472(s0)
	and t0, t0, a7
	sd t0, 1472(s0)
	ld t0, 672(s0)
	ld t1, 384(s0)
	xor t0, t0, t1
	andi t0, t0, 1
	addi t1, zero, 0
	sub a7, t1, t0
	ld t0, 672(s0)
	ld t1, 704(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 736(s0)
	ld t0, 680(s0)
	ld t1, 712(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 744(s0)
	ld t0, 688(s0)
	ld t1, 720(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 752(s0)
	ld t0, 696(s0)
	ld t1, 728(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 760(s0)
	ld t0, 736(s0)
	ld t1, 384(s0)
	xor t0, t0, t1
	andi t0, t0, 1
	addi a7, t0, -1
	ld t0, 1472(s0)
	and t0, t0, a7
	sd t0, 1472(s0)
	ld a7, 1472(s0)
	addi t0, zero, 4
	and t0, t0, a7
	sb t0, 0(s2)
	ld t0, 1144(s0)
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
	ld t0, 1136(s0)
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
	ld t0, 1128(s0)
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
	ld t0, 1120(s0)
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
	ld t0, 760(s0)
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
	ld t0, 752(s0)
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
	ld t0, 744(s0)
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
	ld t0, 736(s0)
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
	ld a0, 1472(s0)
	andi a0, a0, 1
	ld ra, 24(s0)
	ld s2, 16(s0)
	ld s1, 8(s0)
	ld s3, 32(s0)
	ld s0, 0(s0)
	ret
	.option pop
