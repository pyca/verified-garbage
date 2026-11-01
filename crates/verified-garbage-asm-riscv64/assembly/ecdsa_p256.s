// The functions of `src/ecdsa_p256.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_p256_sign:
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
	sd t0, 1080(s0)
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
	sd t0, 1072(s0)
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
	sd t0, 1064(s0)
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
	sd t0, 1056(s0)
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
	sd t0, 1144(s0)
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
	sd t0, 1136(s0)
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
	sd t0, 1128(s0)
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
	sd t0, 1120(s0)
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
	sd t0, 1176(s0)
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
	sd t0, 1168(s0)
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
	sd t0, 1160(s0)
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
	sd t0, 1152(s0)
	addi t0, zero, 0
	addi t0, t0, -1
	sd t0, 1472(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 64(s0)
	lui t0, 0
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
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
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 1
	add t0, t0, t1
	sd t0, 88(s0)
	lui t0, 998301
	addiw t0, t0, -1341
	slli t0, t0, 32
	lui t1, 1033778
	addiw t1, t1, 1361
	add t0, t0, t1
	sd t0, 96(s0)
	lui t0, 773744
	addiw t0, t0, -1362
	slli t0, t0, 32
	lui t1, 684410
	addiw t1, t1, -380
	add t0, t0, t1
	sd t0, 104(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 112(s0)
	lui t0, 0
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
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
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 1
	add t0, t0, t1
	sd t0, 224(s0)
	lui t0, 0
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 232(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 240(s0)
	lui t0, 0
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -2
	add t0, t0, t1
	sd t0, 248(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -4
	add t0, t0, t1
	sd t0, 256(s0)
	lui t0, 0
	addiw t0, t0, 4
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
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
	addiw t0, t0, -4
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 4
	add t0, t0, t1
	sd t0, 280(s0)
	lui t0, 564586
	addiw t0, t0, -474
	slli t0, t0, 32
	lui t1, 513252
	addiw t1, t1, -1633
	add t0, t0, t1
	sd t0, 288(s0)
	lui t0, 27905
	addiw t0, t0, 358
	slli t0, t0, 32
	lui t1, 432329
	addiw t1, t1, 434
	add t0, t0, t1
	sd t0, 296(s0)
	lui t0, 724582
	addiw t0, t0, 516
	slli t0, t0, 32
	lui t1, 939577
	addiw t1, t1, -892
	add t0, t0, t1
	sd t0, 304(s0)
	lui t0, 608513
	addiw t0, t0, 601
	slli t0, t0, 32
	lui t1, 55646
	addiw t1, t1, -1892
	add t0, t0, t1
	sd t0, 312(s0)
	lui t0, 499315
	addiw t0, t0, 212
	slli t0, t0, 32
	lui t1, 101009
	addiw t1, t1, 1084
	add t0, t0, t1
	sd t0, 320(s0)
	lui t0, 482217
	addiw t0, t0, 1532
	slli t0, t0, 32
	lui t1, 392923
	addiw t1, t1, 1537
	add t0, t0, t1
	sd t0, 328(s0)
	lui t0, 499639
	addiw t0, t0, 811
	slli t0, t0, 32
	lui t1, 488994
	addiw t1, t1, 1296
	add t0, t0, t1
	sd t0, 336(s0)
	lui t0, 100614
	addiw t0, t0, -137
	slli t0, t0, 32
	lui t1, 676725
	addiw t1, t1, 1478
	add t0, t0, t1
	sd t0, 344(s0)
	lui t0, 909093
	addiw t0, t0, 856
	slli t0, t0, 32
	lui t1, 846165
	addiw t1, t1, 1546
	add t0, t0, t1
	sd t0, 352(s0)
	lui t0, 570540
	addiw t0, t0, -1819
	slli t0, t0, 32
	lui t1, 762270
	addiw t1, t1, 1116
	add t0, t0, t1
	sd t0, 360(s0)
	lui t0, 863880
	addiw t0, t0, 1673
	slli t0, t0, 32
	lui t1, 905759
	addiw t1, t1, 805
	add t0, t0, t1
	sd t0, 368(s0)
	lui t0, 546592
	addiw t0, t0, -232
	slli t0, t0, 32
	lui t1, 153734
	addiw t1, t1, -635
	add t0, t0, t1
	sd t0, 376(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -3
	add t0, t0, t1
	sd t0, 448(s0)
	lui t0, 0
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 456(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 464(s0)
	lui t0, 0
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 1
	add t0, t0, t1
	sd t0, 472(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 3
	add t0, t0, t1
	sd t0, 1312(s0)
	lui t0, 0
	addiw t0, t0, -4
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 1320(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -2
	add t0, t0, t1
	sd t0, 1328(s0)
	lui t0, 0
	addiw t0, t0, 5
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -3
	add t0, t0, t1
	sd t0, 1336(s0)
	lui t0, 887246
	addiw t0, t0, -158
	slli t0, t0, 32
	lui t1, 171084
	addiw t1, t1, -545
	add t0, t0, t1
	sd t0, 1344(s0)
	lui t0, 708352
	addiw t0, t0, 1485
	slli t0, t0, 32
	lui t1, 493635
	addiw t1, t1, 144
	add t0, t0, t1
	sd t0, 1352(s0)
	lui t0, 940578
	addiw t0, t0, 172
	slli t0, t0, 32
	lui t1, 1012243
	addiw t1, t1, -298
	add t0, t0, t1
	sd t0, 1360(s0)
	lui t0, 901888
	addiw t0, t0, 1565
	slli t0, t0, 32
	lui t1, 18549
	addiw t1, t1, -1996
	add t0, t0, t1
	sd t0, 1368(s0)
	lui t0, 537157
	addiw t0, t0, -874
	slli t0, t0, 32
	lui t1, 780191
	addiw t1, t1, -350
	add t0, t0, t1
	sd t0, 1184(s0)
	lui t0, 289176
	addiw t0, t0, -1636
	slli t0, t0, 32
	lui t1, 302039
	addiw t1, t1, -90
	add t0, t0, t1
	sd t0, 1192(s0)
	lui t0, 164955
	addiw t0, t0, 569
	slli t0, t0, 32
	lui t1, 177855
	addiw t1, t1, -935
	add t0, t0, t1
	sd t0, 1200(s0)
	lui t0, 421395
	addiw t0, t0, -619
	slli t0, t0, 32
	lui t1, 998805
	addiw t1, t1, 1568
	add t0, t0, t1
	sd t0, 1208(s0)
	lui t0, 50275
	addiw t0, t0, 1341
	slli t0, t0, 32
	lui t1, 14798
	addiw t1, t1, -1361
	add t0, t0, t1
	sd t0, 1216(s0)
	lui t0, 274832
	addiw t0, t0, 1362
	slli t0, t0, 32
	lui t1, 364166
	addiw t1, t1, 379
	add t0, t0, t1
	sd t0, 1224(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1232(s0)
	lui t0, 0
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 1240(s0)
	lui t0, 998301
	addiw t0, t0, -1341
	slli t0, t0, 32
	lui t1, 1033778
	addiw t1, t1, 1359
	add t0, t0, t1
	sd t0, 1248(s0)
	lui t0, 773744
	addiw t0, t0, -1362
	slli t0, t0, 32
	lui t1, 684410
	addiw t1, t1, -380
	add t0, t0, t1
	sd t0, 1256(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 1264(s0)
	lui t0, 0
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1272(s0)
	addi t5, zero, 0
	ld t3, 1120(s0)
	ld t4, 96(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1128(s0)
	ld t4, 104(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1136(s0)
	ld t4, 112(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1144(s0)
	ld t4, 120(s0)
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
	addi t3, zero, 0
	ld t4, 1120(s0)
	or t3, t3, t4
	ld t4, 1128(s0)
	or t3, t3, t4
	ld t4, 1136(s0)
	or t3, t3, t4
	ld t4, 1144(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	xori a7, a7, -1
	ld t0, 1472(s0)
	and t0, t0, a7
	sd t0, 1472(s0)
	ld t0, 320(s0)
	sd t0, 512(s0)
	ld t0, 328(s0)
	sd t0, 520(s0)
	ld t0, 336(s0)
	sd t0, 528(s0)
	ld t0, 344(s0)
	sd t0, 536(s0)
	ld t0, 352(s0)
	sd t0, 544(s0)
	ld t0, 360(s0)
	sd t0, 552(s0)
	ld t0, 368(s0)
	sd t0, 560(s0)
	ld t0, 376(s0)
	sd t0, 568(s0)
	addi t5, zero, 0
	ld t3, 1056(s0)
	ld t4, 96(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1064(s0)
	ld t4, 104(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1072(s0)
	ld t4, 112(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1080(s0)
	ld t4, 120(s0)
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
	addi t3, zero, 0
	ld t4, 1056(s0)
	or t3, t3, t4
	ld t4, 1064(s0)
	or t3, t3, t4
	ld t4, 1072(s0)
	or t3, t3, t4
	ld t4, 1080(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	xori a7, a7, -1
	ld t0, 1472(s0)
	and t0, t0, a7
	sd t0, 1472(s0)
	addi a0, s0, 0
	call {vg_p256_mul}
	addi s0, s3, 0
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
	call {vg_p256_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 576
	addi a3, zero, 992
	call {vg_p256_mul_mod_p}
	srli t0, s1, 6
	slli t0, t0, 3
	add t0, t0, s0
	ld t1, 448(t0)
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
	addi a1, zero, 608
	addi a2, zero, 512
	addi a3, zero, 992
	call {vg_p256_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 640
	addi a2, zero, 608
	addi a3, zero, 192
	call {vg_p256_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 672
	addi a2, zero, 640
	addi a3, zero, 160
	call {vg_p256_add_mod_n}
	addi a0, s0, 0
	addi a1, zero, 704
	addi a2, zero, 1056
	addi a3, zero, 1184
	call {vg_p256_mul_mod_n}
	ld t0, 1216(s0)
	sd t0, 992(s0)
	ld t0, 1224(s0)
	sd t0, 1000(s0)
	ld t0, 1232(s0)
	sd t0, 1008(s0)
	ld t0, 1240(s0)
	sd t0, 1016(s0)
	addi s1, zero, 256
21:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p256_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 704
	addi a3, zero, 992
	call {vg_p256_mul_mod_n}
	srli t0, s1, 6
	slli t0, t0, 3
	add t0, t0, s0
	ld t1, 1248(t0)
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
	bnez s1, 21b
	addi a0, s0, 0
	addi a1, zero, 736
	addi a2, zero, 1152
	addi a3, zero, 1184
	call {vg_p256_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 768
	addi a2, zero, 672
	addi a3, zero, 1184
	call {vg_p256_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 800
	addi a2, zero, 1120
	addi a3, zero, 1184
	call {vg_p256_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 832
	addi a2, zero, 768
	addi a3, zero, 800
	call {vg_p256_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 736
	addi a3, zero, 832
	call {vg_p256_add_mod_n}
	addi a0, s0, 0
	addi a1, zero, 896
	addi a2, zero, 992
	addi a3, zero, 864
	call {vg_p256_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 928
	addi a2, zero, 896
	addi a3, zero, 192
	call {vg_p256_mul_mod_n}
	addi t3, zero, 0
	ld t4, 672(s0)
	or t3, t3, t4
	ld t4, 680(s0)
	or t3, t3, t4
	ld t4, 688(s0)
	or t3, t3, t4
	ld t4, 696(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	xori a7, a7, -1
	ld t0, 1472(s0)
	and t0, t0, a7
	sd t0, 1472(s0)
	addi t3, zero, 0
	ld t4, 928(s0)
	or t3, t3, t4
	ld t4, 936(s0)
	or t3, t3, t4
	ld t4, 944(s0)
	or t3, t3, t4
	ld t4, 952(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	xori a7, a7, -1
	ld t0, 1472(s0)
	and t0, t0, a7
	sd t0, 1472(s0)
	ld a7, 1472(s0)
	ld t0, 696(s0)
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
	ld t0, 688(s0)
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
	ld t0, 680(s0)
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
	ld t0, 672(s0)
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
	ld t0, 952(s0)
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
	ld t0, 944(s0)
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
	ld t0, 936(s0)
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
	ld t0, 928(s0)
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
	ld a0, 1472(s0)
	andi a0, a0, 1
	ld ra, 24(s0)
	ld s2, 16(s0)
	ld s1, 8(s0)
	ld s3, 32(s0)
	ld s0, 0(s0)
	ret
	.option pop
