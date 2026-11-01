// The functions of `src/internal/vg_mlkem_inv_ntt.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem_inv_ntt:
	.option push
	.option arch, +m, +c
	lui t0, 1
	addi t0, t0, -2048
	addi t2, t0, -2047
	sw t2, 0(a1)
	addi t2, t0, -319
	sw t2, 4(a1)
	addi t2, t0, 532
	sw t2, 8(a1)
	addi t2, t0, 1241
	sw t2, 12(a1)
	addi t2, t0, 594
	sw t2, 16(a1)
	addi t2, t0, -1418
	sw t2, 20(a1)
	addi t2, t0, -151
	sw t2, 24(a1)
	addi t2, t0, -1200
	sw t2, 28(a1)
	addi t2, t0, -986
	sw t2, 32(a1)
	addi t2, t0, -129
	sw t2, 36(a1)
	addi t2, t0, -1855
	sw t2, 40(a1)
	addi t2, t0, -1251
	sw t2, 44(a1)
	addi t2, t0, 738
	sw t2, 48(a1)
	addi t2, t0, 1212
	sw t2, 52(a1)
	addi t2, t0, -1479
	sw t2, 56(a1)
	addi t2, t0, -302
	sw t2, 60(a1)
	addi t2, t0, -1752
	sw t2, 64(a1)
	addi t2, t0, 399
	sw t2, 68(a1)
	addi t2, t0, -709
	sw t2, 72(a1)
	addi t2, t0, -572
	sw t2, 76(a1)
	addi t2, t0, 998
	sw t2, 80(a1)
	addi t2, t0, -1992
	sw t2, 84(a1)
	addi t2, t0, 192
	sw t2, 88(a1)
	addi t2, t0, -715
	sw t2, 92(a1)
	addi t2, t0, -622
	sw t2, 96(a1)
	addi t2, t0, 46
	sw t2, 100(a1)
	addi t2, t0, -1513
	sw t2, 104(a1)
	addi t2, t0, 834
	sw t2, 108(a1)
	addi t2, t0, 345
	sw t2, 112(a1)
	addi t2, t0, 831
	sw t2, 116(a1)
	addi t2, t0, -74
	sw t2, 120(a1)
	addi t2, t0, -1227
	sw t2, 124(a1)
	addi t2, t0, -1759
	sw t2, 128(a1)
	addi t2, t0, -1717
	sw t2, 132(a1)
	addi t2, t0, 1205
	sw t2, 136(a1)
	addi t2, t0, -292
	sw t2, 140(a1)
	addi t2, t0, -851
	sw t2, 144(a1)
	addi t2, t0, 256
	sw t2, 148(a1)
	addi t2, t0, 229
	sw t2, 152(a1)
	addi t2, t0, 7
	sw t2, 156(a1)
	addi t2, t0, -1398
	sw t2, 160(a1)
	addi t2, t0, -71
	sw t2, 164(a1)
	addi t2, t0, 465
	sw t2, 168(a1)
	addi t2, t0, -1416
	sw t2, 172(a1)
	addi t2, t0, 817
	sw t2, 176(a1)
	addi t2, t0, -2015
	sw t2, 180(a1)
	addi t2, t0, -728
	sw t2, 184(a1)
	addi t2, t0, -133
	sw t2, 188(a1)
	addi t2, t0, 271
	sw t2, 192(a1)
	addi t2, t0, -613
	sw t2, 196(a1)
	addi t2, t0, -1241
	sw t2, 200(a1)
	addi t2, t0, -1596
	sw t2, 204(a1)
	addi t2, t0, -610
	sw t2, 208(a1)
	addi t2, t0, 820
	sw t2, 212(a1)
	addi t2, t0, -514
	sw t2, 216(a1)
	addi t2, t0, 354
	sw t2, 220(a1)
	addi t2, t0, 599
	sw t2, 224(a1)
	addi t2, t0, 569
	sw t2, 228(a1)
	addi t2, t0, -567
	sw t2, 232(a1)
	addi t2, t0, -1400
	sw t2, 236(a1)
	addi t2, t0, 426
	sw t2, 240(a1)
	addi t2, t0, 1062
	sw t2, 244(a1)
	addi t2, t0, -821
	sw t2, 248(a1)
	addi t2, t0, -1138
	sw t2, 252(a1)
	addi t2, t0, -2031
	sw t2, 256(a1)
	addi t2, t0, 713
	sw t2, 260(a1)
	addi t2, t0, -1465
	sw t2, 264(a1)
	addi t2, t0, 601
	sw t2, 268(a1)
	addi t2, t0, -411
	sw t2, 272(a1)
	addi t2, t0, -1325
	sw t2, 276(a1)
	addi t2, t0, 240
	sw t2, 280(a1)
	addi t2, t0, -948
	sw t2, 284(a1)
	addi t2, t0, -639
	sw t2, 288(a1)
	addi t2, t0, 614
	sw t2, 292(a1)
	addi t2, t0, 1233
	sw t2, 296(a1)
	addi t2, t0, -1815
	sw t2, 300(a1)
	addi t2, t0, -1292
	sw t2, 304(a1)
	addi t2, t0, 108
	sw t2, 308(a1)
	addi t2, t0, 967
	sw t2, 312(a1)
	addi t2, t0, 1002
	sw t2, 316(a1)
	addi t2, t0, -345
	sw t2, 320(a1)
	addi t2, t0, -397
	sw t2, 324(a1)
	addi t2, t0, 741
	sw t2, 328(a1)
	addi t2, t0, -259
	sw t2, 332(a1)
	addi t2, t0, -201
	sw t2, 336(a1)
	addi t2, t0, -1096
	sw t2, 340(a1)
	addi t2, t0, -587
	sw t2, 344(a1)
	addi t2, t0, 639
	sw t2, 348(a1)
	addi t2, t0, -1109
	sw t2, 352(a1)
	addi t2, t0, 260
	sw t2, 356(a1)
	addi t2, t0, 389
	sw t2, 360(a1)
	addi t2, t0, 340
	sw t2, 364(a1)
	addi t2, t0, -1315
	sw t2, 368(a1)
	addi t2, t0, 289
	sw t2, 372(a1)
	addi t2, t0, -1780
	sw t2, 376(a1)
	addi t2, t0, -1407
	sw t2, 380(a1)
	addi t2, t0, -464
	sw t2, 384(a1)
	addi t2, t0, 250
	sw t2, 388(a1)
	addi t2, t0, -11
	sw t2, 392(a1)
	addi t2, t0, 1172
	sw t2, 396(a1)
	addi t2, t0, -1673
	sw t2, 400(a1)
	addi t2, t0, 501
	sw t2, 404(a1)
	addi t2, t0, 42
	sw t2, 408(a1)
	addi t2, t0, -403
	sw t2, 412(a1)
	addi t2, t0, -985
	sw t2, 416(a1)
	addi t2, t0, -1729
	sw t2, 420(a1)
	addi t2, t0, 725
	sw t2, 424(a1)
	addi t2, t0, -1291
	sw t2, 428(a1)
	addi t2, t0, 51
	sw t2, 432(a1)
	addi t2, t0, -1487
	sw t2, 436(a1)
	addi t2, t0, 418
	sw t2, 440(a1)
	addi t2, t0, 546
	sw t2, 444(a1)
	addi t2, t0, 756
	sw t2, 448(a1)
	addi t2, t0, -956
	sw t2, 452(a1)
	addi t2, t0, -1645
	sw t2, 456(a1)
	addi t2, t0, -1022
	sw t2, 460(a1)
	addi t2, t0, -905
	sw t2, 464(a1)
	addi t2, t0, 102
	sw t2, 468(a1)
	addi t2, t0, 727
	sw t2, 472(a1)
	addi t2, t0, -1162
	sw t2, 476(a1)
	addi t2, t0, -326
	sw t2, 480(a1)
	addi t2, t0, -836
	sw t2, 484(a1)
	addi t2, t0, -174
	sw t2, 488(a1)
	addi t2, t0, -1019
	sw t2, 492(a1)
	addi t2, t0, 62
	sw t2, 496(a1)
	addi t2, t0, 887
	sw t2, 500(a1)
	addi t2, t0, -1163
	sw t2, 504(a1)
	addi t2, t0, 106
	sw t2, 508(a1)
	lui a5, 39
	addi a5, a5, 1526
	lui a6, 1
	addi a6, a6, -767
	addi a0, a0, 1024
	addi a1, a1, 508
	addi a7, zero, 8
20:
	addi a2, a0, -1024
21:
	lwu a4, 0(a1)
	addi a1, a1, -4
	add a3, a2, a7
	srli t1, a7, 2
22:
	lwu t2, 0(a2)
	lwu t0, 0(a3)
	add t3, t2, t0
	sub t3, t3, a6
	srai t4, t3, 63
	and t4, t4, a6
	add t3, t3, t4
	sw t3, 0(a2)
	sub t0, t0, t2
	srai t4, t0, 63
	and t4, t4, a6
	add t0, t0, t4
	mul t0, a4, t0
	srli t3, t0, 11
	mul t3, t3, a5
	srli t3, t3, 18
	sub t0, t0, t3
	slli t5, t3, 8
	sub t0, t0, t5
	slli t5, t3, 10
	sub t0, t0, t5
	slli t5, t3, 11
	sub t0, t0, t5
	sub t0, t0, a6
	srai t3, t0, 63
	and t3, t3, a6
	add t0, t0, t3
	sw t0, 0(a3)
	addi a2, a2, 4
	addi a3, a3, 4
	addi t1, t1, -1
	bnez t1, 22b
	addi a2, a3, 0
	sub t0, a2, a0
	bnez t0, 21b
	slli a7, a7, 1
	addi t0, a7, -1024
	bnez t0, 20b
	lui a4, 1
	addi a4, a4, -793
	addi a2, a0, -1024
	addi t1, zero, 256
23:
	lwu t2, 0(a2)
	mul t2, t2, a4
	srli t3, t2, 11
	mul t3, t3, a5
	srli t3, t3, 18
	sub t2, t2, t3
	slli t5, t3, 8
	sub t2, t2, t5
	slli t5, t3, 10
	sub t2, t2, t5
	slli t5, t3, 11
	sub t2, t2, t5
	sub t2, t2, a6
	srai t3, t2, 63
	and t3, t3, a6
	add t2, t2, t3
	sw t2, 0(a2)
	addi a2, a2, 4
	addi t1, t1, -1
	bnez t1, 23b
	ret
	.option pop
