// The functions of `src/mlkem.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem_sample_ntt:
	.option push
	.option arch, +m, +c
	sd s7, 1680(a2)
	sd s8, 1688(a2)
	sd s9, 1696(a2)
	sd ra, 1704(a2)
	addi s7, a0, 0
	addi s8, a1, 0
	addi s9, a2, 0
	addi t0, zero, 0
	sd t0, 0(s9)
	sd t0, 8(s9)
	sd t0, 16(s9)
	sd t0, 24(s9)
	sd t0, 32(s9)
	sd t0, 40(s9)
	sd t0, 48(s9)
	sd t0, 56(s9)
	sd t0, 64(s9)
	sd t0, 72(s9)
	sd t0, 80(s9)
	sd t0, 88(s9)
	sd t0, 96(s9)
	sd t0, 104(s9)
	sd t0, 112(s9)
	sd t0, 120(s9)
	sd t0, 128(s9)
	sd t0, 136(s9)
	sd t0, 144(s9)
	sd t0, 152(s9)
	sd t0, 160(s9)
	sd t0, 168(s9)
	sd t0, 176(s9)
	sd t0, 184(s9)
	sd t0, 192(s9)
	addi a0, s9, 0
	addi a1, zero, 168
	addi a2, zero, 0
	addi a3, s7, 0
	addi a4, zero, 34
	call {vg_keccak_absorb}
	addi a2, a0, 0
	addi a0, s9, 0
	addi a1, zero, 168
	addi a3, zero, 31
	call {vg_keccak_pad}
	addi a0, s9, 0
	addi a1, zero, 168
	addi a2, zero, 0
	addi a3, s9, 840
	addi a4, zero, 840
	call {vg_keccak_squeeze}
	addi a0, s9, 840
	addi a1, s8, 0
	addi a2, zero, 0
	addi a3, zero, 280
	lui t3, 1
	addi t3, t3, -767
20:
	lbu a4, 0(a0)
	lbu a5, 1(a0)
	lbu a6, 2(a0)
	slli a7, a5, 60
	srli a7, a7, 52
	add a7, a4, a7
	srli t1, a5, 4
	slli t2, a6, 4
	add t1, t1, t2
	sub t2, a7, t3
	srli t2, t2, 63
	addi a4, a2, -256
	srli a4, a4, 63
	and t2, t2, a4
	beqz t2, 21f
	sw a7, 0(a1)
	addi a1, a1, 4
	addi a2, a2, 1
	j 22f
21:
22:
	sub t2, t1, t3
	srli t2, t2, 63
	addi a4, a2, -256
	srli a4, a4, 63
	and t2, t2, a4
	beqz t2, 23f
	sw t1, 0(a1)
	addi a1, a1, 4
	addi a2, a2, 1
	j 24f
23:
24:
	addi a0, a0, 3
	addi a3, a3, -1
	bnez a3, 20b
	srli a0, a2, 8
	ld ra, 1704(s9)
	ld s7, 1680(s9)
	ld s8, 1688(s9)
	ld s9, 1696(s9)
	ret
	.option pop

vg_mlkem_ntt:
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
	addi a1, a1, 4
	addi a7, zero, 512
20:
	addi a2, a0, -1024
21:
	lwu a4, 0(a1)
	addi a1, a1, 4
	add a3, a2, a7
	srli t1, a7, 2
22:
	lwu t2, 0(a2)
	lwu t0, 0(a3)
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
	sub t3, t2, t0
	srai t4, t3, 63
	and t4, t4, a6
	add t3, t3, t4
	sw t3, 0(a3)
	add t2, t2, t0
	sub t2, t2, a6
	srai t4, t2, 63
	and t4, t4, a6
	add t2, t2, t4
	sw t2, 0(a2)
	addi a2, a2, 4
	addi a3, a3, 4
	addi t1, t1, -1
	bnez t1, 22b
	addi a2, a3, 0
	sub t0, a2, a0
	bnez t0, 21b
	srli a7, a7, 1
	addi t0, a7, -4
	bnez t0, 20b
	ret
	.option pop

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

vg_mlkem_multiply_ntts:
	.option push
	.option arch, +m, +c
	lui t0, 1
	addi t0, t0, -2048
	addi t2, t0, -2031
	sw t2, 0(a3)
	addi t2, t0, 1264
	sw t2, 4(a3)
	addi t2, t0, 713
	sw t2, 8(a3)
	addi t2, t0, -1480
	sw t2, 12(a3)
	addi t2, t0, -1465
	sw t2, 16(a3)
	addi t2, t0, 698
	sw t2, 20(a3)
	addi t2, t0, 601
	sw t2, 24(a3)
	addi t2, t0, -1368
	sw t2, 28(a3)
	addi t2, t0, -411
	sw t2, 32(a3)
	addi t2, t0, -356
	sw t2, 36(a3)
	addi t2, t0, -1325
	sw t2, 40(a3)
	addi t2, t0, 558
	sw t2, 44(a3)
	addi t2, t0, 240
	sw t2, 48(a3)
	addi t2, t0, -1007
	sw t2, 52(a3)
	addi t2, t0, -948
	sw t2, 56(a3)
	addi t2, t0, 181
	sw t2, 60(a3)
	addi t2, t0, -639
	sw t2, 64(a3)
	addi t2, t0, -128
	sw t2, 68(a3)
	addi t2, t0, 614
	sw t2, 72(a3)
	addi t2, t0, -1381
	sw t2, 76(a3)
	addi t2, t0, 1233
	sw t2, 80(a3)
	addi t2, t0, -2000
	sw t2, 84(a3)
	addi t2, t0, -1815
	sw t2, 88(a3)
	addi t2, t0, 1048
	sw t2, 92(a3)
	addi t2, t0, -1292
	sw t2, 96(a3)
	addi t2, t0, 525
	sw t2, 100(a3)
	addi t2, t0, 108
	sw t2, 104(a3)
	addi t2, t0, -875
	sw t2, 108(a3)
	addi t2, t0, 967
	sw t2, 112(a3)
	addi t2, t0, -1734
	sw t2, 116(a3)
	addi t2, t0, 1002
	sw t2, 120(a3)
	addi t2, t0, -1769
	sw t2, 124(a3)
	addi t2, t0, -345
	sw t2, 128(a3)
	addi t2, t0, -422
	sw t2, 132(a3)
	addi t2, t0, -397
	sw t2, 136(a3)
	addi t2, t0, -370
	sw t2, 140(a3)
	addi t2, t0, 741
	sw t2, 144(a3)
	addi t2, t0, -1508
	sw t2, 148(a3)
	addi t2, t0, -259
	sw t2, 152(a3)
	addi t2, t0, -508
	sw t2, 156(a3)
	addi t2, t0, -201
	sw t2, 160(a3)
	addi t2, t0, -566
	sw t2, 164(a3)
	addi t2, t0, -1096
	sw t2, 168(a3)
	addi t2, t0, 329
	sw t2, 172(a3)
	addi t2, t0, -587
	sw t2, 176(a3)
	addi t2, t0, -180
	sw t2, 180(a3)
	addi t2, t0, 639
	sw t2, 184(a3)
	addi t2, t0, -1406
	sw t2, 188(a3)
	addi t2, t0, -1109
	sw t2, 192(a3)
	addi t2, t0, 342
	sw t2, 196(a3)
	addi t2, t0, 260
	sw t2, 200(a3)
	addi t2, t0, -1027
	sw t2, 204(a3)
	addi t2, t0, 389
	sw t2, 208(a3)
	addi t2, t0, -1156
	sw t2, 212(a3)
	addi t2, t0, 340
	sw t2, 216(a3)
	addi t2, t0, -1107
	sw t2, 220(a3)
	addi t2, t0, -1315
	sw t2, 224(a3)
	addi t2, t0, 548
	sw t2, 228(a3)
	addi t2, t0, 289
	sw t2, 232(a3)
	addi t2, t0, -1056
	sw t2, 236(a3)
	addi t2, t0, -1780
	sw t2, 240(a3)
	addi t2, t0, 1013
	sw t2, 244(a3)
	addi t2, t0, -1407
	sw t2, 248(a3)
	addi t2, t0, 640
	sw t2, 252(a3)
	addi t2, t0, -464
	sw t2, 256(a3)
	addi t2, t0, -303
	sw t2, 260(a3)
	addi t2, t0, 250
	sw t2, 264(a3)
	addi t2, t0, -1017
	sw t2, 268(a3)
	addi t2, t0, -11
	sw t2, 272(a3)
	addi t2, t0, -756
	sw t2, 276(a3)
	addi t2, t0, 1172
	sw t2, 280(a3)
	addi t2, t0, -1939
	sw t2, 284(a3)
	addi t2, t0, -1673
	sw t2, 288(a3)
	addi t2, t0, 906
	sw t2, 292(a3)
	addi t2, t0, 501
	sw t2, 296(a3)
	addi t2, t0, -1268
	sw t2, 300(a3)
	addi t2, t0, 42
	sw t2, 304(a3)
	addi t2, t0, -809
	sw t2, 308(a3)
	addi t2, t0, -403
	sw t2, 312(a3)
	addi t2, t0, -364
	sw t2, 316(a3)
	addi t2, t0, -985
	sw t2, 320(a3)
	addi t2, t0, 218
	sw t2, 324(a3)
	addi t2, t0, -1729
	sw t2, 328(a3)
	addi t2, t0, 962
	sw t2, 332(a3)
	addi t2, t0, 725
	sw t2, 336(a3)
	addi t2, t0, -1492
	sw t2, 340(a3)
	addi t2, t0, -1291
	sw t2, 344(a3)
	addi t2, t0, 524
	sw t2, 348(a3)
	addi t2, t0, 51
	sw t2, 352(a3)
	addi t2, t0, -818
	sw t2, 356(a3)
	addi t2, t0, -1487
	sw t2, 360(a3)
	addi t2, t0, 720
	sw t2, 364(a3)
	addi t2, t0, 418
	sw t2, 368(a3)
	addi t2, t0, -1185
	sw t2, 372(a3)
	addi t2, t0, 546
	sw t2, 376(a3)
	addi t2, t0, -1313
	sw t2, 380(a3)
	addi t2, t0, 756
	sw t2, 384(a3)
	addi t2, t0, -1523
	sw t2, 388(a3)
	addi t2, t0, -956
	sw t2, 392(a3)
	addi t2, t0, 189
	sw t2, 396(a3)
	addi t2, t0, -1645
	sw t2, 400(a3)
	addi t2, t0, 878
	sw t2, 404(a3)
	addi t2, t0, -1022
	sw t2, 408(a3)
	addi t2, t0, 255
	sw t2, 412(a3)
	addi t2, t0, -905
	sw t2, 416(a3)
	addi t2, t0, 138
	sw t2, 420(a3)
	addi t2, t0, 102
	sw t2, 424(a3)
	addi t2, t0, -869
	sw t2, 428(a3)
	addi t2, t0, 727
	sw t2, 432(a3)
	addi t2, t0, -1494
	sw t2, 436(a3)
	addi t2, t0, -1162
	sw t2, 440(a3)
	addi t2, t0, 395
	sw t2, 444(a3)
	addi t2, t0, -326
	sw t2, 448(a3)
	addi t2, t0, -441
	sw t2, 452(a3)
	addi t2, t0, -836
	sw t2, 456(a3)
	addi t2, t0, 69
	sw t2, 460(a3)
	addi t2, t0, -174
	sw t2, 464(a3)
	addi t2, t0, -593
	sw t2, 468(a3)
	addi t2, t0, -1019
	sw t2, 472(a3)
	addi t2, t0, 252
	sw t2, 476(a3)
	addi t2, t0, 62
	sw t2, 480(a3)
	addi t2, t0, -829
	sw t2, 484(a3)
	addi t2, t0, 887
	sw t2, 488(a3)
	addi t2, t0, -1654
	sw t2, 492(a3)
	addi t2, t0, -1163
	sw t2, 496(a3)
	addi t2, t0, 396
	sw t2, 500(a3)
	addi t2, t0, 106
	sw t2, 504(a3)
	addi t2, t0, -873
	sw t2, 508(a3)
	lui a5, 39
	addi a5, a5, 1526
	lui a6, 1
	addi a6, a6, -767
	addi t1, zero, 128
20:
	lwu a4, 0(a1)
	lwu t2, 4(a1)
	lwu t3, 0(a2)
	lwu t4, 4(a2)
	mul t0, t2, t4
	srli a7, t0, 11
	mul a7, a7, a5
	srli a7, a7, 18
	sub t0, t0, a7
	slli t5, a7, 8
	sub t0, t0, t5
	slli t5, a7, 10
	sub t0, t0, t5
	slli t5, a7, 11
	sub t0, t0, t5
	sub t0, t0, a6
	srai a7, t0, 63
	and a7, a7, a6
	add t0, t0, a7
	lwu a7, 0(a3)
	mul t0, t0, a7
	mul a7, a4, t3
	add t0, a7, t0
	srli a7, t0, 11
	mul a7, a7, a5
	srli a7, a7, 18
	sub t0, t0, a7
	slli t5, a7, 8
	sub t0, t0, t5
	slli t5, a7, 10
	sub t0, t0, t5
	slli t5, a7, 11
	sub t0, t0, t5
	sub t0, t0, a6
	srai a7, t0, 63
	and a7, a7, a6
	add t0, t0, a7
	sw t0, 0(a0)
	mul t0, a4, t4
	mul a7, t2, t3
	add t0, t0, a7
	srli a7, t0, 11
	mul a7, a7, a5
	srli a7, a7, 18
	sub t0, t0, a7
	slli t5, a7, 8
	sub t0, t0, t5
	slli t5, a7, 10
	sub t0, t0, t5
	slli t5, a7, 11
	sub t0, t0, t5
	sub t0, t0, a6
	srai a7, t0, 63
	and a7, a7, a6
	add t0, t0, a7
	sw t0, 4(a0)
	addi a0, a0, 8
	addi a1, a1, 8
	addi a2, a2, 8
	addi a3, a3, 4
	addi t1, t1, -1
	bnez t1, 20b
	ret
	.option pop

vg_mlkem_add:
	.option push
	.option arch, +m, +c
	addi a2, zero, 256
	lui a5, 1
	addi a5, a5, -767
20:
	lwu a3, 0(a0)
	lwu a4, 0(a1)
	add a3, a3, a4
	sub a3, a3, a5
	srai a4, a3, 63
	and a4, a4, a5
	add a3, a3, a4
	sw a3, 0(a0)
	addi a0, a0, 4
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 20b
	ret
	.option pop

vg_mlkem_sub:
	.option push
	.option arch, +m, +c
	addi a2, zero, 256
	lui a5, 1
	addi a5, a5, -767
20:
	lwu a3, 0(a0)
	lwu a4, 0(a1)
	sub a3, a3, a4
	srai a4, a3, 63
	and a4, a4, a5
	add a3, a3, a4
	sw a3, 0(a0)
	addi a0, a0, 4
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 20b
	ret
	.option pop

vg_mlkem_cbd2:
	.option push
	.option arch, +m, +c
	addi a2, zero, 128
	lui a5, 1
	addi a5, a5, -767
20:
	lbu a3, 0(a0)
	slli a3, a3, 62
	srli a3, a3, 62
	srli a6, a3, 1
	sub a3, a3, a6
	lbu a4, 0(a0)
	slli a4, a4, 60
	srli a4, a4, 62
	srli a6, a4, 1
	sub a4, a4, a6
	sub a3, a3, a4
	srai a4, a3, 63
	and a4, a4, a5
	add a3, a3, a4
	sw a3, 0(a1)
	lbu a3, 0(a0)
	slli a3, a3, 58
	srli a3, a3, 62
	srli a6, a3, 1
	sub a3, a3, a6
	lbu a4, 0(a0)
	slli a4, a4, 56
	srli a4, a4, 62
	srli a6, a4, 1
	sub a4, a4, a6
	sub a3, a3, a4
	srai a4, a3, 63
	and a4, a4, a5
	add a3, a3, a4
	sw a3, 4(a1)
	addi a0, a0, 1
	addi a1, a1, 8
	addi a2, a2, -1
	bnez a2, 20b
	ret
	.option pop

vg_mlkem_encode12:
	.option push
	.option arch, +m, +c
	addi a2, zero, 128
20:
	lwu a3, 0(a0)
	lwu a4, 4(a0)
	sb a3, 0(a1)
	srli a3, a3, 8
	slli a5, a4, 4
	add a3, a3, a5
	sb a3, 1(a1)
	srli a4, a4, 4
	sb a4, 2(a1)
	addi a0, a0, 8
	addi a1, a1, 3
	addi a2, a2, -1
	bnez a2, 20b
	ret
	.option pop

vg_mlkem_decode12:
	.option push
	.option arch, +m, +c
	addi a2, zero, 128
	lui a5, 1
	addi a5, a5, -767
20:
	lbu a3, 0(a0)
	lbu a4, 1(a0)
	slli a4, a4, 60
	srli a4, a4, 52
	add a3, a3, a4
	sub a3, a3, a5
	srai a4, a3, 63
	and a4, a4, a5
	add a3, a3, a4
	sw a3, 0(a1)
	lbu a3, 1(a0)
	srli a3, a3, 4
	lbu a4, 2(a0)
	slli a4, a4, 4
	add a3, a3, a4
	sub a3, a3, a5
	srai a4, a3, 63
	and a4, a4, a5
	add a3, a3, a4
	sw a3, 4(a1)
	addi a0, a0, 3
	addi a1, a1, 8
	addi a2, a2, -1
	bnez a2, 20b
	ret
	.option pop

vg_mlkem_compress_encode:
	.option push
	.option arch, +m, +c
	slli a1, a1, 32
	srli a1, a1, 32
	addi a4, a1, -1
	beqz a4, 20f
	addi a4, a1, -4
	beqz a4, 22f
	lui a7, 64
	addi a7, a7, -64
	lui a6, 39
	addi a6, a6, 1527
	addi t1, zero, 64
24:
	addi a5, zero, 0
	lwu a4, 0(a0)
	mul a4, a4, a6
	add a4, a4, a7
	srli a4, a4, 19
	slli a4, a4, 54
	srli a4, a4, 54
	add a5, a5, a4
	lwu a4, 4(a0)
	mul a4, a4, a6
	add a4, a4, a7
	srli a4, a4, 19
	slli a4, a4, 54
	srli a4, a4, 44
	add a5, a5, a4
	lwu a4, 8(a0)
	mul a4, a4, a6
	add a4, a4, a7
	srli a4, a4, 19
	slli a4, a4, 54
	srli a4, a4, 34
	add a5, a5, a4
	lwu a4, 12(a0)
	mul a4, a4, a6
	add a4, a4, a7
	srli a4, a4, 19
	slli a4, a4, 54
	srli a4, a4, 24
	add a5, a5, a4
	sb a5, 0(a2)
	srli a4, a5, 8
	sb a4, 1(a2)
	srli a4, a5, 16
	sb a4, 2(a2)
	srli a4, a5, 24
	sb a4, 3(a2)
	srli a4, a5, 32
	sb a4, 4(a2)
	addi a0, a0, 16
	addi a2, a2, 5
	addi t1, t1, -1
	bnez t1, 24b
	j 23f
22:
	lui a7, 64
	addi a7, a7, -64
	lui a6, 1
	addi a6, a6, -1576
	addi t1, zero, 128
25:
	lwu a4, 0(a0)
	mul a4, a4, a6
	add a4, a4, a7
	srli a4, a4, 19
	slli a4, a4, 60
	srli a5, a4, 60
	lwu a4, 4(a0)
	mul a4, a4, a6
	add a4, a4, a7
	srli a4, a4, 19
	slli a4, a4, 60
	srli a4, a4, 56
	add a5, a5, a4
	sb a5, 0(a2)
	addi a0, a0, 8
	addi a2, a2, 1
	addi t1, t1, -1
	bnez t1, 25b
23:
	j 21f
20:
	lui a7, 64
	addi a7, a7, -64
	addi a6, zero, 315
	addi t1, zero, 32
26:
	addi a5, zero, 0
	lwu a4, 0(a0)
	mul a4, a4, a6
	add a4, a4, a7
	srli a4, a4, 19
	slli a4, a4, 63
	srli a4, a4, 63
	add a5, a5, a4
	lwu a4, 4(a0)
	mul a4, a4, a6
	add a4, a4, a7
	srli a4, a4, 19
	slli a4, a4, 63
	srli a4, a4, 62
	add a5, a5, a4
	lwu a4, 8(a0)
	mul a4, a4, a6
	add a4, a4, a7
	srli a4, a4, 19
	slli a4, a4, 63
	srli a4, a4, 61
	add a5, a5, a4
	lwu a4, 12(a0)
	mul a4, a4, a6
	add a4, a4, a7
	srli a4, a4, 19
	slli a4, a4, 63
	srli a4, a4, 60
	add a5, a5, a4
	lwu a4, 16(a0)
	mul a4, a4, a6
	add a4, a4, a7
	srli a4, a4, 19
	slli a4, a4, 63
	srli a4, a4, 59
	add a5, a5, a4
	lwu a4, 20(a0)
	mul a4, a4, a6
	add a4, a4, a7
	srli a4, a4, 19
	slli a4, a4, 63
	srli a4, a4, 58
	add a5, a5, a4
	lwu a4, 24(a0)
	mul a4, a4, a6
	add a4, a4, a7
	srli a4, a4, 19
	slli a4, a4, 63
	srli a4, a4, 57
	add a5, a5, a4
	lwu a4, 28(a0)
	mul a4, a4, a6
	add a4, a4, a7
	srli a4, a4, 19
	slli a4, a4, 63
	srli a4, a4, 56
	add a5, a5, a4
	sb a5, 0(a2)
	addi a0, a0, 32
	addi a2, a2, 1
	addi t1, t1, -1
	bnez t1, 26b
21:
	ret
	.option pop

vg_mlkem_decode_decompress:
	.option push
	.option arch, +m, +c
	slli a2, a2, 32
	srli a2, a2, 32
	lui a6, 1
	addi a6, a6, -767
	addi a4, a2, -1
	beqz a4, 20f
	addi a4, a2, -4
	beqz a4, 22f
	addi t1, zero, 64
24:
	lbu a5, 0(a0)
	lbu a4, 1(a0)
	slli a4, a4, 8
	add a5, a5, a4
	lbu a4, 2(a0)
	slli a4, a4, 16
	add a5, a5, a4
	lbu a4, 3(a0)
	slli a4, a4, 24
	add a5, a5, a4
	lbu a4, 4(a0)
	slli a4, a4, 32
	add a5, a5, a4
	slli a4, a5, 54
	srli a4, a4, 54
	mul a4, a4, a6
	addi a4, a4, 512
	srli a4, a4, 10
	sw a4, 0(a3)
	slli a4, a5, 44
	srli a4, a4, 54
	mul a4, a4, a6
	addi a4, a4, 512
	srli a4, a4, 10
	sw a4, 4(a3)
	slli a4, a5, 34
	srli a4, a4, 54
	mul a4, a4, a6
	addi a4, a4, 512
	srli a4, a4, 10
	sw a4, 8(a3)
	slli a4, a5, 24
	srli a4, a4, 54
	mul a4, a4, a6
	addi a4, a4, 512
	srli a4, a4, 10
	sw a4, 12(a3)
	addi a0, a0, 5
	addi a3, a3, 16
	addi t1, t1, -1
	bnez t1, 24b
	j 23f
22:
	addi t1, zero, 128
25:
	lbu a5, 0(a0)
	slli a4, a5, 60
	srli a4, a4, 60
	mul a4, a4, a6
	addi a4, a4, 8
	srli a4, a4, 4
	sw a4, 0(a3)
	srli a4, a5, 4
	mul a4, a4, a6
	addi a4, a4, 8
	srli a4, a4, 4
	sw a4, 4(a3)
	addi a0, a0, 1
	addi a3, a3, 8
	addi t1, t1, -1
	bnez t1, 25b
23:
	j 21f
20:
	addi t1, zero, 32
26:
	lbu a5, 0(a0)
	slli a4, a5, 63
	srli a4, a4, 63
	mul a4, a4, a6
	addi a4, a4, 1
	srli a4, a4, 1
	sw a4, 0(a3)
	slli a4, a5, 62
	srli a4, a4, 63
	mul a4, a4, a6
	addi a4, a4, 1
	srli a4, a4, 1
	sw a4, 4(a3)
	slli a4, a5, 61
	srli a4, a4, 63
	mul a4, a4, a6
	addi a4, a4, 1
	srli a4, a4, 1
	sw a4, 8(a3)
	slli a4, a5, 60
	srli a4, a4, 63
	mul a4, a4, a6
	addi a4, a4, 1
	srli a4, a4, 1
	sw a4, 12(a3)
	slli a4, a5, 59
	srli a4, a4, 63
	mul a4, a4, a6
	addi a4, a4, 1
	srli a4, a4, 1
	sw a4, 16(a3)
	slli a4, a5, 58
	srli a4, a4, 63
	mul a4, a4, a6
	addi a4, a4, 1
	srli a4, a4, 1
	sw a4, 20(a3)
	slli a4, a5, 57
	srli a4, a4, 63
	mul a4, a4, a6
	addi a4, a4, 1
	srli a4, a4, 1
	sw a4, 24(a3)
	slli a4, a5, 56
	srli a4, a4, 63
	mul a4, a4, a6
	addi a4, a4, 1
	srli a4, a4, 1
	sw a4, 28(a3)
	addi a0, a0, 1
	addi a3, a3, 32
	addi t1, t1, -1
	bnez t1, 26b
21:
	ret
	.option pop
