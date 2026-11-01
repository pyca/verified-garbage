// The functions of `src/internal/vg_mlkem_multiply_ntts.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

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
