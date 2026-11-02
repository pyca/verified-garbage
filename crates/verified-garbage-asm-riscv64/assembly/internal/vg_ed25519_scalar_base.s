// The functions of `src/internal/vg_ed25519_scalar_base.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed25519_scalar_base:
	.option push
	.option arch, +m, +c
	addi a3, a2, 0
	sd s0, 1024(a3)
	sd s1, 1032(a3)
	sd s2, 1040(a3)
	sd s3, 1048(a3)
	sd s5, 1056(a3)
	sd s6, 1064(a3)
	sd ra, 1072(a3)
	addi s3, a0, 0
	addi s0, a1, 0
	addi a4, zero, 0
	sw a4, 64(a3)
	sw a4, 68(a3)
	sw a4, 72(a3)
	sw a4, 76(a3)
	sw a4, 80(a3)
	sw a4, 84(a3)
	sw a4, 88(a3)
	sw a4, 92(a3)
	sw a4, 96(a3)
	sw a4, 100(a3)
	sw a4, 104(a3)
	sw a4, 108(a3)
	sw a4, 112(a3)
	sw a4, 116(a3)
	sw a4, 120(a3)
	sw a4, 124(a3)
	sw a4, 128(a3)
	sw a4, 132(a3)
	sw a4, 136(a3)
	sw a4, 140(a3)
	sw a4, 144(a3)
	sw a4, 148(a3)
	sw a4, 152(a3)
	sw a4, 156(a3)
	sw a4, 160(a3)
	sw a4, 164(a3)
	sw a4, 168(a3)
	sw a4, 172(a3)
	sw a4, 176(a3)
	sw a4, 180(a3)
	sw a4, 184(a3)
	sw a4, 188(a3)
	sw a4, 192(a3)
	sw a4, 196(a3)
	sw a4, 200(a3)
	sw a4, 204(a3)
	sw a4, 208(a3)
	sw a4, 212(a3)
	sw a4, 216(a3)
	sw a4, 220(a3)
	sw a4, 224(a3)
	sw a4, 228(a3)
	sw a4, 232(a3)
	sw a4, 236(a3)
	sw a4, 240(a3)
	sw a4, 244(a3)
	sw a4, 248(a3)
	sw a4, 252(a3)
	sw a4, 256(a3)
	sw a4, 260(a3)
	sw a4, 264(a3)
	sw a4, 268(a3)
	sw a4, 272(a3)
	sw a4, 276(a3)
	sw a4, 280(a3)
	sw a4, 284(a3)
	sw a4, 288(a3)
	sw a4, 292(a3)
	sw a4, 296(a3)
	sw a4, 300(a3)
	sw a4, 304(a3)
	sw a4, 308(a3)
	sw a4, 312(a3)
	sw a4, 316(a3)
	sw a4, 320(a3)
	sw a4, 324(a3)
	sw a4, 328(a3)
	sw a4, 332(a3)
	sw a4, 336(a3)
	sw a4, 340(a3)
	sw a4, 344(a3)
	sw a4, 348(a3)
	sw a4, 352(a3)
	sw a4, 356(a3)
	sw a4, 360(a3)
	sw a4, 364(a3)
	sw a4, 368(a3)
	sw a4, 372(a3)
	sw a4, 376(a3)
	sw a4, 380(a3)
	sw a4, 384(a3)
	sw a4, 388(a3)
	sw a4, 392(a3)
	sw a4, 396(a3)
	sw a4, 400(a3)
	sw a4, 404(a3)
	sw a4, 408(a3)
	sw a4, 412(a3)
	sw a4, 416(a3)
	sw a4, 420(a3)
	sw a4, 424(a3)
	sw a4, 428(a3)
	sw a4, 432(a3)
	sw a4, 436(a3)
	sw a4, 440(a3)
	sw a4, 444(a3)
	sw a4, 448(a3)
	sw a4, 452(a3)
	sw a4, 456(a3)
	sw a4, 460(a3)
	sw a4, 464(a3)
	sw a4, 468(a3)
	sw a4, 472(a3)
	sw a4, 476(a3)
	sw a4, 480(a3)
	sw a4, 484(a3)
	sw a4, 488(a3)
	sw a4, 492(a3)
	sw a4, 496(a3)
	sw a4, 500(a3)
	sw a4, 504(a3)
	sw a4, 508(a3)
	sw a4, 512(a3)
	sw a4, 516(a3)
	sw a4, 520(a3)
	sw a4, 524(a3)
	sw a4, 528(a3)
	sw a4, 532(a3)
	sw a4, 536(a3)
	sw a4, 540(a3)
	sw a4, 544(a3)
	sw a4, 548(a3)
	sw a4, 552(a3)
	sw a4, 556(a3)
	sw a4, 560(a3)
	sw a4, 564(a3)
	sw a4, 568(a3)
	sw a4, 572(a3)
	sw a4, 576(a3)
	sw a4, 580(a3)
	sw a4, 584(a3)
	sw a4, 588(a3)
	sw a4, 592(a3)
	sw a4, 596(a3)
	sw a4, 600(a3)
	sw a4, 604(a3)
	sw a4, 608(a3)
	sw a4, 612(a3)
	sw a4, 616(a3)
	sw a4, 620(a3)
	sw a4, 624(a3)
	sw a4, 628(a3)
	sw a4, 632(a3)
	sw a4, 636(a3)
	sw a4, 640(a3)
	sw a4, 644(a3)
	sw a4, 648(a3)
	sw a4, 652(a3)
	sw a4, 656(a3)
	sw a4, 660(a3)
	sw a4, 664(a3)
	sw a4, 668(a3)
	sw a4, 672(a3)
	sw a4, 676(a3)
	sw a4, 680(a3)
	sw a4, 684(a3)
	sw a4, 688(a3)
	sw a4, 692(a3)
	sw a4, 696(a3)
	sw a4, 700(a3)
	sw a4, 704(a3)
	sw a4, 708(a3)
	sw a4, 712(a3)
	sw a4, 716(a3)
	sw a4, 720(a3)
	sw a4, 724(a3)
	sw a4, 728(a3)
	sw a4, 732(a3)
	sw a4, 736(a3)
	sw a4, 740(a3)
	sw a4, 744(a3)
	sw a4, 748(a3)
	sw a4, 752(a3)
	sw a4, 756(a3)
	sw a4, 760(a3)
	sw a4, 764(a3)
	lbu a4, 0(s0)
	sb a4, 1152(a3)
	lbu a4, 1(s0)
	sb a4, 1153(a3)
	lbu a4, 2(s0)
	sb a4, 1154(a3)
	lbu a4, 3(s0)
	sb a4, 1155(a3)
	lbu a4, 4(s0)
	sb a4, 1156(a3)
	lbu a4, 5(s0)
	sb a4, 1157(a3)
	lbu a4, 6(s0)
	sb a4, 1158(a3)
	lbu a4, 7(s0)
	sb a4, 1159(a3)
	lbu a4, 8(s0)
	sb a4, 1160(a3)
	lbu a4, 9(s0)
	sb a4, 1161(a3)
	lbu a4, 10(s0)
	sb a4, 1162(a3)
	lbu a4, 11(s0)
	sb a4, 1163(a3)
	lbu a4, 12(s0)
	sb a4, 1164(a3)
	lbu a4, 13(s0)
	sb a4, 1165(a3)
	lbu a4, 14(s0)
	sb a4, 1166(a3)
	lbu a4, 15(s0)
	sb a4, 1167(a3)
	lbu a4, 16(s0)
	sb a4, 1168(a3)
	lbu a4, 17(s0)
	sb a4, 1169(a3)
	lbu a4, 18(s0)
	sb a4, 1170(a3)
	lbu a4, 19(s0)
	sb a4, 1171(a3)
	lbu a4, 20(s0)
	sb a4, 1172(a3)
	lbu a4, 21(s0)
	sb a4, 1173(a3)
	lbu a4, 22(s0)
	sb a4, 1174(a3)
	lbu a4, 23(s0)
	sb a4, 1175(a3)
	lbu a4, 24(s0)
	sb a4, 1176(a3)
	lbu a4, 25(s0)
	sb a4, 1177(a3)
	lbu a4, 26(s0)
	sb a4, 1178(a3)
	lbu a4, 27(s0)
	sb a4, 1179(a3)
	lbu a4, 28(s0)
	sb a4, 1180(a3)
	lbu a4, 29(s0)
	sb a4, 1181(a3)
	lbu a4, 30(s0)
	sb a4, 1182(a3)
	lbu a4, 31(s0)
	sb a4, 1183(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 736(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 740(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 744(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 748(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 752(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 756(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 760(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 764(a3)
	lui a4, 59269
	addiw a4, a4, -748
	sw a4, 64(a3)
	lui a4, 152099
	addiw a4, a4, 639
	sw a4, 68(a3)
	lui a4, 724337
	addiw a4, a4, 1309
	sw a4, 72(a3)
	lui a4, 52686
	addiw a4, a4, -1462
	sw a4, 76(a3)
	lui a4, 577950
	addiw a4, a4, -1092
	sw a4, 80(a3)
	lui a4, 391648
	addiw a4, a4, 1244
	sw a4, 84(a3)
	lui a4, 214434
	addiw a4, a4, -1260
	sw a4, 88(a3)
	lui a4, 42111
	addiw a4, a4, 1382
	sw a4, 92(a3)
	lui a4, 114447
	addiw a4, a4, 1772
	sw a4, 96(a3)
	lui a4, 676747
	addiw a4, a4, 1447
	sw a4, 100(a3)
	lui a4, 373398
	addiw a4, a4, -1733
	sw a4, 104(a3)
	lui a4, 95100
	addiw a4, a4, -1872
	sw a4, 108(a3)
	lui a4, 635549
	addiw a4, a4, -1543
	sw a4, 112(a3)
	lui a4, 202438
	addiw a4, a4, -1641
	sw a4, 116(a3)
	lui a4, 219248
	addiw a4, a4, 638
	sw a4, 120(a3)
	lui a4, 37940
	addiw a4, a4, 1846
	sw a4, 124(a3)
	lui a4, 0
	addiw a4, a4, 1
	sw a4, 128(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 132(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 136(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 140(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 144(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 148(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 152(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 156(a3)
	lui a4, 283157
	addiw a4, a4, 613
	sw a4, 160(a3)
	lui a4, 840964
	addiw a4, a4, 1802
	sw a4, 164(a3)
	lui a4, 49146
	addiw a4, a4, -521
	sw a4, 168(a3)
	lui a4, 1023042
	addiw a4, a4, 501
	sw a4, 172(a3)
	lui a4, 928872
	addiw a4, a4, -439
	sw a4, 176(a3)
	lui a4, 58152
	addiw a4, a4, 273
	sw a4, 180(a3)
	lui a4, 861116
	addiw a4, a4, 288
	sw a4, 184(a3)
	lui a4, 231641
	addiw a4, a4, 1414
	sw a4, 188(a3)
	addi s1, zero, 0
	lla s2, {VG_ED25519_COMB}
20:
	srli a1, s1, 1
	add a1, a3, a1
	lbu a2, 1152(a1)
	andi t0, s1, 1
	slli t0, t0, 2
	srl a4, a2, t0
	andi a4, a4, 15
	addi a0, zero, 0
	addi a4, a4, -8
	srli a5, a4, 63
	sub a5, a0, a5
	sd a5, 56(a3)
	xor a4, a4, a5
	sub a4, a4, a5
	xori t1, a4, 1
	addi t1, t1, -1
	srli t1, t1, 63
	sub t1, a0, t1
	xori t2, a4, 2
	addi t2, t2, -1
	srli t2, t2, 63
	sub t2, a0, t2
	xori t3, a4, 3
	addi t3, t3, -1
	srli t3, t3, 63
	sub t3, a0, t3
	xori t4, a4, 4
	addi t4, t4, -1
	srli t4, t4, 63
	sub t4, a0, t4
	xori t5, a4, 5
	addi t5, t5, -1
	srli t5, t5, 63
	sub t5, a0, t5
	xori t6, a4, 6
	addi t6, t6, -1
	srli t6, t6, 63
	sub t6, a0, t6
	xori a6, a4, 7
	addi a6, a6, -1
	srli a6, a6, 63
	sub a6, a0, a6
	xori a7, a4, 8
	addi a7, a7, -1
	srli a7, a7, 63
	sub a7, a0, a7
	sltu t0, a0, a4
	xori t0, t0, 1
	addi a4, t0, 0
	ld a5, 0(s2)
	and a5, a5, t1
	or a4, a4, a5
	ld a5, 96(s2)
	and a5, a5, t2
	or a4, a4, a5
	ld a5, 192(s2)
	and a5, a5, t3
	or a4, a4, a5
	ld a5, 288(s2)
	and a5, a5, t4
	or a4, a4, a5
	ld a5, 384(s2)
	and a5, a5, t5
	or a4, a4, a5
	ld a5, 480(s2)
	and a5, a5, t6
	or a4, a4, a5
	ld a5, 576(s2)
	and a5, a5, a6
	or a4, a4, a5
	ld a5, 672(s2)
	and a5, a5, a7
	or a4, a4, a5
	sd a4, 192(a3)
	addi a4, zero, 0
	ld a5, 8(s2)
	and a5, a5, t1
	or a4, a4, a5
	ld a5, 104(s2)
	and a5, a5, t2
	or a4, a4, a5
	ld a5, 200(s2)
	and a5, a5, t3
	or a4, a4, a5
	ld a5, 296(s2)
	and a5, a5, t4
	or a4, a4, a5
	ld a5, 392(s2)
	and a5, a5, t5
	or a4, a4, a5
	ld a5, 488(s2)
	and a5, a5, t6
	or a4, a4, a5
	ld a5, 584(s2)
	and a5, a5, a6
	or a4, a4, a5
	ld a5, 680(s2)
	and a5, a5, a7
	or a4, a4, a5
	sd a4, 200(a3)
	addi a4, zero, 0
	ld a5, 16(s2)
	and a5, a5, t1
	or a4, a4, a5
	ld a5, 112(s2)
	and a5, a5, t2
	or a4, a4, a5
	ld a5, 208(s2)
	and a5, a5, t3
	or a4, a4, a5
	ld a5, 304(s2)
	and a5, a5, t4
	or a4, a4, a5
	ld a5, 400(s2)
	and a5, a5, t5
	or a4, a4, a5
	ld a5, 496(s2)
	and a5, a5, t6
	or a4, a4, a5
	ld a5, 592(s2)
	and a5, a5, a6
	or a4, a4, a5
	ld a5, 688(s2)
	and a5, a5, a7
	or a4, a4, a5
	sd a4, 208(a3)
	addi a4, zero, 0
	ld a5, 24(s2)
	and a5, a5, t1
	or a4, a4, a5
	ld a5, 120(s2)
	and a5, a5, t2
	or a4, a4, a5
	ld a5, 216(s2)
	and a5, a5, t3
	or a4, a4, a5
	ld a5, 312(s2)
	and a5, a5, t4
	or a4, a4, a5
	ld a5, 408(s2)
	and a5, a5, t5
	or a4, a4, a5
	ld a5, 504(s2)
	and a5, a5, t6
	or a4, a4, a5
	ld a5, 600(s2)
	and a5, a5, a6
	or a4, a4, a5
	ld a5, 696(s2)
	and a5, a5, a7
	or a4, a4, a5
	sd a4, 216(a3)
	addi a4, t0, 0
	ld a5, 32(s2)
	and a5, a5, t1
	or a4, a4, a5
	ld a5, 128(s2)
	and a5, a5, t2
	or a4, a4, a5
	ld a5, 224(s2)
	and a5, a5, t3
	or a4, a4, a5
	ld a5, 320(s2)
	and a5, a5, t4
	or a4, a4, a5
	ld a5, 416(s2)
	and a5, a5, t5
	or a4, a4, a5
	ld a5, 512(s2)
	and a5, a5, t6
	or a4, a4, a5
	ld a5, 608(s2)
	and a5, a5, a6
	or a4, a4, a5
	ld a5, 704(s2)
	and a5, a5, a7
	or a4, a4, a5
	sd a4, 224(a3)
	addi a4, zero, 0
	ld a5, 40(s2)
	and a5, a5, t1
	or a4, a4, a5
	ld a5, 136(s2)
	and a5, a5, t2
	or a4, a4, a5
	ld a5, 232(s2)
	and a5, a5, t3
	or a4, a4, a5
	ld a5, 328(s2)
	and a5, a5, t4
	or a4, a4, a5
	ld a5, 424(s2)
	and a5, a5, t5
	or a4, a4, a5
	ld a5, 520(s2)
	and a5, a5, t6
	or a4, a4, a5
	ld a5, 616(s2)
	and a5, a5, a6
	or a4, a4, a5
	ld a5, 712(s2)
	and a5, a5, a7
	or a4, a4, a5
	sd a4, 232(a3)
	addi a4, zero, 0
	ld a5, 48(s2)
	and a5, a5, t1
	or a4, a4, a5
	ld a5, 144(s2)
	and a5, a5, t2
	or a4, a4, a5
	ld a5, 240(s2)
	and a5, a5, t3
	or a4, a4, a5
	ld a5, 336(s2)
	and a5, a5, t4
	or a4, a4, a5
	ld a5, 432(s2)
	and a5, a5, t5
	or a4, a4, a5
	ld a5, 528(s2)
	and a5, a5, t6
	or a4, a4, a5
	ld a5, 624(s2)
	and a5, a5, a6
	or a4, a4, a5
	ld a5, 720(s2)
	and a5, a5, a7
	or a4, a4, a5
	sd a4, 240(a3)
	addi a4, zero, 0
	ld a5, 56(s2)
	and a5, a5, t1
	or a4, a4, a5
	ld a5, 152(s2)
	and a5, a5, t2
	or a4, a4, a5
	ld a5, 248(s2)
	and a5, a5, t3
	or a4, a4, a5
	ld a5, 344(s2)
	and a5, a5, t4
	or a4, a4, a5
	ld a5, 440(s2)
	and a5, a5, t5
	or a4, a4, a5
	ld a5, 536(s2)
	and a5, a5, t6
	or a4, a4, a5
	ld a5, 632(s2)
	and a5, a5, a6
	or a4, a4, a5
	ld a5, 728(s2)
	and a5, a5, a7
	or a4, a4, a5
	sd a4, 248(a3)
	addi a4, zero, 0
	ld a5, 64(s2)
	and a5, a5, t1
	or a4, a4, a5
	ld a5, 160(s2)
	and a5, a5, t2
	or a4, a4, a5
	ld a5, 256(s2)
	and a5, a5, t3
	or a4, a4, a5
	ld a5, 352(s2)
	and a5, a5, t4
	or a4, a4, a5
	ld a5, 448(s2)
	and a5, a5, t5
	or a4, a4, a5
	ld a5, 544(s2)
	and a5, a5, t6
	or a4, a4, a5
	ld a5, 640(s2)
	and a5, a5, a6
	or a4, a4, a5
	ld a5, 736(s2)
	and a5, a5, a7
	or a4, a4, a5
	sd a4, 256(a3)
	addi a4, zero, 0
	ld a5, 72(s2)
	and a5, a5, t1
	or a4, a4, a5
	ld a5, 168(s2)
	and a5, a5, t2
	or a4, a4, a5
	ld a5, 264(s2)
	and a5, a5, t3
	or a4, a4, a5
	ld a5, 360(s2)
	and a5, a5, t4
	or a4, a4, a5
	ld a5, 456(s2)
	and a5, a5, t5
	or a4, a4, a5
	ld a5, 552(s2)
	and a5, a5, t6
	or a4, a4, a5
	ld a5, 648(s2)
	and a5, a5, a6
	or a4, a4, a5
	ld a5, 744(s2)
	and a5, a5, a7
	or a4, a4, a5
	sd a4, 264(a3)
	addi a4, zero, 0
	ld a5, 80(s2)
	and a5, a5, t1
	or a4, a4, a5
	ld a5, 176(s2)
	and a5, a5, t2
	or a4, a4, a5
	ld a5, 272(s2)
	and a5, a5, t3
	or a4, a4, a5
	ld a5, 368(s2)
	and a5, a5, t4
	or a4, a4, a5
	ld a5, 464(s2)
	and a5, a5, t5
	or a4, a4, a5
	ld a5, 560(s2)
	and a5, a5, t6
	or a4, a4, a5
	ld a5, 656(s2)
	and a5, a5, a6
	or a4, a4, a5
	ld a5, 752(s2)
	and a5, a5, a7
	or a4, a4, a5
	sd a4, 272(a3)
	addi a4, zero, 0
	ld a5, 88(s2)
	and a5, a5, t1
	or a4, a4, a5
	ld a5, 184(s2)
	and a5, a5, t2
	or a4, a4, a5
	ld a5, 280(s2)
	and a5, a5, t3
	or a4, a4, a5
	ld a5, 376(s2)
	and a5, a5, t4
	or a4, a4, a5
	ld a5, 472(s2)
	and a5, a5, t5
	or a4, a4, a5
	ld a5, 568(s2)
	and a5, a5, t6
	or a4, a4, a5
	ld a5, 664(s2)
	and a5, a5, a6
	or a4, a4, a5
	ld a5, 760(s2)
	and a5, a5, a7
	or a4, a4, a5
	sd a4, 280(a3)
	ld t3, 736(a3)
	ld a7, 256(a3)
	sltu a5, t3, a7
	sub t3, t3, a7
	ld t4, 744(a3)
	ld a7, 264(a3)
	sltu a6, t4, a7
	sub t4, t4, a7
	sltu a7, t4, a5
	sub t4, t4, a5
	add a5, a6, a7
	ld t5, 752(a3)
	ld a7, 272(a3)
	sltu a6, t5, a7
	sub t5, t5, a7
	sltu a7, t5, a5
	sub t5, t5, a5
	add a5, a6, a7
	ld t6, 760(a3)
	ld a7, 280(a3)
	sltu a6, t6, a7
	sub t6, t6, a7
	sltu a7, t6, a5
	sub t6, t6, a5
	add a5, a6, a7
	addi a4, zero, 38
	mul a7, a5, a4
	sltu t0, t3, a7
	sub t3, t3, a7
	sltu a7, t4, t0
	sub t4, t4, t0
	sltu t0, t5, a7
	sub t5, t5, a7
	sltu a5, t6, t0
	sub t6, t6, t0
	mul a7, a5, a4
	sltu t0, t3, a7
	sub t3, t3, a7
	sltu a7, t4, t0
	sub t4, t4, t0
	sltu t0, t5, a7
	sub t5, t5, a7
	sltu a5, t6, t0
	sub t6, t6, t0
	sd t3, 288(a3)
	sd t4, 296(a3)
	sd t5, 304(a3)
	sd t6, 312(a3)
	ld t0, 56(a3)
	lwu a2, 192(a3)
	lwu a4, 224(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 192(a3)
	sw a4, 224(a3)
	lwu a2, 196(a3)
	lwu a4, 228(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 196(a3)
	sw a4, 228(a3)
	lwu a2, 200(a3)
	lwu a4, 232(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 200(a3)
	sw a4, 232(a3)
	lwu a2, 204(a3)
	lwu a4, 236(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 204(a3)
	sw a4, 236(a3)
	lwu a2, 208(a3)
	lwu a4, 240(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 208(a3)
	sw a4, 240(a3)
	lwu a2, 212(a3)
	lwu a4, 244(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 212(a3)
	sw a4, 244(a3)
	lwu a2, 216(a3)
	lwu a4, 248(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 216(a3)
	sw a4, 248(a3)
	lwu a2, 220(a3)
	lwu a4, 252(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 220(a3)
	sw a4, 252(a3)
	lwu a2, 256(a3)
	lwu a4, 288(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 256(a3)
	sw a4, 288(a3)
	lwu a2, 260(a3)
	lwu a4, 292(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 260(a3)
	sw a4, 292(a3)
	lwu a2, 264(a3)
	lwu a4, 296(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 264(a3)
	sw a4, 296(a3)
	lwu a2, 268(a3)
	lwu a4, 300(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 268(a3)
	sw a4, 300(a3)
	lwu a2, 272(a3)
	lwu a4, 304(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 272(a3)
	sw a4, 304(a3)
	lwu a2, 276(a3)
	lwu a4, 308(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 276(a3)
	sw a4, 308(a3)
	lwu a2, 280(a3)
	lwu a4, 312(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 280(a3)
	sw a4, 312(a3)
	lwu a2, 284(a3)
	lwu a4, 316(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 284(a3)
	sw a4, 316(a3)
	ld t3, 96(a3)
	ld a7, 64(a3)
	sltu a5, t3, a7
	sub t3, t3, a7
	ld t4, 104(a3)
	ld a7, 72(a3)
	sltu a6, t4, a7
	sub t4, t4, a7
	sltu a7, t4, a5
	sub t4, t4, a5
	add a5, a6, a7
	ld t5, 112(a3)
	ld a7, 80(a3)
	sltu a6, t5, a7
	sub t5, t5, a7
	sltu a7, t5, a5
	sub t5, t5, a5
	add a5, a6, a7
	ld t6, 120(a3)
	ld a7, 88(a3)
	sltu a6, t6, a7
	sub t6, t6, a7
	sltu a7, t6, a5
	sub t6, t6, a5
	add a5, a6, a7
	addi a4, zero, 38
	mul a7, a5, a4
	sltu t0, t3, a7
	sub t3, t3, a7
	sltu a7, t4, t0
	sub t4, t4, t0
	sltu t0, t5, a7
	sub t5, t5, a7
	sltu a5, t6, t0
	sub t6, t6, t0
	mul a7, a5, a4
	sltu t0, t3, a7
	sub t3, t3, a7
	sltu a7, t4, t0
	sub t4, t4, t0
	sltu t0, t5, a7
	sub t5, t5, a7
	sltu a5, t6, t0
	sub t6, t6, t0
	sd t3, 320(a3)
	sd t4, 328(a3)
	sd t5, 336(a3)
	sd t6, 344(a3)
	ld t3, 192(a3)
	ld t4, 200(a3)
	ld t5, 208(a3)
	ld t6, 216(a3)
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	ld t0, 320(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 864(a3)
	addi a4, zero, 0
	ld t0, 328(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 320(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 872(a3)
	addi a5, zero, 0
	ld t0, 336(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 328(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 320(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 880(a3)
	addi a6, zero, 0
	ld t0, 344(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 336(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 328(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 320(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 888(a3)
	addi a4, zero, 0
	ld t0, 344(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 336(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 328(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 896(a3)
	addi a5, zero, 0
	ld t0, 344(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 336(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 904(a3)
	addi a6, zero, 0
	ld t0, 344(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 912(a3)
	addi a4, zero, 0
	sd a5, 920(a3)
	addi a5, zero, 0
	addi a4, zero, 38
	ld t3, 864(a3)
	ld a7, 896(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t3, t3, t0
	sltu a5, t3, t0
	ld t4, 872(a3)
	ld a7, 904(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t4, t4, t0
	sltu a6, t4, t0
	add t4, t4, a1
	sltu a7, t4, a1
	add a6, a6, a7
	add t4, t4, a5
	sltu a7, t4, a5
	add a6, a6, a7
	ld t5, 880(a3)
	ld a7, 912(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t5, t5, t0
	sltu a5, t5, t0
	add t5, t5, a2
	sltu a7, t5, a2
	add a5, a5, a7
	add t5, t5, a6
	sltu a7, t5, a6
	add a5, a5, a7
	ld t6, 888(a3)
	ld a7, 920(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t6, t6, t0
	sltu a6, t6, t0
	add t6, t6, a1
	sltu a7, t6, a1
	add a6, a6, a7
	add t6, t6, a5
	sltu a7, t6, a5
	add a6, a6, a7
	add a5, a2, a6
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	sd t3, 320(a3)
	sd t4, 328(a3)
	sd t5, 336(a3)
	sd t6, 344(a3)
	ld t3, 96(a3)
	ld a7, 64(a3)
	add t3, t3, a7
	sltu a5, t3, a7
	ld t4, 104(a3)
	ld a7, 72(a3)
	add t4, t4, a7
	sltu a6, t4, a7
	add t4, t4, a5
	sltu a7, t4, a5
	add a5, a6, a7
	ld t5, 112(a3)
	ld a7, 80(a3)
	add t5, t5, a7
	sltu a6, t5, a7
	add t5, t5, a5
	sltu a7, t5, a5
	add a5, a6, a7
	ld t6, 120(a3)
	ld a7, 88(a3)
	add t6, t6, a7
	sltu a6, t6, a7
	add t6, t6, a5
	sltu a7, t6, a5
	add a5, a6, a7
	addi a4, zero, 38
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	sd t3, 352(a3)
	sd t4, 360(a3)
	sd t5, 368(a3)
	sd t6, 376(a3)
	ld t3, 224(a3)
	ld t4, 232(a3)
	ld t5, 240(a3)
	ld t6, 248(a3)
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	ld t0, 352(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 864(a3)
	addi a4, zero, 0
	ld t0, 360(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 352(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 872(a3)
	addi a5, zero, 0
	ld t0, 368(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 360(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 352(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 880(a3)
	addi a6, zero, 0
	ld t0, 376(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 368(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 360(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 352(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 888(a3)
	addi a4, zero, 0
	ld t0, 376(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 368(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 360(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 896(a3)
	addi a5, zero, 0
	ld t0, 376(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 368(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 904(a3)
	addi a6, zero, 0
	ld t0, 376(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 912(a3)
	addi a4, zero, 0
	sd a5, 920(a3)
	addi a5, zero, 0
	addi a4, zero, 38
	ld t3, 864(a3)
	ld a7, 896(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t3, t3, t0
	sltu a5, t3, t0
	ld t4, 872(a3)
	ld a7, 904(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t4, t4, t0
	sltu a6, t4, t0
	add t4, t4, a1
	sltu a7, t4, a1
	add a6, a6, a7
	add t4, t4, a5
	sltu a7, t4, a5
	add a6, a6, a7
	ld t5, 880(a3)
	ld a7, 912(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t5, t5, t0
	sltu a5, t5, t0
	add t5, t5, a2
	sltu a7, t5, a2
	add a5, a5, a7
	add t5, t5, a6
	sltu a7, t5, a6
	add a5, a5, a7
	ld t6, 888(a3)
	ld a7, 920(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t6, t6, t0
	sltu a6, t6, t0
	add t6, t6, a1
	sltu a7, t6, a1
	add a6, a6, a7
	add t6, t6, a5
	sltu a7, t6, a5
	add a6, a6, a7
	add a5, a2, a6
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	sd t3, 352(a3)
	sd t4, 360(a3)
	sd t5, 368(a3)
	sd t6, 376(a3)
	ld t3, 256(a3)
	ld t4, 264(a3)
	ld t5, 272(a3)
	ld t6, 280(a3)
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	ld t0, 160(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 864(a3)
	addi a4, zero, 0
	ld t0, 168(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 160(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 872(a3)
	addi a5, zero, 0
	ld t0, 176(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 168(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 160(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 880(a3)
	addi a6, zero, 0
	ld t0, 184(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 176(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 168(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 160(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 888(a3)
	addi a4, zero, 0
	ld t0, 184(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 176(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 168(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 896(a3)
	addi a5, zero, 0
	ld t0, 184(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 176(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 904(a3)
	addi a6, zero, 0
	ld t0, 184(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 912(a3)
	addi a4, zero, 0
	sd a5, 920(a3)
	addi a5, zero, 0
	addi a4, zero, 38
	ld t3, 864(a3)
	ld a7, 896(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t3, t3, t0
	sltu a5, t3, t0
	ld t4, 872(a3)
	ld a7, 904(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t4, t4, t0
	sltu a6, t4, t0
	add t4, t4, a1
	sltu a7, t4, a1
	add a6, a6, a7
	add t4, t4, a5
	sltu a7, t4, a5
	add a6, a6, a7
	ld t5, 880(a3)
	ld a7, 912(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t5, t5, t0
	sltu a5, t5, t0
	add t5, t5, a2
	sltu a7, t5, a2
	add a5, a5, a7
	add t5, t5, a6
	sltu a7, t5, a6
	add a5, a5, a7
	ld t6, 888(a3)
	ld a7, 920(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t6, t6, t0
	sltu a6, t6, t0
	add t6, t6, a1
	sltu a7, t6, a1
	add a6, a6, a7
	add t6, t6, a5
	sltu a7, t6, a5
	add a6, a6, a7
	add a5, a2, a6
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	sd t3, 384(a3)
	sd t4, 392(a3)
	sd t5, 400(a3)
	sd t6, 408(a3)
	ld t3, 128(a3)
	ld a7, 128(a3)
	add t3, t3, a7
	sltu a5, t3, a7
	ld t4, 136(a3)
	ld a7, 136(a3)
	add t4, t4, a7
	sltu a6, t4, a7
	add t4, t4, a5
	sltu a7, t4, a5
	add a5, a6, a7
	ld t5, 144(a3)
	ld a7, 144(a3)
	add t5, t5, a7
	sltu a6, t5, a7
	add t5, t5, a5
	sltu a7, t5, a5
	add a5, a6, a7
	ld t6, 152(a3)
	ld a7, 152(a3)
	add t6, t6, a7
	sltu a6, t6, a7
	add t6, t6, a5
	sltu a7, t6, a5
	add a5, a6, a7
	addi a4, zero, 38
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	sd t3, 416(a3)
	sd t4, 424(a3)
	sd t5, 432(a3)
	sd t6, 440(a3)
	ld t3, 352(a3)
	ld a7, 320(a3)
	sltu a5, t3, a7
	sub t3, t3, a7
	ld t4, 360(a3)
	ld a7, 328(a3)
	sltu a6, t4, a7
	sub t4, t4, a7
	sltu a7, t4, a5
	sub t4, t4, a5
	add a5, a6, a7
	ld t5, 368(a3)
	ld a7, 336(a3)
	sltu a6, t5, a7
	sub t5, t5, a7
	sltu a7, t5, a5
	sub t5, t5, a5
	add a5, a6, a7
	ld t6, 376(a3)
	ld a7, 344(a3)
	sltu a6, t6, a7
	sub t6, t6, a7
	sltu a7, t6, a5
	sub t6, t6, a5
	add a5, a6, a7
	addi a4, zero, 38
	mul a7, a5, a4
	sltu t0, t3, a7
	sub t3, t3, a7
	sltu a7, t4, t0
	sub t4, t4, t0
	sltu t0, t5, a7
	sub t5, t5, a7
	sltu a5, t6, t0
	sub t6, t6, t0
	mul a7, a5, a4
	sltu t0, t3, a7
	sub t3, t3, a7
	sltu a7, t4, t0
	sub t4, t4, t0
	sltu t0, t5, a7
	sub t5, t5, a7
	sltu a5, t6, t0
	sub t6, t6, t0
	sd t3, 448(a3)
	sd t4, 456(a3)
	sd t5, 464(a3)
	sd t6, 472(a3)
	ld t3, 352(a3)
	ld a7, 320(a3)
	add t3, t3, a7
	sltu a5, t3, a7
	ld t4, 360(a3)
	ld a7, 328(a3)
	add t4, t4, a7
	sltu a6, t4, a7
	add t4, t4, a5
	sltu a7, t4, a5
	add a5, a6, a7
	ld t5, 368(a3)
	ld a7, 336(a3)
	add t5, t5, a7
	sltu a6, t5, a7
	add t5, t5, a5
	sltu a7, t5, a5
	add a5, a6, a7
	ld t6, 376(a3)
	ld a7, 344(a3)
	add t6, t6, a7
	sltu a6, t6, a7
	add t6, t6, a5
	sltu a7, t6, a5
	add a5, a6, a7
	addi a4, zero, 38
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	sd t3, 480(a3)
	sd t4, 488(a3)
	sd t5, 496(a3)
	sd t6, 504(a3)
	ld t3, 416(a3)
	ld a7, 384(a3)
	sltu a5, t3, a7
	sub t3, t3, a7
	ld t4, 424(a3)
	ld a7, 392(a3)
	sltu a6, t4, a7
	sub t4, t4, a7
	sltu a7, t4, a5
	sub t4, t4, a5
	add a5, a6, a7
	ld t5, 432(a3)
	ld a7, 400(a3)
	sltu a6, t5, a7
	sub t5, t5, a7
	sltu a7, t5, a5
	sub t5, t5, a5
	add a5, a6, a7
	ld t6, 440(a3)
	ld a7, 408(a3)
	sltu a6, t6, a7
	sub t6, t6, a7
	sltu a7, t6, a5
	sub t6, t6, a5
	add a5, a6, a7
	addi a4, zero, 38
	mul a7, a5, a4
	sltu t0, t3, a7
	sub t3, t3, a7
	sltu a7, t4, t0
	sub t4, t4, t0
	sltu t0, t5, a7
	sub t5, t5, a7
	sltu a5, t6, t0
	sub t6, t6, t0
	mul a7, a5, a4
	sltu t0, t3, a7
	sub t3, t3, a7
	sltu a7, t4, t0
	sub t4, t4, t0
	sltu t0, t5, a7
	sub t5, t5, a7
	sltu a5, t6, t0
	sub t6, t6, t0
	sd t3, 512(a3)
	sd t4, 520(a3)
	sd t5, 528(a3)
	sd t6, 536(a3)
	ld t3, 416(a3)
	ld a7, 384(a3)
	add t3, t3, a7
	sltu a5, t3, a7
	ld t4, 424(a3)
	ld a7, 392(a3)
	add t4, t4, a7
	sltu a6, t4, a7
	add t4, t4, a5
	sltu a7, t4, a5
	add a5, a6, a7
	ld t5, 432(a3)
	ld a7, 400(a3)
	add t5, t5, a7
	sltu a6, t5, a7
	add t5, t5, a5
	sltu a7, t5, a5
	add a5, a6, a7
	ld t6, 440(a3)
	ld a7, 408(a3)
	add t6, t6, a7
	sltu a6, t6, a7
	add t6, t6, a5
	sltu a7, t6, a5
	add a5, a6, a7
	addi a4, zero, 38
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	sd t3, 544(a3)
	sd t4, 552(a3)
	sd t5, 560(a3)
	sd t6, 568(a3)
	ld t3, 512(a3)
	ld t4, 520(a3)
	ld t5, 528(a3)
	ld t6, 536(a3)
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	ld t0, 448(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 864(a3)
	addi a4, zero, 0
	ld t0, 456(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 448(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 872(a3)
	addi a5, zero, 0
	ld t0, 464(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 456(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 448(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 880(a3)
	addi a6, zero, 0
	ld t0, 472(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 464(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 456(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 448(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 888(a3)
	addi a4, zero, 0
	ld t0, 472(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 464(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 456(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 896(a3)
	addi a5, zero, 0
	ld t0, 472(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 464(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 904(a3)
	addi a6, zero, 0
	ld t0, 472(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 912(a3)
	addi a4, zero, 0
	sd a5, 920(a3)
	addi a5, zero, 0
	addi a4, zero, 38
	ld t3, 864(a3)
	ld a7, 896(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t3, t3, t0
	sltu a5, t3, t0
	ld t4, 872(a3)
	ld a7, 904(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t4, t4, t0
	sltu a6, t4, t0
	add t4, t4, a1
	sltu a7, t4, a1
	add a6, a6, a7
	add t4, t4, a5
	sltu a7, t4, a5
	add a6, a6, a7
	ld t5, 880(a3)
	ld a7, 912(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t5, t5, t0
	sltu a5, t5, t0
	add t5, t5, a2
	sltu a7, t5, a2
	add a5, a5, a7
	add t5, t5, a6
	sltu a7, t5, a6
	add a5, a5, a7
	ld t6, 888(a3)
	ld a7, 920(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t6, t6, t0
	sltu a6, t6, t0
	add t6, t6, a1
	sltu a7, t6, a1
	add a6, a6, a7
	add t6, t6, a5
	sltu a7, t6, a5
	add a6, a6, a7
	add a5, a2, a6
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	sd t3, 64(a3)
	sd t4, 72(a3)
	sd t5, 80(a3)
	sd t6, 88(a3)
	ld t3, 480(a3)
	ld t4, 488(a3)
	ld t5, 496(a3)
	ld t6, 504(a3)
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	ld t0, 544(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 864(a3)
	addi a4, zero, 0
	ld t0, 552(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 544(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 872(a3)
	addi a5, zero, 0
	ld t0, 560(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 552(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 544(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 880(a3)
	addi a6, zero, 0
	ld t0, 568(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 560(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 552(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 544(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 888(a3)
	addi a4, zero, 0
	ld t0, 568(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 560(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 552(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 896(a3)
	addi a5, zero, 0
	ld t0, 568(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 560(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 904(a3)
	addi a6, zero, 0
	ld t0, 568(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 912(a3)
	addi a4, zero, 0
	sd a5, 920(a3)
	addi a5, zero, 0
	addi a4, zero, 38
	ld t3, 864(a3)
	ld a7, 896(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t3, t3, t0
	sltu a5, t3, t0
	ld t4, 872(a3)
	ld a7, 904(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t4, t4, t0
	sltu a6, t4, t0
	add t4, t4, a1
	sltu a7, t4, a1
	add a6, a6, a7
	add t4, t4, a5
	sltu a7, t4, a5
	add a6, a6, a7
	ld t5, 880(a3)
	ld a7, 912(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t5, t5, t0
	sltu a5, t5, t0
	add t5, t5, a2
	sltu a7, t5, a2
	add a5, a5, a7
	add t5, t5, a6
	sltu a7, t5, a6
	add a5, a5, a7
	ld t6, 888(a3)
	ld a7, 920(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t6, t6, t0
	sltu a6, t6, t0
	add t6, t6, a1
	sltu a7, t6, a1
	add a6, a6, a7
	add t6, t6, a5
	sltu a7, t6, a5
	add a6, a6, a7
	add a5, a2, a6
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	sd t3, 96(a3)
	sd t4, 104(a3)
	sd t5, 112(a3)
	sd t6, 120(a3)
	ld t3, 544(a3)
	ld t4, 552(a3)
	ld t5, 560(a3)
	ld t6, 568(a3)
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	ld t0, 512(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 864(a3)
	addi a4, zero, 0
	ld t0, 520(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 512(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 872(a3)
	addi a5, zero, 0
	ld t0, 528(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 520(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 512(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 880(a3)
	addi a6, zero, 0
	ld t0, 536(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 528(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 520(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 512(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 888(a3)
	addi a4, zero, 0
	ld t0, 536(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 528(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 520(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 896(a3)
	addi a5, zero, 0
	ld t0, 536(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 528(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 904(a3)
	addi a6, zero, 0
	ld t0, 536(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 912(a3)
	addi a4, zero, 0
	sd a5, 920(a3)
	addi a5, zero, 0
	addi a4, zero, 38
	ld t3, 864(a3)
	ld a7, 896(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t3, t3, t0
	sltu a5, t3, t0
	ld t4, 872(a3)
	ld a7, 904(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t4, t4, t0
	sltu a6, t4, t0
	add t4, t4, a1
	sltu a7, t4, a1
	add a6, a6, a7
	add t4, t4, a5
	sltu a7, t4, a5
	add a6, a6, a7
	ld t5, 880(a3)
	ld a7, 912(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t5, t5, t0
	sltu a5, t5, t0
	add t5, t5, a2
	sltu a7, t5, a2
	add a5, a5, a7
	add t5, t5, a6
	sltu a7, t5, a6
	add a5, a5, a7
	ld t6, 888(a3)
	ld a7, 920(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t6, t6, t0
	sltu a6, t6, t0
	add t6, t6, a1
	sltu a7, t6, a1
	add a6, a6, a7
	add t6, t6, a5
	sltu a7, t6, a5
	add a6, a6, a7
	add a5, a2, a6
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	sd t3, 128(a3)
	sd t4, 136(a3)
	sd t5, 144(a3)
	sd t6, 152(a3)
	ld t3, 480(a3)
	ld t4, 488(a3)
	ld t5, 496(a3)
	ld t6, 504(a3)
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	ld t0, 448(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 864(a3)
	addi a4, zero, 0
	ld t0, 456(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 448(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 872(a3)
	addi a5, zero, 0
	ld t0, 464(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 456(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 448(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 880(a3)
	addi a6, zero, 0
	ld t0, 472(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 464(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 456(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 448(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 888(a3)
	addi a4, zero, 0
	ld t0, 472(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 464(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 456(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 896(a3)
	addi a5, zero, 0
	ld t0, 472(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 464(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 904(a3)
	addi a6, zero, 0
	ld t0, 472(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 912(a3)
	addi a4, zero, 0
	sd a5, 920(a3)
	addi a5, zero, 0
	addi a4, zero, 38
	ld t3, 864(a3)
	ld a7, 896(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t3, t3, t0
	sltu a5, t3, t0
	ld t4, 872(a3)
	ld a7, 904(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t4, t4, t0
	sltu a6, t4, t0
	add t4, t4, a1
	sltu a7, t4, a1
	add a6, a6, a7
	add t4, t4, a5
	sltu a7, t4, a5
	add a6, a6, a7
	ld t5, 880(a3)
	ld a7, 912(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t5, t5, t0
	sltu a5, t5, t0
	add t5, t5, a2
	sltu a7, t5, a2
	add a5, a5, a7
	add t5, t5, a6
	sltu a7, t5, a6
	add a5, a5, a7
	ld t6, 888(a3)
	ld a7, 920(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t6, t6, t0
	sltu a6, t6, t0
	add t6, t6, a1
	sltu a7, t6, a1
	add a6, a6, a7
	add t6, t6, a5
	sltu a7, t6, a5
	add a6, a6, a7
	add a5, a2, a6
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	sd t3, 160(a3)
	sd t4, 168(a3)
	sd t5, 176(a3)
	sd t6, 184(a3)
	addi s1, s1, 1
	addi s2, s2, 768
	addi a4, s1, -64
	bnez a4, 20b
	addi a0, a3, 0
	call {vg_gf25519_r32_pow250}
	addi a3, a0, 0
	addi t1, zero, 5
21:
	ld t3, 544(a3)
	ld t4, 552(a3)
	ld t5, 560(a3)
	ld t6, 568(a3)
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	sd a4, 864(a3)
	addi a4, zero, 0
	mul a7, t3, t4
	mulhu t0, t3, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 872(a3)
	addi a5, zero, 0
	mul a7, t3, t5
	mulhu t0, t3, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 880(a3)
	addi a6, zero, 0
	mul a7, t3, t6
	mulhu t0, t3, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	mul a7, t4, t5
	mulhu t0, t4, t5
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 888(a3)
	addi a4, zero, 0
	mul a7, t4, t6
	mulhu t0, t4, t6
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 896(a3)
	addi a5, zero, 0
	mul a7, t5, t6
	mulhu t0, t5, t6
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 904(a3)
	addi a6, zero, 0
	sd a4, 912(a3)
	addi a4, zero, 0
	sd a5, 920(a3)
	addi a5, zero, 0
	addi a5, zero, 0
	addi a4, zero, 0
	srli a7, a5, 63
	ld a5, 864(a3)
	slli a6, a5, 1
	or a6, a6, a7
	ld t3, 544(a3)
	mul t0, t3, t3
	mulhu t3, t3, t3
	add a6, a6, t0
	sltu a7, a6, t0
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 864(a3)
	srli a7, a5, 63
	ld a5, 872(a3)
	slli a6, a5, 1
	or a6, a6, a7
	add a6, a6, t3
	sltu a7, a6, t3
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 872(a3)
	srli a7, a5, 63
	ld a5, 880(a3)
	slli a6, a5, 1
	or a6, a6, a7
	ld t3, 552(a3)
	mul t0, t3, t3
	mulhu t3, t3, t3
	add a6, a6, t0
	sltu a7, a6, t0
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 880(a3)
	srli a7, a5, 63
	ld a5, 888(a3)
	slli a6, a5, 1
	or a6, a6, a7
	add a6, a6, t3
	sltu a7, a6, t3
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 888(a3)
	srli a7, a5, 63
	ld a5, 896(a3)
	slli a6, a5, 1
	or a6, a6, a7
	ld t3, 560(a3)
	mul t0, t3, t3
	mulhu t3, t3, t3
	add a6, a6, t0
	sltu a7, a6, t0
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 896(a3)
	srli a7, a5, 63
	ld a5, 904(a3)
	slli a6, a5, 1
	or a6, a6, a7
	add a6, a6, t3
	sltu a7, a6, t3
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 904(a3)
	srli a7, a5, 63
	ld a5, 912(a3)
	slli a6, a5, 1
	or a6, a6, a7
	ld t3, 568(a3)
	mul t0, t3, t3
	mulhu t3, t3, t3
	add a6, a6, t0
	sltu a7, a6, t0
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 912(a3)
	srli a7, a5, 63
	ld a5, 920(a3)
	slli a6, a5, 1
	or a6, a6, a7
	add a6, a6, t3
	sltu a7, a6, t3
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 920(a3)
	addi a4, zero, 38
	ld t3, 864(a3)
	ld a7, 896(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t3, t3, t0
	sltu a5, t3, t0
	ld t4, 872(a3)
	ld a7, 904(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t4, t4, t0
	sltu a6, t4, t0
	add t4, t4, a1
	sltu a7, t4, a1
	add a6, a6, a7
	add t4, t4, a5
	sltu a7, t4, a5
	add a6, a6, a7
	ld t5, 880(a3)
	ld a7, 912(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t5, t5, t0
	sltu a5, t5, t0
	add t5, t5, a2
	sltu a7, t5, a2
	add a5, a5, a7
	add t5, t5, a6
	sltu a7, t5, a6
	add a5, a5, a7
	ld t6, 888(a3)
	ld a7, 920(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t6, t6, t0
	sltu a6, t6, t0
	add t6, t6, a1
	sltu a7, t6, a1
	add a6, a6, a7
	add t6, t6, a5
	sltu a7, t6, a5
	add a6, a6, a7
	add a5, a2, a6
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	sd t3, 544(a3)
	sd t4, 552(a3)
	sd t5, 560(a3)
	sd t6, 568(a3)
	addi t1, t1, -1
	bnez t1, 21b
	addi a0, a3, 0
	addi a1, zero, 544
	addi a2, zero, 544
	addi a3, zero, 512
	call {vg_gf25519_r32_mul}
	addi a3, a0, 0
	addi a0, a3, 0
	addi a1, zero, 64
	addi a2, zero, 64
	addi a3, zero, 544
	call {vg_gf25519_r32_mul}
	addi a3, a0, 0
	addi a0, a3, 0
	addi a1, zero, 96
	addi a2, zero, 96
	addi a3, zero, 544
	call {vg_gf25519_r32_mul}
	addi a3, a0, 0
	lwu a4, 64(a3)
	sw a4, 864(a3)
	lwu a4, 68(a3)
	sw a4, 868(a3)
	lwu a4, 72(a3)
	sw a4, 872(a3)
	lwu a4, 76(a3)
	sw a4, 876(a3)
	lwu a4, 80(a3)
	sw a4, 880(a3)
	lwu a4, 84(a3)
	sw a4, 884(a3)
	lwu a4, 88(a3)
	sw a4, 888(a3)
	lwu a4, 92(a3)
	sw a4, 892(a3)
	lwu a4, 892(a3)
	srli a5, a4, 31
	slli a4, a4, 33
	srli a4, a4, 33
	sw a4, 892(a3)
	addi a2, zero, 19
	mul a5, a5, a2
	lwu a4, 864(a3)
	add a4, a4, a5
	sw a4, 864(a3)
	srli a5, a4, 32
	lwu a4, 868(a3)
	add a4, a4, a5
	sw a4, 868(a3)
	srli a5, a4, 32
	lwu a4, 872(a3)
	add a4, a4, a5
	sw a4, 872(a3)
	srli a5, a4, 32
	lwu a4, 876(a3)
	add a4, a4, a5
	sw a4, 876(a3)
	srli a5, a4, 32
	lwu a4, 880(a3)
	add a4, a4, a5
	sw a4, 880(a3)
	srli a5, a4, 32
	lwu a4, 884(a3)
	add a4, a4, a5
	sw a4, 884(a3)
	srli a5, a4, 32
	lwu a4, 888(a3)
	add a4, a4, a5
	sw a4, 888(a3)
	srli a5, a4, 32
	lwu a4, 892(a3)
	add a4, a4, a5
	sw a4, 892(a3)
	srli a5, a4, 32
	addi a5, zero, 19
	lwu a4, 864(a3)
	add a4, a4, a5
	sw a4, 896(a3)
	srli a5, a4, 32
	lwu a4, 868(a3)
	add a4, a4, a5
	sw a4, 900(a3)
	srli a5, a4, 32
	lwu a4, 872(a3)
	add a4, a4, a5
	sw a4, 904(a3)
	srli a5, a4, 32
	lwu a4, 876(a3)
	add a4, a4, a5
	sw a4, 908(a3)
	srli a5, a4, 32
	lwu a4, 880(a3)
	add a4, a4, a5
	sw a4, 912(a3)
	srli a5, a4, 32
	lwu a4, 884(a3)
	add a4, a4, a5
	sw a4, 916(a3)
	srli a5, a4, 32
	lwu a4, 888(a3)
	add a4, a4, a5
	sw a4, 920(a3)
	srli a5, a4, 32
	lwu a4, 892(a3)
	add a4, a4, a5
	sw a4, 924(a3)
	srli a5, a4, 32
	lwu a4, 924(a3)
	srli t0, a4, 31
	addi a1, zero, 0
	sub t0, a1, t0
	slli a4, a4, 33
	srli a4, a4, 33
	sw a4, 924(a3)
	lwu a4, 864(a3)
	lwu a2, 896(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 864(a3)
	lwu a4, 868(a3)
	lwu a2, 900(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 868(a3)
	lwu a4, 872(a3)
	lwu a2, 904(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 872(a3)
	lwu a4, 876(a3)
	lwu a2, 908(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 876(a3)
	lwu a4, 880(a3)
	lwu a2, 912(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 880(a3)
	lwu a4, 884(a3)
	lwu a2, 916(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 884(a3)
	lwu a4, 888(a3)
	lwu a2, 920(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 888(a3)
	lwu a4, 892(a3)
	lwu a2, 924(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 892(a3)
	lwu a4, 864(a3)
	slli t6, a4, 63
	srli t6, t6, 32
	lwu a4, 96(a3)
	sw a4, 864(a3)
	lwu a4, 100(a3)
	sw a4, 868(a3)
	lwu a4, 104(a3)
	sw a4, 872(a3)
	lwu a4, 108(a3)
	sw a4, 876(a3)
	lwu a4, 112(a3)
	sw a4, 880(a3)
	lwu a4, 116(a3)
	sw a4, 884(a3)
	lwu a4, 120(a3)
	sw a4, 888(a3)
	lwu a4, 124(a3)
	sw a4, 892(a3)
	lwu a4, 892(a3)
	srli a5, a4, 31
	slli a4, a4, 33
	srli a4, a4, 33
	sw a4, 892(a3)
	addi a2, zero, 19
	mul a5, a5, a2
	lwu a4, 864(a3)
	add a4, a4, a5
	sw a4, 864(a3)
	srli a5, a4, 32
	lwu a4, 868(a3)
	add a4, a4, a5
	sw a4, 868(a3)
	srli a5, a4, 32
	lwu a4, 872(a3)
	add a4, a4, a5
	sw a4, 872(a3)
	srli a5, a4, 32
	lwu a4, 876(a3)
	add a4, a4, a5
	sw a4, 876(a3)
	srli a5, a4, 32
	lwu a4, 880(a3)
	add a4, a4, a5
	sw a4, 880(a3)
	srli a5, a4, 32
	lwu a4, 884(a3)
	add a4, a4, a5
	sw a4, 884(a3)
	srli a5, a4, 32
	lwu a4, 888(a3)
	add a4, a4, a5
	sw a4, 888(a3)
	srli a5, a4, 32
	lwu a4, 892(a3)
	add a4, a4, a5
	sw a4, 892(a3)
	srli a5, a4, 32
	addi a5, zero, 19
	lwu a4, 864(a3)
	add a4, a4, a5
	sw a4, 896(a3)
	srli a5, a4, 32
	lwu a4, 868(a3)
	add a4, a4, a5
	sw a4, 900(a3)
	srli a5, a4, 32
	lwu a4, 872(a3)
	add a4, a4, a5
	sw a4, 904(a3)
	srli a5, a4, 32
	lwu a4, 876(a3)
	add a4, a4, a5
	sw a4, 908(a3)
	srli a5, a4, 32
	lwu a4, 880(a3)
	add a4, a4, a5
	sw a4, 912(a3)
	srli a5, a4, 32
	lwu a4, 884(a3)
	add a4, a4, a5
	sw a4, 916(a3)
	srli a5, a4, 32
	lwu a4, 888(a3)
	add a4, a4, a5
	sw a4, 920(a3)
	srli a5, a4, 32
	lwu a4, 892(a3)
	add a4, a4, a5
	sw a4, 924(a3)
	srli a5, a4, 32
	lwu a4, 924(a3)
	srli t0, a4, 31
	addi a1, zero, 0
	sub t0, a1, t0
	slli a4, a4, 33
	srli a4, a4, 33
	sw a4, 924(a3)
	lwu a4, 864(a3)
	lwu a2, 896(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 864(a3)
	lwu a4, 868(a3)
	lwu a2, 900(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 868(a3)
	lwu a4, 872(a3)
	lwu a2, 904(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 872(a3)
	lwu a4, 876(a3)
	lwu a2, 908(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 876(a3)
	lwu a4, 880(a3)
	lwu a2, 912(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 880(a3)
	lwu a4, 884(a3)
	lwu a2, 916(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 884(a3)
	lwu a4, 888(a3)
	lwu a2, 920(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 888(a3)
	lwu a4, 892(a3)
	lwu a2, 924(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 892(a3)
	lwu a4, 892(a3)
	add a4, a4, t6
	sw a4, 892(a3)
	addi s0, s3, 0
	lwu a4, 864(a3)
	sb a4, 0(s0)
	srli a5, a4, 8
	sb a5, 1(s0)
	srli a5, a4, 16
	sb a5, 2(s0)
	srli a5, a4, 24
	sb a5, 3(s0)
	lwu a4, 868(a3)
	sb a4, 4(s0)
	srli a5, a4, 8
	sb a5, 5(s0)
	srli a5, a4, 16
	sb a5, 6(s0)
	srli a5, a4, 24
	sb a5, 7(s0)
	lwu a4, 872(a3)
	sb a4, 8(s0)
	srli a5, a4, 8
	sb a5, 9(s0)
	srli a5, a4, 16
	sb a5, 10(s0)
	srli a5, a4, 24
	sb a5, 11(s0)
	lwu a4, 876(a3)
	sb a4, 12(s0)
	srli a5, a4, 8
	sb a5, 13(s0)
	srli a5, a4, 16
	sb a5, 14(s0)
	srli a5, a4, 24
	sb a5, 15(s0)
	lwu a4, 880(a3)
	sb a4, 16(s0)
	srli a5, a4, 8
	sb a5, 17(s0)
	srli a5, a4, 16
	sb a5, 18(s0)
	srli a5, a4, 24
	sb a5, 19(s0)
	lwu a4, 884(a3)
	sb a4, 20(s0)
	srli a5, a4, 8
	sb a5, 21(s0)
	srli a5, a4, 16
	sb a5, 22(s0)
	srli a5, a4, 24
	sb a5, 23(s0)
	lwu a4, 888(a3)
	sb a4, 24(s0)
	srli a5, a4, 8
	sb a5, 25(s0)
	srli a5, a4, 16
	sb a5, 26(s0)
	srli a5, a4, 24
	sb a5, 27(s0)
	lwu a4, 892(a3)
	sb a4, 28(s0)
	srli a5, a4, 8
	sb a5, 29(s0)
	srli a5, a4, 16
	sb a5, 30(s0)
	srli a5, a4, 24
	sb a5, 31(s0)
	ld s0, 1024(a3)
	ld s1, 1032(a3)
	ld s2, 1040(a3)
	ld s3, 1048(a3)
	ld s5, 1056(a3)
	ld s6, 1064(a3)
	ld ra, 1072(a3)
	ret
	.option pop
