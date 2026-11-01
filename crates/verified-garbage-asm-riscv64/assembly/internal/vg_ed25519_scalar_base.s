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
	lui a4, 586333
	addiw a4, a4, 1306
	sw a4, 64(a3)
	lui a4, 824675
	addiw a4, a4, -672
	sw a4, 68(a3)
	lui a4, 610906
	addiw a4, a4, 1970
	sw a4, 72(a3)
	lui a4, 430796
	addiw a4, a4, 1888
	sw a4, 76(a3)
	lui a4, 1039726
	addiw a4, a4, -932
	sw a4, 80(a3)
	lui a4, 789070
	addiw a4, a4, 561
	sw a4, 84(a3)
	lui a4, 841445
	addiw a4, a4, 1022
	sw a4, 88(a3)
	lui a4, 136851
	addiw a4, a4, 1747
	sw a4, 92(a3)
	lui a4, 419430
	addiw a4, a4, 1624
	sw a4, 96(a3)
	lui a4, 419430
	addiw a4, a4, 1638
	sw a4, 100(a3)
	lui a4, 419430
	addiw a4, a4, 1638
	sw a4, 104(a3)
	lui a4, 419430
	addiw a4, a4, 1638
	sw a4, 108(a3)
	lui a4, 419430
	addiw a4, a4, 1638
	sw a4, 112(a3)
	lui a4, 419430
	addiw a4, a4, 1638
	sw a4, 116(a3)
	lui a4, 419430
	addiw a4, a4, 1638
	sw a4, 120(a3)
	lui a4, 419430
	addiw a4, a4, 1638
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
	lui a4, 678782
	addiw a4, a4, -605
	sw a4, 160(a3)
	lui a4, 450025
	addiw a4, a4, -1357
	sw a4, 164(a3)
	lui a4, 488725
	addiw a4, a4, 757
	sw a4, 168(a3)
	lui a4, 134922
	addiw a4, a4, -128
	sw a4, 172(a3)
	lui a4, 412350
	addiw a4, a4, 893
	sw a4, 176(a3)
	lui a4, 421541
	addiw a4, a4, -370
	sw a4, 180(a3)
	lui a4, 882871
	addiw a4, a4, 1637
	sw a4, 184(a3)
	lui a4, 424054
	addiw a4, a4, -241
	sw a4, 188(a3)
	addi s5, s0, 0
	lui a4, 79256
	addiw a4, a4, -1885
	sw a4, 576(a3)
	lui a4, 482997
	addiw a4, a4, -566
	sw a4, 580(a3)
	lui a4, 267294
	addiw a4, a4, -1877
	sw a4, 584(a3)
	lui a4, 1793
	addiw a4, a4, -1459
	sw a4, 588(a3)
	lui a4, 489375
	addiw a4, a4, -1896
	sw a4, 592(a3)
	lui a4, 576628
	addiw a4, a4, 121
	sw a4, 596(a3)
	lui a4, 177920
	addiw a4, a4, -397
	sw a4, 600(a3)
	lui a4, 335927
	addiw a4, a4, -786
	sw a4, 604(a3)
	addi s2, zero, 0
20:
	lui s0, 0
	addiw s0, s0, 1632
	add s0, a3, s0
	slli a4, s2, 7
	add s0, s0, a4
	lwu a4, 64(a3)
	sb a4, 0(s0)
	srli a5, a4, 8
	sb a5, 1(s0)
	srli a5, a4, 16
	sb a5, 2(s0)
	srli a5, a4, 24
	sb a5, 3(s0)
	lwu a4, 68(a3)
	sb a4, 4(s0)
	srli a5, a4, 8
	sb a5, 5(s0)
	srli a5, a4, 16
	sb a5, 6(s0)
	srli a5, a4, 24
	sb a5, 7(s0)
	lwu a4, 72(a3)
	sb a4, 8(s0)
	srli a5, a4, 8
	sb a5, 9(s0)
	srli a5, a4, 16
	sb a5, 10(s0)
	srli a5, a4, 24
	sb a5, 11(s0)
	lwu a4, 76(a3)
	sb a4, 12(s0)
	srli a5, a4, 8
	sb a5, 13(s0)
	srli a5, a4, 16
	sb a5, 14(s0)
	srli a5, a4, 24
	sb a5, 15(s0)
	lwu a4, 80(a3)
	sb a4, 16(s0)
	srli a5, a4, 8
	sb a5, 17(s0)
	srli a5, a4, 16
	sb a5, 18(s0)
	srli a5, a4, 24
	sb a5, 19(s0)
	lwu a4, 84(a3)
	sb a4, 20(s0)
	srli a5, a4, 8
	sb a5, 21(s0)
	srli a5, a4, 16
	sb a5, 22(s0)
	srli a5, a4, 24
	sb a5, 23(s0)
	lwu a4, 88(a3)
	sb a4, 24(s0)
	srli a5, a4, 8
	sb a5, 25(s0)
	srli a5, a4, 16
	sb a5, 26(s0)
	srli a5, a4, 24
	sb a5, 27(s0)
	lwu a4, 92(a3)
	sb a4, 28(s0)
	srli a5, a4, 8
	sb a5, 29(s0)
	srli a5, a4, 16
	sb a5, 30(s0)
	srli a5, a4, 24
	sb a5, 31(s0)
	lwu a4, 96(a3)
	sb a4, 32(s0)
	srli a5, a4, 8
	sb a5, 33(s0)
	srli a5, a4, 16
	sb a5, 34(s0)
	srli a5, a4, 24
	sb a5, 35(s0)
	lwu a4, 100(a3)
	sb a4, 36(s0)
	srli a5, a4, 8
	sb a5, 37(s0)
	srli a5, a4, 16
	sb a5, 38(s0)
	srli a5, a4, 24
	sb a5, 39(s0)
	lwu a4, 104(a3)
	sb a4, 40(s0)
	srli a5, a4, 8
	sb a5, 41(s0)
	srli a5, a4, 16
	sb a5, 42(s0)
	srli a5, a4, 24
	sb a5, 43(s0)
	lwu a4, 108(a3)
	sb a4, 44(s0)
	srli a5, a4, 8
	sb a5, 45(s0)
	srli a5, a4, 16
	sb a5, 46(s0)
	srli a5, a4, 24
	sb a5, 47(s0)
	lwu a4, 112(a3)
	sb a4, 48(s0)
	srli a5, a4, 8
	sb a5, 49(s0)
	srli a5, a4, 16
	sb a5, 50(s0)
	srli a5, a4, 24
	sb a5, 51(s0)
	lwu a4, 116(a3)
	sb a4, 52(s0)
	srli a5, a4, 8
	sb a5, 53(s0)
	srli a5, a4, 16
	sb a5, 54(s0)
	srli a5, a4, 24
	sb a5, 55(s0)
	lwu a4, 120(a3)
	sb a4, 56(s0)
	srli a5, a4, 8
	sb a5, 57(s0)
	srli a5, a4, 16
	sb a5, 58(s0)
	srli a5, a4, 24
	sb a5, 59(s0)
	lwu a4, 124(a3)
	sb a4, 60(s0)
	srli a5, a4, 8
	sb a5, 61(s0)
	srli a5, a4, 16
	sb a5, 62(s0)
	srli a5, a4, 24
	sb a5, 63(s0)
	lwu a4, 128(a3)
	sb a4, 64(s0)
	srli a5, a4, 8
	sb a5, 65(s0)
	srli a5, a4, 16
	sb a5, 66(s0)
	srli a5, a4, 24
	sb a5, 67(s0)
	lwu a4, 132(a3)
	sb a4, 68(s0)
	srli a5, a4, 8
	sb a5, 69(s0)
	srli a5, a4, 16
	sb a5, 70(s0)
	srli a5, a4, 24
	sb a5, 71(s0)
	lwu a4, 136(a3)
	sb a4, 72(s0)
	srli a5, a4, 8
	sb a5, 73(s0)
	srli a5, a4, 16
	sb a5, 74(s0)
	srli a5, a4, 24
	sb a5, 75(s0)
	lwu a4, 140(a3)
	sb a4, 76(s0)
	srli a5, a4, 8
	sb a5, 77(s0)
	srli a5, a4, 16
	sb a5, 78(s0)
	srli a5, a4, 24
	sb a5, 79(s0)
	lwu a4, 144(a3)
	sb a4, 80(s0)
	srli a5, a4, 8
	sb a5, 81(s0)
	srli a5, a4, 16
	sb a5, 82(s0)
	srli a5, a4, 24
	sb a5, 83(s0)
	lwu a4, 148(a3)
	sb a4, 84(s0)
	srli a5, a4, 8
	sb a5, 85(s0)
	srli a5, a4, 16
	sb a5, 86(s0)
	srli a5, a4, 24
	sb a5, 87(s0)
	lwu a4, 152(a3)
	sb a4, 88(s0)
	srli a5, a4, 8
	sb a5, 89(s0)
	srli a5, a4, 16
	sb a5, 90(s0)
	srli a5, a4, 24
	sb a5, 91(s0)
	lwu a4, 156(a3)
	sb a4, 92(s0)
	srli a5, a4, 8
	sb a5, 93(s0)
	srli a5, a4, 16
	sb a5, 94(s0)
	srli a5, a4, 24
	sb a5, 95(s0)
	lwu a4, 160(a3)
	sb a4, 96(s0)
	srli a5, a4, 8
	sb a5, 97(s0)
	srli a5, a4, 16
	sb a5, 98(s0)
	srli a5, a4, 24
	sb a5, 99(s0)
	lwu a4, 164(a3)
	sb a4, 100(s0)
	srli a5, a4, 8
	sb a5, 101(s0)
	srli a5, a4, 16
	sb a5, 102(s0)
	srli a5, a4, 24
	sb a5, 103(s0)
	lwu a4, 168(a3)
	sb a4, 104(s0)
	srli a5, a4, 8
	sb a5, 105(s0)
	srli a5, a4, 16
	sb a5, 106(s0)
	srli a5, a4, 24
	sb a5, 107(s0)
	lwu a4, 172(a3)
	sb a4, 108(s0)
	srli a5, a4, 8
	sb a5, 109(s0)
	srli a5, a4, 16
	sb a5, 110(s0)
	srli a5, a4, 24
	sb a5, 111(s0)
	lwu a4, 176(a3)
	sb a4, 112(s0)
	srli a5, a4, 8
	sb a5, 113(s0)
	srli a5, a4, 16
	sb a5, 114(s0)
	srli a5, a4, 24
	sb a5, 115(s0)
	lwu a4, 180(a3)
	sb a4, 116(s0)
	srli a5, a4, 8
	sb a5, 117(s0)
	srli a5, a4, 16
	sb a5, 118(s0)
	srli a5, a4, 24
	sb a5, 119(s0)
	lwu a4, 184(a3)
	sb a4, 120(s0)
	srli a5, a4, 8
	sb a5, 121(s0)
	srli a5, a4, 16
	sb a5, 122(s0)
	srli a5, a4, 24
	sb a5, 123(s0)
	lwu a4, 188(a3)
	sb a4, 124(s0)
	srli a5, a4, 8
	sb a5, 125(s0)
	srli a5, a4, 16
	sb a5, 126(s0)
	srli a5, a4, 24
	sb a5, 127(s0)
	addi s1, zero, 16
21:
	lwu a4, 64(a3)
	sw a4, 192(a3)
	lwu a4, 68(a3)
	sw a4, 196(a3)
	lwu a4, 72(a3)
	sw a4, 200(a3)
	lwu a4, 76(a3)
	sw a4, 204(a3)
	lwu a4, 80(a3)
	sw a4, 208(a3)
	lwu a4, 84(a3)
	sw a4, 212(a3)
	lwu a4, 88(a3)
	sw a4, 216(a3)
	lwu a4, 92(a3)
	sw a4, 220(a3)
	lwu a4, 96(a3)
	sw a4, 224(a3)
	lwu a4, 100(a3)
	sw a4, 228(a3)
	lwu a4, 104(a3)
	sw a4, 232(a3)
	lwu a4, 108(a3)
	sw a4, 236(a3)
	lwu a4, 112(a3)
	sw a4, 240(a3)
	lwu a4, 116(a3)
	sw a4, 244(a3)
	lwu a4, 120(a3)
	sw a4, 248(a3)
	lwu a4, 124(a3)
	sw a4, 252(a3)
	lwu a4, 128(a3)
	sw a4, 256(a3)
	lwu a4, 132(a3)
	sw a4, 260(a3)
	lwu a4, 136(a3)
	sw a4, 264(a3)
	lwu a4, 140(a3)
	sw a4, 268(a3)
	lwu a4, 144(a3)
	sw a4, 272(a3)
	lwu a4, 148(a3)
	sw a4, 276(a3)
	lwu a4, 152(a3)
	sw a4, 280(a3)
	lwu a4, 156(a3)
	sw a4, 284(a3)
	lwu a4, 160(a3)
	sw a4, 288(a3)
	lwu a4, 164(a3)
	sw a4, 292(a3)
	lwu a4, 168(a3)
	sw a4, 296(a3)
	lwu a4, 172(a3)
	sw a4, 300(a3)
	lwu a4, 176(a3)
	sw a4, 304(a3)
	lwu a4, 180(a3)
	sw a4, 308(a3)
	lwu a4, 184(a3)
	sw a4, 312(a3)
	lwu a4, 188(a3)
	sw a4, 316(a3)
	addi a0, a3, 0
	call {vg_ed25519_r32_point_add}
	addi a3, a0, 0
	addi s1, s1, -1
	bnez s1, 21b
	addi s2, s2, 1
	addi a4, s2, -16
	bnez a4, 20b
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 64(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 68(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 72(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 76(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 80(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 84(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 88(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 92(a3)
	lui a4, 0
	addiw a4, a4, 1
	sw a4, 96(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 100(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 104(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 108(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 112(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 116(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 120(a3)
	lui a4, 0
	addiw a4, a4, 0
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
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 160(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 164(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 168(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 172(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 176(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 180(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 184(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 188(a3)
	addi s6, zero, 16
22:
	addi s6, s6, -1
	addi s2, s6, 0
	lwu a4, 64(a3)
	sw a4, 608(a3)
	lwu a4, 68(a3)
	sw a4, 612(a3)
	lwu a4, 72(a3)
	sw a4, 616(a3)
	lwu a4, 76(a3)
	sw a4, 620(a3)
	lwu a4, 80(a3)
	sw a4, 624(a3)
	lwu a4, 84(a3)
	sw a4, 628(a3)
	lwu a4, 88(a3)
	sw a4, 632(a3)
	lwu a4, 92(a3)
	sw a4, 636(a3)
	lwu a4, 96(a3)
	sw a4, 640(a3)
	lwu a4, 100(a3)
	sw a4, 644(a3)
	lwu a4, 104(a3)
	sw a4, 648(a3)
	lwu a4, 108(a3)
	sw a4, 652(a3)
	lwu a4, 112(a3)
	sw a4, 656(a3)
	lwu a4, 116(a3)
	sw a4, 660(a3)
	lwu a4, 120(a3)
	sw a4, 664(a3)
	lwu a4, 124(a3)
	sw a4, 668(a3)
	lwu a4, 128(a3)
	sw a4, 672(a3)
	lwu a4, 132(a3)
	sw a4, 676(a3)
	lwu a4, 136(a3)
	sw a4, 680(a3)
	lwu a4, 140(a3)
	sw a4, 684(a3)
	lwu a4, 144(a3)
	sw a4, 688(a3)
	lwu a4, 148(a3)
	sw a4, 692(a3)
	lwu a4, 152(a3)
	sw a4, 696(a3)
	lwu a4, 156(a3)
	sw a4, 700(a3)
	lwu a4, 160(a3)
	sw a4, 704(a3)
	lwu a4, 164(a3)
	sw a4, 708(a3)
	lwu a4, 168(a3)
	sw a4, 712(a3)
	lwu a4, 172(a3)
	sw a4, 716(a3)
	lwu a4, 176(a3)
	sw a4, 720(a3)
	lwu a4, 180(a3)
	sw a4, 724(a3)
	lwu a4, 184(a3)
	sw a4, 728(a3)
	lwu a4, 188(a3)
	sw a4, 732(a3)
	lui s0, 0
	addiw s0, s0, 1632
	add s0, a3, s0
	slli a4, s2, 7
	add s0, s0, a4
	lbu a4, 0(s0)
	lbu a5, 1(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 2(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 3(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 64(a3)
	lbu a4, 4(s0)
	lbu a5, 5(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 6(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 7(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 68(a3)
	lbu a4, 8(s0)
	lbu a5, 9(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 10(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 11(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 72(a3)
	lbu a4, 12(s0)
	lbu a5, 13(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 14(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 15(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 76(a3)
	lbu a4, 16(s0)
	lbu a5, 17(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 18(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 19(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 80(a3)
	lbu a4, 20(s0)
	lbu a5, 21(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 22(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 23(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 84(a3)
	lbu a4, 24(s0)
	lbu a5, 25(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 26(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 27(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 88(a3)
	lbu a4, 28(s0)
	lbu a5, 29(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 30(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 31(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 92(a3)
	lbu a4, 32(s0)
	lbu a5, 33(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 34(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 35(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 96(a3)
	lbu a4, 36(s0)
	lbu a5, 37(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 38(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 39(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 100(a3)
	lbu a4, 40(s0)
	lbu a5, 41(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 42(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 43(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 104(a3)
	lbu a4, 44(s0)
	lbu a5, 45(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 46(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 47(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 108(a3)
	lbu a4, 48(s0)
	lbu a5, 49(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 50(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 51(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 112(a3)
	lbu a4, 52(s0)
	lbu a5, 53(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 54(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 55(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 116(a3)
	lbu a4, 56(s0)
	lbu a5, 57(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 58(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 59(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 120(a3)
	lbu a4, 60(s0)
	lbu a5, 61(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 62(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 63(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 124(a3)
	lbu a4, 64(s0)
	lbu a5, 65(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 66(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 67(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 128(a3)
	lbu a4, 68(s0)
	lbu a5, 69(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 70(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 71(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 132(a3)
	lbu a4, 72(s0)
	lbu a5, 73(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 74(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 75(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 136(a3)
	lbu a4, 76(s0)
	lbu a5, 77(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 78(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 79(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 140(a3)
	lbu a4, 80(s0)
	lbu a5, 81(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 82(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 83(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 144(a3)
	lbu a4, 84(s0)
	lbu a5, 85(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 86(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 87(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 148(a3)
	lbu a4, 88(s0)
	lbu a5, 89(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 90(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 91(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 152(a3)
	lbu a4, 92(s0)
	lbu a5, 93(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 94(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 95(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 156(a3)
	lbu a4, 96(s0)
	lbu a5, 97(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 98(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 99(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 160(a3)
	lbu a4, 100(s0)
	lbu a5, 101(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 102(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 103(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 164(a3)
	lbu a4, 104(s0)
	lbu a5, 105(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 106(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 107(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 168(a3)
	lbu a4, 108(s0)
	lbu a5, 109(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 110(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 111(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 172(a3)
	lbu a4, 112(s0)
	lbu a5, 113(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 114(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 115(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 176(a3)
	lbu a4, 116(s0)
	lbu a5, 117(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 118(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 119(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 180(a3)
	lbu a4, 120(s0)
	lbu a5, 121(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 122(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 123(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 184(a3)
	lbu a4, 124(s0)
	lbu a5, 125(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 126(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 127(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 188(a3)
	addi s2, zero, 0
23:
	lui s0, 1
	addiw s0, s0, 1632
	add s0, a3, s0
	slli a4, s2, 7
	add s0, s0, a4
	lwu a4, 64(a3)
	sb a4, 0(s0)
	srli a5, a4, 8
	sb a5, 1(s0)
	srli a5, a4, 16
	sb a5, 2(s0)
	srli a5, a4, 24
	sb a5, 3(s0)
	lwu a4, 68(a3)
	sb a4, 4(s0)
	srli a5, a4, 8
	sb a5, 5(s0)
	srli a5, a4, 16
	sb a5, 6(s0)
	srli a5, a4, 24
	sb a5, 7(s0)
	lwu a4, 72(a3)
	sb a4, 8(s0)
	srli a5, a4, 8
	sb a5, 9(s0)
	srli a5, a4, 16
	sb a5, 10(s0)
	srli a5, a4, 24
	sb a5, 11(s0)
	lwu a4, 76(a3)
	sb a4, 12(s0)
	srli a5, a4, 8
	sb a5, 13(s0)
	srli a5, a4, 16
	sb a5, 14(s0)
	srli a5, a4, 24
	sb a5, 15(s0)
	lwu a4, 80(a3)
	sb a4, 16(s0)
	srli a5, a4, 8
	sb a5, 17(s0)
	srli a5, a4, 16
	sb a5, 18(s0)
	srli a5, a4, 24
	sb a5, 19(s0)
	lwu a4, 84(a3)
	sb a4, 20(s0)
	srli a5, a4, 8
	sb a5, 21(s0)
	srli a5, a4, 16
	sb a5, 22(s0)
	srli a5, a4, 24
	sb a5, 23(s0)
	lwu a4, 88(a3)
	sb a4, 24(s0)
	srli a5, a4, 8
	sb a5, 25(s0)
	srli a5, a4, 16
	sb a5, 26(s0)
	srli a5, a4, 24
	sb a5, 27(s0)
	lwu a4, 92(a3)
	sb a4, 28(s0)
	srli a5, a4, 8
	sb a5, 29(s0)
	srli a5, a4, 16
	sb a5, 30(s0)
	srli a5, a4, 24
	sb a5, 31(s0)
	lwu a4, 96(a3)
	sb a4, 32(s0)
	srli a5, a4, 8
	sb a5, 33(s0)
	srli a5, a4, 16
	sb a5, 34(s0)
	srli a5, a4, 24
	sb a5, 35(s0)
	lwu a4, 100(a3)
	sb a4, 36(s0)
	srli a5, a4, 8
	sb a5, 37(s0)
	srli a5, a4, 16
	sb a5, 38(s0)
	srli a5, a4, 24
	sb a5, 39(s0)
	lwu a4, 104(a3)
	sb a4, 40(s0)
	srli a5, a4, 8
	sb a5, 41(s0)
	srli a5, a4, 16
	sb a5, 42(s0)
	srli a5, a4, 24
	sb a5, 43(s0)
	lwu a4, 108(a3)
	sb a4, 44(s0)
	srli a5, a4, 8
	sb a5, 45(s0)
	srli a5, a4, 16
	sb a5, 46(s0)
	srli a5, a4, 24
	sb a5, 47(s0)
	lwu a4, 112(a3)
	sb a4, 48(s0)
	srli a5, a4, 8
	sb a5, 49(s0)
	srli a5, a4, 16
	sb a5, 50(s0)
	srli a5, a4, 24
	sb a5, 51(s0)
	lwu a4, 116(a3)
	sb a4, 52(s0)
	srli a5, a4, 8
	sb a5, 53(s0)
	srli a5, a4, 16
	sb a5, 54(s0)
	srli a5, a4, 24
	sb a5, 55(s0)
	lwu a4, 120(a3)
	sb a4, 56(s0)
	srli a5, a4, 8
	sb a5, 57(s0)
	srli a5, a4, 16
	sb a5, 58(s0)
	srli a5, a4, 24
	sb a5, 59(s0)
	lwu a4, 124(a3)
	sb a4, 60(s0)
	srli a5, a4, 8
	sb a5, 61(s0)
	srli a5, a4, 16
	sb a5, 62(s0)
	srli a5, a4, 24
	sb a5, 63(s0)
	lwu a4, 128(a3)
	sb a4, 64(s0)
	srli a5, a4, 8
	sb a5, 65(s0)
	srli a5, a4, 16
	sb a5, 66(s0)
	srli a5, a4, 24
	sb a5, 67(s0)
	lwu a4, 132(a3)
	sb a4, 68(s0)
	srli a5, a4, 8
	sb a5, 69(s0)
	srli a5, a4, 16
	sb a5, 70(s0)
	srli a5, a4, 24
	sb a5, 71(s0)
	lwu a4, 136(a3)
	sb a4, 72(s0)
	srli a5, a4, 8
	sb a5, 73(s0)
	srli a5, a4, 16
	sb a5, 74(s0)
	srli a5, a4, 24
	sb a5, 75(s0)
	lwu a4, 140(a3)
	sb a4, 76(s0)
	srli a5, a4, 8
	sb a5, 77(s0)
	srli a5, a4, 16
	sb a5, 78(s0)
	srli a5, a4, 24
	sb a5, 79(s0)
	lwu a4, 144(a3)
	sb a4, 80(s0)
	srli a5, a4, 8
	sb a5, 81(s0)
	srli a5, a4, 16
	sb a5, 82(s0)
	srli a5, a4, 24
	sb a5, 83(s0)
	lwu a4, 148(a3)
	sb a4, 84(s0)
	srli a5, a4, 8
	sb a5, 85(s0)
	srli a5, a4, 16
	sb a5, 86(s0)
	srli a5, a4, 24
	sb a5, 87(s0)
	lwu a4, 152(a3)
	sb a4, 88(s0)
	srli a5, a4, 8
	sb a5, 89(s0)
	srli a5, a4, 16
	sb a5, 90(s0)
	srli a5, a4, 24
	sb a5, 91(s0)
	lwu a4, 156(a3)
	sb a4, 92(s0)
	srli a5, a4, 8
	sb a5, 93(s0)
	srli a5, a4, 16
	sb a5, 94(s0)
	srli a5, a4, 24
	sb a5, 95(s0)
	lwu a4, 160(a3)
	sb a4, 96(s0)
	srli a5, a4, 8
	sb a5, 97(s0)
	srli a5, a4, 16
	sb a5, 98(s0)
	srli a5, a4, 24
	sb a5, 99(s0)
	lwu a4, 164(a3)
	sb a4, 100(s0)
	srli a5, a4, 8
	sb a5, 101(s0)
	srli a5, a4, 16
	sb a5, 102(s0)
	srli a5, a4, 24
	sb a5, 103(s0)
	lwu a4, 168(a3)
	sb a4, 104(s0)
	srli a5, a4, 8
	sb a5, 105(s0)
	srli a5, a4, 16
	sb a5, 106(s0)
	srli a5, a4, 24
	sb a5, 107(s0)
	lwu a4, 172(a3)
	sb a4, 108(s0)
	srli a5, a4, 8
	sb a5, 109(s0)
	srli a5, a4, 16
	sb a5, 110(s0)
	srli a5, a4, 24
	sb a5, 111(s0)
	lwu a4, 176(a3)
	sb a4, 112(s0)
	srli a5, a4, 8
	sb a5, 113(s0)
	srli a5, a4, 16
	sb a5, 114(s0)
	srli a5, a4, 24
	sb a5, 115(s0)
	lwu a4, 180(a3)
	sb a4, 116(s0)
	srli a5, a4, 8
	sb a5, 117(s0)
	srli a5, a4, 16
	sb a5, 118(s0)
	srli a5, a4, 24
	sb a5, 119(s0)
	lwu a4, 184(a3)
	sb a4, 120(s0)
	srli a5, a4, 8
	sb a5, 121(s0)
	srli a5, a4, 16
	sb a5, 122(s0)
	srli a5, a4, 24
	sb a5, 123(s0)
	lwu a4, 188(a3)
	sb a4, 124(s0)
	srli a5, a4, 8
	sb a5, 125(s0)
	srli a5, a4, 16
	sb a5, 126(s0)
	srli a5, a4, 24
	sb a5, 127(s0)
	lwu a4, 64(a3)
	sw a4, 192(a3)
	lwu a4, 68(a3)
	sw a4, 196(a3)
	lwu a4, 72(a3)
	sw a4, 200(a3)
	lwu a4, 76(a3)
	sw a4, 204(a3)
	lwu a4, 80(a3)
	sw a4, 208(a3)
	lwu a4, 84(a3)
	sw a4, 212(a3)
	lwu a4, 88(a3)
	sw a4, 216(a3)
	lwu a4, 92(a3)
	sw a4, 220(a3)
	lwu a4, 96(a3)
	sw a4, 224(a3)
	lwu a4, 100(a3)
	sw a4, 228(a3)
	lwu a4, 104(a3)
	sw a4, 232(a3)
	lwu a4, 108(a3)
	sw a4, 236(a3)
	lwu a4, 112(a3)
	sw a4, 240(a3)
	lwu a4, 116(a3)
	sw a4, 244(a3)
	lwu a4, 120(a3)
	sw a4, 248(a3)
	lwu a4, 124(a3)
	sw a4, 252(a3)
	lwu a4, 128(a3)
	sw a4, 256(a3)
	lwu a4, 132(a3)
	sw a4, 260(a3)
	lwu a4, 136(a3)
	sw a4, 264(a3)
	lwu a4, 140(a3)
	sw a4, 268(a3)
	lwu a4, 144(a3)
	sw a4, 272(a3)
	lwu a4, 148(a3)
	sw a4, 276(a3)
	lwu a4, 152(a3)
	sw a4, 280(a3)
	lwu a4, 156(a3)
	sw a4, 284(a3)
	lwu a4, 160(a3)
	sw a4, 288(a3)
	lwu a4, 164(a3)
	sw a4, 292(a3)
	lwu a4, 168(a3)
	sw a4, 296(a3)
	lwu a4, 172(a3)
	sw a4, 300(a3)
	lwu a4, 176(a3)
	sw a4, 304(a3)
	lwu a4, 180(a3)
	sw a4, 308(a3)
	lwu a4, 184(a3)
	sw a4, 312(a3)
	lwu a4, 188(a3)
	sw a4, 316(a3)
	addi a0, a3, 0
	call {vg_ed25519_r32_point_add}
	addi a3, a0, 0
	addi s2, s2, 1
	addi a4, s2, -16
	bnez a4, 23b
	lwu a4, 608(a3)
	sw a4, 64(a3)
	lwu a4, 612(a3)
	sw a4, 68(a3)
	lwu a4, 616(a3)
	sw a4, 72(a3)
	lwu a4, 620(a3)
	sw a4, 76(a3)
	lwu a4, 624(a3)
	sw a4, 80(a3)
	lwu a4, 628(a3)
	sw a4, 84(a3)
	lwu a4, 632(a3)
	sw a4, 88(a3)
	lwu a4, 636(a3)
	sw a4, 92(a3)
	lwu a4, 640(a3)
	sw a4, 96(a3)
	lwu a4, 644(a3)
	sw a4, 100(a3)
	lwu a4, 648(a3)
	sw a4, 104(a3)
	lwu a4, 652(a3)
	sw a4, 108(a3)
	lwu a4, 656(a3)
	sw a4, 112(a3)
	lwu a4, 660(a3)
	sw a4, 116(a3)
	lwu a4, 664(a3)
	sw a4, 120(a3)
	lwu a4, 668(a3)
	sw a4, 124(a3)
	lwu a4, 672(a3)
	sw a4, 128(a3)
	lwu a4, 676(a3)
	sw a4, 132(a3)
	lwu a4, 680(a3)
	sw a4, 136(a3)
	lwu a4, 684(a3)
	sw a4, 140(a3)
	lwu a4, 688(a3)
	sw a4, 144(a3)
	lwu a4, 692(a3)
	sw a4, 148(a3)
	lwu a4, 696(a3)
	sw a4, 152(a3)
	lwu a4, 700(a3)
	sw a4, 156(a3)
	lwu a4, 704(a3)
	sw a4, 160(a3)
	lwu a4, 708(a3)
	sw a4, 164(a3)
	lwu a4, 712(a3)
	sw a4, 168(a3)
	lwu a4, 716(a3)
	sw a4, 172(a3)
	lwu a4, 720(a3)
	sw a4, 176(a3)
	lwu a4, 724(a3)
	sw a4, 180(a3)
	lwu a4, 728(a3)
	sw a4, 184(a3)
	lwu a4, 732(a3)
	sw a4, 188(a3)
	slli a4, s6, 1
	add s0, s5, a4
	lbu a4, 0(s0)
	lbu a5, 1(s0)
	slli a5, a5, 8
	add a4, a4, a5
	slli a5, a4, 63
	srli a5, a5, 63
	sb a5, 32(a3)
	slli a5, a4, 62
	srli a5, a5, 63
	sb a5, 33(a3)
	slli a5, a4, 61
	srli a5, a5, 63
	sb a5, 34(a3)
	slli a5, a4, 60
	srli a5, a5, 63
	sb a5, 35(a3)
	slli a5, a4, 59
	srli a5, a5, 63
	sb a5, 36(a3)
	slli a5, a4, 58
	srli a5, a5, 63
	sb a5, 37(a3)
	slli a5, a4, 57
	srli a5, a5, 63
	sb a5, 38(a3)
	slli a5, a4, 56
	srli a5, a5, 63
	sb a5, 39(a3)
	slli a5, a4, 55
	srli a5, a5, 63
	sb a5, 40(a3)
	slli a5, a4, 54
	srli a5, a5, 63
	sb a5, 41(a3)
	slli a5, a4, 53
	srli a5, a5, 63
	sb a5, 42(a3)
	slli a5, a4, 52
	srli a5, a5, 63
	sb a5, 43(a3)
	slli a5, a4, 51
	srli a5, a5, 63
	sb a5, 44(a3)
	slli a5, a4, 50
	srli a5, a5, 63
	sb a5, 45(a3)
	slli a5, a4, 49
	srli a5, a5, 63
	sb a5, 46(a3)
	slli a5, a4, 48
	srli a5, a5, 63
	sb a5, 47(a3)
	addi s2, zero, 16
24:
	addi s2, s2, -1
	lwu a4, 64(a3)
	sw a4, 608(a3)
	lwu a4, 68(a3)
	sw a4, 612(a3)
	lwu a4, 72(a3)
	sw a4, 616(a3)
	lwu a4, 76(a3)
	sw a4, 620(a3)
	lwu a4, 80(a3)
	sw a4, 624(a3)
	lwu a4, 84(a3)
	sw a4, 628(a3)
	lwu a4, 88(a3)
	sw a4, 632(a3)
	lwu a4, 92(a3)
	sw a4, 636(a3)
	lwu a4, 96(a3)
	sw a4, 640(a3)
	lwu a4, 100(a3)
	sw a4, 644(a3)
	lwu a4, 104(a3)
	sw a4, 648(a3)
	lwu a4, 108(a3)
	sw a4, 652(a3)
	lwu a4, 112(a3)
	sw a4, 656(a3)
	lwu a4, 116(a3)
	sw a4, 660(a3)
	lwu a4, 120(a3)
	sw a4, 664(a3)
	lwu a4, 124(a3)
	sw a4, 668(a3)
	lwu a4, 128(a3)
	sw a4, 672(a3)
	lwu a4, 132(a3)
	sw a4, 676(a3)
	lwu a4, 136(a3)
	sw a4, 680(a3)
	lwu a4, 140(a3)
	sw a4, 684(a3)
	lwu a4, 144(a3)
	sw a4, 688(a3)
	lwu a4, 148(a3)
	sw a4, 692(a3)
	lwu a4, 152(a3)
	sw a4, 696(a3)
	lwu a4, 156(a3)
	sw a4, 700(a3)
	lwu a4, 160(a3)
	sw a4, 704(a3)
	lwu a4, 164(a3)
	sw a4, 708(a3)
	lwu a4, 168(a3)
	sw a4, 712(a3)
	lwu a4, 172(a3)
	sw a4, 716(a3)
	lwu a4, 176(a3)
	sw a4, 720(a3)
	lwu a4, 180(a3)
	sw a4, 724(a3)
	lwu a4, 184(a3)
	sw a4, 728(a3)
	lwu a4, 188(a3)
	sw a4, 732(a3)
	lui s0, 1
	addiw s0, s0, 1632
	add s0, a3, s0
	slli a4, s2, 7
	add s0, s0, a4
	lbu a4, 0(s0)
	lbu a5, 1(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 2(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 3(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 64(a3)
	lbu a4, 4(s0)
	lbu a5, 5(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 6(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 7(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 68(a3)
	lbu a4, 8(s0)
	lbu a5, 9(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 10(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 11(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 72(a3)
	lbu a4, 12(s0)
	lbu a5, 13(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 14(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 15(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 76(a3)
	lbu a4, 16(s0)
	lbu a5, 17(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 18(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 19(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 80(a3)
	lbu a4, 20(s0)
	lbu a5, 21(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 22(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 23(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 84(a3)
	lbu a4, 24(s0)
	lbu a5, 25(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 26(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 27(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 88(a3)
	lbu a4, 28(s0)
	lbu a5, 29(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 30(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 31(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 92(a3)
	lbu a4, 32(s0)
	lbu a5, 33(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 34(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 35(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 96(a3)
	lbu a4, 36(s0)
	lbu a5, 37(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 38(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 39(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 100(a3)
	lbu a4, 40(s0)
	lbu a5, 41(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 42(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 43(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 104(a3)
	lbu a4, 44(s0)
	lbu a5, 45(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 46(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 47(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 108(a3)
	lbu a4, 48(s0)
	lbu a5, 49(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 50(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 51(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 112(a3)
	lbu a4, 52(s0)
	lbu a5, 53(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 54(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 55(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 116(a3)
	lbu a4, 56(s0)
	lbu a5, 57(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 58(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 59(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 120(a3)
	lbu a4, 60(s0)
	lbu a5, 61(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 62(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 63(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 124(a3)
	lbu a4, 64(s0)
	lbu a5, 65(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 66(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 67(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 128(a3)
	lbu a4, 68(s0)
	lbu a5, 69(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 70(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 71(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 132(a3)
	lbu a4, 72(s0)
	lbu a5, 73(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 74(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 75(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 136(a3)
	lbu a4, 76(s0)
	lbu a5, 77(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 78(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 79(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 140(a3)
	lbu a4, 80(s0)
	lbu a5, 81(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 82(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 83(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 144(a3)
	lbu a4, 84(s0)
	lbu a5, 85(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 86(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 87(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 148(a3)
	lbu a4, 88(s0)
	lbu a5, 89(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 90(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 91(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 152(a3)
	lbu a4, 92(s0)
	lbu a5, 93(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 94(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 95(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 156(a3)
	lbu a4, 96(s0)
	lbu a5, 97(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 98(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 99(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 160(a3)
	lbu a4, 100(s0)
	lbu a5, 101(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 102(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 103(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 164(a3)
	lbu a4, 104(s0)
	lbu a5, 105(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 106(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 107(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 168(a3)
	lbu a4, 108(s0)
	lbu a5, 109(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 110(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 111(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 172(a3)
	lbu a4, 112(s0)
	lbu a5, 113(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 114(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 115(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 176(a3)
	lbu a4, 116(s0)
	lbu a5, 117(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 118(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 119(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 180(a3)
	lbu a4, 120(s0)
	lbu a5, 121(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 122(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 123(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 184(a3)
	lbu a4, 124(s0)
	lbu a5, 125(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 126(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 127(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 188(a3)
	lwu a4, 64(a3)
	sw a4, 192(a3)
	lwu a4, 68(a3)
	sw a4, 196(a3)
	lwu a4, 72(a3)
	sw a4, 200(a3)
	lwu a4, 76(a3)
	sw a4, 204(a3)
	lwu a4, 80(a3)
	sw a4, 208(a3)
	lwu a4, 84(a3)
	sw a4, 212(a3)
	lwu a4, 88(a3)
	sw a4, 216(a3)
	lwu a4, 92(a3)
	sw a4, 220(a3)
	lwu a4, 96(a3)
	sw a4, 224(a3)
	lwu a4, 100(a3)
	sw a4, 228(a3)
	lwu a4, 104(a3)
	sw a4, 232(a3)
	lwu a4, 108(a3)
	sw a4, 236(a3)
	lwu a4, 112(a3)
	sw a4, 240(a3)
	lwu a4, 116(a3)
	sw a4, 244(a3)
	lwu a4, 120(a3)
	sw a4, 248(a3)
	lwu a4, 124(a3)
	sw a4, 252(a3)
	lwu a4, 128(a3)
	sw a4, 256(a3)
	lwu a4, 132(a3)
	sw a4, 260(a3)
	lwu a4, 136(a3)
	sw a4, 264(a3)
	lwu a4, 140(a3)
	sw a4, 268(a3)
	lwu a4, 144(a3)
	sw a4, 272(a3)
	lwu a4, 148(a3)
	sw a4, 276(a3)
	lwu a4, 152(a3)
	sw a4, 280(a3)
	lwu a4, 156(a3)
	sw a4, 284(a3)
	lwu a4, 160(a3)
	sw a4, 288(a3)
	lwu a4, 164(a3)
	sw a4, 292(a3)
	lwu a4, 168(a3)
	sw a4, 296(a3)
	lwu a4, 172(a3)
	sw a4, 300(a3)
	lwu a4, 176(a3)
	sw a4, 304(a3)
	lwu a4, 180(a3)
	sw a4, 308(a3)
	lwu a4, 184(a3)
	sw a4, 312(a3)
	lwu a4, 188(a3)
	sw a4, 316(a3)
	lwu a4, 608(a3)
	sw a4, 64(a3)
	lwu a4, 612(a3)
	sw a4, 68(a3)
	lwu a4, 616(a3)
	sw a4, 72(a3)
	lwu a4, 620(a3)
	sw a4, 76(a3)
	lwu a4, 624(a3)
	sw a4, 80(a3)
	lwu a4, 628(a3)
	sw a4, 84(a3)
	lwu a4, 632(a3)
	sw a4, 88(a3)
	lwu a4, 636(a3)
	sw a4, 92(a3)
	lwu a4, 640(a3)
	sw a4, 96(a3)
	lwu a4, 644(a3)
	sw a4, 100(a3)
	lwu a4, 648(a3)
	sw a4, 104(a3)
	lwu a4, 652(a3)
	sw a4, 108(a3)
	lwu a4, 656(a3)
	sw a4, 112(a3)
	lwu a4, 660(a3)
	sw a4, 116(a3)
	lwu a4, 664(a3)
	sw a4, 120(a3)
	lwu a4, 668(a3)
	sw a4, 124(a3)
	lwu a4, 672(a3)
	sw a4, 128(a3)
	lwu a4, 676(a3)
	sw a4, 132(a3)
	lwu a4, 680(a3)
	sw a4, 136(a3)
	lwu a4, 684(a3)
	sw a4, 140(a3)
	lwu a4, 688(a3)
	sw a4, 144(a3)
	lwu a4, 692(a3)
	sw a4, 148(a3)
	lwu a4, 696(a3)
	sw a4, 152(a3)
	lwu a4, 700(a3)
	sw a4, 156(a3)
	lwu a4, 704(a3)
	sw a4, 160(a3)
	lwu a4, 708(a3)
	sw a4, 164(a3)
	lwu a4, 712(a3)
	sw a4, 168(a3)
	lwu a4, 716(a3)
	sw a4, 172(a3)
	lwu a4, 720(a3)
	sw a4, 176(a3)
	lwu a4, 724(a3)
	sw a4, 180(a3)
	lwu a4, 728(a3)
	sw a4, 184(a3)
	lwu a4, 732(a3)
	sw a4, 188(a3)
	addi a0, a3, 0
	call {vg_ed25519_r32_point_add}
	addi a3, a0, 0
	add a4, a3, s2
	lbu a4, 32(a4)
	addi t0, a4, -1
	lwu a2, 64(a3)
	lwu a4, 608(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 64(a3)
	sw a4, 608(a3)
	lwu a2, 68(a3)
	lwu a4, 612(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 68(a3)
	sw a4, 612(a3)
	lwu a2, 72(a3)
	lwu a4, 616(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 72(a3)
	sw a4, 616(a3)
	lwu a2, 76(a3)
	lwu a4, 620(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 76(a3)
	sw a4, 620(a3)
	lwu a2, 80(a3)
	lwu a4, 624(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 80(a3)
	sw a4, 624(a3)
	lwu a2, 84(a3)
	lwu a4, 628(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 84(a3)
	sw a4, 628(a3)
	lwu a2, 88(a3)
	lwu a4, 632(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 88(a3)
	sw a4, 632(a3)
	lwu a2, 92(a3)
	lwu a4, 636(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 92(a3)
	sw a4, 636(a3)
	lwu a2, 96(a3)
	lwu a4, 640(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 96(a3)
	sw a4, 640(a3)
	lwu a2, 100(a3)
	lwu a4, 644(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 100(a3)
	sw a4, 644(a3)
	lwu a2, 104(a3)
	lwu a4, 648(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 104(a3)
	sw a4, 648(a3)
	lwu a2, 108(a3)
	lwu a4, 652(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 108(a3)
	sw a4, 652(a3)
	lwu a2, 112(a3)
	lwu a4, 656(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 112(a3)
	sw a4, 656(a3)
	lwu a2, 116(a3)
	lwu a4, 660(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 116(a3)
	sw a4, 660(a3)
	lwu a2, 120(a3)
	lwu a4, 664(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 120(a3)
	sw a4, 664(a3)
	lwu a2, 124(a3)
	lwu a4, 668(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 124(a3)
	sw a4, 668(a3)
	lwu a2, 128(a3)
	lwu a4, 672(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 128(a3)
	sw a4, 672(a3)
	lwu a2, 132(a3)
	lwu a4, 676(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 132(a3)
	sw a4, 676(a3)
	lwu a2, 136(a3)
	lwu a4, 680(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 136(a3)
	sw a4, 680(a3)
	lwu a2, 140(a3)
	lwu a4, 684(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 140(a3)
	sw a4, 684(a3)
	lwu a2, 144(a3)
	lwu a4, 688(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 144(a3)
	sw a4, 688(a3)
	lwu a2, 148(a3)
	lwu a4, 692(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 148(a3)
	sw a4, 692(a3)
	lwu a2, 152(a3)
	lwu a4, 696(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 152(a3)
	sw a4, 696(a3)
	lwu a2, 156(a3)
	lwu a4, 700(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 156(a3)
	sw a4, 700(a3)
	lwu a2, 160(a3)
	lwu a4, 704(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 160(a3)
	sw a4, 704(a3)
	lwu a2, 164(a3)
	lwu a4, 708(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 164(a3)
	sw a4, 708(a3)
	lwu a2, 168(a3)
	lwu a4, 712(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 168(a3)
	sw a4, 712(a3)
	lwu a2, 172(a3)
	lwu a4, 716(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 172(a3)
	sw a4, 716(a3)
	lwu a2, 176(a3)
	lwu a4, 720(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 176(a3)
	sw a4, 720(a3)
	lwu a2, 180(a3)
	lwu a4, 724(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 180(a3)
	sw a4, 724(a3)
	lwu a2, 184(a3)
	lwu a4, 728(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 184(a3)
	sw a4, 728(a3)
	lwu a2, 188(a3)
	lwu a4, 732(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 188(a3)
	sw a4, 732(a3)
	bnez s2, 24b
	bnez s6, 22b
	addi a0, a3, 0
	call {vg_gf25519_r32_pow250}
	addi a3, a0, 0
	addi t1, zero, 5
25:
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
	bnez t1, 25b
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
