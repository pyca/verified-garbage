// The functions of `src/gcm.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ghash:
	.option push
	.option arch, +m, +c
	beqz a3, 20f
	addi sp, sp, -2032
	addi sp, sp, -16
	lbu a6, 0(a0)
	slli a6, a6, 8
	lbu t3, 1(a0)
	or a6, a6, t3
	slli a6, a6, 8
	lbu t3, 2(a0)
	or a6, a6, t3
	slli a6, a6, 8
	lbu t3, 3(a0)
	or a6, a6, t3
	slli a6, a6, 8
	lbu t3, 4(a0)
	or a6, a6, t3
	slli a6, a6, 8
	lbu t3, 5(a0)
	or a6, a6, t3
	slli a6, a6, 8
	lbu t3, 6(a0)
	or a6, a6, t3
	slli a6, a6, 8
	lbu t3, 7(a0)
	or a6, a6, t3
	lbu a7, 8(a0)
	slli a7, a7, 8
	lbu t3, 9(a0)
	or a7, a7, t3
	slli a7, a7, 8
	lbu t3, 10(a0)
	or a7, a7, t3
	slli a7, a7, 8
	lbu t3, 11(a0)
	or a7, a7, t3
	slli a7, a7, 8
	lbu t3, 12(a0)
	or a7, a7, t3
	slli a7, a7, 8
	lbu t3, 13(a0)
	or a7, a7, t3
	slli a7, a7, 8
	lbu t3, 14(a0)
	or a7, a7, t3
	slli a7, a7, 8
	lbu t3, 15(a0)
	or a7, a7, t3
	addi t6, zero, -31
	slli t6, t6, 56
	addi t4, sp, 0
	addi t5, t4, 1024
	addi t5, t5, 1024
22:
	sd a6, 0(t4)
	sd a7, 8(t4)
	slli t2, a7, 63
	srai t2, t2, 63
	and t2, t2, t6
	slli t3, a6, 63
	srli a7, a7, 1
	or a7, a7, t3
	srli a6, a6, 1
	xor a6, a6, t2
	sd a6, 16(t4)
	sd a7, 24(t4)
	slli t2, a7, 63
	srai t2, t2, 63
	and t2, t2, t6
	slli t3, a6, 63
	srli a7, a7, 1
	or a7, a7, t3
	srli a6, a6, 1
	xor a6, a6, t2
	sd a6, 32(t4)
	sd a7, 40(t4)
	slli t2, a7, 63
	srai t2, t2, 63
	and t2, t2, t6
	slli t3, a6, 63
	srli a7, a7, 1
	or a7, a7, t3
	srli a6, a6, 1
	xor a6, a6, t2
	sd a6, 48(t4)
	sd a7, 56(t4)
	slli t2, a7, 63
	srai t2, t2, 63
	and t2, t2, t6
	slli t3, a6, 63
	srli a7, a7, 1
	or a7, a7, t3
	srli a6, a6, 1
	xor a6, a6, t2
	sd a6, 64(t4)
	sd a7, 72(t4)
	slli t2, a7, 63
	srai t2, t2, 63
	and t2, t2, t6
	slli t3, a6, 63
	srli a7, a7, 1
	or a7, a7, t3
	srli a6, a6, 1
	xor a6, a6, t2
	sd a6, 80(t4)
	sd a7, 88(t4)
	slli t2, a7, 63
	srai t2, t2, 63
	and t2, t2, t6
	slli t3, a6, 63
	srli a7, a7, 1
	or a7, a7, t3
	srli a6, a6, 1
	xor a6, a6, t2
	sd a6, 96(t4)
	sd a7, 104(t4)
	slli t2, a7, 63
	srai t2, t2, 63
	and t2, t2, t6
	slli t3, a6, 63
	srli a7, a7, 1
	or a7, a7, t3
	srli a6, a6, 1
	xor a6, a6, t2
	sd a6, 112(t4)
	sd a7, 120(t4)
	slli t2, a7, 63
	srai t2, t2, 63
	and t2, t2, t6
	slli t3, a6, 63
	srli a7, a7, 1
	or a7, a7, t3
	srli a6, a6, 1
	xor a6, a6, t2
	addi t4, t4, 128
	bne t4, t5, 22b
	lbu a4, 0(a1)
	slli a4, a4, 8
	lbu t3, 1(a1)
	or a4, a4, t3
	slli a4, a4, 8
	lbu t3, 2(a1)
	or a4, a4, t3
	slli a4, a4, 8
	lbu t3, 3(a1)
	or a4, a4, t3
	slli a4, a4, 8
	lbu t3, 4(a1)
	or a4, a4, t3
	slli a4, a4, 8
	lbu t3, 5(a1)
	or a4, a4, t3
	slli a4, a4, 8
	lbu t3, 6(a1)
	or a4, a4, t3
	slli a4, a4, 8
	lbu t3, 7(a1)
	or a4, a4, t3
	lbu a5, 8(a1)
	slli a5, a5, 8
	lbu t3, 9(a1)
	or a5, a5, t3
	slli a5, a5, 8
	lbu t3, 10(a1)
	or a5, a5, t3
	slli a5, a5, 8
	lbu t3, 11(a1)
	or a5, a5, t3
	slli a5, a5, 8
	lbu t3, 12(a1)
	or a5, a5, t3
	slli a5, a5, 8
	lbu t3, 13(a1)
	or a5, a5, t3
	slli a5, a5, 8
	lbu t3, 14(a1)
	or a5, a5, t3
	slli a5, a5, 8
	lbu t3, 15(a1)
	or a5, a5, t3
23:
	lbu a6, 0(a2)
	slli a6, a6, 8
	lbu t3, 1(a2)
	or a6, a6, t3
	slli a6, a6, 8
	lbu t3, 2(a2)
	or a6, a6, t3
	slli a6, a6, 8
	lbu t3, 3(a2)
	or a6, a6, t3
	slli a6, a6, 8
	lbu t3, 4(a2)
	or a6, a6, t3
	slli a6, a6, 8
	lbu t3, 5(a2)
	or a6, a6, t3
	slli a6, a6, 8
	lbu t3, 6(a2)
	or a6, a6, t3
	slli a6, a6, 8
	lbu t3, 7(a2)
	or a6, a6, t3
	lbu a7, 8(a2)
	slli a7, a7, 8
	lbu t3, 9(a2)
	or a7, a7, t3
	slli a7, a7, 8
	lbu t3, 10(a2)
	or a7, a7, t3
	slli a7, a7, 8
	lbu t3, 11(a2)
	or a7, a7, t3
	slli a7, a7, 8
	lbu t3, 12(a2)
	or a7, a7, t3
	slli a7, a7, 8
	lbu t3, 13(a2)
	or a7, a7, t3
	slli a7, a7, 8
	lbu t3, 14(a2)
	or a7, a7, t3
	slli a7, a7, 8
	lbu t3, 15(a2)
	or a7, a7, t3
	xor a6, a6, a4
	xor a7, a7, a5
	addi a4, zero, 0
	addi a5, zero, 0
	addi t4, sp, 0
24:
	slli t2, a6, 0
	srai t2, t2, 63
	ld t0, 0(t4)
	ld t1, 8(t4)
	and t0, t0, t2
	and t1, t1, t2
	xor a4, a4, t0
	xor a5, a5, t1
	slli t2, a6, 1
	srai t2, t2, 63
	ld t0, 16(t4)
	ld t1, 24(t4)
	and t0, t0, t2
	and t1, t1, t2
	xor a4, a4, t0
	xor a5, a5, t1
	slli t2, a6, 2
	srai t2, t2, 63
	ld t0, 32(t4)
	ld t1, 40(t4)
	and t0, t0, t2
	and t1, t1, t2
	xor a4, a4, t0
	xor a5, a5, t1
	slli t2, a6, 3
	srai t2, t2, 63
	ld t0, 48(t4)
	ld t1, 56(t4)
	and t0, t0, t2
	and t1, t1, t2
	xor a4, a4, t0
	xor a5, a5, t1
	slli t2, a6, 4
	srai t2, t2, 63
	ld t0, 64(t4)
	ld t1, 72(t4)
	and t0, t0, t2
	and t1, t1, t2
	xor a4, a4, t0
	xor a5, a5, t1
	slli t2, a6, 5
	srai t2, t2, 63
	ld t0, 80(t4)
	ld t1, 88(t4)
	and t0, t0, t2
	and t1, t1, t2
	xor a4, a4, t0
	xor a5, a5, t1
	slli t2, a6, 6
	srai t2, t2, 63
	ld t0, 96(t4)
	ld t1, 104(t4)
	and t0, t0, t2
	and t1, t1, t2
	xor a4, a4, t0
	xor a5, a5, t1
	slli t2, a6, 7
	srai t2, t2, 63
	ld t0, 112(t4)
	ld t1, 120(t4)
	and t0, t0, t2
	and t1, t1, t2
	xor a4, a4, t0
	xor a5, a5, t1
	slli a6, a6, 8
	srli t3, a7, 56
	or a6, a6, t3
	slli a7, a7, 8
	addi t4, t4, 128
	bne t4, t5, 24b
	addi a2, a2, 16
	addi a3, a3, -1
	bnez a3, 23b
	srli t3, a4, 56
	sb t3, 0(a1)
	srli t3, a4, 48
	sb t3, 1(a1)
	srli t3, a4, 40
	sb t3, 2(a1)
	srli t3, a4, 32
	sb t3, 3(a1)
	srli t3, a4, 24
	sb t3, 4(a1)
	srli t3, a4, 16
	sb t3, 5(a1)
	srli t3, a4, 8
	sb t3, 6(a1)
	srli t3, a4, 0
	sb t3, 7(a1)
	srli t3, a5, 56
	sb t3, 8(a1)
	srli t3, a5, 48
	sb t3, 9(a1)
	srli t3, a5, 40
	sb t3, 10(a1)
	srli t3, a5, 32
	sb t3, 11(a1)
	srli t3, a5, 24
	sb t3, 12(a1)
	srli t3, a5, 16
	sb t3, 13(a1)
	srli t3, a5, 8
	sb t3, 14(a1)
	srli t3, a5, 0
	sb t3, 15(a1)
	addi t5, sp, 0
	addi t6, zero, 0
	sd t6, 0(t5)
	sd t6, 8(t5)
	sd t6, 16(t5)
	sd t6, 24(t5)
	sd t6, 32(t5)
	sd t6, 40(t5)
	sd t6, 48(t5)
	sd t6, 56(t5)
	sd t6, 64(t5)
	sd t6, 72(t5)
	sd t6, 80(t5)
	sd t6, 88(t5)
	sd t6, 96(t5)
	sd t6, 104(t5)
	sd t6, 112(t5)
	sd t6, 120(t5)
	sd t6, 128(t5)
	sd t6, 136(t5)
	sd t6, 144(t5)
	sd t6, 152(t5)
	sd t6, 160(t5)
	sd t6, 168(t5)
	sd t6, 176(t5)
	sd t6, 184(t5)
	sd t6, 192(t5)
	sd t6, 200(t5)
	sd t6, 208(t5)
	sd t6, 216(t5)
	sd t6, 224(t5)
	sd t6, 232(t5)
	sd t6, 240(t5)
	sd t6, 248(t5)
	sd t6, 256(t5)
	sd t6, 264(t5)
	sd t6, 272(t5)
	sd t6, 280(t5)
	sd t6, 288(t5)
	sd t6, 296(t5)
	sd t6, 304(t5)
	sd t6, 312(t5)
	sd t6, 320(t5)
	sd t6, 328(t5)
	sd t6, 336(t5)
	sd t6, 344(t5)
	sd t6, 352(t5)
	sd t6, 360(t5)
	sd t6, 368(t5)
	sd t6, 376(t5)
	sd t6, 384(t5)
	sd t6, 392(t5)
	sd t6, 400(t5)
	sd t6, 408(t5)
	sd t6, 416(t5)
	sd t6, 424(t5)
	sd t6, 432(t5)
	sd t6, 440(t5)
	sd t6, 448(t5)
	sd t6, 456(t5)
	sd t6, 464(t5)
	sd t6, 472(t5)
	sd t6, 480(t5)
	sd t6, 488(t5)
	sd t6, 496(t5)
	sd t6, 504(t5)
	sd t6, 512(t5)
	sd t6, 520(t5)
	sd t6, 528(t5)
	sd t6, 536(t5)
	sd t6, 544(t5)
	sd t6, 552(t5)
	sd t6, 560(t5)
	sd t6, 568(t5)
	sd t6, 576(t5)
	sd t6, 584(t5)
	sd t6, 592(t5)
	sd t6, 600(t5)
	sd t6, 608(t5)
	sd t6, 616(t5)
	sd t6, 624(t5)
	sd t6, 632(t5)
	sd t6, 640(t5)
	sd t6, 648(t5)
	sd t6, 656(t5)
	sd t6, 664(t5)
	sd t6, 672(t5)
	sd t6, 680(t5)
	sd t6, 688(t5)
	sd t6, 696(t5)
	sd t6, 704(t5)
	sd t6, 712(t5)
	sd t6, 720(t5)
	sd t6, 728(t5)
	sd t6, 736(t5)
	sd t6, 744(t5)
	sd t6, 752(t5)
	sd t6, 760(t5)
	sd t6, 768(t5)
	sd t6, 776(t5)
	sd t6, 784(t5)
	sd t6, 792(t5)
	sd t6, 800(t5)
	sd t6, 808(t5)
	sd t6, 816(t5)
	sd t6, 824(t5)
	sd t6, 832(t5)
	sd t6, 840(t5)
	sd t6, 848(t5)
	sd t6, 856(t5)
	sd t6, 864(t5)
	sd t6, 872(t5)
	sd t6, 880(t5)
	sd t6, 888(t5)
	sd t6, 896(t5)
	sd t6, 904(t5)
	sd t6, 912(t5)
	sd t6, 920(t5)
	sd t6, 928(t5)
	sd t6, 936(t5)
	sd t6, 944(t5)
	sd t6, 952(t5)
	sd t6, 960(t5)
	sd t6, 968(t5)
	sd t6, 976(t5)
	sd t6, 984(t5)
	sd t6, 992(t5)
	sd t6, 1000(t5)
	sd t6, 1008(t5)
	sd t6, 1016(t5)
	sd t6, 1024(t5)
	sd t6, 1032(t5)
	sd t6, 1040(t5)
	sd t6, 1048(t5)
	sd t6, 1056(t5)
	sd t6, 1064(t5)
	sd t6, 1072(t5)
	sd t6, 1080(t5)
	sd t6, 1088(t5)
	sd t6, 1096(t5)
	sd t6, 1104(t5)
	sd t6, 1112(t5)
	sd t6, 1120(t5)
	sd t6, 1128(t5)
	sd t6, 1136(t5)
	sd t6, 1144(t5)
	sd t6, 1152(t5)
	sd t6, 1160(t5)
	sd t6, 1168(t5)
	sd t6, 1176(t5)
	sd t6, 1184(t5)
	sd t6, 1192(t5)
	sd t6, 1200(t5)
	sd t6, 1208(t5)
	sd t6, 1216(t5)
	sd t6, 1224(t5)
	sd t6, 1232(t5)
	sd t6, 1240(t5)
	sd t6, 1248(t5)
	sd t6, 1256(t5)
	sd t6, 1264(t5)
	sd t6, 1272(t5)
	sd t6, 1280(t5)
	sd t6, 1288(t5)
	sd t6, 1296(t5)
	sd t6, 1304(t5)
	sd t6, 1312(t5)
	sd t6, 1320(t5)
	sd t6, 1328(t5)
	sd t6, 1336(t5)
	sd t6, 1344(t5)
	sd t6, 1352(t5)
	sd t6, 1360(t5)
	sd t6, 1368(t5)
	sd t6, 1376(t5)
	sd t6, 1384(t5)
	sd t6, 1392(t5)
	sd t6, 1400(t5)
	sd t6, 1408(t5)
	sd t6, 1416(t5)
	sd t6, 1424(t5)
	sd t6, 1432(t5)
	sd t6, 1440(t5)
	sd t6, 1448(t5)
	sd t6, 1456(t5)
	sd t6, 1464(t5)
	sd t6, 1472(t5)
	sd t6, 1480(t5)
	sd t6, 1488(t5)
	sd t6, 1496(t5)
	sd t6, 1504(t5)
	sd t6, 1512(t5)
	sd t6, 1520(t5)
	sd t6, 1528(t5)
	sd t6, 1536(t5)
	sd t6, 1544(t5)
	sd t6, 1552(t5)
	sd t6, 1560(t5)
	sd t6, 1568(t5)
	sd t6, 1576(t5)
	sd t6, 1584(t5)
	sd t6, 1592(t5)
	sd t6, 1600(t5)
	sd t6, 1608(t5)
	sd t6, 1616(t5)
	sd t6, 1624(t5)
	sd t6, 1632(t5)
	sd t6, 1640(t5)
	sd t6, 1648(t5)
	sd t6, 1656(t5)
	sd t6, 1664(t5)
	sd t6, 1672(t5)
	sd t6, 1680(t5)
	sd t6, 1688(t5)
	sd t6, 1696(t5)
	sd t6, 1704(t5)
	sd t6, 1712(t5)
	sd t6, 1720(t5)
	sd t6, 1728(t5)
	sd t6, 1736(t5)
	sd t6, 1744(t5)
	sd t6, 1752(t5)
	sd t6, 1760(t5)
	sd t6, 1768(t5)
	sd t6, 1776(t5)
	sd t6, 1784(t5)
	sd t6, 1792(t5)
	sd t6, 1800(t5)
	sd t6, 1808(t5)
	sd t6, 1816(t5)
	sd t6, 1824(t5)
	sd t6, 1832(t5)
	sd t6, 1840(t5)
	sd t6, 1848(t5)
	sd t6, 1856(t5)
	sd t6, 1864(t5)
	sd t6, 1872(t5)
	sd t6, 1880(t5)
	sd t6, 1888(t5)
	sd t6, 1896(t5)
	sd t6, 1904(t5)
	sd t6, 1912(t5)
	sd t6, 1920(t5)
	sd t6, 1928(t5)
	sd t6, 1936(t5)
	sd t6, 1944(t5)
	sd t6, 1952(t5)
	sd t6, 1960(t5)
	sd t6, 1968(t5)
	sd t6, 1976(t5)
	sd t6, 1984(t5)
	sd t6, 1992(t5)
	sd t6, 2000(t5)
	sd t6, 2008(t5)
	sd t6, 2016(t5)
	sd t6, 2024(t5)
	sd t6, 2032(t5)
	sd t6, 2040(t5)
	addi sp, sp, 16
	addi sp, sp, 2032
	j 21f
20:
21:
	ret
	.option pop
