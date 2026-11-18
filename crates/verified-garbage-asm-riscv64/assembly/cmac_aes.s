// The functions of `src/cmac_aes.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_cmac_aes_init:
	.option push
	.option arch, +m, +c
	addi sp, sp, -2032
	addi sp, sp, -272
	addi a3, sp, 0
	addi t0, a3, 2047
	addi t0, t0, 136
	andi t0, t0, -8
	sd ra, 0(t0)
	sd s1, 8(t0)
	sd s2, 16(t0)
	sd s3, 24(t0)
	addi s1, a0, 0
	addi s2, a3, 0
	srli s3, a2, 2
	addi s3, s3, 6
	addi a0, a1, 0
	addi a1, a2, 0
	addi a2, s1, 0
	call {vg_aes_expand_key_scratch}
	addi a0, s1, 0
	addi a1, s3, 0
	addi a2, s1, 240
	addi a3, s2, 0
	call {vg_cmac_aes_subkeys}
	addi t1, zero, 0
	sb t1, 272(s1)
	addi t1, zero, 0
	sb t1, 273(s1)
	addi t1, zero, 0
	sb t1, 274(s1)
	addi t1, zero, 0
	sb t1, 275(s1)
	addi t1, zero, 0
	sb t1, 276(s1)
	addi t1, zero, 0
	sb t1, 277(s1)
	addi t1, zero, 0
	sb t1, 278(s1)
	addi t1, zero, 0
	sb t1, 279(s1)
	addi t1, zero, 0
	sb t1, 280(s1)
	addi t1, zero, 0
	sb t1, 281(s1)
	addi t1, zero, 0
	sb t1, 282(s1)
	addi t1, zero, 0
	sb t1, 283(s1)
	addi t1, zero, 0
	sb t1, 284(s1)
	addi t1, zero, 0
	sb t1, 285(s1)
	addi t1, zero, 0
	sb t1, 286(s1)
	addi t1, zero, 0
	sb t1, 287(s1)
	addi t0, s2, 2047
	addi t0, t0, 136
	andi t0, t0, -8
	ld ra, 0(t0)
	ld s1, 8(t0)
	ld s2, 16(t0)
	ld s3, 24(t0)
	addi sp, sp, 272
	addi sp, sp, 2032
	addi t0, zero, 0
	addi sp, sp, -2032
	addi sp, sp, -16
	addi t1, sp, 0
	sd t0, 0(t1)
	sd t0, 8(t1)
	sd t0, 16(t1)
	sd t0, 24(t1)
	sd t0, 32(t1)
	sd t0, 40(t1)
	sd t0, 48(t1)
	sd t0, 56(t1)
	sd t0, 64(t1)
	sd t0, 72(t1)
	sd t0, 80(t1)
	sd t0, 88(t1)
	sd t0, 96(t1)
	sd t0, 104(t1)
	sd t0, 112(t1)
	sd t0, 120(t1)
	sd t0, 128(t1)
	sd t0, 136(t1)
	sd t0, 144(t1)
	sd t0, 152(t1)
	sd t0, 160(t1)
	sd t0, 168(t1)
	sd t0, 176(t1)
	sd t0, 184(t1)
	sd t0, 192(t1)
	sd t0, 200(t1)
	sd t0, 208(t1)
	sd t0, 216(t1)
	sd t0, 224(t1)
	sd t0, 232(t1)
	sd t0, 240(t1)
	sd t0, 248(t1)
	sd t0, 256(t1)
	sd t0, 264(t1)
	sd t0, 272(t1)
	sd t0, 280(t1)
	sd t0, 288(t1)
	sd t0, 296(t1)
	sd t0, 304(t1)
	sd t0, 312(t1)
	sd t0, 320(t1)
	sd t0, 328(t1)
	sd t0, 336(t1)
	sd t0, 344(t1)
	sd t0, 352(t1)
	sd t0, 360(t1)
	sd t0, 368(t1)
	sd t0, 376(t1)
	sd t0, 384(t1)
	sd t0, 392(t1)
	sd t0, 400(t1)
	sd t0, 408(t1)
	sd t0, 416(t1)
	sd t0, 424(t1)
	sd t0, 432(t1)
	sd t0, 440(t1)
	sd t0, 448(t1)
	sd t0, 456(t1)
	sd t0, 464(t1)
	sd t0, 472(t1)
	sd t0, 480(t1)
	sd t0, 488(t1)
	sd t0, 496(t1)
	sd t0, 504(t1)
	sd t0, 512(t1)
	sd t0, 520(t1)
	sd t0, 528(t1)
	sd t0, 536(t1)
	sd t0, 544(t1)
	sd t0, 552(t1)
	sd t0, 560(t1)
	sd t0, 568(t1)
	sd t0, 576(t1)
	sd t0, 584(t1)
	sd t0, 592(t1)
	sd t0, 600(t1)
	sd t0, 608(t1)
	sd t0, 616(t1)
	sd t0, 624(t1)
	sd t0, 632(t1)
	sd t0, 640(t1)
	sd t0, 648(t1)
	sd t0, 656(t1)
	sd t0, 664(t1)
	sd t0, 672(t1)
	sd t0, 680(t1)
	sd t0, 688(t1)
	sd t0, 696(t1)
	sd t0, 704(t1)
	sd t0, 712(t1)
	sd t0, 720(t1)
	sd t0, 728(t1)
	sd t0, 736(t1)
	sd t0, 744(t1)
	sd t0, 752(t1)
	sd t0, 760(t1)
	sd t0, 768(t1)
	sd t0, 776(t1)
	sd t0, 784(t1)
	sd t0, 792(t1)
	sd t0, 800(t1)
	sd t0, 808(t1)
	sd t0, 816(t1)
	sd t0, 824(t1)
	sd t0, 832(t1)
	sd t0, 840(t1)
	sd t0, 848(t1)
	sd t0, 856(t1)
	sd t0, 864(t1)
	sd t0, 872(t1)
	sd t0, 880(t1)
	sd t0, 888(t1)
	sd t0, 896(t1)
	sd t0, 904(t1)
	sd t0, 912(t1)
	sd t0, 920(t1)
	sd t0, 928(t1)
	sd t0, 936(t1)
	sd t0, 944(t1)
	sd t0, 952(t1)
	sd t0, 960(t1)
	sd t0, 968(t1)
	sd t0, 976(t1)
	sd t0, 984(t1)
	sd t0, 992(t1)
	sd t0, 1000(t1)
	sd t0, 1008(t1)
	sd t0, 1016(t1)
	sd t0, 1024(t1)
	sd t0, 1032(t1)
	sd t0, 1040(t1)
	sd t0, 1048(t1)
	sd t0, 1056(t1)
	sd t0, 1064(t1)
	sd t0, 1072(t1)
	sd t0, 1080(t1)
	sd t0, 1088(t1)
	sd t0, 1096(t1)
	sd t0, 1104(t1)
	sd t0, 1112(t1)
	sd t0, 1120(t1)
	sd t0, 1128(t1)
	sd t0, 1136(t1)
	sd t0, 1144(t1)
	sd t0, 1152(t1)
	sd t0, 1160(t1)
	sd t0, 1168(t1)
	sd t0, 1176(t1)
	sd t0, 1184(t1)
	sd t0, 1192(t1)
	sd t0, 1200(t1)
	sd t0, 1208(t1)
	sd t0, 1216(t1)
	sd t0, 1224(t1)
	sd t0, 1232(t1)
	sd t0, 1240(t1)
	sd t0, 1248(t1)
	sd t0, 1256(t1)
	sd t0, 1264(t1)
	sd t0, 1272(t1)
	sd t0, 1280(t1)
	sd t0, 1288(t1)
	sd t0, 1296(t1)
	sd t0, 1304(t1)
	sd t0, 1312(t1)
	sd t0, 1320(t1)
	sd t0, 1328(t1)
	sd t0, 1336(t1)
	sd t0, 1344(t1)
	sd t0, 1352(t1)
	sd t0, 1360(t1)
	sd t0, 1368(t1)
	sd t0, 1376(t1)
	sd t0, 1384(t1)
	sd t0, 1392(t1)
	sd t0, 1400(t1)
	sd t0, 1408(t1)
	sd t0, 1416(t1)
	sd t0, 1424(t1)
	sd t0, 1432(t1)
	sd t0, 1440(t1)
	sd t0, 1448(t1)
	sd t0, 1456(t1)
	sd t0, 1464(t1)
	sd t0, 1472(t1)
	sd t0, 1480(t1)
	sd t0, 1488(t1)
	sd t0, 1496(t1)
	sd t0, 1504(t1)
	sd t0, 1512(t1)
	sd t0, 1520(t1)
	sd t0, 1528(t1)
	sd t0, 1536(t1)
	sd t0, 1544(t1)
	sd t0, 1552(t1)
	sd t0, 1560(t1)
	sd t0, 1568(t1)
	sd t0, 1576(t1)
	sd t0, 1584(t1)
	sd t0, 1592(t1)
	sd t0, 1600(t1)
	sd t0, 1608(t1)
	sd t0, 1616(t1)
	sd t0, 1624(t1)
	sd t0, 1632(t1)
	sd t0, 1640(t1)
	sd t0, 1648(t1)
	sd t0, 1656(t1)
	sd t0, 1664(t1)
	sd t0, 1672(t1)
	sd t0, 1680(t1)
	sd t0, 1688(t1)
	sd t0, 1696(t1)
	sd t0, 1704(t1)
	sd t0, 1712(t1)
	sd t0, 1720(t1)
	sd t0, 1728(t1)
	sd t0, 1736(t1)
	sd t0, 1744(t1)
	sd t0, 1752(t1)
	sd t0, 1760(t1)
	sd t0, 1768(t1)
	sd t0, 1776(t1)
	sd t0, 1784(t1)
	sd t0, 1792(t1)
	sd t0, 1800(t1)
	sd t0, 1808(t1)
	sd t0, 1816(t1)
	sd t0, 1824(t1)
	sd t0, 1832(t1)
	sd t0, 1840(t1)
	sd t0, 1848(t1)
	sd t0, 1856(t1)
	sd t0, 1864(t1)
	sd t0, 1872(t1)
	sd t0, 1880(t1)
	sd t0, 1888(t1)
	sd t0, 1896(t1)
	sd t0, 1904(t1)
	sd t0, 1912(t1)
	sd t0, 1920(t1)
	sd t0, 1928(t1)
	sd t0, 1936(t1)
	sd t0, 1944(t1)
	sd t0, 1952(t1)
	sd t0, 1960(t1)
	sd t0, 1968(t1)
	sd t0, 1976(t1)
	sd t0, 1984(t1)
	sd t0, 1992(t1)
	sd t0, 2000(t1)
	sd t0, 2008(t1)
	sd t0, 2016(t1)
	sd t0, 2024(t1)
	sd t0, 2032(t1)
	sd t0, 2040(t1)
	addi sp, sp, -256
	addi t1, sp, 0
	sd t0, 0(t1)
	sd t0, 8(t1)
	sd t0, 16(t1)
	sd t0, 24(t1)
	sd t0, 32(t1)
	sd t0, 40(t1)
	sd t0, 48(t1)
	sd t0, 56(t1)
	sd t0, 64(t1)
	sd t0, 72(t1)
	sd t0, 80(t1)
	sd t0, 88(t1)
	sd t0, 96(t1)
	sd t0, 104(t1)
	sd t0, 112(t1)
	sd t0, 120(t1)
	sd t0, 128(t1)
	sd t0, 136(t1)
	sd t0, 144(t1)
	sd t0, 152(t1)
	sd t0, 160(t1)
	sd t0, 168(t1)
	sd t0, 176(t1)
	sd t0, 184(t1)
	sd t0, 192(t1)
	sd t0, 200(t1)
	sd t0, 208(t1)
	sd t0, 216(t1)
	sd t0, 224(t1)
	sd t0, 232(t1)
	sd t0, 240(t1)
	sd t0, 248(t1)
	addi sp, sp, 256
	addi sp, sp, 16
	addi sp, sp, 2032
	addi a0, zero, 0
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

vg_cmac_aes_absorb:
	.option push
	.option arch, +m, +c
	addi sp, sp, -2032
	addi sp, sp, -272
	addi a5, sp, 0
	addi t0, a5, 2047
	addi t0, t0, 136
	andi t0, t0, -8
	sd ra, 0(t0)
	sd s1, 8(t0)
	sd s2, 16(t0)
	sd s3, 24(t0)
	sd s4, 32(t0)
	sd s5, 40(t0)
	sd s6, 48(t0)
	addi s1, a0, 0
	addi s2, a1, 0
	addi s3, a3, 0
	addi s4, a4, 0
	addi s6, a5, 0
	beqz a2, 20f
	addi t1, a2, -1
	andi t1, t1, 15
	addi t1, t1, 1
	j 21f
20:
	addi t1, zero, 0
21:
	srli t2, s4, 4
	beqz t2, 22f
	addi t2, zero, 16
	j 23f
22:
	addi t2, s4, 0
23:
	addi t3, zero, 16
	sub t3, t3, t1
	sltu t4, t2, t3
	beqz t4, 24f
	j 25f
24:
	addi t2, t3, 0
25:
	addi a7, t2, 0
	add t5, s1, t1
	addi t5, t5, 288
	addi t6, s3, 0
	beqz t2, 26f
28:
	lbu t3, 0(t6)
	sb t3, 0(t5)
	addi t6, t6, 1
	addi t5, t5, 1
	addi t2, t2, -1
	bnez t2, 28b
	j 27f
26:
27:
	add s3, s3, a7
	sub s4, s4, a7
	addi a4, zero, 0
	beqz s4, 29f
	addi a4, zero, 1
	j 210f
29:
210:
	addi a0, s1, 0
	addi a1, s2, 0
	addi a2, s1, 272
	addi a3, s1, 288
	addi a5, s6, 0
	call {vg_cmac_aes_update}
	addi s5, zero, 0
	beqz s4, 211f
	addi s5, s4, -1
	andi t1, s5, 15
	sub s5, s5, t1
	j 212f
211:
212:
	srli a4, s5, 4
	addi a0, s1, 0
	addi a1, s2, 0
	addi a2, s1, 272
	addi a3, s3, 0
	addi a5, s6, 0
	call {vg_cmac_aes_update}
	add s3, s3, s5
	sub s4, s4, s5
	addi t5, s1, 288
	addi t6, s3, 0
	addi t2, s4, 0
	beqz t2, 213f
215:
	lbu t3, 0(t6)
	sb t3, 0(t5)
	addi t6, t6, 1
	addi t5, t5, 1
	addi t2, t2, -1
	bnez t2, 215b
	j 214f
213:
214:
	addi t0, s6, 2047
	addi t0, t0, 136
	andi t0, t0, -8
	ld ra, 0(t0)
	ld s1, 8(t0)
	ld s2, 16(t0)
	ld s3, 24(t0)
	ld s4, 32(t0)
	ld s5, 40(t0)
	ld s6, 48(t0)
	addi sp, sp, 272
	addi sp, sp, 2032
	addi t0, zero, 0
	addi sp, sp, -2032
	addi sp, sp, -16
	addi t1, sp, 0
	sd t0, 0(t1)
	sd t0, 8(t1)
	sd t0, 16(t1)
	sd t0, 24(t1)
	sd t0, 32(t1)
	sd t0, 40(t1)
	sd t0, 48(t1)
	sd t0, 56(t1)
	sd t0, 64(t1)
	sd t0, 72(t1)
	sd t0, 80(t1)
	sd t0, 88(t1)
	sd t0, 96(t1)
	sd t0, 104(t1)
	sd t0, 112(t1)
	sd t0, 120(t1)
	sd t0, 128(t1)
	sd t0, 136(t1)
	sd t0, 144(t1)
	sd t0, 152(t1)
	sd t0, 160(t1)
	sd t0, 168(t1)
	sd t0, 176(t1)
	sd t0, 184(t1)
	sd t0, 192(t1)
	sd t0, 200(t1)
	sd t0, 208(t1)
	sd t0, 216(t1)
	sd t0, 224(t1)
	sd t0, 232(t1)
	sd t0, 240(t1)
	sd t0, 248(t1)
	sd t0, 256(t1)
	sd t0, 264(t1)
	sd t0, 272(t1)
	sd t0, 280(t1)
	sd t0, 288(t1)
	sd t0, 296(t1)
	sd t0, 304(t1)
	sd t0, 312(t1)
	sd t0, 320(t1)
	sd t0, 328(t1)
	sd t0, 336(t1)
	sd t0, 344(t1)
	sd t0, 352(t1)
	sd t0, 360(t1)
	sd t0, 368(t1)
	sd t0, 376(t1)
	sd t0, 384(t1)
	sd t0, 392(t1)
	sd t0, 400(t1)
	sd t0, 408(t1)
	sd t0, 416(t1)
	sd t0, 424(t1)
	sd t0, 432(t1)
	sd t0, 440(t1)
	sd t0, 448(t1)
	sd t0, 456(t1)
	sd t0, 464(t1)
	sd t0, 472(t1)
	sd t0, 480(t1)
	sd t0, 488(t1)
	sd t0, 496(t1)
	sd t0, 504(t1)
	sd t0, 512(t1)
	sd t0, 520(t1)
	sd t0, 528(t1)
	sd t0, 536(t1)
	sd t0, 544(t1)
	sd t0, 552(t1)
	sd t0, 560(t1)
	sd t0, 568(t1)
	sd t0, 576(t1)
	sd t0, 584(t1)
	sd t0, 592(t1)
	sd t0, 600(t1)
	sd t0, 608(t1)
	sd t0, 616(t1)
	sd t0, 624(t1)
	sd t0, 632(t1)
	sd t0, 640(t1)
	sd t0, 648(t1)
	sd t0, 656(t1)
	sd t0, 664(t1)
	sd t0, 672(t1)
	sd t0, 680(t1)
	sd t0, 688(t1)
	sd t0, 696(t1)
	sd t0, 704(t1)
	sd t0, 712(t1)
	sd t0, 720(t1)
	sd t0, 728(t1)
	sd t0, 736(t1)
	sd t0, 744(t1)
	sd t0, 752(t1)
	sd t0, 760(t1)
	sd t0, 768(t1)
	sd t0, 776(t1)
	sd t0, 784(t1)
	sd t0, 792(t1)
	sd t0, 800(t1)
	sd t0, 808(t1)
	sd t0, 816(t1)
	sd t0, 824(t1)
	sd t0, 832(t1)
	sd t0, 840(t1)
	sd t0, 848(t1)
	sd t0, 856(t1)
	sd t0, 864(t1)
	sd t0, 872(t1)
	sd t0, 880(t1)
	sd t0, 888(t1)
	sd t0, 896(t1)
	sd t0, 904(t1)
	sd t0, 912(t1)
	sd t0, 920(t1)
	sd t0, 928(t1)
	sd t0, 936(t1)
	sd t0, 944(t1)
	sd t0, 952(t1)
	sd t0, 960(t1)
	sd t0, 968(t1)
	sd t0, 976(t1)
	sd t0, 984(t1)
	sd t0, 992(t1)
	sd t0, 1000(t1)
	sd t0, 1008(t1)
	sd t0, 1016(t1)
	sd t0, 1024(t1)
	sd t0, 1032(t1)
	sd t0, 1040(t1)
	sd t0, 1048(t1)
	sd t0, 1056(t1)
	sd t0, 1064(t1)
	sd t0, 1072(t1)
	sd t0, 1080(t1)
	sd t0, 1088(t1)
	sd t0, 1096(t1)
	sd t0, 1104(t1)
	sd t0, 1112(t1)
	sd t0, 1120(t1)
	sd t0, 1128(t1)
	sd t0, 1136(t1)
	sd t0, 1144(t1)
	sd t0, 1152(t1)
	sd t0, 1160(t1)
	sd t0, 1168(t1)
	sd t0, 1176(t1)
	sd t0, 1184(t1)
	sd t0, 1192(t1)
	sd t0, 1200(t1)
	sd t0, 1208(t1)
	sd t0, 1216(t1)
	sd t0, 1224(t1)
	sd t0, 1232(t1)
	sd t0, 1240(t1)
	sd t0, 1248(t1)
	sd t0, 1256(t1)
	sd t0, 1264(t1)
	sd t0, 1272(t1)
	sd t0, 1280(t1)
	sd t0, 1288(t1)
	sd t0, 1296(t1)
	sd t0, 1304(t1)
	sd t0, 1312(t1)
	sd t0, 1320(t1)
	sd t0, 1328(t1)
	sd t0, 1336(t1)
	sd t0, 1344(t1)
	sd t0, 1352(t1)
	sd t0, 1360(t1)
	sd t0, 1368(t1)
	sd t0, 1376(t1)
	sd t0, 1384(t1)
	sd t0, 1392(t1)
	sd t0, 1400(t1)
	sd t0, 1408(t1)
	sd t0, 1416(t1)
	sd t0, 1424(t1)
	sd t0, 1432(t1)
	sd t0, 1440(t1)
	sd t0, 1448(t1)
	sd t0, 1456(t1)
	sd t0, 1464(t1)
	sd t0, 1472(t1)
	sd t0, 1480(t1)
	sd t0, 1488(t1)
	sd t0, 1496(t1)
	sd t0, 1504(t1)
	sd t0, 1512(t1)
	sd t0, 1520(t1)
	sd t0, 1528(t1)
	sd t0, 1536(t1)
	sd t0, 1544(t1)
	sd t0, 1552(t1)
	sd t0, 1560(t1)
	sd t0, 1568(t1)
	sd t0, 1576(t1)
	sd t0, 1584(t1)
	sd t0, 1592(t1)
	sd t0, 1600(t1)
	sd t0, 1608(t1)
	sd t0, 1616(t1)
	sd t0, 1624(t1)
	sd t0, 1632(t1)
	sd t0, 1640(t1)
	sd t0, 1648(t1)
	sd t0, 1656(t1)
	sd t0, 1664(t1)
	sd t0, 1672(t1)
	sd t0, 1680(t1)
	sd t0, 1688(t1)
	sd t0, 1696(t1)
	sd t0, 1704(t1)
	sd t0, 1712(t1)
	sd t0, 1720(t1)
	sd t0, 1728(t1)
	sd t0, 1736(t1)
	sd t0, 1744(t1)
	sd t0, 1752(t1)
	sd t0, 1760(t1)
	sd t0, 1768(t1)
	sd t0, 1776(t1)
	sd t0, 1784(t1)
	sd t0, 1792(t1)
	sd t0, 1800(t1)
	sd t0, 1808(t1)
	sd t0, 1816(t1)
	sd t0, 1824(t1)
	sd t0, 1832(t1)
	sd t0, 1840(t1)
	sd t0, 1848(t1)
	sd t0, 1856(t1)
	sd t0, 1864(t1)
	sd t0, 1872(t1)
	sd t0, 1880(t1)
	sd t0, 1888(t1)
	sd t0, 1896(t1)
	sd t0, 1904(t1)
	sd t0, 1912(t1)
	sd t0, 1920(t1)
	sd t0, 1928(t1)
	sd t0, 1936(t1)
	sd t0, 1944(t1)
	sd t0, 1952(t1)
	sd t0, 1960(t1)
	sd t0, 1968(t1)
	sd t0, 1976(t1)
	sd t0, 1984(t1)
	sd t0, 1992(t1)
	sd t0, 2000(t1)
	sd t0, 2008(t1)
	sd t0, 2016(t1)
	sd t0, 2024(t1)
	sd t0, 2032(t1)
	sd t0, 2040(t1)
	addi sp, sp, -256
	addi t1, sp, 0
	sd t0, 0(t1)
	sd t0, 8(t1)
	sd t0, 16(t1)
	sd t0, 24(t1)
	sd t0, 32(t1)
	sd t0, 40(t1)
	sd t0, 48(t1)
	sd t0, 56(t1)
	sd t0, 64(t1)
	sd t0, 72(t1)
	sd t0, 80(t1)
	sd t0, 88(t1)
	sd t0, 96(t1)
	sd t0, 104(t1)
	sd t0, 112(t1)
	sd t0, 120(t1)
	sd t0, 128(t1)
	sd t0, 136(t1)
	sd t0, 144(t1)
	sd t0, 152(t1)
	sd t0, 160(t1)
	sd t0, 168(t1)
	sd t0, 176(t1)
	sd t0, 184(t1)
	sd t0, 192(t1)
	sd t0, 200(t1)
	sd t0, 208(t1)
	sd t0, 216(t1)
	sd t0, 224(t1)
	sd t0, 232(t1)
	sd t0, 240(t1)
	sd t0, 248(t1)
	addi sp, sp, 256
	addi sp, sp, 16
	addi sp, sp, 2032
	addi a0, zero, 0
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

vg_cmac_aes_finish:
	.option push
	.option arch, +m, +c
	addi sp, sp, -2032
	addi sp, sp, -272
	addi a4, sp, 0
	lbu t1, 272(a0)
	sb t1, 0(a3)
	lbu t1, 273(a0)
	sb t1, 1(a3)
	lbu t1, 274(a0)
	sb t1, 2(a3)
	lbu t1, 275(a0)
	sb t1, 3(a3)
	lbu t1, 276(a0)
	sb t1, 4(a3)
	lbu t1, 277(a0)
	sb t1, 5(a3)
	lbu t1, 278(a0)
	sb t1, 6(a3)
	lbu t1, 279(a0)
	sb t1, 7(a3)
	lbu t1, 280(a0)
	sb t1, 8(a3)
	lbu t1, 281(a0)
	sb t1, 9(a3)
	lbu t1, 282(a0)
	sb t1, 10(a3)
	lbu t1, 283(a0)
	sb t1, 11(a3)
	lbu t1, 284(a0)
	sb t1, 12(a3)
	lbu t1, 285(a0)
	sb t1, 13(a3)
	lbu t1, 286(a0)
	sb t1, 14(a3)
	lbu t1, 287(a0)
	sb t1, 15(a3)
	addi t0, a4, 2047
	addi t0, t0, 136
	andi t0, t0, -8
	sd ra, 0(t0)
	sd s1, 8(t0)
	addi s1, a4, 0
	addi a5, a4, 0
	addi a4, a2, 0
	addi a2, a3, 0
	addi a3, a0, 288
	beqz a4, 20f
	addi a4, a4, -1
	andi a4, a4, 15
	addi a4, a4, 1
	j 21f
20:
21:
	call {vg_cmac_aes_finalize}
	addi t0, s1, 2047
	addi t0, t0, 136
	andi t0, t0, -8
	ld ra, 0(t0)
	ld s1, 8(t0)
	addi sp, sp, 272
	addi sp, sp, 2032
	addi t0, zero, 0
	addi sp, sp, -2032
	addi sp, sp, -16
	addi t1, sp, 0
	sd t0, 0(t1)
	sd t0, 8(t1)
	sd t0, 16(t1)
	sd t0, 24(t1)
	sd t0, 32(t1)
	sd t0, 40(t1)
	sd t0, 48(t1)
	sd t0, 56(t1)
	sd t0, 64(t1)
	sd t0, 72(t1)
	sd t0, 80(t1)
	sd t0, 88(t1)
	sd t0, 96(t1)
	sd t0, 104(t1)
	sd t0, 112(t1)
	sd t0, 120(t1)
	sd t0, 128(t1)
	sd t0, 136(t1)
	sd t0, 144(t1)
	sd t0, 152(t1)
	sd t0, 160(t1)
	sd t0, 168(t1)
	sd t0, 176(t1)
	sd t0, 184(t1)
	sd t0, 192(t1)
	sd t0, 200(t1)
	sd t0, 208(t1)
	sd t0, 216(t1)
	sd t0, 224(t1)
	sd t0, 232(t1)
	sd t0, 240(t1)
	sd t0, 248(t1)
	sd t0, 256(t1)
	sd t0, 264(t1)
	sd t0, 272(t1)
	sd t0, 280(t1)
	sd t0, 288(t1)
	sd t0, 296(t1)
	sd t0, 304(t1)
	sd t0, 312(t1)
	sd t0, 320(t1)
	sd t0, 328(t1)
	sd t0, 336(t1)
	sd t0, 344(t1)
	sd t0, 352(t1)
	sd t0, 360(t1)
	sd t0, 368(t1)
	sd t0, 376(t1)
	sd t0, 384(t1)
	sd t0, 392(t1)
	sd t0, 400(t1)
	sd t0, 408(t1)
	sd t0, 416(t1)
	sd t0, 424(t1)
	sd t0, 432(t1)
	sd t0, 440(t1)
	sd t0, 448(t1)
	sd t0, 456(t1)
	sd t0, 464(t1)
	sd t0, 472(t1)
	sd t0, 480(t1)
	sd t0, 488(t1)
	sd t0, 496(t1)
	sd t0, 504(t1)
	sd t0, 512(t1)
	sd t0, 520(t1)
	sd t0, 528(t1)
	sd t0, 536(t1)
	sd t0, 544(t1)
	sd t0, 552(t1)
	sd t0, 560(t1)
	sd t0, 568(t1)
	sd t0, 576(t1)
	sd t0, 584(t1)
	sd t0, 592(t1)
	sd t0, 600(t1)
	sd t0, 608(t1)
	sd t0, 616(t1)
	sd t0, 624(t1)
	sd t0, 632(t1)
	sd t0, 640(t1)
	sd t0, 648(t1)
	sd t0, 656(t1)
	sd t0, 664(t1)
	sd t0, 672(t1)
	sd t0, 680(t1)
	sd t0, 688(t1)
	sd t0, 696(t1)
	sd t0, 704(t1)
	sd t0, 712(t1)
	sd t0, 720(t1)
	sd t0, 728(t1)
	sd t0, 736(t1)
	sd t0, 744(t1)
	sd t0, 752(t1)
	sd t0, 760(t1)
	sd t0, 768(t1)
	sd t0, 776(t1)
	sd t0, 784(t1)
	sd t0, 792(t1)
	sd t0, 800(t1)
	sd t0, 808(t1)
	sd t0, 816(t1)
	sd t0, 824(t1)
	sd t0, 832(t1)
	sd t0, 840(t1)
	sd t0, 848(t1)
	sd t0, 856(t1)
	sd t0, 864(t1)
	sd t0, 872(t1)
	sd t0, 880(t1)
	sd t0, 888(t1)
	sd t0, 896(t1)
	sd t0, 904(t1)
	sd t0, 912(t1)
	sd t0, 920(t1)
	sd t0, 928(t1)
	sd t0, 936(t1)
	sd t0, 944(t1)
	sd t0, 952(t1)
	sd t0, 960(t1)
	sd t0, 968(t1)
	sd t0, 976(t1)
	sd t0, 984(t1)
	sd t0, 992(t1)
	sd t0, 1000(t1)
	sd t0, 1008(t1)
	sd t0, 1016(t1)
	sd t0, 1024(t1)
	sd t0, 1032(t1)
	sd t0, 1040(t1)
	sd t0, 1048(t1)
	sd t0, 1056(t1)
	sd t0, 1064(t1)
	sd t0, 1072(t1)
	sd t0, 1080(t1)
	sd t0, 1088(t1)
	sd t0, 1096(t1)
	sd t0, 1104(t1)
	sd t0, 1112(t1)
	sd t0, 1120(t1)
	sd t0, 1128(t1)
	sd t0, 1136(t1)
	sd t0, 1144(t1)
	sd t0, 1152(t1)
	sd t0, 1160(t1)
	sd t0, 1168(t1)
	sd t0, 1176(t1)
	sd t0, 1184(t1)
	sd t0, 1192(t1)
	sd t0, 1200(t1)
	sd t0, 1208(t1)
	sd t0, 1216(t1)
	sd t0, 1224(t1)
	sd t0, 1232(t1)
	sd t0, 1240(t1)
	sd t0, 1248(t1)
	sd t0, 1256(t1)
	sd t0, 1264(t1)
	sd t0, 1272(t1)
	sd t0, 1280(t1)
	sd t0, 1288(t1)
	sd t0, 1296(t1)
	sd t0, 1304(t1)
	sd t0, 1312(t1)
	sd t0, 1320(t1)
	sd t0, 1328(t1)
	sd t0, 1336(t1)
	sd t0, 1344(t1)
	sd t0, 1352(t1)
	sd t0, 1360(t1)
	sd t0, 1368(t1)
	sd t0, 1376(t1)
	sd t0, 1384(t1)
	sd t0, 1392(t1)
	sd t0, 1400(t1)
	sd t0, 1408(t1)
	sd t0, 1416(t1)
	sd t0, 1424(t1)
	sd t0, 1432(t1)
	sd t0, 1440(t1)
	sd t0, 1448(t1)
	sd t0, 1456(t1)
	sd t0, 1464(t1)
	sd t0, 1472(t1)
	sd t0, 1480(t1)
	sd t0, 1488(t1)
	sd t0, 1496(t1)
	sd t0, 1504(t1)
	sd t0, 1512(t1)
	sd t0, 1520(t1)
	sd t0, 1528(t1)
	sd t0, 1536(t1)
	sd t0, 1544(t1)
	sd t0, 1552(t1)
	sd t0, 1560(t1)
	sd t0, 1568(t1)
	sd t0, 1576(t1)
	sd t0, 1584(t1)
	sd t0, 1592(t1)
	sd t0, 1600(t1)
	sd t0, 1608(t1)
	sd t0, 1616(t1)
	sd t0, 1624(t1)
	sd t0, 1632(t1)
	sd t0, 1640(t1)
	sd t0, 1648(t1)
	sd t0, 1656(t1)
	sd t0, 1664(t1)
	sd t0, 1672(t1)
	sd t0, 1680(t1)
	sd t0, 1688(t1)
	sd t0, 1696(t1)
	sd t0, 1704(t1)
	sd t0, 1712(t1)
	sd t0, 1720(t1)
	sd t0, 1728(t1)
	sd t0, 1736(t1)
	sd t0, 1744(t1)
	sd t0, 1752(t1)
	sd t0, 1760(t1)
	sd t0, 1768(t1)
	sd t0, 1776(t1)
	sd t0, 1784(t1)
	sd t0, 1792(t1)
	sd t0, 1800(t1)
	sd t0, 1808(t1)
	sd t0, 1816(t1)
	sd t0, 1824(t1)
	sd t0, 1832(t1)
	sd t0, 1840(t1)
	sd t0, 1848(t1)
	sd t0, 1856(t1)
	sd t0, 1864(t1)
	sd t0, 1872(t1)
	sd t0, 1880(t1)
	sd t0, 1888(t1)
	sd t0, 1896(t1)
	sd t0, 1904(t1)
	sd t0, 1912(t1)
	sd t0, 1920(t1)
	sd t0, 1928(t1)
	sd t0, 1936(t1)
	sd t0, 1944(t1)
	sd t0, 1952(t1)
	sd t0, 1960(t1)
	sd t0, 1968(t1)
	sd t0, 1976(t1)
	sd t0, 1984(t1)
	sd t0, 1992(t1)
	sd t0, 2000(t1)
	sd t0, 2008(t1)
	sd t0, 2016(t1)
	sd t0, 2024(t1)
	sd t0, 2032(t1)
	sd t0, 2040(t1)
	addi sp, sp, -256
	addi t1, sp, 0
	sd t0, 0(t1)
	sd t0, 8(t1)
	sd t0, 16(t1)
	sd t0, 24(t1)
	sd t0, 32(t1)
	sd t0, 40(t1)
	sd t0, 48(t1)
	sd t0, 56(t1)
	sd t0, 64(t1)
	sd t0, 72(t1)
	sd t0, 80(t1)
	sd t0, 88(t1)
	sd t0, 96(t1)
	sd t0, 104(t1)
	sd t0, 112(t1)
	sd t0, 120(t1)
	sd t0, 128(t1)
	sd t0, 136(t1)
	sd t0, 144(t1)
	sd t0, 152(t1)
	sd t0, 160(t1)
	sd t0, 168(t1)
	sd t0, 176(t1)
	sd t0, 184(t1)
	sd t0, 192(t1)
	sd t0, 200(t1)
	sd t0, 208(t1)
	sd t0, 216(t1)
	sd t0, 224(t1)
	sd t0, 232(t1)
	sd t0, 240(t1)
	sd t0, 248(t1)
	addi sp, sp, 256
	addi sp, sp, 16
	addi sp, sp, 2032
	addi a0, zero, 0
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
