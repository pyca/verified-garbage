// The functions of `src/sm4.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sm4_expand_key:
	.option push
	.option arch, +m, +c
	addi sp, sp, -2032
	addi sp, sp, -1136
	addi a2, sp, 0
	addi a5, a2, 0
	addi t0, a5, 2040
	addi t0, t0, 1032
	sd s0, 0(t0)
	sd s1, 8(t0)
	sd s2, 16(t0)
	sd s3, 24(t0)
	sd s4, 32(t0)
	sd s5, 40(t0)
	sd s6, 48(t0)
	sd s7, 56(t0)
	sd s8, 64(t0)
	sd s9, 72(t0)
	sd s10, 80(t0)
	sd s11, 88(t0)
	lbu t0, 0(a0)
	lbu t2, 1(a0)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(a0)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(a0)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t3, 4(a0)
	lbu t2, 5(a0)
	slli t2, t2, 8
	or t3, t3, t2
	lbu t2, 6(a0)
	slli t2, t2, 16
	or t3, t3, t2
	lbu t2, 7(a0)
	slli t2, t2, 24
	or t3, t3, t2
	slli t3, t3, 32
	or t0, t0, t3
	lui t1, 328507
	addiw t1, t1, -1449
	slli t1, t1, 32
	lui t2, 813995
	addiw t2, t2, 419
	add t1, t1, t2
	xor t0, t0, t1
	sd t0, 768(a5)
	sd t0, 784(a5)
	sd t0, 800(a5)
	sd t0, 816(a5)
	sd t0, 832(a5)
	sd t0, 848(a5)
	sd t0, 864(a5)
	sd t0, 880(a5)
	sd t0, 896(a5)
	sd t0, 912(a5)
	sd t0, 928(a5)
	sd t0, 944(a5)
	sd t0, 960(a5)
	sd t0, 976(a5)
	sd t0, 992(a5)
	sd t0, 1008(a5)
	lbu t0, 8(a0)
	lbu t2, 9(a0)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 10(a0)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 11(a0)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t3, 12(a0)
	lbu t2, 13(a0)
	slli t2, t2, 8
	or t3, t3, t2
	lbu t2, 14(a0)
	slli t2, t2, 16
	or t3, t3, t2
	lbu t2, 15(a0)
	slli t2, t2, 24
	or t3, t3, t2
	slli t3, t3, 32
	or t0, t0, t3
	lui t1, 901671
	addiw t1, t1, 179
	slli t1, t1, 32
	lui t2, 620824
	addiw t2, t2, -665
	add t1, t1, t2
	xor t0, t0, t1
	sd t0, 776(a5)
	sd t0, 792(a5)
	sd t0, 808(a5)
	sd t0, 824(a5)
	sd t0, 840(a5)
	sd t0, 856(a5)
	sd t0, 872(a5)
	sd t0, 888(a5)
	sd t0, 904(a5)
	sd t0, 920(a5)
	sd t0, 936(a5)
	sd t0, 952(a5)
	sd t0, 968(a5)
	sd t0, 984(a5)
	sd t0, 1000(a5)
	sd t0, 1016(a5)
	addi a0, ra, 0
	call {vg_sm4_expand_key_shared}
	addi ra, a0, 0
	addi t0, a5, 2040
	addi t0, t0, 1032
	ld s0, 0(t0)
	ld s1, 8(t0)
	ld s2, 16(t0)
	ld s3, 24(t0)
	ld s4, 32(t0)
	ld s5, 40(t0)
	ld s6, 48(t0)
	ld s7, 56(t0)
	ld s8, 64(t0)
	ld s9, 72(t0)
	ld s10, 80(t0)
	ld s11, 88(t0)
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
	addi t5, t5, 1024
	addi t5, t5, 1024
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
	addi sp, sp, 1136
	addi sp, sp, 2032
	addi t0, zero, 0
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
	addi a0, zero, 0
	ret
	.option pop

vg_sm4_ecb_encrypt:
	.option push
	.option arch, +m, +c
	addi sp, sp, -2032
	addi sp, sp, -1136
	addi a3, sp, 0
	addi a5, a3, 0
	addi t0, a5, 2040
	addi t0, t0, 1032
	sd s0, 0(t0)
	sd s1, 8(t0)
	sd s2, 16(t0)
	sd s3, 24(t0)
	sd s4, 32(t0)
	sd s5, 40(t0)
	sd s6, 48(t0)
	sd s7, 56(t0)
	sd s8, 64(t0)
	sd s9, 72(t0)
	sd s10, 80(t0)
	sd s11, 88(t0)
	lui t0, 0
	addiw t0, t0, 255
	slli t0, t0, 32
	lui t1, 4080
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 320(a5)
	lui t0, 16
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, 1
	add t0, t0, t1
	sd t0, 328(a5)
	lui t0, 0
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 360(a5)
	lui t0, 16
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 368(a5)
	lui t0, 4080
	addiw t0, t0, 255
	slli t0, t0, 32
	lui t1, 4080
	addiw t1, t1, 255
	add t0, t0, t1
	sd t0, 376(a5)
	lui t0, 349525
	addiw t0, t0, 1365
	slli t0, t0, 32
	lui t1, 349525
	addiw t1, t1, 1365
	add t0, t0, t1
	sd t0, 384(a5)
	lui t0, 209715
	addiw t0, t0, 819
	slli t0, t0, 32
	lui t1, 209715
	addiw t1, t1, 819
	add t0, t0, t1
	sd t0, 392(a5)
	lui t0, 61681
	addiw t0, t0, -241
	slli t0, t0, 32
	lui t1, 61681
	addiw t1, t1, -241
	add t0, t0, t1
	sd t0, 400(a5)
	addi t1, a0, 0
	addi t2, a5, 768
	addi t3, zero, 128
	or t4, t1, t2
	andi t4, t4, 7
	beqz t4, 20f
22:
	lbu t4, 0(t1)
	sb t4, 0(t2)
	addi t1, t1, 1
	addi t2, t2, 1
	addi t3, t3, -1
	bnez t3, 22b
	j 21f
20:
	srli t3, t3, 3
23:
	ld t4, 0(t1)
	sd t4, 0(t2)
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 23b
21:
	addi a0, a5, 768
	addi a3, a5, 1024
	addi s8, zero, 16
24:
	ld t1, 0(a0)
	ld t2, 360(a5)
	and t1, t1, t2
	ld t2, 320(a5)
	slli t0, t1, 24
	slli t3, t1, 48
	xor t0, t0, t1
	srli t4, t1, 24
	and t0, t0, t2
	xor t3, t3, t4
	xor t1, t0, t3
	ld t6, 328(a5)
	and s0, t1, t6
	srli s1, t1, 1
	and s1, s1, t6
	srli s2, t1, 2
	and s2, s2, t6
	srli s3, t1, 3
	and s3, s3, t6
	srli s4, t1, 4
	and s4, s4, t6
	srli s5, t1, 5
	and s5, s5, t6
	srli s6, t1, 6
	and s6, s6, t6
	srli s7, t1, 7
	and s7, s7, t6
	lui t0, 16
	addiw t0, t0, -1
	mul s0, s0, t0
	mul s1, s1, t0
	mul s2, s2, t0
	mul s3, s3, t0
	mul s4, s4, t0
	mul s5, s5, t0
	mul s6, s6, t0
	mul s7, s7, t0
	sd s0, 0(a3)
	sd s1, 8(a3)
	sd s2, 16(a3)
	sd s3, 24(a3)
	sd s4, 32(a3)
	sd s5, 40(a3)
	sd s6, 48(a3)
	sd s7, 56(a3)
	addi a3, a3, 64
	ld t1, 0(a0)
	srli t1, t1, 32
	ld t2, 320(a5)
	slli t0, t1, 24
	slli t3, t1, 48
	xor t0, t0, t1
	srli t4, t1, 24
	and t0, t0, t2
	xor t3, t3, t4
	xor t1, t0, t3
	ld t6, 328(a5)
	and s0, t1, t6
	srli s1, t1, 1
	and s1, s1, t6
	srli s2, t1, 2
	and s2, s2, t6
	srli s3, t1, 3
	and s3, s3, t6
	srli s4, t1, 4
	and s4, s4, t6
	srli s5, t1, 5
	and s5, s5, t6
	srli s6, t1, 6
	and s6, s6, t6
	srli s7, t1, 7
	and s7, s7, t6
	lui t0, 16
	addiw t0, t0, -1
	mul s0, s0, t0
	mul s1, s1, t0
	mul s2, s2, t0
	mul s3, s3, t0
	mul s4, s4, t0
	mul s5, s5, t0
	mul s6, s6, t0
	mul s7, s7, t0
	sd s0, 0(a3)
	sd s1, 8(a3)
	sd s2, 16(a3)
	sd s3, 24(a3)
	sd s4, 32(a3)
	sd s5, 40(a3)
	sd s6, 48(a3)
	sd s7, 56(a3)
	addi a3, a3, 64
	addi a0, a0, 8
	addi s8, s8, -1
	bnez s8, 24b
	addi a0, a5, 2040
	addi a0, a0, 1032
	beqz a2, 25f
27:
	srli t0, a2, 4
	bnez t0, 28f
	addi a4, a2, 0
	j 29f
28:
	addi a4, zero, 16
29:
	addi t1, a1, 0
	addi t2, a5, 768
	slli t3, a4, 4
	or t4, t1, t2
	andi t4, t4, 7
	beqz t4, 210f
212:
	lbu t4, 0(t1)
	sb t4, 0(t2)
	addi t1, t1, 1
	addi t2, t2, 1
	addi t3, t3, -1
	bnez t3, 212b
	j 211f
210:
	srli t3, t3, 3
213:
	ld t4, 0(t1)
	sd t4, 0(t2)
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 213b
211:
	ld t3, 360(a5)
	ld t4, 368(a5)
	ld t5, 376(a5)
	ld t6, 384(a5)
	ld a6, 392(a5)
	ld s8, 400(a5)
	ld s0, 768(a5)
	ld s4, 896(a5)
	ld s1, 784(a5)
	ld s5, 912(a5)
	ld s2, 800(a5)
	ld s6, 928(a5)
	ld s3, 816(a5)
	ld s7, 944(a5)
	srli t0, s0, 8
	xor t0, t0, s4
	and t0, t0, t5
	xor s4, s4, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s5
	and t0, t0, t5
	xor s5, s5, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s6
	and t0, t0, t5
	xor s6, s6, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s7
	and t0, t0, t5
	xor s7, s7, t0
	slli t0, t0, 8
	xor s3, s3, t0
	srli t0, s0, 16
	xor t0, t0, s4
	and t0, t0, t4
	xor s4, s4, t0
	slli t0, t0, 16
	xor s0, s0, t0
	srli t0, s1, 16
	xor t0, t0, s5
	and t0, t0, t4
	xor s5, s5, t0
	slli t0, t0, 16
	xor s1, s1, t0
	srli t0, s2, 16
	xor t0, t0, s6
	and t0, t0, t4
	xor s6, s6, t0
	slli t0, t0, 16
	xor s2, s2, t0
	srli t0, s3, 16
	xor t0, t0, s7
	and t0, t0, t4
	xor s7, s7, t0
	slli t0, t0, 16
	xor s3, s3, t0
	srli t0, s0, 32
	xor t0, t0, s4
	and t0, t0, t3
	xor s4, s4, t0
	slli t0, t0, 32
	xor s0, s0, t0
	srli t0, s1, 32
	xor t0, t0, s5
	and t0, t0, t3
	xor s5, s5, t0
	slli t0, t0, 32
	xor s1, s1, t0
	srli t0, s2, 32
	xor t0, t0, s6
	and t0, t0, t3
	xor s6, s6, t0
	slli t0, t0, 32
	xor s2, s2, t0
	srli t0, s3, 32
	xor t0, t0, s7
	and t0, t0, t3
	xor s7, s7, t0
	slli t0, t0, 32
	xor s3, s3, t0
	sd s0, 768(a5)
	sd s4, 896(a5)
	sd s1, 784(a5)
	sd s5, 912(a5)
	sd s2, 800(a5)
	sd s6, 928(a5)
	sd s3, 816(a5)
	sd s7, 944(a5)
	ld s0, 832(a5)
	ld s4, 960(a5)
	ld s1, 848(a5)
	ld s5, 976(a5)
	ld s2, 864(a5)
	ld s6, 992(a5)
	ld s3, 880(a5)
	ld s7, 1008(a5)
	srli t0, s0, 8
	xor t0, t0, s4
	and t0, t0, t5
	xor s4, s4, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s5
	and t0, t0, t5
	xor s5, s5, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s6
	and t0, t0, t5
	xor s6, s6, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s7
	and t0, t0, t5
	xor s7, s7, t0
	slli t0, t0, 8
	xor s3, s3, t0
	srli t0, s0, 16
	xor t0, t0, s4
	and t0, t0, t4
	xor s4, s4, t0
	slli t0, t0, 16
	xor s0, s0, t0
	srli t0, s1, 16
	xor t0, t0, s5
	and t0, t0, t4
	xor s5, s5, t0
	slli t0, t0, 16
	xor s1, s1, t0
	srli t0, s2, 16
	xor t0, t0, s6
	and t0, t0, t4
	xor s6, s6, t0
	slli t0, t0, 16
	xor s2, s2, t0
	srli t0, s3, 16
	xor t0, t0, s7
	and t0, t0, t4
	xor s7, s7, t0
	slli t0, t0, 16
	xor s3, s3, t0
	srli t0, s0, 32
	xor t0, t0, s4
	and t0, t0, t3
	xor s4, s4, t0
	slli t0, t0, 32
	xor s0, s0, t0
	srli t0, s1, 32
	xor t0, t0, s5
	and t0, t0, t3
	xor s5, s5, t0
	slli t0, t0, 32
	xor s1, s1, t0
	srli t0, s2, 32
	xor t0, t0, s6
	and t0, t0, t3
	xor s6, s6, t0
	slli t0, t0, 32
	xor s2, s2, t0
	srli t0, s3, 32
	xor t0, t0, s7
	and t0, t0, t3
	xor s7, s7, t0
	slli t0, t0, 32
	xor s3, s3, t0
	sd s0, 832(a5)
	sd s4, 960(a5)
	sd s1, 848(a5)
	sd s5, 976(a5)
	sd s2, 864(a5)
	sd s6, 992(a5)
	sd s3, 880(a5)
	sd s7, 1008(a5)
	ld s0, 776(a5)
	ld s4, 904(a5)
	ld s1, 792(a5)
	ld s5, 920(a5)
	ld s2, 808(a5)
	ld s6, 936(a5)
	ld s3, 824(a5)
	ld s7, 952(a5)
	srli t0, s0, 8
	xor t0, t0, s4
	and t0, t0, t5
	xor s4, s4, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s5
	and t0, t0, t5
	xor s5, s5, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s6
	and t0, t0, t5
	xor s6, s6, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s7
	and t0, t0, t5
	xor s7, s7, t0
	slli t0, t0, 8
	xor s3, s3, t0
	srli t0, s0, 16
	xor t0, t0, s4
	and t0, t0, t4
	xor s4, s4, t0
	slli t0, t0, 16
	xor s0, s0, t0
	srli t0, s1, 16
	xor t0, t0, s5
	and t0, t0, t4
	xor s5, s5, t0
	slli t0, t0, 16
	xor s1, s1, t0
	srli t0, s2, 16
	xor t0, t0, s6
	and t0, t0, t4
	xor s6, s6, t0
	slli t0, t0, 16
	xor s2, s2, t0
	srli t0, s3, 16
	xor t0, t0, s7
	and t0, t0, t4
	xor s7, s7, t0
	slli t0, t0, 16
	xor s3, s3, t0
	srli t0, s0, 32
	xor t0, t0, s4
	and t0, t0, t3
	xor s4, s4, t0
	slli t0, t0, 32
	xor s0, s0, t0
	srli t0, s1, 32
	xor t0, t0, s5
	and t0, t0, t3
	xor s5, s5, t0
	slli t0, t0, 32
	xor s1, s1, t0
	srli t0, s2, 32
	xor t0, t0, s6
	and t0, t0, t3
	xor s6, s6, t0
	slli t0, t0, 32
	xor s2, s2, t0
	srli t0, s3, 32
	xor t0, t0, s7
	and t0, t0, t3
	xor s7, s7, t0
	slli t0, t0, 32
	xor s3, s3, t0
	sd s0, 776(a5)
	sd s4, 904(a5)
	sd s1, 792(a5)
	sd s5, 920(a5)
	sd s2, 808(a5)
	sd s6, 936(a5)
	sd s3, 824(a5)
	sd s7, 952(a5)
	ld s0, 840(a5)
	ld s4, 968(a5)
	ld s1, 856(a5)
	ld s5, 984(a5)
	ld s2, 872(a5)
	ld s6, 1000(a5)
	ld s3, 888(a5)
	ld s7, 1016(a5)
	srli t0, s0, 8
	xor t0, t0, s4
	and t0, t0, t5
	xor s4, s4, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s5
	and t0, t0, t5
	xor s5, s5, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s6
	and t0, t0, t5
	xor s6, s6, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s7
	and t0, t0, t5
	xor s7, s7, t0
	slli t0, t0, 8
	xor s3, s3, t0
	srli t0, s0, 16
	xor t0, t0, s4
	and t0, t0, t4
	xor s4, s4, t0
	slli t0, t0, 16
	xor s0, s0, t0
	srli t0, s1, 16
	xor t0, t0, s5
	and t0, t0, t4
	xor s5, s5, t0
	slli t0, t0, 16
	xor s1, s1, t0
	srli t0, s2, 16
	xor t0, t0, s6
	and t0, t0, t4
	xor s6, s6, t0
	slli t0, t0, 16
	xor s2, s2, t0
	srli t0, s3, 16
	xor t0, t0, s7
	and t0, t0, t4
	xor s7, s7, t0
	slli t0, t0, 16
	xor s3, s3, t0
	srli t0, s0, 32
	xor t0, t0, s4
	and t0, t0, t3
	xor s4, s4, t0
	slli t0, t0, 32
	xor s0, s0, t0
	srli t0, s1, 32
	xor t0, t0, s5
	and t0, t0, t3
	xor s5, s5, t0
	slli t0, t0, 32
	xor s1, s1, t0
	srli t0, s2, 32
	xor t0, t0, s6
	and t0, t0, t3
	xor s6, s6, t0
	slli t0, t0, 32
	xor s2, s2, t0
	srli t0, s3, 32
	xor t0, t0, s7
	and t0, t0, t3
	xor s7, s7, t0
	slli t0, t0, 32
	xor s3, s3, t0
	sd s0, 840(a5)
	sd s4, 968(a5)
	sd s1, 856(a5)
	sd s5, 984(a5)
	sd s2, 872(a5)
	sd s6, 1000(a5)
	sd s3, 888(a5)
	sd s7, 1016(a5)
	ld s0, 768(a5)
	ld s1, 784(a5)
	ld s2, 800(a5)
	ld s3, 816(a5)
	ld s4, 832(a5)
	ld s5, 848(a5)
	ld s6, 864(a5)
	ld s7, 880(a5)
	srli t0, s0, 4
	xor t0, t0, s4
	and t0, t0, s8
	xor s4, s4, t0
	slli t0, t0, 4
	xor s0, s0, t0
	srli t0, s1, 4
	xor t0, t0, s5
	and t0, t0, s8
	xor s5, s5, t0
	slli t0, t0, 4
	xor s1, s1, t0
	srli t0, s2, 4
	xor t0, t0, s6
	and t0, t0, s8
	xor s6, s6, t0
	slli t0, t0, 4
	xor s2, s2, t0
	srli t0, s3, 4
	xor t0, t0, s7
	and t0, t0, s8
	xor s7, s7, t0
	slli t0, t0, 4
	xor s3, s3, t0
	srli t0, s0, 2
	xor t0, t0, s2
	and t0, t0, a6
	xor s2, s2, t0
	slli t0, t0, 2
	xor s0, s0, t0
	srli t0, s1, 2
	xor t0, t0, s3
	and t0, t0, a6
	xor s3, s3, t0
	slli t0, t0, 2
	xor s1, s1, t0
	srli t0, s4, 2
	xor t0, t0, s6
	and t0, t0, a6
	xor s6, s6, t0
	slli t0, t0, 2
	xor s4, s4, t0
	srli t0, s5, 2
	xor t0, t0, s7
	and t0, t0, a6
	xor s7, s7, t0
	slli t0, t0, 2
	xor s5, s5, t0
	srli t0, s0, 1
	xor t0, t0, s1
	and t0, t0, t6
	xor s1, s1, t0
	slli t0, t0, 1
	xor s0, s0, t0
	srli t0, s2, 1
	xor t0, t0, s3
	and t0, t0, t6
	xor s3, s3, t0
	slli t0, t0, 1
	xor s2, s2, t0
	srli t0, s4, 1
	xor t0, t0, s5
	and t0, t0, t6
	xor s5, s5, t0
	slli t0, t0, 1
	xor s4, s4, t0
	srli t0, s6, 1
	xor t0, t0, s7
	and t0, t0, t6
	xor s7, s7, t0
	slli t0, t0, 1
	xor s6, s6, t0
	sd s0, 512(a5)
	sd s1, 520(a5)
	sd s2, 528(a5)
	sd s3, 536(a5)
	sd s4, 544(a5)
	sd s5, 552(a5)
	sd s6, 560(a5)
	sd s7, 568(a5)
	ld s0, 896(a5)
	ld s1, 912(a5)
	ld s2, 928(a5)
	ld s3, 944(a5)
	ld s4, 960(a5)
	ld s5, 976(a5)
	ld s6, 992(a5)
	ld s7, 1008(a5)
	srli t0, s0, 4
	xor t0, t0, s4
	and t0, t0, s8
	xor s4, s4, t0
	slli t0, t0, 4
	xor s0, s0, t0
	srli t0, s1, 4
	xor t0, t0, s5
	and t0, t0, s8
	xor s5, s5, t0
	slli t0, t0, 4
	xor s1, s1, t0
	srli t0, s2, 4
	xor t0, t0, s6
	and t0, t0, s8
	xor s6, s6, t0
	slli t0, t0, 4
	xor s2, s2, t0
	srli t0, s3, 4
	xor t0, t0, s7
	and t0, t0, s8
	xor s7, s7, t0
	slli t0, t0, 4
	xor s3, s3, t0
	srli t0, s0, 2
	xor t0, t0, s2
	and t0, t0, a6
	xor s2, s2, t0
	slli t0, t0, 2
	xor s0, s0, t0
	srli t0, s1, 2
	xor t0, t0, s3
	and t0, t0, a6
	xor s3, s3, t0
	slli t0, t0, 2
	xor s1, s1, t0
	srli t0, s4, 2
	xor t0, t0, s6
	and t0, t0, a6
	xor s6, s6, t0
	slli t0, t0, 2
	xor s4, s4, t0
	srli t0, s5, 2
	xor t0, t0, s7
	and t0, t0, a6
	xor s7, s7, t0
	slli t0, t0, 2
	xor s5, s5, t0
	srli t0, s0, 1
	xor t0, t0, s1
	and t0, t0, t6
	xor s1, s1, t0
	slli t0, t0, 1
	xor s0, s0, t0
	srli t0, s2, 1
	xor t0, t0, s3
	and t0, t0, t6
	xor s3, s3, t0
	slli t0, t0, 1
	xor s2, s2, t0
	srli t0, s4, 1
	xor t0, t0, s5
	and t0, t0, t6
	xor s5, s5, t0
	slli t0, t0, 1
	xor s4, s4, t0
	srli t0, s6, 1
	xor t0, t0, s7
	and t0, t0, t6
	xor s7, s7, t0
	slli t0, t0, 1
	xor s6, s6, t0
	sd s0, 576(a5)
	sd s1, 584(a5)
	sd s2, 592(a5)
	sd s3, 600(a5)
	sd s4, 608(a5)
	sd s5, 616(a5)
	sd s6, 624(a5)
	sd s7, 632(a5)
	ld s0, 776(a5)
	ld s1, 792(a5)
	ld s2, 808(a5)
	ld s3, 824(a5)
	ld s4, 840(a5)
	ld s5, 856(a5)
	ld s6, 872(a5)
	ld s7, 888(a5)
	srli t0, s0, 4
	xor t0, t0, s4
	and t0, t0, s8
	xor s4, s4, t0
	slli t0, t0, 4
	xor s0, s0, t0
	srli t0, s1, 4
	xor t0, t0, s5
	and t0, t0, s8
	xor s5, s5, t0
	slli t0, t0, 4
	xor s1, s1, t0
	srli t0, s2, 4
	xor t0, t0, s6
	and t0, t0, s8
	xor s6, s6, t0
	slli t0, t0, 4
	xor s2, s2, t0
	srli t0, s3, 4
	xor t0, t0, s7
	and t0, t0, s8
	xor s7, s7, t0
	slli t0, t0, 4
	xor s3, s3, t0
	srli t0, s0, 2
	xor t0, t0, s2
	and t0, t0, a6
	xor s2, s2, t0
	slli t0, t0, 2
	xor s0, s0, t0
	srli t0, s1, 2
	xor t0, t0, s3
	and t0, t0, a6
	xor s3, s3, t0
	slli t0, t0, 2
	xor s1, s1, t0
	srli t0, s4, 2
	xor t0, t0, s6
	and t0, t0, a6
	xor s6, s6, t0
	slli t0, t0, 2
	xor s4, s4, t0
	srli t0, s5, 2
	xor t0, t0, s7
	and t0, t0, a6
	xor s7, s7, t0
	slli t0, t0, 2
	xor s5, s5, t0
	srli t0, s0, 1
	xor t0, t0, s1
	and t0, t0, t6
	xor s1, s1, t0
	slli t0, t0, 1
	xor s0, s0, t0
	srli t0, s2, 1
	xor t0, t0, s3
	and t0, t0, t6
	xor s3, s3, t0
	slli t0, t0, 1
	xor s2, s2, t0
	srli t0, s4, 1
	xor t0, t0, s5
	and t0, t0, t6
	xor s5, s5, t0
	slli t0, t0, 1
	xor s4, s4, t0
	srli t0, s6, 1
	xor t0, t0, s7
	and t0, t0, t6
	xor s7, s7, t0
	slli t0, t0, 1
	xor s6, s6, t0
	sd s0, 640(a5)
	sd s1, 648(a5)
	sd s2, 656(a5)
	sd s3, 664(a5)
	sd s4, 672(a5)
	sd s5, 680(a5)
	sd s6, 688(a5)
	sd s7, 696(a5)
	ld s0, 904(a5)
	ld s1, 920(a5)
	ld s2, 936(a5)
	ld s3, 952(a5)
	ld s4, 968(a5)
	ld s5, 984(a5)
	ld s6, 1000(a5)
	ld s7, 1016(a5)
	srli t0, s0, 4
	xor t0, t0, s4
	and t0, t0, s8
	xor s4, s4, t0
	slli t0, t0, 4
	xor s0, s0, t0
	srli t0, s1, 4
	xor t0, t0, s5
	and t0, t0, s8
	xor s5, s5, t0
	slli t0, t0, 4
	xor s1, s1, t0
	srli t0, s2, 4
	xor t0, t0, s6
	and t0, t0, s8
	xor s6, s6, t0
	slli t0, t0, 4
	xor s2, s2, t0
	srli t0, s3, 4
	xor t0, t0, s7
	and t0, t0, s8
	xor s7, s7, t0
	slli t0, t0, 4
	xor s3, s3, t0
	srli t0, s0, 2
	xor t0, t0, s2
	and t0, t0, a6
	xor s2, s2, t0
	slli t0, t0, 2
	xor s0, s0, t0
	srli t0, s1, 2
	xor t0, t0, s3
	and t0, t0, a6
	xor s3, s3, t0
	slli t0, t0, 2
	xor s1, s1, t0
	srli t0, s4, 2
	xor t0, t0, s6
	and t0, t0, a6
	xor s6, s6, t0
	slli t0, t0, 2
	xor s4, s4, t0
	srli t0, s5, 2
	xor t0, t0, s7
	and t0, t0, a6
	xor s7, s7, t0
	slli t0, t0, 2
	xor s5, s5, t0
	srli t0, s0, 1
	xor t0, t0, s1
	and t0, t0, t6
	xor s1, s1, t0
	slli t0, t0, 1
	xor s0, s0, t0
	srli t0, s2, 1
	xor t0, t0, s3
	and t0, t0, t6
	xor s3, s3, t0
	slli t0, t0, 1
	xor s2, s2, t0
	srli t0, s4, 1
	xor t0, t0, s5
	and t0, t0, t6
	xor s5, s5, t0
	slli t0, t0, 1
	xor s4, s4, t0
	srli t0, s6, 1
	xor t0, t0, s7
	and t0, t0, t6
	xor s7, s7, t0
	slli t0, t0, 1
	xor s6, s6, t0
	sd s0, 704(a5)
	sd s1, 712(a5)
	sd s2, 720(a5)
	sd s3, 728(a5)
	sd s4, 736(a5)
	sd s5, 744(a5)
	sd s6, 752(a5)
	sd s7, 760(a5)
	addi a3, a5, 1024
214:
	ld s0, 576(a5)
	ld t0, 640(a5)
	xor s0, s0, t0
	ld t0, 704(a5)
	xor s0, s0, t0
	ld t0, 0(a3)
	xor s0, s0, t0
	ld s1, 584(a5)
	ld t0, 648(a5)
	xor s1, s1, t0
	ld t0, 712(a5)
	xor s1, s1, t0
	ld t0, 8(a3)
	xor s1, s1, t0
	ld s2, 592(a5)
	ld t0, 656(a5)
	xor s2, s2, t0
	ld t0, 720(a5)
	xor s2, s2, t0
	ld t0, 16(a3)
	xor s2, s2, t0
	ld s3, 600(a5)
	ld t0, 664(a5)
	xor s3, s3, t0
	ld t0, 728(a5)
	xor s3, s3, t0
	ld t0, 24(a3)
	xor s3, s3, t0
	ld s4, 608(a5)
	ld t0, 672(a5)
	xor s4, s4, t0
	ld t0, 736(a5)
	xor s4, s4, t0
	ld t0, 32(a3)
	xor s4, s4, t0
	ld s5, 616(a5)
	ld t0, 680(a5)
	xor s5, s5, t0
	ld t0, 744(a5)
	xor s5, s5, t0
	ld t0, 40(a3)
	xor s5, s5, t0
	ld s6, 624(a5)
	ld t0, 688(a5)
	xor s6, s6, t0
	ld t0, 752(a5)
	xor s6, s6, t0
	ld t0, 48(a3)
	xor s6, s6, t0
	ld s7, 632(a5)
	ld t0, 696(a5)
	xor s7, s7, t0
	ld t0, 760(a5)
	xor s7, s7, t0
	ld t0, 56(a3)
	xor s7, s7, t0
	xori s2, s2, -1
	xori s6, s6, -1
	xor t0, s2, s6
	xori s5, s5, -1
	xor s3, s3, s5
	xor t1, s0, s3
	xori t1, t1, -1
	xor s7, s7, t0
	xor t2, s7, s3
	xor t3, s6, s3
	xor t4, s6, t2
	xor s0, s0, s4
	xor s0, s6, s0
	xor s5, s5, s0
	xor s4, s5, t4
	and t5, s4, t4
	xor t6, s1, t0
	xor a6, s1, t1
	and a7, a6, t3
	xor t5, t5, a7
	xor s8, t0, s4
	xor s9, t6, s0
	xor s3, s9, s3
	and s10, t6, s9
	xor s11, s7, s9
	sd t0, 0(a5)
	and t0, t0, s6
	xor s10, s10, t0
	xor t5, t5, s10
	sd s6, 8(a5)
	xor s6, s6, s9
	sd s1, 16(a5)
	and s1, s1, s6
	xor s1, s1, t0
	xor t5, t5, s5
	xor s5, t1, s8
	and t0, s8, t2
	sd s6, 24(a5)
	and s6, t1, s3
	xor t0, t0, s6
	xor t0, t0, s10
	xor s10, t6, s5
	xor t0, t0, s0
	and s0, s10, s7
	xor s0, s0, a7
	and a7, s5, s11
	xor a7, a7, s6
	xor a7, a7, s1
	xor s0, s0, s1
	xor a7, a7, s2
	xor s1, a6, t3
	xor s0, s0, s1
	and s1, a7, s0
	xor a7, a7, t0
	xor s2, t0, s1
	xor s6, s0, t5
	and s2, s2, s6
	xor s2, s2, t5
	xor s0, s0, s2
	xor s1, t5, s1
	xor s6, s1, s2
	and t2, s2, t2
	and t5, t5, s6
	xor s0, t5, s0
	xor t5, s1, t5
	and s8, s2, s8
	and s1, a7, s1
	xor s1, s1, t0
	and s4, s1, s4
	and t5, s1, t5
	xor a7, a7, t5
	xor s6, s1, a7
	xor t0, a7, s0
	and s11, s0, s11
	xor t5, s2, s0
	and s7, a7, s7
	and t6, t0, t6
	and s9, t0, s9
	and t3, s6, t3
	and t1, t5, t1
	and s0, s0, s5
	and t5, t5, s3
	and s6, s6, a6
	and t4, s1, t4
	xor s1, s1, s2
	xor s6, s6, s4
	ld s2, 8(a5)
	and s2, s1, s2
	xor t5, t5, t2
	xor s2, s2, s9
	and a7, a7, s10
	xor t0, s1, t0
	ld s3, 24(a5)
	and s3, t0, s3
	xor s11, s11, t2
	xor t3, t3, t5
	xori s3, s3, -1
	ld s5, 16(a5)
	and t0, t0, s5
	xor a7, a7, s4
	xor s3, s3, s9
	xor s11, s11, s3
	xor s7, s7, t3
	xor s7, s7, s3
	xor s2, s2, t5
	xor a7, a7, s7
	xor t4, t4, t3
	xor t1, t1, s6
	xor t0, t0, a7
	xor t0, t0, t6
	ld s3, 0(a5)
	and s1, s1, s3
	xor s0, s0, a7
	xor s2, s2, s0
	xor s1, s1, s6
	xor s3, s1, t6
	xor s4, s8, s0
	xor s0, s2, t1
	xor s1, s7, s3
	xor s2, t0, s0
	xor s5, s11, s4
	xor s8, s8, t1
	xori s7, s8, -1
	xor s6, t4, t0
	srli t0, s2, 16
	slli t1, s2, 48
	ld t2, 528(a5)
	xor t0, t0, t1
	srli t1, s0, 16
	slli t3, s0, 48
	srli t4, s1, 16
	slli t5, s1, 48
	xor t0, s2, t0
	xor t1, t1, t3
	xor t4, t4, t5
	srli t3, s3, 16
	srli t5, t0, 16
	slli t6, t0, 48
	xor t1, s0, t1
	slli a6, s3, 48
	xor t4, s1, t4
	xor t3, t3, a6
	xor t5, t5, t6
	xor t3, s3, t3
	xor t5, t5, s0
	ld s0, 536(a5)
	srli t6, t3, 16
	slli a6, t3, 48
	xor t6, t6, a6
	srli a6, t5, 32
	xor t6, t6, s1
	slli t5, t5, 32
	srli s1, s4, 16
	xor a6, a6, t5
	slli t5, s4, 48
	xor a6, a6, t1
	xor s1, s1, t5
	srli t5, t6, 32
	xor s1, s4, s1
	slli t6, t6, 32
	xor t5, t5, t6
	xor a6, a6, t2
	srli t2, s1, 16
	xor t5, t5, t4
	sd a6, 528(a5)
	srli t6, s5, 16
	slli a6, s5, 48
	xor t6, t6, a6
	slli a6, s1, 48
	xor t6, s5, t6
	xor t2, t2, a6
	ld a6, 544(a5)
	xor t2, t2, s2
	xor t5, t5, s0
	srli s0, t6, 16
	srli s2, t2, 32
	sd t5, 536(a5)
	slli t5, t6, 48
	slli t2, t2, 32
	xor s0, s0, t5
	ld t5, 552(a5)
	xor s2, s2, t2
	srli t2, s6, 16
	xor s0, s0, s3
	slli s3, s6, 48
	xor s2, s2, t0
	xor t2, t2, s3
	srli s3, s0, 32
	xor t2, s6, t2
	slli s0, s0, 32
	xor s3, s3, s0
	xor s2, s2, a6
	srli s0, t2, 16
	xor s3, s3, t3
	sd s2, 544(a5)
	srli s2, s7, 16
	slli t0, s7, 48
	ld t3, 560(a5)
	xor s2, s2, t0
	slli t2, t2, 48
	xor s2, s7, s2
	xor s0, s0, t2
	xor s4, s0, s4
	xor s3, s3, t5
	srli t0, s2, 16
	srli t2, s4, 32
	sd s3, 552(a5)
	slli s2, s2, 48
	slli s4, s4, 32
	ld s3, 568(a5)
	xor t0, t0, s2
	xor t1, t1, s6
	xor s5, t0, s5
	xor t2, t2, s4
	srli s2, s5, 32
	slli s5, s5, 32
	srli s4, t1, 48
	xor s2, s2, s5
	xor t2, t2, s1
	xor s2, s2, t6
	slli t1, t1, 16
	xor t2, t2, t3
	xor s4, s4, t1
	xor s2, s2, s3
	sd t2, 560(a5)
	xor t4, t4, s7
	ld s1, 512(a5)
	xor s4, s4, s0
	sd s2, 568(a5)
	srli s0, t4, 48
	slli t4, t4, 16
	ld s2, 520(a5)
	xor s0, s0, t4
	xor s4, s4, s1
	xor s0, s0, t0
	sd s4, 512(a5)
	xor s0, s0, s2
	sd s0, 520(a5)
	ld s0, 640(a5)
	ld t0, 704(a5)
	xor s0, s0, t0
	ld t0, 512(a5)
	xor s0, s0, t0
	ld t0, 64(a3)
	xor s0, s0, t0
	ld s1, 648(a5)
	ld t0, 712(a5)
	xor s1, s1, t0
	ld t0, 520(a5)
	xor s1, s1, t0
	ld t0, 72(a3)
	xor s1, s1, t0
	ld s2, 656(a5)
	ld t0, 720(a5)
	xor s2, s2, t0
	ld t0, 528(a5)
	xor s2, s2, t0
	ld t0, 80(a3)
	xor s2, s2, t0
	ld s3, 664(a5)
	ld t0, 728(a5)
	xor s3, s3, t0
	ld t0, 536(a5)
	xor s3, s3, t0
	ld t0, 88(a3)
	xor s3, s3, t0
	ld s4, 672(a5)
	ld t0, 736(a5)
	xor s4, s4, t0
	ld t0, 544(a5)
	xor s4, s4, t0
	ld t0, 96(a3)
	xor s4, s4, t0
	ld s5, 680(a5)
	ld t0, 744(a5)
	xor s5, s5, t0
	ld t0, 552(a5)
	xor s5, s5, t0
	ld t0, 104(a3)
	xor s5, s5, t0
	ld s6, 688(a5)
	ld t0, 752(a5)
	xor s6, s6, t0
	ld t0, 560(a5)
	xor s6, s6, t0
	ld t0, 112(a3)
	xor s6, s6, t0
	ld s7, 696(a5)
	ld t0, 760(a5)
	xor s7, s7, t0
	ld t0, 568(a5)
	xor s7, s7, t0
	ld t0, 120(a3)
	xor s7, s7, t0
	xori s2, s2, -1
	xori s6, s6, -1
	xor t0, s2, s6
	xori s5, s5, -1
	xor s3, s3, s5
	xor t1, s0, s3
	xori t1, t1, -1
	xor s7, s7, t0
	xor t2, s7, s3
	xor t3, s6, s3
	xor t4, s6, t2
	xor s0, s0, s4
	xor s0, s6, s0
	xor s5, s5, s0
	xor s4, s5, t4
	and t5, s4, t4
	xor t6, s1, t0
	xor a6, s1, t1
	and a7, a6, t3
	xor t5, t5, a7
	xor s8, t0, s4
	xor s9, t6, s0
	xor s3, s9, s3
	and s10, t6, s9
	xor s11, s7, s9
	sd t0, 0(a5)
	and t0, t0, s6
	xor s10, s10, t0
	xor t5, t5, s10
	sd s6, 8(a5)
	xor s6, s6, s9
	sd s1, 16(a5)
	and s1, s1, s6
	xor s1, s1, t0
	xor t5, t5, s5
	xor s5, t1, s8
	and t0, s8, t2
	sd s6, 24(a5)
	and s6, t1, s3
	xor t0, t0, s6
	xor t0, t0, s10
	xor s10, t6, s5
	xor t0, t0, s0
	and s0, s10, s7
	xor s0, s0, a7
	and a7, s5, s11
	xor a7, a7, s6
	xor a7, a7, s1
	xor s0, s0, s1
	xor a7, a7, s2
	xor s1, a6, t3
	xor s0, s0, s1
	and s1, a7, s0
	xor a7, a7, t0
	xor s2, t0, s1
	xor s6, s0, t5
	and s2, s2, s6
	xor s2, s2, t5
	xor s0, s0, s2
	xor s1, t5, s1
	xor s6, s1, s2
	and t2, s2, t2
	and t5, t5, s6
	xor s0, t5, s0
	xor t5, s1, t5
	and s8, s2, s8
	and s1, a7, s1
	xor s1, s1, t0
	and s4, s1, s4
	and t5, s1, t5
	xor a7, a7, t5
	xor s6, s1, a7
	xor t0, a7, s0
	and s11, s0, s11
	xor t5, s2, s0
	and s7, a7, s7
	and t6, t0, t6
	and s9, t0, s9
	and t3, s6, t3
	and t1, t5, t1
	and s0, s0, s5
	and t5, t5, s3
	and s6, s6, a6
	and t4, s1, t4
	xor s1, s1, s2
	xor s6, s6, s4
	ld s2, 8(a5)
	and s2, s1, s2
	xor t5, t5, t2
	xor s2, s2, s9
	and a7, a7, s10
	xor t0, s1, t0
	ld s3, 24(a5)
	and s3, t0, s3
	xor s11, s11, t2
	xor t3, t3, t5
	xori s3, s3, -1
	ld s5, 16(a5)
	and t0, t0, s5
	xor a7, a7, s4
	xor s3, s3, s9
	xor s11, s11, s3
	xor s7, s7, t3
	xor s7, s7, s3
	xor s2, s2, t5
	xor a7, a7, s7
	xor t4, t4, t3
	xor t1, t1, s6
	xor t0, t0, a7
	xor t0, t0, t6
	ld s3, 0(a5)
	and s1, s1, s3
	xor s0, s0, a7
	xor s2, s2, s0
	xor s1, s1, s6
	xor s3, s1, t6
	xor s4, s8, s0
	xor s0, s2, t1
	xor s1, s7, s3
	xor s2, t0, s0
	xor s5, s11, s4
	xor s8, s8, t1
	xori s7, s8, -1
	xor s6, t4, t0
	srli t0, s2, 16
	slli t1, s2, 48
	ld t2, 592(a5)
	xor t0, t0, t1
	srli t1, s0, 16
	slli t3, s0, 48
	srli t4, s1, 16
	slli t5, s1, 48
	xor t0, s2, t0
	xor t1, t1, t3
	xor t4, t4, t5
	srli t3, s3, 16
	srli t5, t0, 16
	slli t6, t0, 48
	xor t1, s0, t1
	slli a6, s3, 48
	xor t4, s1, t4
	xor t3, t3, a6
	xor t5, t5, t6
	xor t3, s3, t3
	xor t5, t5, s0
	ld s0, 600(a5)
	srli t6, t3, 16
	slli a6, t3, 48
	xor t6, t6, a6
	srli a6, t5, 32
	xor t6, t6, s1
	slli t5, t5, 32
	srli s1, s4, 16
	xor a6, a6, t5
	slli t5, s4, 48
	xor a6, a6, t1
	xor s1, s1, t5
	srli t5, t6, 32
	xor s1, s4, s1
	slli t6, t6, 32
	xor t5, t5, t6
	xor a6, a6, t2
	srli t2, s1, 16
	xor t5, t5, t4
	sd a6, 592(a5)
	srli t6, s5, 16
	slli a6, s5, 48
	xor t6, t6, a6
	slli a6, s1, 48
	xor t6, s5, t6
	xor t2, t2, a6
	ld a6, 608(a5)
	xor t2, t2, s2
	xor t5, t5, s0
	srli s0, t6, 16
	srli s2, t2, 32
	sd t5, 600(a5)
	slli t5, t6, 48
	slli t2, t2, 32
	xor s0, s0, t5
	ld t5, 616(a5)
	xor s2, s2, t2
	srli t2, s6, 16
	xor s0, s0, s3
	slli s3, s6, 48
	xor s2, s2, t0
	xor t2, t2, s3
	srli s3, s0, 32
	xor t2, s6, t2
	slli s0, s0, 32
	xor s3, s3, s0
	xor s2, s2, a6
	srli s0, t2, 16
	xor s3, s3, t3
	sd s2, 608(a5)
	srli s2, s7, 16
	slli t0, s7, 48
	ld t3, 624(a5)
	xor s2, s2, t0
	slli t2, t2, 48
	xor s2, s7, s2
	xor s0, s0, t2
	xor s4, s0, s4
	xor s3, s3, t5
	srli t0, s2, 16
	srli t2, s4, 32
	sd s3, 616(a5)
	slli s2, s2, 48
	slli s4, s4, 32
	ld s3, 632(a5)
	xor t0, t0, s2
	xor t1, t1, s6
	xor s5, t0, s5
	xor t2, t2, s4
	srli s2, s5, 32
	slli s5, s5, 32
	srli s4, t1, 48
	xor s2, s2, s5
	xor t2, t2, s1
	xor s2, s2, t6
	slli t1, t1, 16
	xor t2, t2, t3
	xor s4, s4, t1
	xor s2, s2, s3
	sd t2, 624(a5)
	xor t4, t4, s7
	ld s1, 576(a5)
	xor s4, s4, s0
	sd s2, 632(a5)
	srli s0, t4, 48
	slli t4, t4, 16
	ld s2, 584(a5)
	xor s0, s0, t4
	xor s4, s4, s1
	xor s0, s0, t0
	sd s4, 576(a5)
	xor s0, s0, s2
	sd s0, 584(a5)
	ld s0, 704(a5)
	ld t0, 512(a5)
	xor s0, s0, t0
	ld t0, 576(a5)
	xor s0, s0, t0
	ld t0, 128(a3)
	xor s0, s0, t0
	ld s1, 712(a5)
	ld t0, 520(a5)
	xor s1, s1, t0
	ld t0, 584(a5)
	xor s1, s1, t0
	ld t0, 136(a3)
	xor s1, s1, t0
	ld s2, 720(a5)
	ld t0, 528(a5)
	xor s2, s2, t0
	ld t0, 592(a5)
	xor s2, s2, t0
	ld t0, 144(a3)
	xor s2, s2, t0
	ld s3, 728(a5)
	ld t0, 536(a5)
	xor s3, s3, t0
	ld t0, 600(a5)
	xor s3, s3, t0
	ld t0, 152(a3)
	xor s3, s3, t0
	ld s4, 736(a5)
	ld t0, 544(a5)
	xor s4, s4, t0
	ld t0, 608(a5)
	xor s4, s4, t0
	ld t0, 160(a3)
	xor s4, s4, t0
	ld s5, 744(a5)
	ld t0, 552(a5)
	xor s5, s5, t0
	ld t0, 616(a5)
	xor s5, s5, t0
	ld t0, 168(a3)
	xor s5, s5, t0
	ld s6, 752(a5)
	ld t0, 560(a5)
	xor s6, s6, t0
	ld t0, 624(a5)
	xor s6, s6, t0
	ld t0, 176(a3)
	xor s6, s6, t0
	ld s7, 760(a5)
	ld t0, 568(a5)
	xor s7, s7, t0
	ld t0, 632(a5)
	xor s7, s7, t0
	ld t0, 184(a3)
	xor s7, s7, t0
	xori s2, s2, -1
	xori s6, s6, -1
	xor t0, s2, s6
	xori s5, s5, -1
	xor s3, s3, s5
	xor t1, s0, s3
	xori t1, t1, -1
	xor s7, s7, t0
	xor t2, s7, s3
	xor t3, s6, s3
	xor t4, s6, t2
	xor s0, s0, s4
	xor s0, s6, s0
	xor s5, s5, s0
	xor s4, s5, t4
	and t5, s4, t4
	xor t6, s1, t0
	xor a6, s1, t1
	and a7, a6, t3
	xor t5, t5, a7
	xor s8, t0, s4
	xor s9, t6, s0
	xor s3, s9, s3
	and s10, t6, s9
	xor s11, s7, s9
	sd t0, 0(a5)
	and t0, t0, s6
	xor s10, s10, t0
	xor t5, t5, s10
	sd s6, 8(a5)
	xor s6, s6, s9
	sd s1, 16(a5)
	and s1, s1, s6
	xor s1, s1, t0
	xor t5, t5, s5
	xor s5, t1, s8
	and t0, s8, t2
	sd s6, 24(a5)
	and s6, t1, s3
	xor t0, t0, s6
	xor t0, t0, s10
	xor s10, t6, s5
	xor t0, t0, s0
	and s0, s10, s7
	xor s0, s0, a7
	and a7, s5, s11
	xor a7, a7, s6
	xor a7, a7, s1
	xor s0, s0, s1
	xor a7, a7, s2
	xor s1, a6, t3
	xor s0, s0, s1
	and s1, a7, s0
	xor a7, a7, t0
	xor s2, t0, s1
	xor s6, s0, t5
	and s2, s2, s6
	xor s2, s2, t5
	xor s0, s0, s2
	xor s1, t5, s1
	xor s6, s1, s2
	and t2, s2, t2
	and t5, t5, s6
	xor s0, t5, s0
	xor t5, s1, t5
	and s8, s2, s8
	and s1, a7, s1
	xor s1, s1, t0
	and s4, s1, s4
	and t5, s1, t5
	xor a7, a7, t5
	xor s6, s1, a7
	xor t0, a7, s0
	and s11, s0, s11
	xor t5, s2, s0
	and s7, a7, s7
	and t6, t0, t6
	and s9, t0, s9
	and t3, s6, t3
	and t1, t5, t1
	and s0, s0, s5
	and t5, t5, s3
	and s6, s6, a6
	and t4, s1, t4
	xor s1, s1, s2
	xor s6, s6, s4
	ld s2, 8(a5)
	and s2, s1, s2
	xor t5, t5, t2
	xor s2, s2, s9
	and a7, a7, s10
	xor t0, s1, t0
	ld s3, 24(a5)
	and s3, t0, s3
	xor s11, s11, t2
	xor t3, t3, t5
	xori s3, s3, -1
	ld s5, 16(a5)
	and t0, t0, s5
	xor a7, a7, s4
	xor s3, s3, s9
	xor s11, s11, s3
	xor s7, s7, t3
	xor s7, s7, s3
	xor s2, s2, t5
	xor a7, a7, s7
	xor t4, t4, t3
	xor t1, t1, s6
	xor t0, t0, a7
	xor t0, t0, t6
	ld s3, 0(a5)
	and s1, s1, s3
	xor s0, s0, a7
	xor s2, s2, s0
	xor s1, s1, s6
	xor s3, s1, t6
	xor s4, s8, s0
	xor s0, s2, t1
	xor s1, s7, s3
	xor s2, t0, s0
	xor s5, s11, s4
	xor s8, s8, t1
	xori s7, s8, -1
	xor s6, t4, t0
	srli t0, s2, 16
	slli t1, s2, 48
	ld t2, 656(a5)
	xor t0, t0, t1
	srli t1, s0, 16
	slli t3, s0, 48
	srli t4, s1, 16
	slli t5, s1, 48
	xor t0, s2, t0
	xor t1, t1, t3
	xor t4, t4, t5
	srli t3, s3, 16
	srli t5, t0, 16
	slli t6, t0, 48
	xor t1, s0, t1
	slli a6, s3, 48
	xor t4, s1, t4
	xor t3, t3, a6
	xor t5, t5, t6
	xor t3, s3, t3
	xor t5, t5, s0
	ld s0, 664(a5)
	srli t6, t3, 16
	slli a6, t3, 48
	xor t6, t6, a6
	srli a6, t5, 32
	xor t6, t6, s1
	slli t5, t5, 32
	srli s1, s4, 16
	xor a6, a6, t5
	slli t5, s4, 48
	xor a6, a6, t1
	xor s1, s1, t5
	srli t5, t6, 32
	xor s1, s4, s1
	slli t6, t6, 32
	xor t5, t5, t6
	xor a6, a6, t2
	srli t2, s1, 16
	xor t5, t5, t4
	sd a6, 656(a5)
	srli t6, s5, 16
	slli a6, s5, 48
	xor t6, t6, a6
	slli a6, s1, 48
	xor t6, s5, t6
	xor t2, t2, a6
	ld a6, 672(a5)
	xor t2, t2, s2
	xor t5, t5, s0
	srli s0, t6, 16
	srli s2, t2, 32
	sd t5, 664(a5)
	slli t5, t6, 48
	slli t2, t2, 32
	xor s0, s0, t5
	ld t5, 680(a5)
	xor s2, s2, t2
	srli t2, s6, 16
	xor s0, s0, s3
	slli s3, s6, 48
	xor s2, s2, t0
	xor t2, t2, s3
	srli s3, s0, 32
	xor t2, s6, t2
	slli s0, s0, 32
	xor s3, s3, s0
	xor s2, s2, a6
	srli s0, t2, 16
	xor s3, s3, t3
	sd s2, 672(a5)
	srli s2, s7, 16
	slli t0, s7, 48
	ld t3, 688(a5)
	xor s2, s2, t0
	slli t2, t2, 48
	xor s2, s7, s2
	xor s0, s0, t2
	xor s4, s0, s4
	xor s3, s3, t5
	srli t0, s2, 16
	srli t2, s4, 32
	sd s3, 680(a5)
	slli s2, s2, 48
	slli s4, s4, 32
	ld s3, 696(a5)
	xor t0, t0, s2
	xor t1, t1, s6
	xor s5, t0, s5
	xor t2, t2, s4
	srli s2, s5, 32
	slli s5, s5, 32
	srli s4, t1, 48
	xor s2, s2, s5
	xor t2, t2, s1
	xor s2, s2, t6
	slli t1, t1, 16
	xor t2, t2, t3
	xor s4, s4, t1
	xor s2, s2, s3
	sd t2, 688(a5)
	xor t4, t4, s7
	ld s1, 640(a5)
	xor s4, s4, s0
	sd s2, 696(a5)
	srli s0, t4, 48
	slli t4, t4, 16
	ld s2, 648(a5)
	xor s0, s0, t4
	xor s4, s4, s1
	xor s0, s0, t0
	sd s4, 640(a5)
	xor s0, s0, s2
	sd s0, 648(a5)
	ld s0, 512(a5)
	ld t0, 576(a5)
	xor s0, s0, t0
	ld t0, 640(a5)
	xor s0, s0, t0
	ld t0, 192(a3)
	xor s0, s0, t0
	ld s1, 520(a5)
	ld t0, 584(a5)
	xor s1, s1, t0
	ld t0, 648(a5)
	xor s1, s1, t0
	ld t0, 200(a3)
	xor s1, s1, t0
	ld s2, 528(a5)
	ld t0, 592(a5)
	xor s2, s2, t0
	ld t0, 656(a5)
	xor s2, s2, t0
	ld t0, 208(a3)
	xor s2, s2, t0
	ld s3, 536(a5)
	ld t0, 600(a5)
	xor s3, s3, t0
	ld t0, 664(a5)
	xor s3, s3, t0
	ld t0, 216(a3)
	xor s3, s3, t0
	ld s4, 544(a5)
	ld t0, 608(a5)
	xor s4, s4, t0
	ld t0, 672(a5)
	xor s4, s4, t0
	ld t0, 224(a3)
	xor s4, s4, t0
	ld s5, 552(a5)
	ld t0, 616(a5)
	xor s5, s5, t0
	ld t0, 680(a5)
	xor s5, s5, t0
	ld t0, 232(a3)
	xor s5, s5, t0
	ld s6, 560(a5)
	ld t0, 624(a5)
	xor s6, s6, t0
	ld t0, 688(a5)
	xor s6, s6, t0
	ld t0, 240(a3)
	xor s6, s6, t0
	ld s7, 568(a5)
	ld t0, 632(a5)
	xor s7, s7, t0
	ld t0, 696(a5)
	xor s7, s7, t0
	ld t0, 248(a3)
	xor s7, s7, t0
	xori s2, s2, -1
	xori s6, s6, -1
	xor t0, s2, s6
	xori s5, s5, -1
	xor s3, s3, s5
	xor t1, s0, s3
	xori t1, t1, -1
	xor s7, s7, t0
	xor t2, s7, s3
	xor t3, s6, s3
	xor t4, s6, t2
	xor s0, s0, s4
	xor s0, s6, s0
	xor s5, s5, s0
	xor s4, s5, t4
	and t5, s4, t4
	xor t6, s1, t0
	xor a6, s1, t1
	and a7, a6, t3
	xor t5, t5, a7
	xor s8, t0, s4
	xor s9, t6, s0
	xor s3, s9, s3
	and s10, t6, s9
	xor s11, s7, s9
	sd t0, 0(a5)
	and t0, t0, s6
	xor s10, s10, t0
	xor t5, t5, s10
	sd s6, 8(a5)
	xor s6, s6, s9
	sd s1, 16(a5)
	and s1, s1, s6
	xor s1, s1, t0
	xor t5, t5, s5
	xor s5, t1, s8
	and t0, s8, t2
	sd s6, 24(a5)
	and s6, t1, s3
	xor t0, t0, s6
	xor t0, t0, s10
	xor s10, t6, s5
	xor t0, t0, s0
	and s0, s10, s7
	xor s0, s0, a7
	and a7, s5, s11
	xor a7, a7, s6
	xor a7, a7, s1
	xor s0, s0, s1
	xor a7, a7, s2
	xor s1, a6, t3
	xor s0, s0, s1
	and s1, a7, s0
	xor a7, a7, t0
	xor s2, t0, s1
	xor s6, s0, t5
	and s2, s2, s6
	xor s2, s2, t5
	xor s0, s0, s2
	xor s1, t5, s1
	xor s6, s1, s2
	and t2, s2, t2
	and t5, t5, s6
	xor s0, t5, s0
	xor t5, s1, t5
	and s8, s2, s8
	and s1, a7, s1
	xor s1, s1, t0
	and s4, s1, s4
	and t5, s1, t5
	xor a7, a7, t5
	xor s6, s1, a7
	xor t0, a7, s0
	and s11, s0, s11
	xor t5, s2, s0
	and s7, a7, s7
	and t6, t0, t6
	and s9, t0, s9
	and t3, s6, t3
	and t1, t5, t1
	and s0, s0, s5
	and t5, t5, s3
	and s6, s6, a6
	and t4, s1, t4
	xor s1, s1, s2
	xor s6, s6, s4
	ld s2, 8(a5)
	and s2, s1, s2
	xor t5, t5, t2
	xor s2, s2, s9
	and a7, a7, s10
	xor t0, s1, t0
	ld s3, 24(a5)
	and s3, t0, s3
	xor s11, s11, t2
	xor t3, t3, t5
	xori s3, s3, -1
	ld s5, 16(a5)
	and t0, t0, s5
	xor a7, a7, s4
	xor s3, s3, s9
	xor s11, s11, s3
	xor s7, s7, t3
	xor s7, s7, s3
	xor s2, s2, t5
	xor a7, a7, s7
	xor t4, t4, t3
	xor t1, t1, s6
	xor t0, t0, a7
	xor t0, t0, t6
	ld s3, 0(a5)
	and s1, s1, s3
	xor s0, s0, a7
	xor s2, s2, s0
	xor s1, s1, s6
	xor s3, s1, t6
	xor s4, s8, s0
	xor s0, s2, t1
	xor s1, s7, s3
	xor s2, t0, s0
	xor s5, s11, s4
	xor s8, s8, t1
	xori s7, s8, -1
	xor s6, t4, t0
	srli t0, s2, 16
	slli t1, s2, 48
	ld t2, 720(a5)
	xor t0, t0, t1
	srli t1, s0, 16
	slli t3, s0, 48
	srli t4, s1, 16
	slli t5, s1, 48
	xor t0, s2, t0
	xor t1, t1, t3
	xor t4, t4, t5
	srli t3, s3, 16
	srli t5, t0, 16
	slli t6, t0, 48
	xor t1, s0, t1
	slli a6, s3, 48
	xor t4, s1, t4
	xor t3, t3, a6
	xor t5, t5, t6
	xor t3, s3, t3
	xor t5, t5, s0
	ld s0, 728(a5)
	srli t6, t3, 16
	slli a6, t3, 48
	xor t6, t6, a6
	srli a6, t5, 32
	xor t6, t6, s1
	slli t5, t5, 32
	srli s1, s4, 16
	xor a6, a6, t5
	slli t5, s4, 48
	xor a6, a6, t1
	xor s1, s1, t5
	srli t5, t6, 32
	xor s1, s4, s1
	slli t6, t6, 32
	xor t5, t5, t6
	xor a6, a6, t2
	srli t2, s1, 16
	xor t5, t5, t4
	sd a6, 720(a5)
	srli t6, s5, 16
	slli a6, s5, 48
	xor t6, t6, a6
	slli a6, s1, 48
	xor t6, s5, t6
	xor t2, t2, a6
	ld a6, 736(a5)
	xor t2, t2, s2
	xor t5, t5, s0
	srli s0, t6, 16
	srli s2, t2, 32
	sd t5, 728(a5)
	slli t5, t6, 48
	slli t2, t2, 32
	xor s0, s0, t5
	ld t5, 744(a5)
	xor s2, s2, t2
	srli t2, s6, 16
	xor s0, s0, s3
	slli s3, s6, 48
	xor s2, s2, t0
	xor t2, t2, s3
	srli s3, s0, 32
	xor t2, s6, t2
	slli s0, s0, 32
	xor s3, s3, s0
	xor s2, s2, a6
	srli s0, t2, 16
	xor s3, s3, t3
	sd s2, 736(a5)
	srli s2, s7, 16
	slli t0, s7, 48
	ld t3, 752(a5)
	xor s2, s2, t0
	slli t2, t2, 48
	xor s2, s7, s2
	xor s0, s0, t2
	xor s4, s0, s4
	xor s3, s3, t5
	srli t0, s2, 16
	srli t2, s4, 32
	sd s3, 744(a5)
	slli s2, s2, 48
	slli s4, s4, 32
	ld s3, 760(a5)
	xor t0, t0, s2
	xor t1, t1, s6
	xor s5, t0, s5
	xor t2, t2, s4
	srli s2, s5, 32
	slli s5, s5, 32
	srli s4, t1, 48
	xor s2, s2, s5
	xor t2, t2, s1
	xor s2, s2, t6
	slli t1, t1, 16
	xor t2, t2, t3
	xor s4, s4, t1
	xor s2, s2, s3
	sd t2, 752(a5)
	xor t4, t4, s7
	ld s1, 704(a5)
	xor s4, s4, s0
	sd s2, 760(a5)
	srli s0, t4, 48
	slli t4, t4, 16
	ld s2, 712(a5)
	xor s0, s0, t4
	xor s4, s4, s1
	xor s0, s0, t0
	sd s4, 704(a5)
	xor s0, s0, s2
	sd s0, 712(a5)
	addi a3, a3, 256
	sub t0, a3, a0
	bnez t0, 214b
	ld t3, 360(a5)
	ld t4, 368(a5)
	ld t5, 376(a5)
	ld t6, 384(a5)
	ld a6, 392(a5)
	ld s8, 400(a5)
	ld s0, 704(a5)
	ld s1, 712(a5)
	ld s2, 720(a5)
	ld s3, 728(a5)
	ld s4, 736(a5)
	ld s5, 744(a5)
	ld s6, 752(a5)
	ld s7, 760(a5)
	srli t0, s0, 4
	xor t0, t0, s4
	and t0, t0, s8
	xor s4, s4, t0
	slli t0, t0, 4
	xor s0, s0, t0
	srli t0, s1, 4
	xor t0, t0, s5
	and t0, t0, s8
	xor s5, s5, t0
	slli t0, t0, 4
	xor s1, s1, t0
	srli t0, s2, 4
	xor t0, t0, s6
	and t0, t0, s8
	xor s6, s6, t0
	slli t0, t0, 4
	xor s2, s2, t0
	srli t0, s3, 4
	xor t0, t0, s7
	and t0, t0, s8
	xor s7, s7, t0
	slli t0, t0, 4
	xor s3, s3, t0
	srli t0, s0, 2
	xor t0, t0, s2
	and t0, t0, a6
	xor s2, s2, t0
	slli t0, t0, 2
	xor s0, s0, t0
	srli t0, s1, 2
	xor t0, t0, s3
	and t0, t0, a6
	xor s3, s3, t0
	slli t0, t0, 2
	xor s1, s1, t0
	srli t0, s4, 2
	xor t0, t0, s6
	and t0, t0, a6
	xor s6, s6, t0
	slli t0, t0, 2
	xor s4, s4, t0
	srli t0, s5, 2
	xor t0, t0, s7
	and t0, t0, a6
	xor s7, s7, t0
	slli t0, t0, 2
	xor s5, s5, t0
	srli t0, s0, 1
	xor t0, t0, s1
	and t0, t0, t6
	xor s1, s1, t0
	slli t0, t0, 1
	xor s0, s0, t0
	srli t0, s2, 1
	xor t0, t0, s3
	and t0, t0, t6
	xor s3, s3, t0
	slli t0, t0, 1
	xor s2, s2, t0
	srli t0, s4, 1
	xor t0, t0, s5
	and t0, t0, t6
	xor s5, s5, t0
	slli t0, t0, 1
	xor s4, s4, t0
	srli t0, s6, 1
	xor t0, t0, s7
	and t0, t0, t6
	xor s7, s7, t0
	slli t0, t0, 1
	xor s6, s6, t0
	sd s0, 768(a5)
	sd s1, 784(a5)
	sd s2, 800(a5)
	sd s3, 816(a5)
	sd s4, 832(a5)
	sd s5, 848(a5)
	sd s6, 864(a5)
	sd s7, 880(a5)
	ld s0, 640(a5)
	ld s1, 648(a5)
	ld s2, 656(a5)
	ld s3, 664(a5)
	ld s4, 672(a5)
	ld s5, 680(a5)
	ld s6, 688(a5)
	ld s7, 696(a5)
	srli t0, s0, 4
	xor t0, t0, s4
	and t0, t0, s8
	xor s4, s4, t0
	slli t0, t0, 4
	xor s0, s0, t0
	srli t0, s1, 4
	xor t0, t0, s5
	and t0, t0, s8
	xor s5, s5, t0
	slli t0, t0, 4
	xor s1, s1, t0
	srli t0, s2, 4
	xor t0, t0, s6
	and t0, t0, s8
	xor s6, s6, t0
	slli t0, t0, 4
	xor s2, s2, t0
	srli t0, s3, 4
	xor t0, t0, s7
	and t0, t0, s8
	xor s7, s7, t0
	slli t0, t0, 4
	xor s3, s3, t0
	srli t0, s0, 2
	xor t0, t0, s2
	and t0, t0, a6
	xor s2, s2, t0
	slli t0, t0, 2
	xor s0, s0, t0
	srli t0, s1, 2
	xor t0, t0, s3
	and t0, t0, a6
	xor s3, s3, t0
	slli t0, t0, 2
	xor s1, s1, t0
	srli t0, s4, 2
	xor t0, t0, s6
	and t0, t0, a6
	xor s6, s6, t0
	slli t0, t0, 2
	xor s4, s4, t0
	srli t0, s5, 2
	xor t0, t0, s7
	and t0, t0, a6
	xor s7, s7, t0
	slli t0, t0, 2
	xor s5, s5, t0
	srli t0, s0, 1
	xor t0, t0, s1
	and t0, t0, t6
	xor s1, s1, t0
	slli t0, t0, 1
	xor s0, s0, t0
	srli t0, s2, 1
	xor t0, t0, s3
	and t0, t0, t6
	xor s3, s3, t0
	slli t0, t0, 1
	xor s2, s2, t0
	srli t0, s4, 1
	xor t0, t0, s5
	and t0, t0, t6
	xor s5, s5, t0
	slli t0, t0, 1
	xor s4, s4, t0
	srli t0, s6, 1
	xor t0, t0, s7
	and t0, t0, t6
	xor s7, s7, t0
	slli t0, t0, 1
	xor s6, s6, t0
	sd s0, 896(a5)
	sd s1, 912(a5)
	sd s2, 928(a5)
	sd s3, 944(a5)
	sd s4, 960(a5)
	sd s5, 976(a5)
	sd s6, 992(a5)
	sd s7, 1008(a5)
	ld s0, 576(a5)
	ld s1, 584(a5)
	ld s2, 592(a5)
	ld s3, 600(a5)
	ld s4, 608(a5)
	ld s5, 616(a5)
	ld s6, 624(a5)
	ld s7, 632(a5)
	srli t0, s0, 4
	xor t0, t0, s4
	and t0, t0, s8
	xor s4, s4, t0
	slli t0, t0, 4
	xor s0, s0, t0
	srli t0, s1, 4
	xor t0, t0, s5
	and t0, t0, s8
	xor s5, s5, t0
	slli t0, t0, 4
	xor s1, s1, t0
	srli t0, s2, 4
	xor t0, t0, s6
	and t0, t0, s8
	xor s6, s6, t0
	slli t0, t0, 4
	xor s2, s2, t0
	srli t0, s3, 4
	xor t0, t0, s7
	and t0, t0, s8
	xor s7, s7, t0
	slli t0, t0, 4
	xor s3, s3, t0
	srli t0, s0, 2
	xor t0, t0, s2
	and t0, t0, a6
	xor s2, s2, t0
	slli t0, t0, 2
	xor s0, s0, t0
	srli t0, s1, 2
	xor t0, t0, s3
	and t0, t0, a6
	xor s3, s3, t0
	slli t0, t0, 2
	xor s1, s1, t0
	srli t0, s4, 2
	xor t0, t0, s6
	and t0, t0, a6
	xor s6, s6, t0
	slli t0, t0, 2
	xor s4, s4, t0
	srli t0, s5, 2
	xor t0, t0, s7
	and t0, t0, a6
	xor s7, s7, t0
	slli t0, t0, 2
	xor s5, s5, t0
	srli t0, s0, 1
	xor t0, t0, s1
	and t0, t0, t6
	xor s1, s1, t0
	slli t0, t0, 1
	xor s0, s0, t0
	srli t0, s2, 1
	xor t0, t0, s3
	and t0, t0, t6
	xor s3, s3, t0
	slli t0, t0, 1
	xor s2, s2, t0
	srli t0, s4, 1
	xor t0, t0, s5
	and t0, t0, t6
	xor s5, s5, t0
	slli t0, t0, 1
	xor s4, s4, t0
	srli t0, s6, 1
	xor t0, t0, s7
	and t0, t0, t6
	xor s7, s7, t0
	slli t0, t0, 1
	xor s6, s6, t0
	sd s0, 776(a5)
	sd s1, 792(a5)
	sd s2, 808(a5)
	sd s3, 824(a5)
	sd s4, 840(a5)
	sd s5, 856(a5)
	sd s6, 872(a5)
	sd s7, 888(a5)
	ld s0, 512(a5)
	ld s1, 520(a5)
	ld s2, 528(a5)
	ld s3, 536(a5)
	ld s4, 544(a5)
	ld s5, 552(a5)
	ld s6, 560(a5)
	ld s7, 568(a5)
	srli t0, s0, 4
	xor t0, t0, s4
	and t0, t0, s8
	xor s4, s4, t0
	slli t0, t0, 4
	xor s0, s0, t0
	srli t0, s1, 4
	xor t0, t0, s5
	and t0, t0, s8
	xor s5, s5, t0
	slli t0, t0, 4
	xor s1, s1, t0
	srli t0, s2, 4
	xor t0, t0, s6
	and t0, t0, s8
	xor s6, s6, t0
	slli t0, t0, 4
	xor s2, s2, t0
	srli t0, s3, 4
	xor t0, t0, s7
	and t0, t0, s8
	xor s7, s7, t0
	slli t0, t0, 4
	xor s3, s3, t0
	srli t0, s0, 2
	xor t0, t0, s2
	and t0, t0, a6
	xor s2, s2, t0
	slli t0, t0, 2
	xor s0, s0, t0
	srli t0, s1, 2
	xor t0, t0, s3
	and t0, t0, a6
	xor s3, s3, t0
	slli t0, t0, 2
	xor s1, s1, t0
	srli t0, s4, 2
	xor t0, t0, s6
	and t0, t0, a6
	xor s6, s6, t0
	slli t0, t0, 2
	xor s4, s4, t0
	srli t0, s5, 2
	xor t0, t0, s7
	and t0, t0, a6
	xor s7, s7, t0
	slli t0, t0, 2
	xor s5, s5, t0
	srli t0, s0, 1
	xor t0, t0, s1
	and t0, t0, t6
	xor s1, s1, t0
	slli t0, t0, 1
	xor s0, s0, t0
	srli t0, s2, 1
	xor t0, t0, s3
	and t0, t0, t6
	xor s3, s3, t0
	slli t0, t0, 1
	xor s2, s2, t0
	srli t0, s4, 1
	xor t0, t0, s5
	and t0, t0, t6
	xor s5, s5, t0
	slli t0, t0, 1
	xor s4, s4, t0
	srli t0, s6, 1
	xor t0, t0, s7
	and t0, t0, t6
	xor s7, s7, t0
	slli t0, t0, 1
	xor s6, s6, t0
	sd s0, 904(a5)
	sd s1, 920(a5)
	sd s2, 936(a5)
	sd s3, 952(a5)
	sd s4, 968(a5)
	sd s5, 984(a5)
	sd s6, 1000(a5)
	sd s7, 1016(a5)
	ld s0, 768(a5)
	ld s4, 896(a5)
	ld s1, 784(a5)
	ld s5, 912(a5)
	ld s2, 800(a5)
	ld s6, 928(a5)
	ld s3, 816(a5)
	ld s7, 944(a5)
	srli t0, s0, 32
	xor t0, t0, s4
	and t0, t0, t3
	xor s4, s4, t0
	slli t0, t0, 32
	xor s0, s0, t0
	srli t0, s1, 32
	xor t0, t0, s5
	and t0, t0, t3
	xor s5, s5, t0
	slli t0, t0, 32
	xor s1, s1, t0
	srli t0, s2, 32
	xor t0, t0, s6
	and t0, t0, t3
	xor s6, s6, t0
	slli t0, t0, 32
	xor s2, s2, t0
	srli t0, s3, 32
	xor t0, t0, s7
	and t0, t0, t3
	xor s7, s7, t0
	slli t0, t0, 32
	xor s3, s3, t0
	srli t0, s0, 16
	xor t0, t0, s4
	and t0, t0, t4
	xor s4, s4, t0
	slli t0, t0, 16
	xor s0, s0, t0
	srli t0, s1, 16
	xor t0, t0, s5
	and t0, t0, t4
	xor s5, s5, t0
	slli t0, t0, 16
	xor s1, s1, t0
	srli t0, s2, 16
	xor t0, t0, s6
	and t0, t0, t4
	xor s6, s6, t0
	slli t0, t0, 16
	xor s2, s2, t0
	srli t0, s3, 16
	xor t0, t0, s7
	and t0, t0, t4
	xor s7, s7, t0
	slli t0, t0, 16
	xor s3, s3, t0
	srli t0, s0, 8
	xor t0, t0, s4
	and t0, t0, t5
	xor s4, s4, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s5
	and t0, t0, t5
	xor s5, s5, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s6
	and t0, t0, t5
	xor s6, s6, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s7
	and t0, t0, t5
	xor s7, s7, t0
	slli t0, t0, 8
	xor s3, s3, t0
	sd s0, 768(a5)
	sd s4, 896(a5)
	sd s1, 784(a5)
	sd s5, 912(a5)
	sd s2, 800(a5)
	sd s6, 928(a5)
	sd s3, 816(a5)
	sd s7, 944(a5)
	ld s0, 832(a5)
	ld s4, 960(a5)
	ld s1, 848(a5)
	ld s5, 976(a5)
	ld s2, 864(a5)
	ld s6, 992(a5)
	ld s3, 880(a5)
	ld s7, 1008(a5)
	srli t0, s0, 32
	xor t0, t0, s4
	and t0, t0, t3
	xor s4, s4, t0
	slli t0, t0, 32
	xor s0, s0, t0
	srli t0, s1, 32
	xor t0, t0, s5
	and t0, t0, t3
	xor s5, s5, t0
	slli t0, t0, 32
	xor s1, s1, t0
	srli t0, s2, 32
	xor t0, t0, s6
	and t0, t0, t3
	xor s6, s6, t0
	slli t0, t0, 32
	xor s2, s2, t0
	srli t0, s3, 32
	xor t0, t0, s7
	and t0, t0, t3
	xor s7, s7, t0
	slli t0, t0, 32
	xor s3, s3, t0
	srli t0, s0, 16
	xor t0, t0, s4
	and t0, t0, t4
	xor s4, s4, t0
	slli t0, t0, 16
	xor s0, s0, t0
	srli t0, s1, 16
	xor t0, t0, s5
	and t0, t0, t4
	xor s5, s5, t0
	slli t0, t0, 16
	xor s1, s1, t0
	srli t0, s2, 16
	xor t0, t0, s6
	and t0, t0, t4
	xor s6, s6, t0
	slli t0, t0, 16
	xor s2, s2, t0
	srli t0, s3, 16
	xor t0, t0, s7
	and t0, t0, t4
	xor s7, s7, t0
	slli t0, t0, 16
	xor s3, s3, t0
	srli t0, s0, 8
	xor t0, t0, s4
	and t0, t0, t5
	xor s4, s4, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s5
	and t0, t0, t5
	xor s5, s5, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s6
	and t0, t0, t5
	xor s6, s6, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s7
	and t0, t0, t5
	xor s7, s7, t0
	slli t0, t0, 8
	xor s3, s3, t0
	sd s0, 832(a5)
	sd s4, 960(a5)
	sd s1, 848(a5)
	sd s5, 976(a5)
	sd s2, 864(a5)
	sd s6, 992(a5)
	sd s3, 880(a5)
	sd s7, 1008(a5)
	ld s0, 776(a5)
	ld s4, 904(a5)
	ld s1, 792(a5)
	ld s5, 920(a5)
	ld s2, 808(a5)
	ld s6, 936(a5)
	ld s3, 824(a5)
	ld s7, 952(a5)
	srli t0, s0, 32
	xor t0, t0, s4
	and t0, t0, t3
	xor s4, s4, t0
	slli t0, t0, 32
	xor s0, s0, t0
	srli t0, s1, 32
	xor t0, t0, s5
	and t0, t0, t3
	xor s5, s5, t0
	slli t0, t0, 32
	xor s1, s1, t0
	srli t0, s2, 32
	xor t0, t0, s6
	and t0, t0, t3
	xor s6, s6, t0
	slli t0, t0, 32
	xor s2, s2, t0
	srli t0, s3, 32
	xor t0, t0, s7
	and t0, t0, t3
	xor s7, s7, t0
	slli t0, t0, 32
	xor s3, s3, t0
	srli t0, s0, 16
	xor t0, t0, s4
	and t0, t0, t4
	xor s4, s4, t0
	slli t0, t0, 16
	xor s0, s0, t0
	srli t0, s1, 16
	xor t0, t0, s5
	and t0, t0, t4
	xor s5, s5, t0
	slli t0, t0, 16
	xor s1, s1, t0
	srli t0, s2, 16
	xor t0, t0, s6
	and t0, t0, t4
	xor s6, s6, t0
	slli t0, t0, 16
	xor s2, s2, t0
	srli t0, s3, 16
	xor t0, t0, s7
	and t0, t0, t4
	xor s7, s7, t0
	slli t0, t0, 16
	xor s3, s3, t0
	srli t0, s0, 8
	xor t0, t0, s4
	and t0, t0, t5
	xor s4, s4, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s5
	and t0, t0, t5
	xor s5, s5, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s6
	and t0, t0, t5
	xor s6, s6, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s7
	and t0, t0, t5
	xor s7, s7, t0
	slli t0, t0, 8
	xor s3, s3, t0
	sd s0, 776(a5)
	sd s4, 904(a5)
	sd s1, 792(a5)
	sd s5, 920(a5)
	sd s2, 808(a5)
	sd s6, 936(a5)
	sd s3, 824(a5)
	sd s7, 952(a5)
	ld s0, 840(a5)
	ld s4, 968(a5)
	ld s1, 856(a5)
	ld s5, 984(a5)
	ld s2, 872(a5)
	ld s6, 1000(a5)
	ld s3, 888(a5)
	ld s7, 1016(a5)
	srli t0, s0, 32
	xor t0, t0, s4
	and t0, t0, t3
	xor s4, s4, t0
	slli t0, t0, 32
	xor s0, s0, t0
	srli t0, s1, 32
	xor t0, t0, s5
	and t0, t0, t3
	xor s5, s5, t0
	slli t0, t0, 32
	xor s1, s1, t0
	srli t0, s2, 32
	xor t0, t0, s6
	and t0, t0, t3
	xor s6, s6, t0
	slli t0, t0, 32
	xor s2, s2, t0
	srli t0, s3, 32
	xor t0, t0, s7
	and t0, t0, t3
	xor s7, s7, t0
	slli t0, t0, 32
	xor s3, s3, t0
	srli t0, s0, 16
	xor t0, t0, s4
	and t0, t0, t4
	xor s4, s4, t0
	slli t0, t0, 16
	xor s0, s0, t0
	srli t0, s1, 16
	xor t0, t0, s5
	and t0, t0, t4
	xor s5, s5, t0
	slli t0, t0, 16
	xor s1, s1, t0
	srli t0, s2, 16
	xor t0, t0, s6
	and t0, t0, t4
	xor s6, s6, t0
	slli t0, t0, 16
	xor s2, s2, t0
	srli t0, s3, 16
	xor t0, t0, s7
	and t0, t0, t4
	xor s7, s7, t0
	slli t0, t0, 16
	xor s3, s3, t0
	srli t0, s0, 8
	xor t0, t0, s4
	and t0, t0, t5
	xor s4, s4, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s5
	and t0, t0, t5
	xor s5, s5, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s6
	and t0, t0, t5
	xor s6, s6, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s7
	and t0, t0, t5
	xor s7, s7, t0
	slli t0, t0, 8
	xor s3, s3, t0
	sd s0, 840(a5)
	sd s4, 968(a5)
	sd s1, 856(a5)
	sd s5, 984(a5)
	sd s2, 872(a5)
	sd s6, 1000(a5)
	sd s3, 888(a5)
	sd s7, 1016(a5)
	srli t0, a2, 4
	bnez t0, 215f
	addi a4, a2, 0
	j 216f
215:
	addi a4, zero, 16
216:
	addi t1, a5, 768
	addi t2, a1, 0
	slli t3, a4, 4
	or t4, t1, t2
	andi t4, t4, 7
	beqz t4, 217f
219:
	lbu t4, 0(t1)
	sb t4, 0(t2)
	addi t1, t1, 1
	addi t2, t2, 1
	addi t3, t3, -1
	bnez t3, 219b
	j 218f
217:
	srli t3, t3, 3
220:
	ld t4, 0(t1)
	sd t4, 0(t2)
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 220b
218:
	sub a2, a2, a4
	addi a1, a1, 256
	bnez a2, 27b
	j 26f
25:
26:
	addi t0, a5, 2040
	addi t0, t0, 1032
	ld s0, 0(t0)
	ld s1, 8(t0)
	ld s2, 16(t0)
	ld s3, 24(t0)
	ld s4, 32(t0)
	ld s5, 40(t0)
	ld s6, 48(t0)
	ld s7, 56(t0)
	ld s8, 64(t0)
	ld s9, 72(t0)
	ld s10, 80(t0)
	ld s11, 88(t0)
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
	addi t5, t5, 1024
	addi t5, t5, 1024
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
	addi sp, sp, 1136
	addi sp, sp, 2032
	addi t0, zero, 0
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
	addi a0, zero, 0
	ret
	.option pop

vg_sm4_ecb_decrypt:
	.option push
	.option arch, +m, +c
	addi sp, sp, -2032
	addi sp, sp, -1136
	addi a3, sp, 0
	addi a5, a3, 0
	addi t0, a5, 2040
	addi t0, t0, 1032
	sd s0, 0(t0)
	sd s1, 8(t0)
	sd s2, 16(t0)
	sd s3, 24(t0)
	sd s4, 32(t0)
	sd s5, 40(t0)
	sd s6, 48(t0)
	sd s7, 56(t0)
	sd s8, 64(t0)
	sd s9, 72(t0)
	sd s10, 80(t0)
	sd s11, 88(t0)
	lui t0, 0
	addiw t0, t0, 255
	slli t0, t0, 32
	lui t1, 4080
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 320(a5)
	lui t0, 16
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, 1
	add t0, t0, t1
	sd t0, 328(a5)
	lui t0, 0
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 360(a5)
	lui t0, 16
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 368(a5)
	lui t0, 4080
	addiw t0, t0, 255
	slli t0, t0, 32
	lui t1, 4080
	addiw t1, t1, 255
	add t0, t0, t1
	sd t0, 376(a5)
	lui t0, 349525
	addiw t0, t0, 1365
	slli t0, t0, 32
	lui t1, 349525
	addiw t1, t1, 1365
	add t0, t0, t1
	sd t0, 384(a5)
	lui t0, 209715
	addiw t0, t0, 819
	slli t0, t0, 32
	lui t1, 209715
	addiw t1, t1, 819
	add t0, t0, t1
	sd t0, 392(a5)
	lui t0, 61681
	addiw t0, t0, -241
	slli t0, t0, 32
	lui t1, 61681
	addiw t1, t1, -241
	add t0, t0, t1
	sd t0, 400(a5)
	addi t1, a0, 0
	addi t2, a5, 768
	addi t3, zero, 128
	or t4, t1, t2
	andi t4, t4, 7
	beqz t4, 20f
22:
	lbu t4, 0(t1)
	sb t4, 0(t2)
	addi t1, t1, 1
	addi t2, t2, 1
	addi t3, t3, -1
	bnez t3, 22b
	j 21f
20:
	srli t3, t3, 3
23:
	ld t4, 0(t1)
	sd t4, 0(t2)
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 23b
21:
	addi a0, a5, 768
	addi a3, a5, 2040
	addi a3, a3, 968
	addi s8, zero, 16
24:
	ld t1, 0(a0)
	ld t2, 360(a5)
	and t1, t1, t2
	ld t2, 320(a5)
	slli t0, t1, 24
	slli t3, t1, 48
	xor t0, t0, t1
	srli t4, t1, 24
	and t0, t0, t2
	xor t3, t3, t4
	xor t1, t0, t3
	ld t6, 328(a5)
	and s0, t1, t6
	srli s1, t1, 1
	and s1, s1, t6
	srli s2, t1, 2
	and s2, s2, t6
	srli s3, t1, 3
	and s3, s3, t6
	srli s4, t1, 4
	and s4, s4, t6
	srli s5, t1, 5
	and s5, s5, t6
	srli s6, t1, 6
	and s6, s6, t6
	srli s7, t1, 7
	and s7, s7, t6
	lui t0, 16
	addiw t0, t0, -1
	mul s0, s0, t0
	mul s1, s1, t0
	mul s2, s2, t0
	mul s3, s3, t0
	mul s4, s4, t0
	mul s5, s5, t0
	mul s6, s6, t0
	mul s7, s7, t0
	sd s0, 0(a3)
	sd s1, 8(a3)
	sd s2, 16(a3)
	sd s3, 24(a3)
	sd s4, 32(a3)
	sd s5, 40(a3)
	sd s6, 48(a3)
	sd s7, 56(a3)
	addi a3, a3, -64
	ld t1, 0(a0)
	srli t1, t1, 32
	ld t2, 320(a5)
	slli t0, t1, 24
	slli t3, t1, 48
	xor t0, t0, t1
	srli t4, t1, 24
	and t0, t0, t2
	xor t3, t3, t4
	xor t1, t0, t3
	ld t6, 328(a5)
	and s0, t1, t6
	srli s1, t1, 1
	and s1, s1, t6
	srli s2, t1, 2
	and s2, s2, t6
	srli s3, t1, 3
	and s3, s3, t6
	srli s4, t1, 4
	and s4, s4, t6
	srli s5, t1, 5
	and s5, s5, t6
	srli s6, t1, 6
	and s6, s6, t6
	srli s7, t1, 7
	and s7, s7, t6
	lui t0, 16
	addiw t0, t0, -1
	mul s0, s0, t0
	mul s1, s1, t0
	mul s2, s2, t0
	mul s3, s3, t0
	mul s4, s4, t0
	mul s5, s5, t0
	mul s6, s6, t0
	mul s7, s7, t0
	sd s0, 0(a3)
	sd s1, 8(a3)
	sd s2, 16(a3)
	sd s3, 24(a3)
	sd s4, 32(a3)
	sd s5, 40(a3)
	sd s6, 48(a3)
	sd s7, 56(a3)
	addi a3, a3, -64
	addi a0, a0, 8
	addi s8, s8, -1
	bnez s8, 24b
	addi a0, a5, 2040
	addi a0, a0, 1032
	beqz a2, 25f
27:
	srli t0, a2, 4
	bnez t0, 28f
	addi a4, a2, 0
	j 29f
28:
	addi a4, zero, 16
29:
	addi t1, a1, 0
	addi t2, a5, 768
	slli t3, a4, 4
	or t4, t1, t2
	andi t4, t4, 7
	beqz t4, 210f
212:
	lbu t4, 0(t1)
	sb t4, 0(t2)
	addi t1, t1, 1
	addi t2, t2, 1
	addi t3, t3, -1
	bnez t3, 212b
	j 211f
210:
	srli t3, t3, 3
213:
	ld t4, 0(t1)
	sd t4, 0(t2)
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 213b
211:
	ld t3, 360(a5)
	ld t4, 368(a5)
	ld t5, 376(a5)
	ld t6, 384(a5)
	ld a6, 392(a5)
	ld s8, 400(a5)
	ld s0, 768(a5)
	ld s4, 896(a5)
	ld s1, 784(a5)
	ld s5, 912(a5)
	ld s2, 800(a5)
	ld s6, 928(a5)
	ld s3, 816(a5)
	ld s7, 944(a5)
	srli t0, s0, 8
	xor t0, t0, s4
	and t0, t0, t5
	xor s4, s4, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s5
	and t0, t0, t5
	xor s5, s5, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s6
	and t0, t0, t5
	xor s6, s6, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s7
	and t0, t0, t5
	xor s7, s7, t0
	slli t0, t0, 8
	xor s3, s3, t0
	srli t0, s0, 16
	xor t0, t0, s4
	and t0, t0, t4
	xor s4, s4, t0
	slli t0, t0, 16
	xor s0, s0, t0
	srli t0, s1, 16
	xor t0, t0, s5
	and t0, t0, t4
	xor s5, s5, t0
	slli t0, t0, 16
	xor s1, s1, t0
	srli t0, s2, 16
	xor t0, t0, s6
	and t0, t0, t4
	xor s6, s6, t0
	slli t0, t0, 16
	xor s2, s2, t0
	srli t0, s3, 16
	xor t0, t0, s7
	and t0, t0, t4
	xor s7, s7, t0
	slli t0, t0, 16
	xor s3, s3, t0
	srli t0, s0, 32
	xor t0, t0, s4
	and t0, t0, t3
	xor s4, s4, t0
	slli t0, t0, 32
	xor s0, s0, t0
	srli t0, s1, 32
	xor t0, t0, s5
	and t0, t0, t3
	xor s5, s5, t0
	slli t0, t0, 32
	xor s1, s1, t0
	srli t0, s2, 32
	xor t0, t0, s6
	and t0, t0, t3
	xor s6, s6, t0
	slli t0, t0, 32
	xor s2, s2, t0
	srli t0, s3, 32
	xor t0, t0, s7
	and t0, t0, t3
	xor s7, s7, t0
	slli t0, t0, 32
	xor s3, s3, t0
	sd s0, 768(a5)
	sd s4, 896(a5)
	sd s1, 784(a5)
	sd s5, 912(a5)
	sd s2, 800(a5)
	sd s6, 928(a5)
	sd s3, 816(a5)
	sd s7, 944(a5)
	ld s0, 832(a5)
	ld s4, 960(a5)
	ld s1, 848(a5)
	ld s5, 976(a5)
	ld s2, 864(a5)
	ld s6, 992(a5)
	ld s3, 880(a5)
	ld s7, 1008(a5)
	srli t0, s0, 8
	xor t0, t0, s4
	and t0, t0, t5
	xor s4, s4, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s5
	and t0, t0, t5
	xor s5, s5, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s6
	and t0, t0, t5
	xor s6, s6, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s7
	and t0, t0, t5
	xor s7, s7, t0
	slli t0, t0, 8
	xor s3, s3, t0
	srli t0, s0, 16
	xor t0, t0, s4
	and t0, t0, t4
	xor s4, s4, t0
	slli t0, t0, 16
	xor s0, s0, t0
	srli t0, s1, 16
	xor t0, t0, s5
	and t0, t0, t4
	xor s5, s5, t0
	slli t0, t0, 16
	xor s1, s1, t0
	srli t0, s2, 16
	xor t0, t0, s6
	and t0, t0, t4
	xor s6, s6, t0
	slli t0, t0, 16
	xor s2, s2, t0
	srli t0, s3, 16
	xor t0, t0, s7
	and t0, t0, t4
	xor s7, s7, t0
	slli t0, t0, 16
	xor s3, s3, t0
	srli t0, s0, 32
	xor t0, t0, s4
	and t0, t0, t3
	xor s4, s4, t0
	slli t0, t0, 32
	xor s0, s0, t0
	srli t0, s1, 32
	xor t0, t0, s5
	and t0, t0, t3
	xor s5, s5, t0
	slli t0, t0, 32
	xor s1, s1, t0
	srli t0, s2, 32
	xor t0, t0, s6
	and t0, t0, t3
	xor s6, s6, t0
	slli t0, t0, 32
	xor s2, s2, t0
	srli t0, s3, 32
	xor t0, t0, s7
	and t0, t0, t3
	xor s7, s7, t0
	slli t0, t0, 32
	xor s3, s3, t0
	sd s0, 832(a5)
	sd s4, 960(a5)
	sd s1, 848(a5)
	sd s5, 976(a5)
	sd s2, 864(a5)
	sd s6, 992(a5)
	sd s3, 880(a5)
	sd s7, 1008(a5)
	ld s0, 776(a5)
	ld s4, 904(a5)
	ld s1, 792(a5)
	ld s5, 920(a5)
	ld s2, 808(a5)
	ld s6, 936(a5)
	ld s3, 824(a5)
	ld s7, 952(a5)
	srli t0, s0, 8
	xor t0, t0, s4
	and t0, t0, t5
	xor s4, s4, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s5
	and t0, t0, t5
	xor s5, s5, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s6
	and t0, t0, t5
	xor s6, s6, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s7
	and t0, t0, t5
	xor s7, s7, t0
	slli t0, t0, 8
	xor s3, s3, t0
	srli t0, s0, 16
	xor t0, t0, s4
	and t0, t0, t4
	xor s4, s4, t0
	slli t0, t0, 16
	xor s0, s0, t0
	srli t0, s1, 16
	xor t0, t0, s5
	and t0, t0, t4
	xor s5, s5, t0
	slli t0, t0, 16
	xor s1, s1, t0
	srli t0, s2, 16
	xor t0, t0, s6
	and t0, t0, t4
	xor s6, s6, t0
	slli t0, t0, 16
	xor s2, s2, t0
	srli t0, s3, 16
	xor t0, t0, s7
	and t0, t0, t4
	xor s7, s7, t0
	slli t0, t0, 16
	xor s3, s3, t0
	srli t0, s0, 32
	xor t0, t0, s4
	and t0, t0, t3
	xor s4, s4, t0
	slli t0, t0, 32
	xor s0, s0, t0
	srli t0, s1, 32
	xor t0, t0, s5
	and t0, t0, t3
	xor s5, s5, t0
	slli t0, t0, 32
	xor s1, s1, t0
	srli t0, s2, 32
	xor t0, t0, s6
	and t0, t0, t3
	xor s6, s6, t0
	slli t0, t0, 32
	xor s2, s2, t0
	srli t0, s3, 32
	xor t0, t0, s7
	and t0, t0, t3
	xor s7, s7, t0
	slli t0, t0, 32
	xor s3, s3, t0
	sd s0, 776(a5)
	sd s4, 904(a5)
	sd s1, 792(a5)
	sd s5, 920(a5)
	sd s2, 808(a5)
	sd s6, 936(a5)
	sd s3, 824(a5)
	sd s7, 952(a5)
	ld s0, 840(a5)
	ld s4, 968(a5)
	ld s1, 856(a5)
	ld s5, 984(a5)
	ld s2, 872(a5)
	ld s6, 1000(a5)
	ld s3, 888(a5)
	ld s7, 1016(a5)
	srli t0, s0, 8
	xor t0, t0, s4
	and t0, t0, t5
	xor s4, s4, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s5
	and t0, t0, t5
	xor s5, s5, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s6
	and t0, t0, t5
	xor s6, s6, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s7
	and t0, t0, t5
	xor s7, s7, t0
	slli t0, t0, 8
	xor s3, s3, t0
	srli t0, s0, 16
	xor t0, t0, s4
	and t0, t0, t4
	xor s4, s4, t0
	slli t0, t0, 16
	xor s0, s0, t0
	srli t0, s1, 16
	xor t0, t0, s5
	and t0, t0, t4
	xor s5, s5, t0
	slli t0, t0, 16
	xor s1, s1, t0
	srli t0, s2, 16
	xor t0, t0, s6
	and t0, t0, t4
	xor s6, s6, t0
	slli t0, t0, 16
	xor s2, s2, t0
	srli t0, s3, 16
	xor t0, t0, s7
	and t0, t0, t4
	xor s7, s7, t0
	slli t0, t0, 16
	xor s3, s3, t0
	srli t0, s0, 32
	xor t0, t0, s4
	and t0, t0, t3
	xor s4, s4, t0
	slli t0, t0, 32
	xor s0, s0, t0
	srli t0, s1, 32
	xor t0, t0, s5
	and t0, t0, t3
	xor s5, s5, t0
	slli t0, t0, 32
	xor s1, s1, t0
	srli t0, s2, 32
	xor t0, t0, s6
	and t0, t0, t3
	xor s6, s6, t0
	slli t0, t0, 32
	xor s2, s2, t0
	srli t0, s3, 32
	xor t0, t0, s7
	and t0, t0, t3
	xor s7, s7, t0
	slli t0, t0, 32
	xor s3, s3, t0
	sd s0, 840(a5)
	sd s4, 968(a5)
	sd s1, 856(a5)
	sd s5, 984(a5)
	sd s2, 872(a5)
	sd s6, 1000(a5)
	sd s3, 888(a5)
	sd s7, 1016(a5)
	ld s0, 768(a5)
	ld s1, 784(a5)
	ld s2, 800(a5)
	ld s3, 816(a5)
	ld s4, 832(a5)
	ld s5, 848(a5)
	ld s6, 864(a5)
	ld s7, 880(a5)
	srli t0, s0, 4
	xor t0, t0, s4
	and t0, t0, s8
	xor s4, s4, t0
	slli t0, t0, 4
	xor s0, s0, t0
	srli t0, s1, 4
	xor t0, t0, s5
	and t0, t0, s8
	xor s5, s5, t0
	slli t0, t0, 4
	xor s1, s1, t0
	srli t0, s2, 4
	xor t0, t0, s6
	and t0, t0, s8
	xor s6, s6, t0
	slli t0, t0, 4
	xor s2, s2, t0
	srli t0, s3, 4
	xor t0, t0, s7
	and t0, t0, s8
	xor s7, s7, t0
	slli t0, t0, 4
	xor s3, s3, t0
	srli t0, s0, 2
	xor t0, t0, s2
	and t0, t0, a6
	xor s2, s2, t0
	slli t0, t0, 2
	xor s0, s0, t0
	srli t0, s1, 2
	xor t0, t0, s3
	and t0, t0, a6
	xor s3, s3, t0
	slli t0, t0, 2
	xor s1, s1, t0
	srli t0, s4, 2
	xor t0, t0, s6
	and t0, t0, a6
	xor s6, s6, t0
	slli t0, t0, 2
	xor s4, s4, t0
	srli t0, s5, 2
	xor t0, t0, s7
	and t0, t0, a6
	xor s7, s7, t0
	slli t0, t0, 2
	xor s5, s5, t0
	srli t0, s0, 1
	xor t0, t0, s1
	and t0, t0, t6
	xor s1, s1, t0
	slli t0, t0, 1
	xor s0, s0, t0
	srli t0, s2, 1
	xor t0, t0, s3
	and t0, t0, t6
	xor s3, s3, t0
	slli t0, t0, 1
	xor s2, s2, t0
	srli t0, s4, 1
	xor t0, t0, s5
	and t0, t0, t6
	xor s5, s5, t0
	slli t0, t0, 1
	xor s4, s4, t0
	srli t0, s6, 1
	xor t0, t0, s7
	and t0, t0, t6
	xor s7, s7, t0
	slli t0, t0, 1
	xor s6, s6, t0
	sd s0, 512(a5)
	sd s1, 520(a5)
	sd s2, 528(a5)
	sd s3, 536(a5)
	sd s4, 544(a5)
	sd s5, 552(a5)
	sd s6, 560(a5)
	sd s7, 568(a5)
	ld s0, 896(a5)
	ld s1, 912(a5)
	ld s2, 928(a5)
	ld s3, 944(a5)
	ld s4, 960(a5)
	ld s5, 976(a5)
	ld s6, 992(a5)
	ld s7, 1008(a5)
	srli t0, s0, 4
	xor t0, t0, s4
	and t0, t0, s8
	xor s4, s4, t0
	slli t0, t0, 4
	xor s0, s0, t0
	srli t0, s1, 4
	xor t0, t0, s5
	and t0, t0, s8
	xor s5, s5, t0
	slli t0, t0, 4
	xor s1, s1, t0
	srli t0, s2, 4
	xor t0, t0, s6
	and t0, t0, s8
	xor s6, s6, t0
	slli t0, t0, 4
	xor s2, s2, t0
	srli t0, s3, 4
	xor t0, t0, s7
	and t0, t0, s8
	xor s7, s7, t0
	slli t0, t0, 4
	xor s3, s3, t0
	srli t0, s0, 2
	xor t0, t0, s2
	and t0, t0, a6
	xor s2, s2, t0
	slli t0, t0, 2
	xor s0, s0, t0
	srli t0, s1, 2
	xor t0, t0, s3
	and t0, t0, a6
	xor s3, s3, t0
	slli t0, t0, 2
	xor s1, s1, t0
	srli t0, s4, 2
	xor t0, t0, s6
	and t0, t0, a6
	xor s6, s6, t0
	slli t0, t0, 2
	xor s4, s4, t0
	srli t0, s5, 2
	xor t0, t0, s7
	and t0, t0, a6
	xor s7, s7, t0
	slli t0, t0, 2
	xor s5, s5, t0
	srli t0, s0, 1
	xor t0, t0, s1
	and t0, t0, t6
	xor s1, s1, t0
	slli t0, t0, 1
	xor s0, s0, t0
	srli t0, s2, 1
	xor t0, t0, s3
	and t0, t0, t6
	xor s3, s3, t0
	slli t0, t0, 1
	xor s2, s2, t0
	srli t0, s4, 1
	xor t0, t0, s5
	and t0, t0, t6
	xor s5, s5, t0
	slli t0, t0, 1
	xor s4, s4, t0
	srli t0, s6, 1
	xor t0, t0, s7
	and t0, t0, t6
	xor s7, s7, t0
	slli t0, t0, 1
	xor s6, s6, t0
	sd s0, 576(a5)
	sd s1, 584(a5)
	sd s2, 592(a5)
	sd s3, 600(a5)
	sd s4, 608(a5)
	sd s5, 616(a5)
	sd s6, 624(a5)
	sd s7, 632(a5)
	ld s0, 776(a5)
	ld s1, 792(a5)
	ld s2, 808(a5)
	ld s3, 824(a5)
	ld s4, 840(a5)
	ld s5, 856(a5)
	ld s6, 872(a5)
	ld s7, 888(a5)
	srli t0, s0, 4
	xor t0, t0, s4
	and t0, t0, s8
	xor s4, s4, t0
	slli t0, t0, 4
	xor s0, s0, t0
	srli t0, s1, 4
	xor t0, t0, s5
	and t0, t0, s8
	xor s5, s5, t0
	slli t0, t0, 4
	xor s1, s1, t0
	srli t0, s2, 4
	xor t0, t0, s6
	and t0, t0, s8
	xor s6, s6, t0
	slli t0, t0, 4
	xor s2, s2, t0
	srli t0, s3, 4
	xor t0, t0, s7
	and t0, t0, s8
	xor s7, s7, t0
	slli t0, t0, 4
	xor s3, s3, t0
	srli t0, s0, 2
	xor t0, t0, s2
	and t0, t0, a6
	xor s2, s2, t0
	slli t0, t0, 2
	xor s0, s0, t0
	srli t0, s1, 2
	xor t0, t0, s3
	and t0, t0, a6
	xor s3, s3, t0
	slli t0, t0, 2
	xor s1, s1, t0
	srli t0, s4, 2
	xor t0, t0, s6
	and t0, t0, a6
	xor s6, s6, t0
	slli t0, t0, 2
	xor s4, s4, t0
	srli t0, s5, 2
	xor t0, t0, s7
	and t0, t0, a6
	xor s7, s7, t0
	slli t0, t0, 2
	xor s5, s5, t0
	srli t0, s0, 1
	xor t0, t0, s1
	and t0, t0, t6
	xor s1, s1, t0
	slli t0, t0, 1
	xor s0, s0, t0
	srli t0, s2, 1
	xor t0, t0, s3
	and t0, t0, t6
	xor s3, s3, t0
	slli t0, t0, 1
	xor s2, s2, t0
	srli t0, s4, 1
	xor t0, t0, s5
	and t0, t0, t6
	xor s5, s5, t0
	slli t0, t0, 1
	xor s4, s4, t0
	srli t0, s6, 1
	xor t0, t0, s7
	and t0, t0, t6
	xor s7, s7, t0
	slli t0, t0, 1
	xor s6, s6, t0
	sd s0, 640(a5)
	sd s1, 648(a5)
	sd s2, 656(a5)
	sd s3, 664(a5)
	sd s4, 672(a5)
	sd s5, 680(a5)
	sd s6, 688(a5)
	sd s7, 696(a5)
	ld s0, 904(a5)
	ld s1, 920(a5)
	ld s2, 936(a5)
	ld s3, 952(a5)
	ld s4, 968(a5)
	ld s5, 984(a5)
	ld s6, 1000(a5)
	ld s7, 1016(a5)
	srli t0, s0, 4
	xor t0, t0, s4
	and t0, t0, s8
	xor s4, s4, t0
	slli t0, t0, 4
	xor s0, s0, t0
	srli t0, s1, 4
	xor t0, t0, s5
	and t0, t0, s8
	xor s5, s5, t0
	slli t0, t0, 4
	xor s1, s1, t0
	srli t0, s2, 4
	xor t0, t0, s6
	and t0, t0, s8
	xor s6, s6, t0
	slli t0, t0, 4
	xor s2, s2, t0
	srli t0, s3, 4
	xor t0, t0, s7
	and t0, t0, s8
	xor s7, s7, t0
	slli t0, t0, 4
	xor s3, s3, t0
	srli t0, s0, 2
	xor t0, t0, s2
	and t0, t0, a6
	xor s2, s2, t0
	slli t0, t0, 2
	xor s0, s0, t0
	srli t0, s1, 2
	xor t0, t0, s3
	and t0, t0, a6
	xor s3, s3, t0
	slli t0, t0, 2
	xor s1, s1, t0
	srli t0, s4, 2
	xor t0, t0, s6
	and t0, t0, a6
	xor s6, s6, t0
	slli t0, t0, 2
	xor s4, s4, t0
	srli t0, s5, 2
	xor t0, t0, s7
	and t0, t0, a6
	xor s7, s7, t0
	slli t0, t0, 2
	xor s5, s5, t0
	srli t0, s0, 1
	xor t0, t0, s1
	and t0, t0, t6
	xor s1, s1, t0
	slli t0, t0, 1
	xor s0, s0, t0
	srli t0, s2, 1
	xor t0, t0, s3
	and t0, t0, t6
	xor s3, s3, t0
	slli t0, t0, 1
	xor s2, s2, t0
	srli t0, s4, 1
	xor t0, t0, s5
	and t0, t0, t6
	xor s5, s5, t0
	slli t0, t0, 1
	xor s4, s4, t0
	srli t0, s6, 1
	xor t0, t0, s7
	and t0, t0, t6
	xor s7, s7, t0
	slli t0, t0, 1
	xor s6, s6, t0
	sd s0, 704(a5)
	sd s1, 712(a5)
	sd s2, 720(a5)
	sd s3, 728(a5)
	sd s4, 736(a5)
	sd s5, 744(a5)
	sd s6, 752(a5)
	sd s7, 760(a5)
	addi a3, a5, 1024
214:
	ld s0, 576(a5)
	ld t0, 640(a5)
	xor s0, s0, t0
	ld t0, 704(a5)
	xor s0, s0, t0
	ld t0, 0(a3)
	xor s0, s0, t0
	ld s1, 584(a5)
	ld t0, 648(a5)
	xor s1, s1, t0
	ld t0, 712(a5)
	xor s1, s1, t0
	ld t0, 8(a3)
	xor s1, s1, t0
	ld s2, 592(a5)
	ld t0, 656(a5)
	xor s2, s2, t0
	ld t0, 720(a5)
	xor s2, s2, t0
	ld t0, 16(a3)
	xor s2, s2, t0
	ld s3, 600(a5)
	ld t0, 664(a5)
	xor s3, s3, t0
	ld t0, 728(a5)
	xor s3, s3, t0
	ld t0, 24(a3)
	xor s3, s3, t0
	ld s4, 608(a5)
	ld t0, 672(a5)
	xor s4, s4, t0
	ld t0, 736(a5)
	xor s4, s4, t0
	ld t0, 32(a3)
	xor s4, s4, t0
	ld s5, 616(a5)
	ld t0, 680(a5)
	xor s5, s5, t0
	ld t0, 744(a5)
	xor s5, s5, t0
	ld t0, 40(a3)
	xor s5, s5, t0
	ld s6, 624(a5)
	ld t0, 688(a5)
	xor s6, s6, t0
	ld t0, 752(a5)
	xor s6, s6, t0
	ld t0, 48(a3)
	xor s6, s6, t0
	ld s7, 632(a5)
	ld t0, 696(a5)
	xor s7, s7, t0
	ld t0, 760(a5)
	xor s7, s7, t0
	ld t0, 56(a3)
	xor s7, s7, t0
	xori s2, s2, -1
	xori s6, s6, -1
	xor t0, s2, s6
	xori s5, s5, -1
	xor s3, s3, s5
	xor t1, s0, s3
	xori t1, t1, -1
	xor s7, s7, t0
	xor t2, s7, s3
	xor t3, s6, s3
	xor t4, s6, t2
	xor s0, s0, s4
	xor s0, s6, s0
	xor s5, s5, s0
	xor s4, s5, t4
	and t5, s4, t4
	xor t6, s1, t0
	xor a6, s1, t1
	and a7, a6, t3
	xor t5, t5, a7
	xor s8, t0, s4
	xor s9, t6, s0
	xor s3, s9, s3
	and s10, t6, s9
	xor s11, s7, s9
	sd t0, 0(a5)
	and t0, t0, s6
	xor s10, s10, t0
	xor t5, t5, s10
	sd s6, 8(a5)
	xor s6, s6, s9
	sd s1, 16(a5)
	and s1, s1, s6
	xor s1, s1, t0
	xor t5, t5, s5
	xor s5, t1, s8
	and t0, s8, t2
	sd s6, 24(a5)
	and s6, t1, s3
	xor t0, t0, s6
	xor t0, t0, s10
	xor s10, t6, s5
	xor t0, t0, s0
	and s0, s10, s7
	xor s0, s0, a7
	and a7, s5, s11
	xor a7, a7, s6
	xor a7, a7, s1
	xor s0, s0, s1
	xor a7, a7, s2
	xor s1, a6, t3
	xor s0, s0, s1
	and s1, a7, s0
	xor a7, a7, t0
	xor s2, t0, s1
	xor s6, s0, t5
	and s2, s2, s6
	xor s2, s2, t5
	xor s0, s0, s2
	xor s1, t5, s1
	xor s6, s1, s2
	and t2, s2, t2
	and t5, t5, s6
	xor s0, t5, s0
	xor t5, s1, t5
	and s8, s2, s8
	and s1, a7, s1
	xor s1, s1, t0
	and s4, s1, s4
	and t5, s1, t5
	xor a7, a7, t5
	xor s6, s1, a7
	xor t0, a7, s0
	and s11, s0, s11
	xor t5, s2, s0
	and s7, a7, s7
	and t6, t0, t6
	and s9, t0, s9
	and t3, s6, t3
	and t1, t5, t1
	and s0, s0, s5
	and t5, t5, s3
	and s6, s6, a6
	and t4, s1, t4
	xor s1, s1, s2
	xor s6, s6, s4
	ld s2, 8(a5)
	and s2, s1, s2
	xor t5, t5, t2
	xor s2, s2, s9
	and a7, a7, s10
	xor t0, s1, t0
	ld s3, 24(a5)
	and s3, t0, s3
	xor s11, s11, t2
	xor t3, t3, t5
	xori s3, s3, -1
	ld s5, 16(a5)
	and t0, t0, s5
	xor a7, a7, s4
	xor s3, s3, s9
	xor s11, s11, s3
	xor s7, s7, t3
	xor s7, s7, s3
	xor s2, s2, t5
	xor a7, a7, s7
	xor t4, t4, t3
	xor t1, t1, s6
	xor t0, t0, a7
	xor t0, t0, t6
	ld s3, 0(a5)
	and s1, s1, s3
	xor s0, s0, a7
	xor s2, s2, s0
	xor s1, s1, s6
	xor s3, s1, t6
	xor s4, s8, s0
	xor s0, s2, t1
	xor s1, s7, s3
	xor s2, t0, s0
	xor s5, s11, s4
	xor s8, s8, t1
	xori s7, s8, -1
	xor s6, t4, t0
	srli t0, s2, 16
	slli t1, s2, 48
	ld t2, 528(a5)
	xor t0, t0, t1
	srli t1, s0, 16
	slli t3, s0, 48
	srli t4, s1, 16
	slli t5, s1, 48
	xor t0, s2, t0
	xor t1, t1, t3
	xor t4, t4, t5
	srli t3, s3, 16
	srli t5, t0, 16
	slli t6, t0, 48
	xor t1, s0, t1
	slli a6, s3, 48
	xor t4, s1, t4
	xor t3, t3, a6
	xor t5, t5, t6
	xor t3, s3, t3
	xor t5, t5, s0
	ld s0, 536(a5)
	srli t6, t3, 16
	slli a6, t3, 48
	xor t6, t6, a6
	srli a6, t5, 32
	xor t6, t6, s1
	slli t5, t5, 32
	srli s1, s4, 16
	xor a6, a6, t5
	slli t5, s4, 48
	xor a6, a6, t1
	xor s1, s1, t5
	srli t5, t6, 32
	xor s1, s4, s1
	slli t6, t6, 32
	xor t5, t5, t6
	xor a6, a6, t2
	srli t2, s1, 16
	xor t5, t5, t4
	sd a6, 528(a5)
	srli t6, s5, 16
	slli a6, s5, 48
	xor t6, t6, a6
	slli a6, s1, 48
	xor t6, s5, t6
	xor t2, t2, a6
	ld a6, 544(a5)
	xor t2, t2, s2
	xor t5, t5, s0
	srli s0, t6, 16
	srli s2, t2, 32
	sd t5, 536(a5)
	slli t5, t6, 48
	slli t2, t2, 32
	xor s0, s0, t5
	ld t5, 552(a5)
	xor s2, s2, t2
	srli t2, s6, 16
	xor s0, s0, s3
	slli s3, s6, 48
	xor s2, s2, t0
	xor t2, t2, s3
	srli s3, s0, 32
	xor t2, s6, t2
	slli s0, s0, 32
	xor s3, s3, s0
	xor s2, s2, a6
	srli s0, t2, 16
	xor s3, s3, t3
	sd s2, 544(a5)
	srli s2, s7, 16
	slli t0, s7, 48
	ld t3, 560(a5)
	xor s2, s2, t0
	slli t2, t2, 48
	xor s2, s7, s2
	xor s0, s0, t2
	xor s4, s0, s4
	xor s3, s3, t5
	srli t0, s2, 16
	srli t2, s4, 32
	sd s3, 552(a5)
	slli s2, s2, 48
	slli s4, s4, 32
	ld s3, 568(a5)
	xor t0, t0, s2
	xor t1, t1, s6
	xor s5, t0, s5
	xor t2, t2, s4
	srli s2, s5, 32
	slli s5, s5, 32
	srli s4, t1, 48
	xor s2, s2, s5
	xor t2, t2, s1
	xor s2, s2, t6
	slli t1, t1, 16
	xor t2, t2, t3
	xor s4, s4, t1
	xor s2, s2, s3
	sd t2, 560(a5)
	xor t4, t4, s7
	ld s1, 512(a5)
	xor s4, s4, s0
	sd s2, 568(a5)
	srli s0, t4, 48
	slli t4, t4, 16
	ld s2, 520(a5)
	xor s0, s0, t4
	xor s4, s4, s1
	xor s0, s0, t0
	sd s4, 512(a5)
	xor s0, s0, s2
	sd s0, 520(a5)
	ld s0, 640(a5)
	ld t0, 704(a5)
	xor s0, s0, t0
	ld t0, 512(a5)
	xor s0, s0, t0
	ld t0, 64(a3)
	xor s0, s0, t0
	ld s1, 648(a5)
	ld t0, 712(a5)
	xor s1, s1, t0
	ld t0, 520(a5)
	xor s1, s1, t0
	ld t0, 72(a3)
	xor s1, s1, t0
	ld s2, 656(a5)
	ld t0, 720(a5)
	xor s2, s2, t0
	ld t0, 528(a5)
	xor s2, s2, t0
	ld t0, 80(a3)
	xor s2, s2, t0
	ld s3, 664(a5)
	ld t0, 728(a5)
	xor s3, s3, t0
	ld t0, 536(a5)
	xor s3, s3, t0
	ld t0, 88(a3)
	xor s3, s3, t0
	ld s4, 672(a5)
	ld t0, 736(a5)
	xor s4, s4, t0
	ld t0, 544(a5)
	xor s4, s4, t0
	ld t0, 96(a3)
	xor s4, s4, t0
	ld s5, 680(a5)
	ld t0, 744(a5)
	xor s5, s5, t0
	ld t0, 552(a5)
	xor s5, s5, t0
	ld t0, 104(a3)
	xor s5, s5, t0
	ld s6, 688(a5)
	ld t0, 752(a5)
	xor s6, s6, t0
	ld t0, 560(a5)
	xor s6, s6, t0
	ld t0, 112(a3)
	xor s6, s6, t0
	ld s7, 696(a5)
	ld t0, 760(a5)
	xor s7, s7, t0
	ld t0, 568(a5)
	xor s7, s7, t0
	ld t0, 120(a3)
	xor s7, s7, t0
	xori s2, s2, -1
	xori s6, s6, -1
	xor t0, s2, s6
	xori s5, s5, -1
	xor s3, s3, s5
	xor t1, s0, s3
	xori t1, t1, -1
	xor s7, s7, t0
	xor t2, s7, s3
	xor t3, s6, s3
	xor t4, s6, t2
	xor s0, s0, s4
	xor s0, s6, s0
	xor s5, s5, s0
	xor s4, s5, t4
	and t5, s4, t4
	xor t6, s1, t0
	xor a6, s1, t1
	and a7, a6, t3
	xor t5, t5, a7
	xor s8, t0, s4
	xor s9, t6, s0
	xor s3, s9, s3
	and s10, t6, s9
	xor s11, s7, s9
	sd t0, 0(a5)
	and t0, t0, s6
	xor s10, s10, t0
	xor t5, t5, s10
	sd s6, 8(a5)
	xor s6, s6, s9
	sd s1, 16(a5)
	and s1, s1, s6
	xor s1, s1, t0
	xor t5, t5, s5
	xor s5, t1, s8
	and t0, s8, t2
	sd s6, 24(a5)
	and s6, t1, s3
	xor t0, t0, s6
	xor t0, t0, s10
	xor s10, t6, s5
	xor t0, t0, s0
	and s0, s10, s7
	xor s0, s0, a7
	and a7, s5, s11
	xor a7, a7, s6
	xor a7, a7, s1
	xor s0, s0, s1
	xor a7, a7, s2
	xor s1, a6, t3
	xor s0, s0, s1
	and s1, a7, s0
	xor a7, a7, t0
	xor s2, t0, s1
	xor s6, s0, t5
	and s2, s2, s6
	xor s2, s2, t5
	xor s0, s0, s2
	xor s1, t5, s1
	xor s6, s1, s2
	and t2, s2, t2
	and t5, t5, s6
	xor s0, t5, s0
	xor t5, s1, t5
	and s8, s2, s8
	and s1, a7, s1
	xor s1, s1, t0
	and s4, s1, s4
	and t5, s1, t5
	xor a7, a7, t5
	xor s6, s1, a7
	xor t0, a7, s0
	and s11, s0, s11
	xor t5, s2, s0
	and s7, a7, s7
	and t6, t0, t6
	and s9, t0, s9
	and t3, s6, t3
	and t1, t5, t1
	and s0, s0, s5
	and t5, t5, s3
	and s6, s6, a6
	and t4, s1, t4
	xor s1, s1, s2
	xor s6, s6, s4
	ld s2, 8(a5)
	and s2, s1, s2
	xor t5, t5, t2
	xor s2, s2, s9
	and a7, a7, s10
	xor t0, s1, t0
	ld s3, 24(a5)
	and s3, t0, s3
	xor s11, s11, t2
	xor t3, t3, t5
	xori s3, s3, -1
	ld s5, 16(a5)
	and t0, t0, s5
	xor a7, a7, s4
	xor s3, s3, s9
	xor s11, s11, s3
	xor s7, s7, t3
	xor s7, s7, s3
	xor s2, s2, t5
	xor a7, a7, s7
	xor t4, t4, t3
	xor t1, t1, s6
	xor t0, t0, a7
	xor t0, t0, t6
	ld s3, 0(a5)
	and s1, s1, s3
	xor s0, s0, a7
	xor s2, s2, s0
	xor s1, s1, s6
	xor s3, s1, t6
	xor s4, s8, s0
	xor s0, s2, t1
	xor s1, s7, s3
	xor s2, t0, s0
	xor s5, s11, s4
	xor s8, s8, t1
	xori s7, s8, -1
	xor s6, t4, t0
	srli t0, s2, 16
	slli t1, s2, 48
	ld t2, 592(a5)
	xor t0, t0, t1
	srli t1, s0, 16
	slli t3, s0, 48
	srli t4, s1, 16
	slli t5, s1, 48
	xor t0, s2, t0
	xor t1, t1, t3
	xor t4, t4, t5
	srli t3, s3, 16
	srli t5, t0, 16
	slli t6, t0, 48
	xor t1, s0, t1
	slli a6, s3, 48
	xor t4, s1, t4
	xor t3, t3, a6
	xor t5, t5, t6
	xor t3, s3, t3
	xor t5, t5, s0
	ld s0, 600(a5)
	srli t6, t3, 16
	slli a6, t3, 48
	xor t6, t6, a6
	srli a6, t5, 32
	xor t6, t6, s1
	slli t5, t5, 32
	srli s1, s4, 16
	xor a6, a6, t5
	slli t5, s4, 48
	xor a6, a6, t1
	xor s1, s1, t5
	srli t5, t6, 32
	xor s1, s4, s1
	slli t6, t6, 32
	xor t5, t5, t6
	xor a6, a6, t2
	srli t2, s1, 16
	xor t5, t5, t4
	sd a6, 592(a5)
	srli t6, s5, 16
	slli a6, s5, 48
	xor t6, t6, a6
	slli a6, s1, 48
	xor t6, s5, t6
	xor t2, t2, a6
	ld a6, 608(a5)
	xor t2, t2, s2
	xor t5, t5, s0
	srli s0, t6, 16
	srli s2, t2, 32
	sd t5, 600(a5)
	slli t5, t6, 48
	slli t2, t2, 32
	xor s0, s0, t5
	ld t5, 616(a5)
	xor s2, s2, t2
	srli t2, s6, 16
	xor s0, s0, s3
	slli s3, s6, 48
	xor s2, s2, t0
	xor t2, t2, s3
	srli s3, s0, 32
	xor t2, s6, t2
	slli s0, s0, 32
	xor s3, s3, s0
	xor s2, s2, a6
	srli s0, t2, 16
	xor s3, s3, t3
	sd s2, 608(a5)
	srli s2, s7, 16
	slli t0, s7, 48
	ld t3, 624(a5)
	xor s2, s2, t0
	slli t2, t2, 48
	xor s2, s7, s2
	xor s0, s0, t2
	xor s4, s0, s4
	xor s3, s3, t5
	srli t0, s2, 16
	srli t2, s4, 32
	sd s3, 616(a5)
	slli s2, s2, 48
	slli s4, s4, 32
	ld s3, 632(a5)
	xor t0, t0, s2
	xor t1, t1, s6
	xor s5, t0, s5
	xor t2, t2, s4
	srli s2, s5, 32
	slli s5, s5, 32
	srli s4, t1, 48
	xor s2, s2, s5
	xor t2, t2, s1
	xor s2, s2, t6
	slli t1, t1, 16
	xor t2, t2, t3
	xor s4, s4, t1
	xor s2, s2, s3
	sd t2, 624(a5)
	xor t4, t4, s7
	ld s1, 576(a5)
	xor s4, s4, s0
	sd s2, 632(a5)
	srli s0, t4, 48
	slli t4, t4, 16
	ld s2, 584(a5)
	xor s0, s0, t4
	xor s4, s4, s1
	xor s0, s0, t0
	sd s4, 576(a5)
	xor s0, s0, s2
	sd s0, 584(a5)
	ld s0, 704(a5)
	ld t0, 512(a5)
	xor s0, s0, t0
	ld t0, 576(a5)
	xor s0, s0, t0
	ld t0, 128(a3)
	xor s0, s0, t0
	ld s1, 712(a5)
	ld t0, 520(a5)
	xor s1, s1, t0
	ld t0, 584(a5)
	xor s1, s1, t0
	ld t0, 136(a3)
	xor s1, s1, t0
	ld s2, 720(a5)
	ld t0, 528(a5)
	xor s2, s2, t0
	ld t0, 592(a5)
	xor s2, s2, t0
	ld t0, 144(a3)
	xor s2, s2, t0
	ld s3, 728(a5)
	ld t0, 536(a5)
	xor s3, s3, t0
	ld t0, 600(a5)
	xor s3, s3, t0
	ld t0, 152(a3)
	xor s3, s3, t0
	ld s4, 736(a5)
	ld t0, 544(a5)
	xor s4, s4, t0
	ld t0, 608(a5)
	xor s4, s4, t0
	ld t0, 160(a3)
	xor s4, s4, t0
	ld s5, 744(a5)
	ld t0, 552(a5)
	xor s5, s5, t0
	ld t0, 616(a5)
	xor s5, s5, t0
	ld t0, 168(a3)
	xor s5, s5, t0
	ld s6, 752(a5)
	ld t0, 560(a5)
	xor s6, s6, t0
	ld t0, 624(a5)
	xor s6, s6, t0
	ld t0, 176(a3)
	xor s6, s6, t0
	ld s7, 760(a5)
	ld t0, 568(a5)
	xor s7, s7, t0
	ld t0, 632(a5)
	xor s7, s7, t0
	ld t0, 184(a3)
	xor s7, s7, t0
	xori s2, s2, -1
	xori s6, s6, -1
	xor t0, s2, s6
	xori s5, s5, -1
	xor s3, s3, s5
	xor t1, s0, s3
	xori t1, t1, -1
	xor s7, s7, t0
	xor t2, s7, s3
	xor t3, s6, s3
	xor t4, s6, t2
	xor s0, s0, s4
	xor s0, s6, s0
	xor s5, s5, s0
	xor s4, s5, t4
	and t5, s4, t4
	xor t6, s1, t0
	xor a6, s1, t1
	and a7, a6, t3
	xor t5, t5, a7
	xor s8, t0, s4
	xor s9, t6, s0
	xor s3, s9, s3
	and s10, t6, s9
	xor s11, s7, s9
	sd t0, 0(a5)
	and t0, t0, s6
	xor s10, s10, t0
	xor t5, t5, s10
	sd s6, 8(a5)
	xor s6, s6, s9
	sd s1, 16(a5)
	and s1, s1, s6
	xor s1, s1, t0
	xor t5, t5, s5
	xor s5, t1, s8
	and t0, s8, t2
	sd s6, 24(a5)
	and s6, t1, s3
	xor t0, t0, s6
	xor t0, t0, s10
	xor s10, t6, s5
	xor t0, t0, s0
	and s0, s10, s7
	xor s0, s0, a7
	and a7, s5, s11
	xor a7, a7, s6
	xor a7, a7, s1
	xor s0, s0, s1
	xor a7, a7, s2
	xor s1, a6, t3
	xor s0, s0, s1
	and s1, a7, s0
	xor a7, a7, t0
	xor s2, t0, s1
	xor s6, s0, t5
	and s2, s2, s6
	xor s2, s2, t5
	xor s0, s0, s2
	xor s1, t5, s1
	xor s6, s1, s2
	and t2, s2, t2
	and t5, t5, s6
	xor s0, t5, s0
	xor t5, s1, t5
	and s8, s2, s8
	and s1, a7, s1
	xor s1, s1, t0
	and s4, s1, s4
	and t5, s1, t5
	xor a7, a7, t5
	xor s6, s1, a7
	xor t0, a7, s0
	and s11, s0, s11
	xor t5, s2, s0
	and s7, a7, s7
	and t6, t0, t6
	and s9, t0, s9
	and t3, s6, t3
	and t1, t5, t1
	and s0, s0, s5
	and t5, t5, s3
	and s6, s6, a6
	and t4, s1, t4
	xor s1, s1, s2
	xor s6, s6, s4
	ld s2, 8(a5)
	and s2, s1, s2
	xor t5, t5, t2
	xor s2, s2, s9
	and a7, a7, s10
	xor t0, s1, t0
	ld s3, 24(a5)
	and s3, t0, s3
	xor s11, s11, t2
	xor t3, t3, t5
	xori s3, s3, -1
	ld s5, 16(a5)
	and t0, t0, s5
	xor a7, a7, s4
	xor s3, s3, s9
	xor s11, s11, s3
	xor s7, s7, t3
	xor s7, s7, s3
	xor s2, s2, t5
	xor a7, a7, s7
	xor t4, t4, t3
	xor t1, t1, s6
	xor t0, t0, a7
	xor t0, t0, t6
	ld s3, 0(a5)
	and s1, s1, s3
	xor s0, s0, a7
	xor s2, s2, s0
	xor s1, s1, s6
	xor s3, s1, t6
	xor s4, s8, s0
	xor s0, s2, t1
	xor s1, s7, s3
	xor s2, t0, s0
	xor s5, s11, s4
	xor s8, s8, t1
	xori s7, s8, -1
	xor s6, t4, t0
	srli t0, s2, 16
	slli t1, s2, 48
	ld t2, 656(a5)
	xor t0, t0, t1
	srli t1, s0, 16
	slli t3, s0, 48
	srli t4, s1, 16
	slli t5, s1, 48
	xor t0, s2, t0
	xor t1, t1, t3
	xor t4, t4, t5
	srli t3, s3, 16
	srli t5, t0, 16
	slli t6, t0, 48
	xor t1, s0, t1
	slli a6, s3, 48
	xor t4, s1, t4
	xor t3, t3, a6
	xor t5, t5, t6
	xor t3, s3, t3
	xor t5, t5, s0
	ld s0, 664(a5)
	srli t6, t3, 16
	slli a6, t3, 48
	xor t6, t6, a6
	srli a6, t5, 32
	xor t6, t6, s1
	slli t5, t5, 32
	srli s1, s4, 16
	xor a6, a6, t5
	slli t5, s4, 48
	xor a6, a6, t1
	xor s1, s1, t5
	srli t5, t6, 32
	xor s1, s4, s1
	slli t6, t6, 32
	xor t5, t5, t6
	xor a6, a6, t2
	srli t2, s1, 16
	xor t5, t5, t4
	sd a6, 656(a5)
	srli t6, s5, 16
	slli a6, s5, 48
	xor t6, t6, a6
	slli a6, s1, 48
	xor t6, s5, t6
	xor t2, t2, a6
	ld a6, 672(a5)
	xor t2, t2, s2
	xor t5, t5, s0
	srli s0, t6, 16
	srli s2, t2, 32
	sd t5, 664(a5)
	slli t5, t6, 48
	slli t2, t2, 32
	xor s0, s0, t5
	ld t5, 680(a5)
	xor s2, s2, t2
	srli t2, s6, 16
	xor s0, s0, s3
	slli s3, s6, 48
	xor s2, s2, t0
	xor t2, t2, s3
	srli s3, s0, 32
	xor t2, s6, t2
	slli s0, s0, 32
	xor s3, s3, s0
	xor s2, s2, a6
	srli s0, t2, 16
	xor s3, s3, t3
	sd s2, 672(a5)
	srli s2, s7, 16
	slli t0, s7, 48
	ld t3, 688(a5)
	xor s2, s2, t0
	slli t2, t2, 48
	xor s2, s7, s2
	xor s0, s0, t2
	xor s4, s0, s4
	xor s3, s3, t5
	srli t0, s2, 16
	srli t2, s4, 32
	sd s3, 680(a5)
	slli s2, s2, 48
	slli s4, s4, 32
	ld s3, 696(a5)
	xor t0, t0, s2
	xor t1, t1, s6
	xor s5, t0, s5
	xor t2, t2, s4
	srli s2, s5, 32
	slli s5, s5, 32
	srli s4, t1, 48
	xor s2, s2, s5
	xor t2, t2, s1
	xor s2, s2, t6
	slli t1, t1, 16
	xor t2, t2, t3
	xor s4, s4, t1
	xor s2, s2, s3
	sd t2, 688(a5)
	xor t4, t4, s7
	ld s1, 640(a5)
	xor s4, s4, s0
	sd s2, 696(a5)
	srli s0, t4, 48
	slli t4, t4, 16
	ld s2, 648(a5)
	xor s0, s0, t4
	xor s4, s4, s1
	xor s0, s0, t0
	sd s4, 640(a5)
	xor s0, s0, s2
	sd s0, 648(a5)
	ld s0, 512(a5)
	ld t0, 576(a5)
	xor s0, s0, t0
	ld t0, 640(a5)
	xor s0, s0, t0
	ld t0, 192(a3)
	xor s0, s0, t0
	ld s1, 520(a5)
	ld t0, 584(a5)
	xor s1, s1, t0
	ld t0, 648(a5)
	xor s1, s1, t0
	ld t0, 200(a3)
	xor s1, s1, t0
	ld s2, 528(a5)
	ld t0, 592(a5)
	xor s2, s2, t0
	ld t0, 656(a5)
	xor s2, s2, t0
	ld t0, 208(a3)
	xor s2, s2, t0
	ld s3, 536(a5)
	ld t0, 600(a5)
	xor s3, s3, t0
	ld t0, 664(a5)
	xor s3, s3, t0
	ld t0, 216(a3)
	xor s3, s3, t0
	ld s4, 544(a5)
	ld t0, 608(a5)
	xor s4, s4, t0
	ld t0, 672(a5)
	xor s4, s4, t0
	ld t0, 224(a3)
	xor s4, s4, t0
	ld s5, 552(a5)
	ld t0, 616(a5)
	xor s5, s5, t0
	ld t0, 680(a5)
	xor s5, s5, t0
	ld t0, 232(a3)
	xor s5, s5, t0
	ld s6, 560(a5)
	ld t0, 624(a5)
	xor s6, s6, t0
	ld t0, 688(a5)
	xor s6, s6, t0
	ld t0, 240(a3)
	xor s6, s6, t0
	ld s7, 568(a5)
	ld t0, 632(a5)
	xor s7, s7, t0
	ld t0, 696(a5)
	xor s7, s7, t0
	ld t0, 248(a3)
	xor s7, s7, t0
	xori s2, s2, -1
	xori s6, s6, -1
	xor t0, s2, s6
	xori s5, s5, -1
	xor s3, s3, s5
	xor t1, s0, s3
	xori t1, t1, -1
	xor s7, s7, t0
	xor t2, s7, s3
	xor t3, s6, s3
	xor t4, s6, t2
	xor s0, s0, s4
	xor s0, s6, s0
	xor s5, s5, s0
	xor s4, s5, t4
	and t5, s4, t4
	xor t6, s1, t0
	xor a6, s1, t1
	and a7, a6, t3
	xor t5, t5, a7
	xor s8, t0, s4
	xor s9, t6, s0
	xor s3, s9, s3
	and s10, t6, s9
	xor s11, s7, s9
	sd t0, 0(a5)
	and t0, t0, s6
	xor s10, s10, t0
	xor t5, t5, s10
	sd s6, 8(a5)
	xor s6, s6, s9
	sd s1, 16(a5)
	and s1, s1, s6
	xor s1, s1, t0
	xor t5, t5, s5
	xor s5, t1, s8
	and t0, s8, t2
	sd s6, 24(a5)
	and s6, t1, s3
	xor t0, t0, s6
	xor t0, t0, s10
	xor s10, t6, s5
	xor t0, t0, s0
	and s0, s10, s7
	xor s0, s0, a7
	and a7, s5, s11
	xor a7, a7, s6
	xor a7, a7, s1
	xor s0, s0, s1
	xor a7, a7, s2
	xor s1, a6, t3
	xor s0, s0, s1
	and s1, a7, s0
	xor a7, a7, t0
	xor s2, t0, s1
	xor s6, s0, t5
	and s2, s2, s6
	xor s2, s2, t5
	xor s0, s0, s2
	xor s1, t5, s1
	xor s6, s1, s2
	and t2, s2, t2
	and t5, t5, s6
	xor s0, t5, s0
	xor t5, s1, t5
	and s8, s2, s8
	and s1, a7, s1
	xor s1, s1, t0
	and s4, s1, s4
	and t5, s1, t5
	xor a7, a7, t5
	xor s6, s1, a7
	xor t0, a7, s0
	and s11, s0, s11
	xor t5, s2, s0
	and s7, a7, s7
	and t6, t0, t6
	and s9, t0, s9
	and t3, s6, t3
	and t1, t5, t1
	and s0, s0, s5
	and t5, t5, s3
	and s6, s6, a6
	and t4, s1, t4
	xor s1, s1, s2
	xor s6, s6, s4
	ld s2, 8(a5)
	and s2, s1, s2
	xor t5, t5, t2
	xor s2, s2, s9
	and a7, a7, s10
	xor t0, s1, t0
	ld s3, 24(a5)
	and s3, t0, s3
	xor s11, s11, t2
	xor t3, t3, t5
	xori s3, s3, -1
	ld s5, 16(a5)
	and t0, t0, s5
	xor a7, a7, s4
	xor s3, s3, s9
	xor s11, s11, s3
	xor s7, s7, t3
	xor s7, s7, s3
	xor s2, s2, t5
	xor a7, a7, s7
	xor t4, t4, t3
	xor t1, t1, s6
	xor t0, t0, a7
	xor t0, t0, t6
	ld s3, 0(a5)
	and s1, s1, s3
	xor s0, s0, a7
	xor s2, s2, s0
	xor s1, s1, s6
	xor s3, s1, t6
	xor s4, s8, s0
	xor s0, s2, t1
	xor s1, s7, s3
	xor s2, t0, s0
	xor s5, s11, s4
	xor s8, s8, t1
	xori s7, s8, -1
	xor s6, t4, t0
	srli t0, s2, 16
	slli t1, s2, 48
	ld t2, 720(a5)
	xor t0, t0, t1
	srli t1, s0, 16
	slli t3, s0, 48
	srli t4, s1, 16
	slli t5, s1, 48
	xor t0, s2, t0
	xor t1, t1, t3
	xor t4, t4, t5
	srli t3, s3, 16
	srli t5, t0, 16
	slli t6, t0, 48
	xor t1, s0, t1
	slli a6, s3, 48
	xor t4, s1, t4
	xor t3, t3, a6
	xor t5, t5, t6
	xor t3, s3, t3
	xor t5, t5, s0
	ld s0, 728(a5)
	srli t6, t3, 16
	slli a6, t3, 48
	xor t6, t6, a6
	srli a6, t5, 32
	xor t6, t6, s1
	slli t5, t5, 32
	srli s1, s4, 16
	xor a6, a6, t5
	slli t5, s4, 48
	xor a6, a6, t1
	xor s1, s1, t5
	srli t5, t6, 32
	xor s1, s4, s1
	slli t6, t6, 32
	xor t5, t5, t6
	xor a6, a6, t2
	srli t2, s1, 16
	xor t5, t5, t4
	sd a6, 720(a5)
	srli t6, s5, 16
	slli a6, s5, 48
	xor t6, t6, a6
	slli a6, s1, 48
	xor t6, s5, t6
	xor t2, t2, a6
	ld a6, 736(a5)
	xor t2, t2, s2
	xor t5, t5, s0
	srli s0, t6, 16
	srli s2, t2, 32
	sd t5, 728(a5)
	slli t5, t6, 48
	slli t2, t2, 32
	xor s0, s0, t5
	ld t5, 744(a5)
	xor s2, s2, t2
	srli t2, s6, 16
	xor s0, s0, s3
	slli s3, s6, 48
	xor s2, s2, t0
	xor t2, t2, s3
	srli s3, s0, 32
	xor t2, s6, t2
	slli s0, s0, 32
	xor s3, s3, s0
	xor s2, s2, a6
	srli s0, t2, 16
	xor s3, s3, t3
	sd s2, 736(a5)
	srli s2, s7, 16
	slli t0, s7, 48
	ld t3, 752(a5)
	xor s2, s2, t0
	slli t2, t2, 48
	xor s2, s7, s2
	xor s0, s0, t2
	xor s4, s0, s4
	xor s3, s3, t5
	srli t0, s2, 16
	srli t2, s4, 32
	sd s3, 744(a5)
	slli s2, s2, 48
	slli s4, s4, 32
	ld s3, 760(a5)
	xor t0, t0, s2
	xor t1, t1, s6
	xor s5, t0, s5
	xor t2, t2, s4
	srli s2, s5, 32
	slli s5, s5, 32
	srli s4, t1, 48
	xor s2, s2, s5
	xor t2, t2, s1
	xor s2, s2, t6
	slli t1, t1, 16
	xor t2, t2, t3
	xor s4, s4, t1
	xor s2, s2, s3
	sd t2, 752(a5)
	xor t4, t4, s7
	ld s1, 704(a5)
	xor s4, s4, s0
	sd s2, 760(a5)
	srli s0, t4, 48
	slli t4, t4, 16
	ld s2, 712(a5)
	xor s0, s0, t4
	xor s4, s4, s1
	xor s0, s0, t0
	sd s4, 704(a5)
	xor s0, s0, s2
	sd s0, 712(a5)
	addi a3, a3, 256
	sub t0, a3, a0
	bnez t0, 214b
	ld t3, 360(a5)
	ld t4, 368(a5)
	ld t5, 376(a5)
	ld t6, 384(a5)
	ld a6, 392(a5)
	ld s8, 400(a5)
	ld s0, 704(a5)
	ld s1, 712(a5)
	ld s2, 720(a5)
	ld s3, 728(a5)
	ld s4, 736(a5)
	ld s5, 744(a5)
	ld s6, 752(a5)
	ld s7, 760(a5)
	srli t0, s0, 4
	xor t0, t0, s4
	and t0, t0, s8
	xor s4, s4, t0
	slli t0, t0, 4
	xor s0, s0, t0
	srli t0, s1, 4
	xor t0, t0, s5
	and t0, t0, s8
	xor s5, s5, t0
	slli t0, t0, 4
	xor s1, s1, t0
	srli t0, s2, 4
	xor t0, t0, s6
	and t0, t0, s8
	xor s6, s6, t0
	slli t0, t0, 4
	xor s2, s2, t0
	srli t0, s3, 4
	xor t0, t0, s7
	and t0, t0, s8
	xor s7, s7, t0
	slli t0, t0, 4
	xor s3, s3, t0
	srli t0, s0, 2
	xor t0, t0, s2
	and t0, t0, a6
	xor s2, s2, t0
	slli t0, t0, 2
	xor s0, s0, t0
	srli t0, s1, 2
	xor t0, t0, s3
	and t0, t0, a6
	xor s3, s3, t0
	slli t0, t0, 2
	xor s1, s1, t0
	srli t0, s4, 2
	xor t0, t0, s6
	and t0, t0, a6
	xor s6, s6, t0
	slli t0, t0, 2
	xor s4, s4, t0
	srli t0, s5, 2
	xor t0, t0, s7
	and t0, t0, a6
	xor s7, s7, t0
	slli t0, t0, 2
	xor s5, s5, t0
	srli t0, s0, 1
	xor t0, t0, s1
	and t0, t0, t6
	xor s1, s1, t0
	slli t0, t0, 1
	xor s0, s0, t0
	srli t0, s2, 1
	xor t0, t0, s3
	and t0, t0, t6
	xor s3, s3, t0
	slli t0, t0, 1
	xor s2, s2, t0
	srli t0, s4, 1
	xor t0, t0, s5
	and t0, t0, t6
	xor s5, s5, t0
	slli t0, t0, 1
	xor s4, s4, t0
	srli t0, s6, 1
	xor t0, t0, s7
	and t0, t0, t6
	xor s7, s7, t0
	slli t0, t0, 1
	xor s6, s6, t0
	sd s0, 768(a5)
	sd s1, 784(a5)
	sd s2, 800(a5)
	sd s3, 816(a5)
	sd s4, 832(a5)
	sd s5, 848(a5)
	sd s6, 864(a5)
	sd s7, 880(a5)
	ld s0, 640(a5)
	ld s1, 648(a5)
	ld s2, 656(a5)
	ld s3, 664(a5)
	ld s4, 672(a5)
	ld s5, 680(a5)
	ld s6, 688(a5)
	ld s7, 696(a5)
	srli t0, s0, 4
	xor t0, t0, s4
	and t0, t0, s8
	xor s4, s4, t0
	slli t0, t0, 4
	xor s0, s0, t0
	srli t0, s1, 4
	xor t0, t0, s5
	and t0, t0, s8
	xor s5, s5, t0
	slli t0, t0, 4
	xor s1, s1, t0
	srli t0, s2, 4
	xor t0, t0, s6
	and t0, t0, s8
	xor s6, s6, t0
	slli t0, t0, 4
	xor s2, s2, t0
	srli t0, s3, 4
	xor t0, t0, s7
	and t0, t0, s8
	xor s7, s7, t0
	slli t0, t0, 4
	xor s3, s3, t0
	srli t0, s0, 2
	xor t0, t0, s2
	and t0, t0, a6
	xor s2, s2, t0
	slli t0, t0, 2
	xor s0, s0, t0
	srli t0, s1, 2
	xor t0, t0, s3
	and t0, t0, a6
	xor s3, s3, t0
	slli t0, t0, 2
	xor s1, s1, t0
	srli t0, s4, 2
	xor t0, t0, s6
	and t0, t0, a6
	xor s6, s6, t0
	slli t0, t0, 2
	xor s4, s4, t0
	srli t0, s5, 2
	xor t0, t0, s7
	and t0, t0, a6
	xor s7, s7, t0
	slli t0, t0, 2
	xor s5, s5, t0
	srli t0, s0, 1
	xor t0, t0, s1
	and t0, t0, t6
	xor s1, s1, t0
	slli t0, t0, 1
	xor s0, s0, t0
	srli t0, s2, 1
	xor t0, t0, s3
	and t0, t0, t6
	xor s3, s3, t0
	slli t0, t0, 1
	xor s2, s2, t0
	srli t0, s4, 1
	xor t0, t0, s5
	and t0, t0, t6
	xor s5, s5, t0
	slli t0, t0, 1
	xor s4, s4, t0
	srli t0, s6, 1
	xor t0, t0, s7
	and t0, t0, t6
	xor s7, s7, t0
	slli t0, t0, 1
	xor s6, s6, t0
	sd s0, 896(a5)
	sd s1, 912(a5)
	sd s2, 928(a5)
	sd s3, 944(a5)
	sd s4, 960(a5)
	sd s5, 976(a5)
	sd s6, 992(a5)
	sd s7, 1008(a5)
	ld s0, 576(a5)
	ld s1, 584(a5)
	ld s2, 592(a5)
	ld s3, 600(a5)
	ld s4, 608(a5)
	ld s5, 616(a5)
	ld s6, 624(a5)
	ld s7, 632(a5)
	srli t0, s0, 4
	xor t0, t0, s4
	and t0, t0, s8
	xor s4, s4, t0
	slli t0, t0, 4
	xor s0, s0, t0
	srli t0, s1, 4
	xor t0, t0, s5
	and t0, t0, s8
	xor s5, s5, t0
	slli t0, t0, 4
	xor s1, s1, t0
	srli t0, s2, 4
	xor t0, t0, s6
	and t0, t0, s8
	xor s6, s6, t0
	slli t0, t0, 4
	xor s2, s2, t0
	srli t0, s3, 4
	xor t0, t0, s7
	and t0, t0, s8
	xor s7, s7, t0
	slli t0, t0, 4
	xor s3, s3, t0
	srli t0, s0, 2
	xor t0, t0, s2
	and t0, t0, a6
	xor s2, s2, t0
	slli t0, t0, 2
	xor s0, s0, t0
	srli t0, s1, 2
	xor t0, t0, s3
	and t0, t0, a6
	xor s3, s3, t0
	slli t0, t0, 2
	xor s1, s1, t0
	srli t0, s4, 2
	xor t0, t0, s6
	and t0, t0, a6
	xor s6, s6, t0
	slli t0, t0, 2
	xor s4, s4, t0
	srli t0, s5, 2
	xor t0, t0, s7
	and t0, t0, a6
	xor s7, s7, t0
	slli t0, t0, 2
	xor s5, s5, t0
	srli t0, s0, 1
	xor t0, t0, s1
	and t0, t0, t6
	xor s1, s1, t0
	slli t0, t0, 1
	xor s0, s0, t0
	srli t0, s2, 1
	xor t0, t0, s3
	and t0, t0, t6
	xor s3, s3, t0
	slli t0, t0, 1
	xor s2, s2, t0
	srli t0, s4, 1
	xor t0, t0, s5
	and t0, t0, t6
	xor s5, s5, t0
	slli t0, t0, 1
	xor s4, s4, t0
	srli t0, s6, 1
	xor t0, t0, s7
	and t0, t0, t6
	xor s7, s7, t0
	slli t0, t0, 1
	xor s6, s6, t0
	sd s0, 776(a5)
	sd s1, 792(a5)
	sd s2, 808(a5)
	sd s3, 824(a5)
	sd s4, 840(a5)
	sd s5, 856(a5)
	sd s6, 872(a5)
	sd s7, 888(a5)
	ld s0, 512(a5)
	ld s1, 520(a5)
	ld s2, 528(a5)
	ld s3, 536(a5)
	ld s4, 544(a5)
	ld s5, 552(a5)
	ld s6, 560(a5)
	ld s7, 568(a5)
	srli t0, s0, 4
	xor t0, t0, s4
	and t0, t0, s8
	xor s4, s4, t0
	slli t0, t0, 4
	xor s0, s0, t0
	srli t0, s1, 4
	xor t0, t0, s5
	and t0, t0, s8
	xor s5, s5, t0
	slli t0, t0, 4
	xor s1, s1, t0
	srli t0, s2, 4
	xor t0, t0, s6
	and t0, t0, s8
	xor s6, s6, t0
	slli t0, t0, 4
	xor s2, s2, t0
	srli t0, s3, 4
	xor t0, t0, s7
	and t0, t0, s8
	xor s7, s7, t0
	slli t0, t0, 4
	xor s3, s3, t0
	srli t0, s0, 2
	xor t0, t0, s2
	and t0, t0, a6
	xor s2, s2, t0
	slli t0, t0, 2
	xor s0, s0, t0
	srli t0, s1, 2
	xor t0, t0, s3
	and t0, t0, a6
	xor s3, s3, t0
	slli t0, t0, 2
	xor s1, s1, t0
	srli t0, s4, 2
	xor t0, t0, s6
	and t0, t0, a6
	xor s6, s6, t0
	slli t0, t0, 2
	xor s4, s4, t0
	srli t0, s5, 2
	xor t0, t0, s7
	and t0, t0, a6
	xor s7, s7, t0
	slli t0, t0, 2
	xor s5, s5, t0
	srli t0, s0, 1
	xor t0, t0, s1
	and t0, t0, t6
	xor s1, s1, t0
	slli t0, t0, 1
	xor s0, s0, t0
	srli t0, s2, 1
	xor t0, t0, s3
	and t0, t0, t6
	xor s3, s3, t0
	slli t0, t0, 1
	xor s2, s2, t0
	srli t0, s4, 1
	xor t0, t0, s5
	and t0, t0, t6
	xor s5, s5, t0
	slli t0, t0, 1
	xor s4, s4, t0
	srli t0, s6, 1
	xor t0, t0, s7
	and t0, t0, t6
	xor s7, s7, t0
	slli t0, t0, 1
	xor s6, s6, t0
	sd s0, 904(a5)
	sd s1, 920(a5)
	sd s2, 936(a5)
	sd s3, 952(a5)
	sd s4, 968(a5)
	sd s5, 984(a5)
	sd s6, 1000(a5)
	sd s7, 1016(a5)
	ld s0, 768(a5)
	ld s4, 896(a5)
	ld s1, 784(a5)
	ld s5, 912(a5)
	ld s2, 800(a5)
	ld s6, 928(a5)
	ld s3, 816(a5)
	ld s7, 944(a5)
	srli t0, s0, 32
	xor t0, t0, s4
	and t0, t0, t3
	xor s4, s4, t0
	slli t0, t0, 32
	xor s0, s0, t0
	srli t0, s1, 32
	xor t0, t0, s5
	and t0, t0, t3
	xor s5, s5, t0
	slli t0, t0, 32
	xor s1, s1, t0
	srli t0, s2, 32
	xor t0, t0, s6
	and t0, t0, t3
	xor s6, s6, t0
	slli t0, t0, 32
	xor s2, s2, t0
	srli t0, s3, 32
	xor t0, t0, s7
	and t0, t0, t3
	xor s7, s7, t0
	slli t0, t0, 32
	xor s3, s3, t0
	srli t0, s0, 16
	xor t0, t0, s4
	and t0, t0, t4
	xor s4, s4, t0
	slli t0, t0, 16
	xor s0, s0, t0
	srli t0, s1, 16
	xor t0, t0, s5
	and t0, t0, t4
	xor s5, s5, t0
	slli t0, t0, 16
	xor s1, s1, t0
	srli t0, s2, 16
	xor t0, t0, s6
	and t0, t0, t4
	xor s6, s6, t0
	slli t0, t0, 16
	xor s2, s2, t0
	srli t0, s3, 16
	xor t0, t0, s7
	and t0, t0, t4
	xor s7, s7, t0
	slli t0, t0, 16
	xor s3, s3, t0
	srli t0, s0, 8
	xor t0, t0, s4
	and t0, t0, t5
	xor s4, s4, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s5
	and t0, t0, t5
	xor s5, s5, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s6
	and t0, t0, t5
	xor s6, s6, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s7
	and t0, t0, t5
	xor s7, s7, t0
	slli t0, t0, 8
	xor s3, s3, t0
	sd s0, 768(a5)
	sd s4, 896(a5)
	sd s1, 784(a5)
	sd s5, 912(a5)
	sd s2, 800(a5)
	sd s6, 928(a5)
	sd s3, 816(a5)
	sd s7, 944(a5)
	ld s0, 832(a5)
	ld s4, 960(a5)
	ld s1, 848(a5)
	ld s5, 976(a5)
	ld s2, 864(a5)
	ld s6, 992(a5)
	ld s3, 880(a5)
	ld s7, 1008(a5)
	srli t0, s0, 32
	xor t0, t0, s4
	and t0, t0, t3
	xor s4, s4, t0
	slli t0, t0, 32
	xor s0, s0, t0
	srli t0, s1, 32
	xor t0, t0, s5
	and t0, t0, t3
	xor s5, s5, t0
	slli t0, t0, 32
	xor s1, s1, t0
	srli t0, s2, 32
	xor t0, t0, s6
	and t0, t0, t3
	xor s6, s6, t0
	slli t0, t0, 32
	xor s2, s2, t0
	srli t0, s3, 32
	xor t0, t0, s7
	and t0, t0, t3
	xor s7, s7, t0
	slli t0, t0, 32
	xor s3, s3, t0
	srli t0, s0, 16
	xor t0, t0, s4
	and t0, t0, t4
	xor s4, s4, t0
	slli t0, t0, 16
	xor s0, s0, t0
	srli t0, s1, 16
	xor t0, t0, s5
	and t0, t0, t4
	xor s5, s5, t0
	slli t0, t0, 16
	xor s1, s1, t0
	srli t0, s2, 16
	xor t0, t0, s6
	and t0, t0, t4
	xor s6, s6, t0
	slli t0, t0, 16
	xor s2, s2, t0
	srli t0, s3, 16
	xor t0, t0, s7
	and t0, t0, t4
	xor s7, s7, t0
	slli t0, t0, 16
	xor s3, s3, t0
	srli t0, s0, 8
	xor t0, t0, s4
	and t0, t0, t5
	xor s4, s4, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s5
	and t0, t0, t5
	xor s5, s5, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s6
	and t0, t0, t5
	xor s6, s6, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s7
	and t0, t0, t5
	xor s7, s7, t0
	slli t0, t0, 8
	xor s3, s3, t0
	sd s0, 832(a5)
	sd s4, 960(a5)
	sd s1, 848(a5)
	sd s5, 976(a5)
	sd s2, 864(a5)
	sd s6, 992(a5)
	sd s3, 880(a5)
	sd s7, 1008(a5)
	ld s0, 776(a5)
	ld s4, 904(a5)
	ld s1, 792(a5)
	ld s5, 920(a5)
	ld s2, 808(a5)
	ld s6, 936(a5)
	ld s3, 824(a5)
	ld s7, 952(a5)
	srli t0, s0, 32
	xor t0, t0, s4
	and t0, t0, t3
	xor s4, s4, t0
	slli t0, t0, 32
	xor s0, s0, t0
	srli t0, s1, 32
	xor t0, t0, s5
	and t0, t0, t3
	xor s5, s5, t0
	slli t0, t0, 32
	xor s1, s1, t0
	srli t0, s2, 32
	xor t0, t0, s6
	and t0, t0, t3
	xor s6, s6, t0
	slli t0, t0, 32
	xor s2, s2, t0
	srli t0, s3, 32
	xor t0, t0, s7
	and t0, t0, t3
	xor s7, s7, t0
	slli t0, t0, 32
	xor s3, s3, t0
	srli t0, s0, 16
	xor t0, t0, s4
	and t0, t0, t4
	xor s4, s4, t0
	slli t0, t0, 16
	xor s0, s0, t0
	srli t0, s1, 16
	xor t0, t0, s5
	and t0, t0, t4
	xor s5, s5, t0
	slli t0, t0, 16
	xor s1, s1, t0
	srli t0, s2, 16
	xor t0, t0, s6
	and t0, t0, t4
	xor s6, s6, t0
	slli t0, t0, 16
	xor s2, s2, t0
	srli t0, s3, 16
	xor t0, t0, s7
	and t0, t0, t4
	xor s7, s7, t0
	slli t0, t0, 16
	xor s3, s3, t0
	srli t0, s0, 8
	xor t0, t0, s4
	and t0, t0, t5
	xor s4, s4, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s5
	and t0, t0, t5
	xor s5, s5, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s6
	and t0, t0, t5
	xor s6, s6, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s7
	and t0, t0, t5
	xor s7, s7, t0
	slli t0, t0, 8
	xor s3, s3, t0
	sd s0, 776(a5)
	sd s4, 904(a5)
	sd s1, 792(a5)
	sd s5, 920(a5)
	sd s2, 808(a5)
	sd s6, 936(a5)
	sd s3, 824(a5)
	sd s7, 952(a5)
	ld s0, 840(a5)
	ld s4, 968(a5)
	ld s1, 856(a5)
	ld s5, 984(a5)
	ld s2, 872(a5)
	ld s6, 1000(a5)
	ld s3, 888(a5)
	ld s7, 1016(a5)
	srli t0, s0, 32
	xor t0, t0, s4
	and t0, t0, t3
	xor s4, s4, t0
	slli t0, t0, 32
	xor s0, s0, t0
	srli t0, s1, 32
	xor t0, t0, s5
	and t0, t0, t3
	xor s5, s5, t0
	slli t0, t0, 32
	xor s1, s1, t0
	srli t0, s2, 32
	xor t0, t0, s6
	and t0, t0, t3
	xor s6, s6, t0
	slli t0, t0, 32
	xor s2, s2, t0
	srli t0, s3, 32
	xor t0, t0, s7
	and t0, t0, t3
	xor s7, s7, t0
	slli t0, t0, 32
	xor s3, s3, t0
	srli t0, s0, 16
	xor t0, t0, s4
	and t0, t0, t4
	xor s4, s4, t0
	slli t0, t0, 16
	xor s0, s0, t0
	srli t0, s1, 16
	xor t0, t0, s5
	and t0, t0, t4
	xor s5, s5, t0
	slli t0, t0, 16
	xor s1, s1, t0
	srli t0, s2, 16
	xor t0, t0, s6
	and t0, t0, t4
	xor s6, s6, t0
	slli t0, t0, 16
	xor s2, s2, t0
	srli t0, s3, 16
	xor t0, t0, s7
	and t0, t0, t4
	xor s7, s7, t0
	slli t0, t0, 16
	xor s3, s3, t0
	srli t0, s0, 8
	xor t0, t0, s4
	and t0, t0, t5
	xor s4, s4, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s5
	and t0, t0, t5
	xor s5, s5, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s6
	and t0, t0, t5
	xor s6, s6, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s7
	and t0, t0, t5
	xor s7, s7, t0
	slli t0, t0, 8
	xor s3, s3, t0
	sd s0, 840(a5)
	sd s4, 968(a5)
	sd s1, 856(a5)
	sd s5, 984(a5)
	sd s2, 872(a5)
	sd s6, 1000(a5)
	sd s3, 888(a5)
	sd s7, 1016(a5)
	srli t0, a2, 4
	bnez t0, 215f
	addi a4, a2, 0
	j 216f
215:
	addi a4, zero, 16
216:
	addi t1, a5, 768
	addi t2, a1, 0
	slli t3, a4, 4
	or t4, t1, t2
	andi t4, t4, 7
	beqz t4, 217f
219:
	lbu t4, 0(t1)
	sb t4, 0(t2)
	addi t1, t1, 1
	addi t2, t2, 1
	addi t3, t3, -1
	bnez t3, 219b
	j 218f
217:
	srli t3, t3, 3
220:
	ld t4, 0(t1)
	sd t4, 0(t2)
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 220b
218:
	sub a2, a2, a4
	addi a1, a1, 256
	bnez a2, 27b
	j 26f
25:
26:
	addi t0, a5, 2040
	addi t0, t0, 1032
	ld s0, 0(t0)
	ld s1, 8(t0)
	ld s2, 16(t0)
	ld s3, 24(t0)
	ld s4, 32(t0)
	ld s5, 40(t0)
	ld s6, 48(t0)
	ld s7, 56(t0)
	ld s8, 64(t0)
	ld s9, 72(t0)
	ld s10, 80(t0)
	ld s11, 88(t0)
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
	addi t5, t5, 1024
	addi t5, t5, 1024
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
	addi sp, sp, 1136
	addi sp, sp, 2032
	addi t0, zero, 0
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
	addi a0, zero, 0
	ret
	.option pop
