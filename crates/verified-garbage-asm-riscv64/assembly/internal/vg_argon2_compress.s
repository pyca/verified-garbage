// The functions of `src/internal/vg_argon2_compress.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_argon2_compress:
	.option push
	.option arch, +m, +c
	addi t0, a3, 2040
	sd s0, 8(t0)
	sd s1, 16(t0)
	sd s2, 24(t0)
	sd s3, 32(t0)
	sd s4, 40(t0)
	ld t0, 0(a0)
	ld t1, 0(a1)
	xor t0, t0, t1
	sd t0, 0(a3)
	sd t0, 1024(a3)
	ld t0, 8(a0)
	ld t1, 8(a1)
	xor t0, t0, t1
	sd t0, 8(a3)
	sd t0, 1032(a3)
	ld t0, 16(a0)
	ld t1, 16(a1)
	xor t0, t0, t1
	sd t0, 16(a3)
	sd t0, 1040(a3)
	ld t0, 24(a0)
	ld t1, 24(a1)
	xor t0, t0, t1
	sd t0, 24(a3)
	sd t0, 1048(a3)
	ld t0, 32(a0)
	ld t1, 32(a1)
	xor t0, t0, t1
	sd t0, 32(a3)
	sd t0, 1056(a3)
	ld t0, 40(a0)
	ld t1, 40(a1)
	xor t0, t0, t1
	sd t0, 40(a3)
	sd t0, 1064(a3)
	ld t0, 48(a0)
	ld t1, 48(a1)
	xor t0, t0, t1
	sd t0, 48(a3)
	sd t0, 1072(a3)
	ld t0, 56(a0)
	ld t1, 56(a1)
	xor t0, t0, t1
	sd t0, 56(a3)
	sd t0, 1080(a3)
	ld t0, 64(a0)
	ld t1, 64(a1)
	xor t0, t0, t1
	sd t0, 64(a3)
	sd t0, 1088(a3)
	ld t0, 72(a0)
	ld t1, 72(a1)
	xor t0, t0, t1
	sd t0, 72(a3)
	sd t0, 1096(a3)
	ld t0, 80(a0)
	ld t1, 80(a1)
	xor t0, t0, t1
	sd t0, 80(a3)
	sd t0, 1104(a3)
	ld t0, 88(a0)
	ld t1, 88(a1)
	xor t0, t0, t1
	sd t0, 88(a3)
	sd t0, 1112(a3)
	ld t0, 96(a0)
	ld t1, 96(a1)
	xor t0, t0, t1
	sd t0, 96(a3)
	sd t0, 1120(a3)
	ld t0, 104(a0)
	ld t1, 104(a1)
	xor t0, t0, t1
	sd t0, 104(a3)
	sd t0, 1128(a3)
	ld t0, 112(a0)
	ld t1, 112(a1)
	xor t0, t0, t1
	sd t0, 112(a3)
	sd t0, 1136(a3)
	ld t0, 120(a0)
	ld t1, 120(a1)
	xor t0, t0, t1
	sd t0, 120(a3)
	sd t0, 1144(a3)
	ld t0, 128(a0)
	ld t1, 128(a1)
	xor t0, t0, t1
	sd t0, 128(a3)
	sd t0, 1152(a3)
	ld t0, 136(a0)
	ld t1, 136(a1)
	xor t0, t0, t1
	sd t0, 136(a3)
	sd t0, 1160(a3)
	ld t0, 144(a0)
	ld t1, 144(a1)
	xor t0, t0, t1
	sd t0, 144(a3)
	sd t0, 1168(a3)
	ld t0, 152(a0)
	ld t1, 152(a1)
	xor t0, t0, t1
	sd t0, 152(a3)
	sd t0, 1176(a3)
	ld t0, 160(a0)
	ld t1, 160(a1)
	xor t0, t0, t1
	sd t0, 160(a3)
	sd t0, 1184(a3)
	ld t0, 168(a0)
	ld t1, 168(a1)
	xor t0, t0, t1
	sd t0, 168(a3)
	sd t0, 1192(a3)
	ld t0, 176(a0)
	ld t1, 176(a1)
	xor t0, t0, t1
	sd t0, 176(a3)
	sd t0, 1200(a3)
	ld t0, 184(a0)
	ld t1, 184(a1)
	xor t0, t0, t1
	sd t0, 184(a3)
	sd t0, 1208(a3)
	ld t0, 192(a0)
	ld t1, 192(a1)
	xor t0, t0, t1
	sd t0, 192(a3)
	sd t0, 1216(a3)
	ld t0, 200(a0)
	ld t1, 200(a1)
	xor t0, t0, t1
	sd t0, 200(a3)
	sd t0, 1224(a3)
	ld t0, 208(a0)
	ld t1, 208(a1)
	xor t0, t0, t1
	sd t0, 208(a3)
	sd t0, 1232(a3)
	ld t0, 216(a0)
	ld t1, 216(a1)
	xor t0, t0, t1
	sd t0, 216(a3)
	sd t0, 1240(a3)
	ld t0, 224(a0)
	ld t1, 224(a1)
	xor t0, t0, t1
	sd t0, 224(a3)
	sd t0, 1248(a3)
	ld t0, 232(a0)
	ld t1, 232(a1)
	xor t0, t0, t1
	sd t0, 232(a3)
	sd t0, 1256(a3)
	ld t0, 240(a0)
	ld t1, 240(a1)
	xor t0, t0, t1
	sd t0, 240(a3)
	sd t0, 1264(a3)
	ld t0, 248(a0)
	ld t1, 248(a1)
	xor t0, t0, t1
	sd t0, 248(a3)
	sd t0, 1272(a3)
	ld t0, 256(a0)
	ld t1, 256(a1)
	xor t0, t0, t1
	sd t0, 256(a3)
	sd t0, 1280(a3)
	ld t0, 264(a0)
	ld t1, 264(a1)
	xor t0, t0, t1
	sd t0, 264(a3)
	sd t0, 1288(a3)
	ld t0, 272(a0)
	ld t1, 272(a1)
	xor t0, t0, t1
	sd t0, 272(a3)
	sd t0, 1296(a3)
	ld t0, 280(a0)
	ld t1, 280(a1)
	xor t0, t0, t1
	sd t0, 280(a3)
	sd t0, 1304(a3)
	ld t0, 288(a0)
	ld t1, 288(a1)
	xor t0, t0, t1
	sd t0, 288(a3)
	sd t0, 1312(a3)
	ld t0, 296(a0)
	ld t1, 296(a1)
	xor t0, t0, t1
	sd t0, 296(a3)
	sd t0, 1320(a3)
	ld t0, 304(a0)
	ld t1, 304(a1)
	xor t0, t0, t1
	sd t0, 304(a3)
	sd t0, 1328(a3)
	ld t0, 312(a0)
	ld t1, 312(a1)
	xor t0, t0, t1
	sd t0, 312(a3)
	sd t0, 1336(a3)
	ld t0, 320(a0)
	ld t1, 320(a1)
	xor t0, t0, t1
	sd t0, 320(a3)
	sd t0, 1344(a3)
	ld t0, 328(a0)
	ld t1, 328(a1)
	xor t0, t0, t1
	sd t0, 328(a3)
	sd t0, 1352(a3)
	ld t0, 336(a0)
	ld t1, 336(a1)
	xor t0, t0, t1
	sd t0, 336(a3)
	sd t0, 1360(a3)
	ld t0, 344(a0)
	ld t1, 344(a1)
	xor t0, t0, t1
	sd t0, 344(a3)
	sd t0, 1368(a3)
	ld t0, 352(a0)
	ld t1, 352(a1)
	xor t0, t0, t1
	sd t0, 352(a3)
	sd t0, 1376(a3)
	ld t0, 360(a0)
	ld t1, 360(a1)
	xor t0, t0, t1
	sd t0, 360(a3)
	sd t0, 1384(a3)
	ld t0, 368(a0)
	ld t1, 368(a1)
	xor t0, t0, t1
	sd t0, 368(a3)
	sd t0, 1392(a3)
	ld t0, 376(a0)
	ld t1, 376(a1)
	xor t0, t0, t1
	sd t0, 376(a3)
	sd t0, 1400(a3)
	ld t0, 384(a0)
	ld t1, 384(a1)
	xor t0, t0, t1
	sd t0, 384(a3)
	sd t0, 1408(a3)
	ld t0, 392(a0)
	ld t1, 392(a1)
	xor t0, t0, t1
	sd t0, 392(a3)
	sd t0, 1416(a3)
	ld t0, 400(a0)
	ld t1, 400(a1)
	xor t0, t0, t1
	sd t0, 400(a3)
	sd t0, 1424(a3)
	ld t0, 408(a0)
	ld t1, 408(a1)
	xor t0, t0, t1
	sd t0, 408(a3)
	sd t0, 1432(a3)
	ld t0, 416(a0)
	ld t1, 416(a1)
	xor t0, t0, t1
	sd t0, 416(a3)
	sd t0, 1440(a3)
	ld t0, 424(a0)
	ld t1, 424(a1)
	xor t0, t0, t1
	sd t0, 424(a3)
	sd t0, 1448(a3)
	ld t0, 432(a0)
	ld t1, 432(a1)
	xor t0, t0, t1
	sd t0, 432(a3)
	sd t0, 1456(a3)
	ld t0, 440(a0)
	ld t1, 440(a1)
	xor t0, t0, t1
	sd t0, 440(a3)
	sd t0, 1464(a3)
	ld t0, 448(a0)
	ld t1, 448(a1)
	xor t0, t0, t1
	sd t0, 448(a3)
	sd t0, 1472(a3)
	ld t0, 456(a0)
	ld t1, 456(a1)
	xor t0, t0, t1
	sd t0, 456(a3)
	sd t0, 1480(a3)
	ld t0, 464(a0)
	ld t1, 464(a1)
	xor t0, t0, t1
	sd t0, 464(a3)
	sd t0, 1488(a3)
	ld t0, 472(a0)
	ld t1, 472(a1)
	xor t0, t0, t1
	sd t0, 472(a3)
	sd t0, 1496(a3)
	ld t0, 480(a0)
	ld t1, 480(a1)
	xor t0, t0, t1
	sd t0, 480(a3)
	sd t0, 1504(a3)
	ld t0, 488(a0)
	ld t1, 488(a1)
	xor t0, t0, t1
	sd t0, 488(a3)
	sd t0, 1512(a3)
	ld t0, 496(a0)
	ld t1, 496(a1)
	xor t0, t0, t1
	sd t0, 496(a3)
	sd t0, 1520(a3)
	ld t0, 504(a0)
	ld t1, 504(a1)
	xor t0, t0, t1
	sd t0, 504(a3)
	sd t0, 1528(a3)
	ld t0, 512(a0)
	ld t1, 512(a1)
	xor t0, t0, t1
	sd t0, 512(a3)
	sd t0, 1536(a3)
	ld t0, 520(a0)
	ld t1, 520(a1)
	xor t0, t0, t1
	sd t0, 520(a3)
	sd t0, 1544(a3)
	ld t0, 528(a0)
	ld t1, 528(a1)
	xor t0, t0, t1
	sd t0, 528(a3)
	sd t0, 1552(a3)
	ld t0, 536(a0)
	ld t1, 536(a1)
	xor t0, t0, t1
	sd t0, 536(a3)
	sd t0, 1560(a3)
	ld t0, 544(a0)
	ld t1, 544(a1)
	xor t0, t0, t1
	sd t0, 544(a3)
	sd t0, 1568(a3)
	ld t0, 552(a0)
	ld t1, 552(a1)
	xor t0, t0, t1
	sd t0, 552(a3)
	sd t0, 1576(a3)
	ld t0, 560(a0)
	ld t1, 560(a1)
	xor t0, t0, t1
	sd t0, 560(a3)
	sd t0, 1584(a3)
	ld t0, 568(a0)
	ld t1, 568(a1)
	xor t0, t0, t1
	sd t0, 568(a3)
	sd t0, 1592(a3)
	ld t0, 576(a0)
	ld t1, 576(a1)
	xor t0, t0, t1
	sd t0, 576(a3)
	sd t0, 1600(a3)
	ld t0, 584(a0)
	ld t1, 584(a1)
	xor t0, t0, t1
	sd t0, 584(a3)
	sd t0, 1608(a3)
	ld t0, 592(a0)
	ld t1, 592(a1)
	xor t0, t0, t1
	sd t0, 592(a3)
	sd t0, 1616(a3)
	ld t0, 600(a0)
	ld t1, 600(a1)
	xor t0, t0, t1
	sd t0, 600(a3)
	sd t0, 1624(a3)
	ld t0, 608(a0)
	ld t1, 608(a1)
	xor t0, t0, t1
	sd t0, 608(a3)
	sd t0, 1632(a3)
	ld t0, 616(a0)
	ld t1, 616(a1)
	xor t0, t0, t1
	sd t0, 616(a3)
	sd t0, 1640(a3)
	ld t0, 624(a0)
	ld t1, 624(a1)
	xor t0, t0, t1
	sd t0, 624(a3)
	sd t0, 1648(a3)
	ld t0, 632(a0)
	ld t1, 632(a1)
	xor t0, t0, t1
	sd t0, 632(a3)
	sd t0, 1656(a3)
	ld t0, 640(a0)
	ld t1, 640(a1)
	xor t0, t0, t1
	sd t0, 640(a3)
	sd t0, 1664(a3)
	ld t0, 648(a0)
	ld t1, 648(a1)
	xor t0, t0, t1
	sd t0, 648(a3)
	sd t0, 1672(a3)
	ld t0, 656(a0)
	ld t1, 656(a1)
	xor t0, t0, t1
	sd t0, 656(a3)
	sd t0, 1680(a3)
	ld t0, 664(a0)
	ld t1, 664(a1)
	xor t0, t0, t1
	sd t0, 664(a3)
	sd t0, 1688(a3)
	ld t0, 672(a0)
	ld t1, 672(a1)
	xor t0, t0, t1
	sd t0, 672(a3)
	sd t0, 1696(a3)
	ld t0, 680(a0)
	ld t1, 680(a1)
	xor t0, t0, t1
	sd t0, 680(a3)
	sd t0, 1704(a3)
	ld t0, 688(a0)
	ld t1, 688(a1)
	xor t0, t0, t1
	sd t0, 688(a3)
	sd t0, 1712(a3)
	ld t0, 696(a0)
	ld t1, 696(a1)
	xor t0, t0, t1
	sd t0, 696(a3)
	sd t0, 1720(a3)
	ld t0, 704(a0)
	ld t1, 704(a1)
	xor t0, t0, t1
	sd t0, 704(a3)
	sd t0, 1728(a3)
	ld t0, 712(a0)
	ld t1, 712(a1)
	xor t0, t0, t1
	sd t0, 712(a3)
	sd t0, 1736(a3)
	ld t0, 720(a0)
	ld t1, 720(a1)
	xor t0, t0, t1
	sd t0, 720(a3)
	sd t0, 1744(a3)
	ld t0, 728(a0)
	ld t1, 728(a1)
	xor t0, t0, t1
	sd t0, 728(a3)
	sd t0, 1752(a3)
	ld t0, 736(a0)
	ld t1, 736(a1)
	xor t0, t0, t1
	sd t0, 736(a3)
	sd t0, 1760(a3)
	ld t0, 744(a0)
	ld t1, 744(a1)
	xor t0, t0, t1
	sd t0, 744(a3)
	sd t0, 1768(a3)
	ld t0, 752(a0)
	ld t1, 752(a1)
	xor t0, t0, t1
	sd t0, 752(a3)
	sd t0, 1776(a3)
	ld t0, 760(a0)
	ld t1, 760(a1)
	xor t0, t0, t1
	sd t0, 760(a3)
	sd t0, 1784(a3)
	ld t0, 768(a0)
	ld t1, 768(a1)
	xor t0, t0, t1
	sd t0, 768(a3)
	sd t0, 1792(a3)
	ld t0, 776(a0)
	ld t1, 776(a1)
	xor t0, t0, t1
	sd t0, 776(a3)
	sd t0, 1800(a3)
	ld t0, 784(a0)
	ld t1, 784(a1)
	xor t0, t0, t1
	sd t0, 784(a3)
	sd t0, 1808(a3)
	ld t0, 792(a0)
	ld t1, 792(a1)
	xor t0, t0, t1
	sd t0, 792(a3)
	sd t0, 1816(a3)
	ld t0, 800(a0)
	ld t1, 800(a1)
	xor t0, t0, t1
	sd t0, 800(a3)
	sd t0, 1824(a3)
	ld t0, 808(a0)
	ld t1, 808(a1)
	xor t0, t0, t1
	sd t0, 808(a3)
	sd t0, 1832(a3)
	ld t0, 816(a0)
	ld t1, 816(a1)
	xor t0, t0, t1
	sd t0, 816(a3)
	sd t0, 1840(a3)
	ld t0, 824(a0)
	ld t1, 824(a1)
	xor t0, t0, t1
	sd t0, 824(a3)
	sd t0, 1848(a3)
	ld t0, 832(a0)
	ld t1, 832(a1)
	xor t0, t0, t1
	sd t0, 832(a3)
	sd t0, 1856(a3)
	ld t0, 840(a0)
	ld t1, 840(a1)
	xor t0, t0, t1
	sd t0, 840(a3)
	sd t0, 1864(a3)
	ld t0, 848(a0)
	ld t1, 848(a1)
	xor t0, t0, t1
	sd t0, 848(a3)
	sd t0, 1872(a3)
	ld t0, 856(a0)
	ld t1, 856(a1)
	xor t0, t0, t1
	sd t0, 856(a3)
	sd t0, 1880(a3)
	ld t0, 864(a0)
	ld t1, 864(a1)
	xor t0, t0, t1
	sd t0, 864(a3)
	sd t0, 1888(a3)
	ld t0, 872(a0)
	ld t1, 872(a1)
	xor t0, t0, t1
	sd t0, 872(a3)
	sd t0, 1896(a3)
	ld t0, 880(a0)
	ld t1, 880(a1)
	xor t0, t0, t1
	sd t0, 880(a3)
	sd t0, 1904(a3)
	ld t0, 888(a0)
	ld t1, 888(a1)
	xor t0, t0, t1
	sd t0, 888(a3)
	sd t0, 1912(a3)
	ld t0, 896(a0)
	ld t1, 896(a1)
	xor t0, t0, t1
	sd t0, 896(a3)
	sd t0, 1920(a3)
	ld t0, 904(a0)
	ld t1, 904(a1)
	xor t0, t0, t1
	sd t0, 904(a3)
	sd t0, 1928(a3)
	ld t0, 912(a0)
	ld t1, 912(a1)
	xor t0, t0, t1
	sd t0, 912(a3)
	sd t0, 1936(a3)
	ld t0, 920(a0)
	ld t1, 920(a1)
	xor t0, t0, t1
	sd t0, 920(a3)
	sd t0, 1944(a3)
	ld t0, 928(a0)
	ld t1, 928(a1)
	xor t0, t0, t1
	sd t0, 928(a3)
	sd t0, 1952(a3)
	ld t0, 936(a0)
	ld t1, 936(a1)
	xor t0, t0, t1
	sd t0, 936(a3)
	sd t0, 1960(a3)
	ld t0, 944(a0)
	ld t1, 944(a1)
	xor t0, t0, t1
	sd t0, 944(a3)
	sd t0, 1968(a3)
	ld t0, 952(a0)
	ld t1, 952(a1)
	xor t0, t0, t1
	sd t0, 952(a3)
	sd t0, 1976(a3)
	ld t0, 960(a0)
	ld t1, 960(a1)
	xor t0, t0, t1
	sd t0, 960(a3)
	sd t0, 1984(a3)
	ld t0, 968(a0)
	ld t1, 968(a1)
	xor t0, t0, t1
	sd t0, 968(a3)
	sd t0, 1992(a3)
	ld t0, 976(a0)
	ld t1, 976(a1)
	xor t0, t0, t1
	sd t0, 976(a3)
	sd t0, 2000(a3)
	ld t0, 984(a0)
	ld t1, 984(a1)
	xor t0, t0, t1
	sd t0, 984(a3)
	sd t0, 2008(a3)
	ld t0, 992(a0)
	ld t1, 992(a1)
	xor t0, t0, t1
	sd t0, 992(a3)
	sd t0, 2016(a3)
	ld t0, 1000(a0)
	ld t1, 1000(a1)
	xor t0, t0, t1
	sd t0, 1000(a3)
	sd t0, 2024(a3)
	ld t0, 1008(a0)
	ld t1, 1008(a1)
	xor t0, t0, t1
	sd t0, 1008(a3)
	sd t0, 2032(a3)
	ld t0, 1016(a0)
	ld t1, 1016(a1)
	xor t0, t0, t1
	sd t0, 1016(a3)
	sd t0, 2040(a3)
	ld t0, 1024(a3)
	ld t1, 1032(a3)
	ld t2, 1040(a3)
	ld t3, 1048(a3)
	ld t4, 1056(a3)
	ld a0, 1064(a3)
	ld a1, 1072(a3)
	ld a4, 1080(a3)
	ld a5, 1088(a3)
	ld a6, 1096(a3)
	ld a7, 1104(a3)
	ld s0, 1112(a3)
	ld s1, 1120(a3)
	ld s2, 1128(a3)
	ld s3, 1136(a3)
	ld s4, 1144(a3)
	slli t5, t0, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t0, t0, t4
	add t0, t0, t5
	add t0, t0, t5
	xor s1, s1, t0
	srli t5, s1, 32
	slli s1, s1, 32
	or s1, s1, t5
	slli t5, a5, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add a5, a5, s1
	add a5, a5, t5
	add a5, a5, t5
	xor t4, t4, a5
	srli t5, t4, 24
	slli t4, t4, 40
	or t4, t4, t5
	slli t5, t0, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t0, t0, t4
	add t0, t0, t5
	add t0, t0, t5
	xor s1, s1, t0
	srli t5, s1, 16
	slli s1, s1, 48
	or s1, s1, t5
	slli t5, a5, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add a5, a5, s1
	add a5, a5, t5
	add a5, a5, t5
	xor t4, t4, a5
	srli t5, t4, 63
	slli t4, t4, 1
	or t4, t4, t5
	slli t5, t1, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t1, t1, a0
	add t1, t1, t5
	add t1, t1, t5
	xor s2, s2, t1
	srli t5, s2, 32
	slli s2, s2, 32
	or s2, s2, t5
	slli t5, a6, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a6, a6, s2
	add a6, a6, t5
	add a6, a6, t5
	xor a0, a0, a6
	srli t5, a0, 24
	slli a0, a0, 40
	or a0, a0, t5
	slli t5, t1, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t1, t1, a0
	add t1, t1, t5
	add t1, t1, t5
	xor s2, s2, t1
	srli t5, s2, 16
	slli s2, s2, 48
	or s2, s2, t5
	slli t5, a6, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a6, a6, s2
	add a6, a6, t5
	add a6, a6, t5
	xor a0, a0, a6
	srli t5, a0, 63
	slli a0, a0, 1
	or a0, a0, t5
	slli t5, t2, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t2, t2, a1
	add t2, t2, t5
	add t2, t2, t5
	xor s3, s3, t2
	srli t5, s3, 32
	slli s3, s3, 32
	or s3, s3, t5
	slli t5, a7, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a7, a7, s3
	add a7, a7, t5
	add a7, a7, t5
	xor a1, a1, a7
	srli t5, a1, 24
	slli a1, a1, 40
	or a1, a1, t5
	slli t5, t2, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t2, t2, a1
	add t2, t2, t5
	add t2, t2, t5
	xor s3, s3, t2
	srli t5, s3, 16
	slli s3, s3, 48
	or s3, s3, t5
	slli t5, a7, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a7, a7, s3
	add a7, a7, t5
	add a7, a7, t5
	xor a1, a1, a7
	srli t5, a1, 63
	slli a1, a1, 1
	or a1, a1, t5
	slli t5, t3, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t3, t3, a4
	add t3, t3, t5
	add t3, t3, t5
	xor s4, s4, t3
	srli t5, s4, 32
	slli s4, s4, 32
	or s4, s4, t5
	slli t5, s0, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add s0, s0, s4
	add s0, s0, t5
	add s0, s0, t5
	xor a4, a4, s0
	srli t5, a4, 24
	slli a4, a4, 40
	or a4, a4, t5
	slli t5, t3, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t3, t3, a4
	add t3, t3, t5
	add t3, t3, t5
	xor s4, s4, t3
	srli t5, s4, 16
	slli s4, s4, 48
	or s4, s4, t5
	slli t5, s0, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add s0, s0, s4
	add s0, s0, t5
	add s0, s0, t5
	xor a4, a4, s0
	srli t5, a4, 63
	slli a4, a4, 1
	or a4, a4, t5
	slli t5, t0, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t0, t0, a0
	add t0, t0, t5
	add t0, t0, t5
	xor s4, s4, t0
	srli t5, s4, 32
	slli s4, s4, 32
	or s4, s4, t5
	slli t5, a7, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add a7, a7, s4
	add a7, a7, t5
	add a7, a7, t5
	xor a0, a0, a7
	srli t5, a0, 24
	slli a0, a0, 40
	or a0, a0, t5
	slli t5, t0, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t0, t0, a0
	add t0, t0, t5
	add t0, t0, t5
	xor s4, s4, t0
	srli t5, s4, 16
	slli s4, s4, 48
	or s4, s4, t5
	slli t5, a7, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add a7, a7, s4
	add a7, a7, t5
	add a7, a7, t5
	xor a0, a0, a7
	srli t5, a0, 63
	slli a0, a0, 1
	or a0, a0, t5
	slli t5, t1, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t1, t1, a1
	add t1, t1, t5
	add t1, t1, t5
	xor s1, s1, t1
	srli t5, s1, 32
	slli s1, s1, 32
	or s1, s1, t5
	slli t5, s0, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add s0, s0, s1
	add s0, s0, t5
	add s0, s0, t5
	xor a1, a1, s0
	srli t5, a1, 24
	slli a1, a1, 40
	or a1, a1, t5
	slli t5, t1, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t1, t1, a1
	add t1, t1, t5
	add t1, t1, t5
	xor s1, s1, t1
	srli t5, s1, 16
	slli s1, s1, 48
	or s1, s1, t5
	slli t5, s0, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add s0, s0, s1
	add s0, s0, t5
	add s0, s0, t5
	xor a1, a1, s0
	srli t5, a1, 63
	slli a1, a1, 1
	or a1, a1, t5
	slli t5, t2, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t2, t2, a4
	add t2, t2, t5
	add t2, t2, t5
	xor s2, s2, t2
	srli t5, s2, 32
	slli s2, s2, 32
	or s2, s2, t5
	slli t5, a5, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a5, a5, s2
	add a5, a5, t5
	add a5, a5, t5
	xor a4, a4, a5
	srli t5, a4, 24
	slli a4, a4, 40
	or a4, a4, t5
	slli t5, t2, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t2, t2, a4
	add t2, t2, t5
	add t2, t2, t5
	xor s2, s2, t2
	srli t5, s2, 16
	slli s2, s2, 48
	or s2, s2, t5
	slli t5, a5, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a5, a5, s2
	add a5, a5, t5
	add a5, a5, t5
	xor a4, a4, a5
	srli t5, a4, 63
	slli a4, a4, 1
	or a4, a4, t5
	slli t5, t3, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t3, t3, t4
	add t3, t3, t5
	add t3, t3, t5
	xor s3, s3, t3
	srli t5, s3, 32
	slli s3, s3, 32
	or s3, s3, t5
	slli t5, a6, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a6, a6, s3
	add a6, a6, t5
	add a6, a6, t5
	xor t4, t4, a6
	srli t5, t4, 24
	slli t4, t4, 40
	or t4, t4, t5
	slli t5, t3, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t3, t3, t4
	add t3, t3, t5
	add t3, t3, t5
	xor s3, s3, t3
	srli t5, s3, 16
	slli s3, s3, 48
	or s3, s3, t5
	slli t5, a6, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a6, a6, s3
	add a6, a6, t5
	add a6, a6, t5
	xor t4, t4, a6
	srli t5, t4, 63
	slli t4, t4, 1
	or t4, t4, t5
	sd t0, 1024(a3)
	sd t1, 1032(a3)
	sd t2, 1040(a3)
	sd t3, 1048(a3)
	sd t4, 1056(a3)
	sd a0, 1064(a3)
	sd a1, 1072(a3)
	sd a4, 1080(a3)
	sd a5, 1088(a3)
	sd a6, 1096(a3)
	sd a7, 1104(a3)
	sd s0, 1112(a3)
	sd s1, 1120(a3)
	sd s2, 1128(a3)
	sd s3, 1136(a3)
	sd s4, 1144(a3)
	ld t0, 1152(a3)
	ld t1, 1160(a3)
	ld t2, 1168(a3)
	ld t3, 1176(a3)
	ld t4, 1184(a3)
	ld a0, 1192(a3)
	ld a1, 1200(a3)
	ld a4, 1208(a3)
	ld a5, 1216(a3)
	ld a6, 1224(a3)
	ld a7, 1232(a3)
	ld s0, 1240(a3)
	ld s1, 1248(a3)
	ld s2, 1256(a3)
	ld s3, 1264(a3)
	ld s4, 1272(a3)
	slli t5, t0, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t0, t0, t4
	add t0, t0, t5
	add t0, t0, t5
	xor s1, s1, t0
	srli t5, s1, 32
	slli s1, s1, 32
	or s1, s1, t5
	slli t5, a5, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add a5, a5, s1
	add a5, a5, t5
	add a5, a5, t5
	xor t4, t4, a5
	srli t5, t4, 24
	slli t4, t4, 40
	or t4, t4, t5
	slli t5, t0, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t0, t0, t4
	add t0, t0, t5
	add t0, t0, t5
	xor s1, s1, t0
	srli t5, s1, 16
	slli s1, s1, 48
	or s1, s1, t5
	slli t5, a5, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add a5, a5, s1
	add a5, a5, t5
	add a5, a5, t5
	xor t4, t4, a5
	srli t5, t4, 63
	slli t4, t4, 1
	or t4, t4, t5
	slli t5, t1, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t1, t1, a0
	add t1, t1, t5
	add t1, t1, t5
	xor s2, s2, t1
	srli t5, s2, 32
	slli s2, s2, 32
	or s2, s2, t5
	slli t5, a6, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a6, a6, s2
	add a6, a6, t5
	add a6, a6, t5
	xor a0, a0, a6
	srli t5, a0, 24
	slli a0, a0, 40
	or a0, a0, t5
	slli t5, t1, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t1, t1, a0
	add t1, t1, t5
	add t1, t1, t5
	xor s2, s2, t1
	srli t5, s2, 16
	slli s2, s2, 48
	or s2, s2, t5
	slli t5, a6, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a6, a6, s2
	add a6, a6, t5
	add a6, a6, t5
	xor a0, a0, a6
	srli t5, a0, 63
	slli a0, a0, 1
	or a0, a0, t5
	slli t5, t2, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t2, t2, a1
	add t2, t2, t5
	add t2, t2, t5
	xor s3, s3, t2
	srli t5, s3, 32
	slli s3, s3, 32
	or s3, s3, t5
	slli t5, a7, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a7, a7, s3
	add a7, a7, t5
	add a7, a7, t5
	xor a1, a1, a7
	srli t5, a1, 24
	slli a1, a1, 40
	or a1, a1, t5
	slli t5, t2, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t2, t2, a1
	add t2, t2, t5
	add t2, t2, t5
	xor s3, s3, t2
	srli t5, s3, 16
	slli s3, s3, 48
	or s3, s3, t5
	slli t5, a7, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a7, a7, s3
	add a7, a7, t5
	add a7, a7, t5
	xor a1, a1, a7
	srli t5, a1, 63
	slli a1, a1, 1
	or a1, a1, t5
	slli t5, t3, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t3, t3, a4
	add t3, t3, t5
	add t3, t3, t5
	xor s4, s4, t3
	srli t5, s4, 32
	slli s4, s4, 32
	or s4, s4, t5
	slli t5, s0, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add s0, s0, s4
	add s0, s0, t5
	add s0, s0, t5
	xor a4, a4, s0
	srli t5, a4, 24
	slli a4, a4, 40
	or a4, a4, t5
	slli t5, t3, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t3, t3, a4
	add t3, t3, t5
	add t3, t3, t5
	xor s4, s4, t3
	srli t5, s4, 16
	slli s4, s4, 48
	or s4, s4, t5
	slli t5, s0, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add s0, s0, s4
	add s0, s0, t5
	add s0, s0, t5
	xor a4, a4, s0
	srli t5, a4, 63
	slli a4, a4, 1
	or a4, a4, t5
	slli t5, t0, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t0, t0, a0
	add t0, t0, t5
	add t0, t0, t5
	xor s4, s4, t0
	srli t5, s4, 32
	slli s4, s4, 32
	or s4, s4, t5
	slli t5, a7, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add a7, a7, s4
	add a7, a7, t5
	add a7, a7, t5
	xor a0, a0, a7
	srli t5, a0, 24
	slli a0, a0, 40
	or a0, a0, t5
	slli t5, t0, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t0, t0, a0
	add t0, t0, t5
	add t0, t0, t5
	xor s4, s4, t0
	srli t5, s4, 16
	slli s4, s4, 48
	or s4, s4, t5
	slli t5, a7, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add a7, a7, s4
	add a7, a7, t5
	add a7, a7, t5
	xor a0, a0, a7
	srli t5, a0, 63
	slli a0, a0, 1
	or a0, a0, t5
	slli t5, t1, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t1, t1, a1
	add t1, t1, t5
	add t1, t1, t5
	xor s1, s1, t1
	srli t5, s1, 32
	slli s1, s1, 32
	or s1, s1, t5
	slli t5, s0, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add s0, s0, s1
	add s0, s0, t5
	add s0, s0, t5
	xor a1, a1, s0
	srli t5, a1, 24
	slli a1, a1, 40
	or a1, a1, t5
	slli t5, t1, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t1, t1, a1
	add t1, t1, t5
	add t1, t1, t5
	xor s1, s1, t1
	srli t5, s1, 16
	slli s1, s1, 48
	or s1, s1, t5
	slli t5, s0, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add s0, s0, s1
	add s0, s0, t5
	add s0, s0, t5
	xor a1, a1, s0
	srli t5, a1, 63
	slli a1, a1, 1
	or a1, a1, t5
	slli t5, t2, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t2, t2, a4
	add t2, t2, t5
	add t2, t2, t5
	xor s2, s2, t2
	srli t5, s2, 32
	slli s2, s2, 32
	or s2, s2, t5
	slli t5, a5, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a5, a5, s2
	add a5, a5, t5
	add a5, a5, t5
	xor a4, a4, a5
	srli t5, a4, 24
	slli a4, a4, 40
	or a4, a4, t5
	slli t5, t2, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t2, t2, a4
	add t2, t2, t5
	add t2, t2, t5
	xor s2, s2, t2
	srli t5, s2, 16
	slli s2, s2, 48
	or s2, s2, t5
	slli t5, a5, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a5, a5, s2
	add a5, a5, t5
	add a5, a5, t5
	xor a4, a4, a5
	srli t5, a4, 63
	slli a4, a4, 1
	or a4, a4, t5
	slli t5, t3, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t3, t3, t4
	add t3, t3, t5
	add t3, t3, t5
	xor s3, s3, t3
	srli t5, s3, 32
	slli s3, s3, 32
	or s3, s3, t5
	slli t5, a6, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a6, a6, s3
	add a6, a6, t5
	add a6, a6, t5
	xor t4, t4, a6
	srli t5, t4, 24
	slli t4, t4, 40
	or t4, t4, t5
	slli t5, t3, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t3, t3, t4
	add t3, t3, t5
	add t3, t3, t5
	xor s3, s3, t3
	srli t5, s3, 16
	slli s3, s3, 48
	or s3, s3, t5
	slli t5, a6, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a6, a6, s3
	add a6, a6, t5
	add a6, a6, t5
	xor t4, t4, a6
	srli t5, t4, 63
	slli t4, t4, 1
	or t4, t4, t5
	sd t0, 1152(a3)
	sd t1, 1160(a3)
	sd t2, 1168(a3)
	sd t3, 1176(a3)
	sd t4, 1184(a3)
	sd a0, 1192(a3)
	sd a1, 1200(a3)
	sd a4, 1208(a3)
	sd a5, 1216(a3)
	sd a6, 1224(a3)
	sd a7, 1232(a3)
	sd s0, 1240(a3)
	sd s1, 1248(a3)
	sd s2, 1256(a3)
	sd s3, 1264(a3)
	sd s4, 1272(a3)
	ld t0, 1280(a3)
	ld t1, 1288(a3)
	ld t2, 1296(a3)
	ld t3, 1304(a3)
	ld t4, 1312(a3)
	ld a0, 1320(a3)
	ld a1, 1328(a3)
	ld a4, 1336(a3)
	ld a5, 1344(a3)
	ld a6, 1352(a3)
	ld a7, 1360(a3)
	ld s0, 1368(a3)
	ld s1, 1376(a3)
	ld s2, 1384(a3)
	ld s3, 1392(a3)
	ld s4, 1400(a3)
	slli t5, t0, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t0, t0, t4
	add t0, t0, t5
	add t0, t0, t5
	xor s1, s1, t0
	srli t5, s1, 32
	slli s1, s1, 32
	or s1, s1, t5
	slli t5, a5, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add a5, a5, s1
	add a5, a5, t5
	add a5, a5, t5
	xor t4, t4, a5
	srli t5, t4, 24
	slli t4, t4, 40
	or t4, t4, t5
	slli t5, t0, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t0, t0, t4
	add t0, t0, t5
	add t0, t0, t5
	xor s1, s1, t0
	srli t5, s1, 16
	slli s1, s1, 48
	or s1, s1, t5
	slli t5, a5, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add a5, a5, s1
	add a5, a5, t5
	add a5, a5, t5
	xor t4, t4, a5
	srli t5, t4, 63
	slli t4, t4, 1
	or t4, t4, t5
	slli t5, t1, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t1, t1, a0
	add t1, t1, t5
	add t1, t1, t5
	xor s2, s2, t1
	srli t5, s2, 32
	slli s2, s2, 32
	or s2, s2, t5
	slli t5, a6, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a6, a6, s2
	add a6, a6, t5
	add a6, a6, t5
	xor a0, a0, a6
	srli t5, a0, 24
	slli a0, a0, 40
	or a0, a0, t5
	slli t5, t1, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t1, t1, a0
	add t1, t1, t5
	add t1, t1, t5
	xor s2, s2, t1
	srli t5, s2, 16
	slli s2, s2, 48
	or s2, s2, t5
	slli t5, a6, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a6, a6, s2
	add a6, a6, t5
	add a6, a6, t5
	xor a0, a0, a6
	srli t5, a0, 63
	slli a0, a0, 1
	or a0, a0, t5
	slli t5, t2, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t2, t2, a1
	add t2, t2, t5
	add t2, t2, t5
	xor s3, s3, t2
	srli t5, s3, 32
	slli s3, s3, 32
	or s3, s3, t5
	slli t5, a7, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a7, a7, s3
	add a7, a7, t5
	add a7, a7, t5
	xor a1, a1, a7
	srli t5, a1, 24
	slli a1, a1, 40
	or a1, a1, t5
	slli t5, t2, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t2, t2, a1
	add t2, t2, t5
	add t2, t2, t5
	xor s3, s3, t2
	srli t5, s3, 16
	slli s3, s3, 48
	or s3, s3, t5
	slli t5, a7, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a7, a7, s3
	add a7, a7, t5
	add a7, a7, t5
	xor a1, a1, a7
	srli t5, a1, 63
	slli a1, a1, 1
	or a1, a1, t5
	slli t5, t3, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t3, t3, a4
	add t3, t3, t5
	add t3, t3, t5
	xor s4, s4, t3
	srli t5, s4, 32
	slli s4, s4, 32
	or s4, s4, t5
	slli t5, s0, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add s0, s0, s4
	add s0, s0, t5
	add s0, s0, t5
	xor a4, a4, s0
	srli t5, a4, 24
	slli a4, a4, 40
	or a4, a4, t5
	slli t5, t3, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t3, t3, a4
	add t3, t3, t5
	add t3, t3, t5
	xor s4, s4, t3
	srli t5, s4, 16
	slli s4, s4, 48
	or s4, s4, t5
	slli t5, s0, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add s0, s0, s4
	add s0, s0, t5
	add s0, s0, t5
	xor a4, a4, s0
	srli t5, a4, 63
	slli a4, a4, 1
	or a4, a4, t5
	slli t5, t0, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t0, t0, a0
	add t0, t0, t5
	add t0, t0, t5
	xor s4, s4, t0
	srli t5, s4, 32
	slli s4, s4, 32
	or s4, s4, t5
	slli t5, a7, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add a7, a7, s4
	add a7, a7, t5
	add a7, a7, t5
	xor a0, a0, a7
	srli t5, a0, 24
	slli a0, a0, 40
	or a0, a0, t5
	slli t5, t0, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t0, t0, a0
	add t0, t0, t5
	add t0, t0, t5
	xor s4, s4, t0
	srli t5, s4, 16
	slli s4, s4, 48
	or s4, s4, t5
	slli t5, a7, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add a7, a7, s4
	add a7, a7, t5
	add a7, a7, t5
	xor a0, a0, a7
	srli t5, a0, 63
	slli a0, a0, 1
	or a0, a0, t5
	slli t5, t1, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t1, t1, a1
	add t1, t1, t5
	add t1, t1, t5
	xor s1, s1, t1
	srli t5, s1, 32
	slli s1, s1, 32
	or s1, s1, t5
	slli t5, s0, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add s0, s0, s1
	add s0, s0, t5
	add s0, s0, t5
	xor a1, a1, s0
	srli t5, a1, 24
	slli a1, a1, 40
	or a1, a1, t5
	slli t5, t1, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t1, t1, a1
	add t1, t1, t5
	add t1, t1, t5
	xor s1, s1, t1
	srli t5, s1, 16
	slli s1, s1, 48
	or s1, s1, t5
	slli t5, s0, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add s0, s0, s1
	add s0, s0, t5
	add s0, s0, t5
	xor a1, a1, s0
	srli t5, a1, 63
	slli a1, a1, 1
	or a1, a1, t5
	slli t5, t2, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t2, t2, a4
	add t2, t2, t5
	add t2, t2, t5
	xor s2, s2, t2
	srli t5, s2, 32
	slli s2, s2, 32
	or s2, s2, t5
	slli t5, a5, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a5, a5, s2
	add a5, a5, t5
	add a5, a5, t5
	xor a4, a4, a5
	srli t5, a4, 24
	slli a4, a4, 40
	or a4, a4, t5
	slli t5, t2, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t2, t2, a4
	add t2, t2, t5
	add t2, t2, t5
	xor s2, s2, t2
	srli t5, s2, 16
	slli s2, s2, 48
	or s2, s2, t5
	slli t5, a5, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a5, a5, s2
	add a5, a5, t5
	add a5, a5, t5
	xor a4, a4, a5
	srli t5, a4, 63
	slli a4, a4, 1
	or a4, a4, t5
	slli t5, t3, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t3, t3, t4
	add t3, t3, t5
	add t3, t3, t5
	xor s3, s3, t3
	srli t5, s3, 32
	slli s3, s3, 32
	or s3, s3, t5
	slli t5, a6, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a6, a6, s3
	add a6, a6, t5
	add a6, a6, t5
	xor t4, t4, a6
	srli t5, t4, 24
	slli t4, t4, 40
	or t4, t4, t5
	slli t5, t3, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t3, t3, t4
	add t3, t3, t5
	add t3, t3, t5
	xor s3, s3, t3
	srli t5, s3, 16
	slli s3, s3, 48
	or s3, s3, t5
	slli t5, a6, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a6, a6, s3
	add a6, a6, t5
	add a6, a6, t5
	xor t4, t4, a6
	srli t5, t4, 63
	slli t4, t4, 1
	or t4, t4, t5
	sd t0, 1280(a3)
	sd t1, 1288(a3)
	sd t2, 1296(a3)
	sd t3, 1304(a3)
	sd t4, 1312(a3)
	sd a0, 1320(a3)
	sd a1, 1328(a3)
	sd a4, 1336(a3)
	sd a5, 1344(a3)
	sd a6, 1352(a3)
	sd a7, 1360(a3)
	sd s0, 1368(a3)
	sd s1, 1376(a3)
	sd s2, 1384(a3)
	sd s3, 1392(a3)
	sd s4, 1400(a3)
	ld t0, 1408(a3)
	ld t1, 1416(a3)
	ld t2, 1424(a3)
	ld t3, 1432(a3)
	ld t4, 1440(a3)
	ld a0, 1448(a3)
	ld a1, 1456(a3)
	ld a4, 1464(a3)
	ld a5, 1472(a3)
	ld a6, 1480(a3)
	ld a7, 1488(a3)
	ld s0, 1496(a3)
	ld s1, 1504(a3)
	ld s2, 1512(a3)
	ld s3, 1520(a3)
	ld s4, 1528(a3)
	slli t5, t0, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t0, t0, t4
	add t0, t0, t5
	add t0, t0, t5
	xor s1, s1, t0
	srli t5, s1, 32
	slli s1, s1, 32
	or s1, s1, t5
	slli t5, a5, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add a5, a5, s1
	add a5, a5, t5
	add a5, a5, t5
	xor t4, t4, a5
	srli t5, t4, 24
	slli t4, t4, 40
	or t4, t4, t5
	slli t5, t0, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t0, t0, t4
	add t0, t0, t5
	add t0, t0, t5
	xor s1, s1, t0
	srli t5, s1, 16
	slli s1, s1, 48
	or s1, s1, t5
	slli t5, a5, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add a5, a5, s1
	add a5, a5, t5
	add a5, a5, t5
	xor t4, t4, a5
	srli t5, t4, 63
	slli t4, t4, 1
	or t4, t4, t5
	slli t5, t1, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t1, t1, a0
	add t1, t1, t5
	add t1, t1, t5
	xor s2, s2, t1
	srli t5, s2, 32
	slli s2, s2, 32
	or s2, s2, t5
	slli t5, a6, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a6, a6, s2
	add a6, a6, t5
	add a6, a6, t5
	xor a0, a0, a6
	srli t5, a0, 24
	slli a0, a0, 40
	or a0, a0, t5
	slli t5, t1, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t1, t1, a0
	add t1, t1, t5
	add t1, t1, t5
	xor s2, s2, t1
	srli t5, s2, 16
	slli s2, s2, 48
	or s2, s2, t5
	slli t5, a6, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a6, a6, s2
	add a6, a6, t5
	add a6, a6, t5
	xor a0, a0, a6
	srli t5, a0, 63
	slli a0, a0, 1
	or a0, a0, t5
	slli t5, t2, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t2, t2, a1
	add t2, t2, t5
	add t2, t2, t5
	xor s3, s3, t2
	srli t5, s3, 32
	slli s3, s3, 32
	or s3, s3, t5
	slli t5, a7, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a7, a7, s3
	add a7, a7, t5
	add a7, a7, t5
	xor a1, a1, a7
	srli t5, a1, 24
	slli a1, a1, 40
	or a1, a1, t5
	slli t5, t2, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t2, t2, a1
	add t2, t2, t5
	add t2, t2, t5
	xor s3, s3, t2
	srli t5, s3, 16
	slli s3, s3, 48
	or s3, s3, t5
	slli t5, a7, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a7, a7, s3
	add a7, a7, t5
	add a7, a7, t5
	xor a1, a1, a7
	srli t5, a1, 63
	slli a1, a1, 1
	or a1, a1, t5
	slli t5, t3, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t3, t3, a4
	add t3, t3, t5
	add t3, t3, t5
	xor s4, s4, t3
	srli t5, s4, 32
	slli s4, s4, 32
	or s4, s4, t5
	slli t5, s0, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add s0, s0, s4
	add s0, s0, t5
	add s0, s0, t5
	xor a4, a4, s0
	srli t5, a4, 24
	slli a4, a4, 40
	or a4, a4, t5
	slli t5, t3, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t3, t3, a4
	add t3, t3, t5
	add t3, t3, t5
	xor s4, s4, t3
	srli t5, s4, 16
	slli s4, s4, 48
	or s4, s4, t5
	slli t5, s0, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add s0, s0, s4
	add s0, s0, t5
	add s0, s0, t5
	xor a4, a4, s0
	srli t5, a4, 63
	slli a4, a4, 1
	or a4, a4, t5
	slli t5, t0, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t0, t0, a0
	add t0, t0, t5
	add t0, t0, t5
	xor s4, s4, t0
	srli t5, s4, 32
	slli s4, s4, 32
	or s4, s4, t5
	slli t5, a7, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add a7, a7, s4
	add a7, a7, t5
	add a7, a7, t5
	xor a0, a0, a7
	srli t5, a0, 24
	slli a0, a0, 40
	or a0, a0, t5
	slli t5, t0, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t0, t0, a0
	add t0, t0, t5
	add t0, t0, t5
	xor s4, s4, t0
	srli t5, s4, 16
	slli s4, s4, 48
	or s4, s4, t5
	slli t5, a7, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add a7, a7, s4
	add a7, a7, t5
	add a7, a7, t5
	xor a0, a0, a7
	srli t5, a0, 63
	slli a0, a0, 1
	or a0, a0, t5
	slli t5, t1, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t1, t1, a1
	add t1, t1, t5
	add t1, t1, t5
	xor s1, s1, t1
	srli t5, s1, 32
	slli s1, s1, 32
	or s1, s1, t5
	slli t5, s0, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add s0, s0, s1
	add s0, s0, t5
	add s0, s0, t5
	xor a1, a1, s0
	srli t5, a1, 24
	slli a1, a1, 40
	or a1, a1, t5
	slli t5, t1, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t1, t1, a1
	add t1, t1, t5
	add t1, t1, t5
	xor s1, s1, t1
	srli t5, s1, 16
	slli s1, s1, 48
	or s1, s1, t5
	slli t5, s0, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add s0, s0, s1
	add s0, s0, t5
	add s0, s0, t5
	xor a1, a1, s0
	srli t5, a1, 63
	slli a1, a1, 1
	or a1, a1, t5
	slli t5, t2, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t2, t2, a4
	add t2, t2, t5
	add t2, t2, t5
	xor s2, s2, t2
	srli t5, s2, 32
	slli s2, s2, 32
	or s2, s2, t5
	slli t5, a5, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a5, a5, s2
	add a5, a5, t5
	add a5, a5, t5
	xor a4, a4, a5
	srli t5, a4, 24
	slli a4, a4, 40
	or a4, a4, t5
	slli t5, t2, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t2, t2, a4
	add t2, t2, t5
	add t2, t2, t5
	xor s2, s2, t2
	srli t5, s2, 16
	slli s2, s2, 48
	or s2, s2, t5
	slli t5, a5, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a5, a5, s2
	add a5, a5, t5
	add a5, a5, t5
	xor a4, a4, a5
	srli t5, a4, 63
	slli a4, a4, 1
	or a4, a4, t5
	slli t5, t3, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t3, t3, t4
	add t3, t3, t5
	add t3, t3, t5
	xor s3, s3, t3
	srli t5, s3, 32
	slli s3, s3, 32
	or s3, s3, t5
	slli t5, a6, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a6, a6, s3
	add a6, a6, t5
	add a6, a6, t5
	xor t4, t4, a6
	srli t5, t4, 24
	slli t4, t4, 40
	or t4, t4, t5
	slli t5, t3, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t3, t3, t4
	add t3, t3, t5
	add t3, t3, t5
	xor s3, s3, t3
	srli t5, s3, 16
	slli s3, s3, 48
	or s3, s3, t5
	slli t5, a6, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a6, a6, s3
	add a6, a6, t5
	add a6, a6, t5
	xor t4, t4, a6
	srli t5, t4, 63
	slli t4, t4, 1
	or t4, t4, t5
	sd t0, 1408(a3)
	sd t1, 1416(a3)
	sd t2, 1424(a3)
	sd t3, 1432(a3)
	sd t4, 1440(a3)
	sd a0, 1448(a3)
	sd a1, 1456(a3)
	sd a4, 1464(a3)
	sd a5, 1472(a3)
	sd a6, 1480(a3)
	sd a7, 1488(a3)
	sd s0, 1496(a3)
	sd s1, 1504(a3)
	sd s2, 1512(a3)
	sd s3, 1520(a3)
	sd s4, 1528(a3)
	ld t0, 1536(a3)
	ld t1, 1544(a3)
	ld t2, 1552(a3)
	ld t3, 1560(a3)
	ld t4, 1568(a3)
	ld a0, 1576(a3)
	ld a1, 1584(a3)
	ld a4, 1592(a3)
	ld a5, 1600(a3)
	ld a6, 1608(a3)
	ld a7, 1616(a3)
	ld s0, 1624(a3)
	ld s1, 1632(a3)
	ld s2, 1640(a3)
	ld s3, 1648(a3)
	ld s4, 1656(a3)
	slli t5, t0, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t0, t0, t4
	add t0, t0, t5
	add t0, t0, t5
	xor s1, s1, t0
	srli t5, s1, 32
	slli s1, s1, 32
	or s1, s1, t5
	slli t5, a5, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add a5, a5, s1
	add a5, a5, t5
	add a5, a5, t5
	xor t4, t4, a5
	srli t5, t4, 24
	slli t4, t4, 40
	or t4, t4, t5
	slli t5, t0, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t0, t0, t4
	add t0, t0, t5
	add t0, t0, t5
	xor s1, s1, t0
	srli t5, s1, 16
	slli s1, s1, 48
	or s1, s1, t5
	slli t5, a5, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add a5, a5, s1
	add a5, a5, t5
	add a5, a5, t5
	xor t4, t4, a5
	srli t5, t4, 63
	slli t4, t4, 1
	or t4, t4, t5
	slli t5, t1, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t1, t1, a0
	add t1, t1, t5
	add t1, t1, t5
	xor s2, s2, t1
	srli t5, s2, 32
	slli s2, s2, 32
	or s2, s2, t5
	slli t5, a6, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a6, a6, s2
	add a6, a6, t5
	add a6, a6, t5
	xor a0, a0, a6
	srli t5, a0, 24
	slli a0, a0, 40
	or a0, a0, t5
	slli t5, t1, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t1, t1, a0
	add t1, t1, t5
	add t1, t1, t5
	xor s2, s2, t1
	srli t5, s2, 16
	slli s2, s2, 48
	or s2, s2, t5
	slli t5, a6, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a6, a6, s2
	add a6, a6, t5
	add a6, a6, t5
	xor a0, a0, a6
	srli t5, a0, 63
	slli a0, a0, 1
	or a0, a0, t5
	slli t5, t2, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t2, t2, a1
	add t2, t2, t5
	add t2, t2, t5
	xor s3, s3, t2
	srli t5, s3, 32
	slli s3, s3, 32
	or s3, s3, t5
	slli t5, a7, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a7, a7, s3
	add a7, a7, t5
	add a7, a7, t5
	xor a1, a1, a7
	srli t5, a1, 24
	slli a1, a1, 40
	or a1, a1, t5
	slli t5, t2, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t2, t2, a1
	add t2, t2, t5
	add t2, t2, t5
	xor s3, s3, t2
	srli t5, s3, 16
	slli s3, s3, 48
	or s3, s3, t5
	slli t5, a7, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a7, a7, s3
	add a7, a7, t5
	add a7, a7, t5
	xor a1, a1, a7
	srli t5, a1, 63
	slli a1, a1, 1
	or a1, a1, t5
	slli t5, t3, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t3, t3, a4
	add t3, t3, t5
	add t3, t3, t5
	xor s4, s4, t3
	srli t5, s4, 32
	slli s4, s4, 32
	or s4, s4, t5
	slli t5, s0, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add s0, s0, s4
	add s0, s0, t5
	add s0, s0, t5
	xor a4, a4, s0
	srli t5, a4, 24
	slli a4, a4, 40
	or a4, a4, t5
	slli t5, t3, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t3, t3, a4
	add t3, t3, t5
	add t3, t3, t5
	xor s4, s4, t3
	srli t5, s4, 16
	slli s4, s4, 48
	or s4, s4, t5
	slli t5, s0, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add s0, s0, s4
	add s0, s0, t5
	add s0, s0, t5
	xor a4, a4, s0
	srli t5, a4, 63
	slli a4, a4, 1
	or a4, a4, t5
	slli t5, t0, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t0, t0, a0
	add t0, t0, t5
	add t0, t0, t5
	xor s4, s4, t0
	srli t5, s4, 32
	slli s4, s4, 32
	or s4, s4, t5
	slli t5, a7, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add a7, a7, s4
	add a7, a7, t5
	add a7, a7, t5
	xor a0, a0, a7
	srli t5, a0, 24
	slli a0, a0, 40
	or a0, a0, t5
	slli t5, t0, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t0, t0, a0
	add t0, t0, t5
	add t0, t0, t5
	xor s4, s4, t0
	srli t5, s4, 16
	slli s4, s4, 48
	or s4, s4, t5
	slli t5, a7, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add a7, a7, s4
	add a7, a7, t5
	add a7, a7, t5
	xor a0, a0, a7
	srli t5, a0, 63
	slli a0, a0, 1
	or a0, a0, t5
	slli t5, t1, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t1, t1, a1
	add t1, t1, t5
	add t1, t1, t5
	xor s1, s1, t1
	srli t5, s1, 32
	slli s1, s1, 32
	or s1, s1, t5
	slli t5, s0, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add s0, s0, s1
	add s0, s0, t5
	add s0, s0, t5
	xor a1, a1, s0
	srli t5, a1, 24
	slli a1, a1, 40
	or a1, a1, t5
	slli t5, t1, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t1, t1, a1
	add t1, t1, t5
	add t1, t1, t5
	xor s1, s1, t1
	srli t5, s1, 16
	slli s1, s1, 48
	or s1, s1, t5
	slli t5, s0, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add s0, s0, s1
	add s0, s0, t5
	add s0, s0, t5
	xor a1, a1, s0
	srli t5, a1, 63
	slli a1, a1, 1
	or a1, a1, t5
	slli t5, t2, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t2, t2, a4
	add t2, t2, t5
	add t2, t2, t5
	xor s2, s2, t2
	srli t5, s2, 32
	slli s2, s2, 32
	or s2, s2, t5
	slli t5, a5, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a5, a5, s2
	add a5, a5, t5
	add a5, a5, t5
	xor a4, a4, a5
	srli t5, a4, 24
	slli a4, a4, 40
	or a4, a4, t5
	slli t5, t2, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t2, t2, a4
	add t2, t2, t5
	add t2, t2, t5
	xor s2, s2, t2
	srli t5, s2, 16
	slli s2, s2, 48
	or s2, s2, t5
	slli t5, a5, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a5, a5, s2
	add a5, a5, t5
	add a5, a5, t5
	xor a4, a4, a5
	srli t5, a4, 63
	slli a4, a4, 1
	or a4, a4, t5
	slli t5, t3, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t3, t3, t4
	add t3, t3, t5
	add t3, t3, t5
	xor s3, s3, t3
	srli t5, s3, 32
	slli s3, s3, 32
	or s3, s3, t5
	slli t5, a6, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a6, a6, s3
	add a6, a6, t5
	add a6, a6, t5
	xor t4, t4, a6
	srli t5, t4, 24
	slli t4, t4, 40
	or t4, t4, t5
	slli t5, t3, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t3, t3, t4
	add t3, t3, t5
	add t3, t3, t5
	xor s3, s3, t3
	srli t5, s3, 16
	slli s3, s3, 48
	or s3, s3, t5
	slli t5, a6, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a6, a6, s3
	add a6, a6, t5
	add a6, a6, t5
	xor t4, t4, a6
	srli t5, t4, 63
	slli t4, t4, 1
	or t4, t4, t5
	sd t0, 1536(a3)
	sd t1, 1544(a3)
	sd t2, 1552(a3)
	sd t3, 1560(a3)
	sd t4, 1568(a3)
	sd a0, 1576(a3)
	sd a1, 1584(a3)
	sd a4, 1592(a3)
	sd a5, 1600(a3)
	sd a6, 1608(a3)
	sd a7, 1616(a3)
	sd s0, 1624(a3)
	sd s1, 1632(a3)
	sd s2, 1640(a3)
	sd s3, 1648(a3)
	sd s4, 1656(a3)
	ld t0, 1664(a3)
	ld t1, 1672(a3)
	ld t2, 1680(a3)
	ld t3, 1688(a3)
	ld t4, 1696(a3)
	ld a0, 1704(a3)
	ld a1, 1712(a3)
	ld a4, 1720(a3)
	ld a5, 1728(a3)
	ld a6, 1736(a3)
	ld a7, 1744(a3)
	ld s0, 1752(a3)
	ld s1, 1760(a3)
	ld s2, 1768(a3)
	ld s3, 1776(a3)
	ld s4, 1784(a3)
	slli t5, t0, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t0, t0, t4
	add t0, t0, t5
	add t0, t0, t5
	xor s1, s1, t0
	srli t5, s1, 32
	slli s1, s1, 32
	or s1, s1, t5
	slli t5, a5, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add a5, a5, s1
	add a5, a5, t5
	add a5, a5, t5
	xor t4, t4, a5
	srli t5, t4, 24
	slli t4, t4, 40
	or t4, t4, t5
	slli t5, t0, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t0, t0, t4
	add t0, t0, t5
	add t0, t0, t5
	xor s1, s1, t0
	srli t5, s1, 16
	slli s1, s1, 48
	or s1, s1, t5
	slli t5, a5, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add a5, a5, s1
	add a5, a5, t5
	add a5, a5, t5
	xor t4, t4, a5
	srli t5, t4, 63
	slli t4, t4, 1
	or t4, t4, t5
	slli t5, t1, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t1, t1, a0
	add t1, t1, t5
	add t1, t1, t5
	xor s2, s2, t1
	srli t5, s2, 32
	slli s2, s2, 32
	or s2, s2, t5
	slli t5, a6, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a6, a6, s2
	add a6, a6, t5
	add a6, a6, t5
	xor a0, a0, a6
	srli t5, a0, 24
	slli a0, a0, 40
	or a0, a0, t5
	slli t5, t1, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t1, t1, a0
	add t1, t1, t5
	add t1, t1, t5
	xor s2, s2, t1
	srli t5, s2, 16
	slli s2, s2, 48
	or s2, s2, t5
	slli t5, a6, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a6, a6, s2
	add a6, a6, t5
	add a6, a6, t5
	xor a0, a0, a6
	srli t5, a0, 63
	slli a0, a0, 1
	or a0, a0, t5
	slli t5, t2, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t2, t2, a1
	add t2, t2, t5
	add t2, t2, t5
	xor s3, s3, t2
	srli t5, s3, 32
	slli s3, s3, 32
	or s3, s3, t5
	slli t5, a7, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a7, a7, s3
	add a7, a7, t5
	add a7, a7, t5
	xor a1, a1, a7
	srli t5, a1, 24
	slli a1, a1, 40
	or a1, a1, t5
	slli t5, t2, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t2, t2, a1
	add t2, t2, t5
	add t2, t2, t5
	xor s3, s3, t2
	srli t5, s3, 16
	slli s3, s3, 48
	or s3, s3, t5
	slli t5, a7, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a7, a7, s3
	add a7, a7, t5
	add a7, a7, t5
	xor a1, a1, a7
	srli t5, a1, 63
	slli a1, a1, 1
	or a1, a1, t5
	slli t5, t3, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t3, t3, a4
	add t3, t3, t5
	add t3, t3, t5
	xor s4, s4, t3
	srli t5, s4, 32
	slli s4, s4, 32
	or s4, s4, t5
	slli t5, s0, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add s0, s0, s4
	add s0, s0, t5
	add s0, s0, t5
	xor a4, a4, s0
	srli t5, a4, 24
	slli a4, a4, 40
	or a4, a4, t5
	slli t5, t3, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t3, t3, a4
	add t3, t3, t5
	add t3, t3, t5
	xor s4, s4, t3
	srli t5, s4, 16
	slli s4, s4, 48
	or s4, s4, t5
	slli t5, s0, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add s0, s0, s4
	add s0, s0, t5
	add s0, s0, t5
	xor a4, a4, s0
	srli t5, a4, 63
	slli a4, a4, 1
	or a4, a4, t5
	slli t5, t0, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t0, t0, a0
	add t0, t0, t5
	add t0, t0, t5
	xor s4, s4, t0
	srli t5, s4, 32
	slli s4, s4, 32
	or s4, s4, t5
	slli t5, a7, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add a7, a7, s4
	add a7, a7, t5
	add a7, a7, t5
	xor a0, a0, a7
	srli t5, a0, 24
	slli a0, a0, 40
	or a0, a0, t5
	slli t5, t0, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t0, t0, a0
	add t0, t0, t5
	add t0, t0, t5
	xor s4, s4, t0
	srli t5, s4, 16
	slli s4, s4, 48
	or s4, s4, t5
	slli t5, a7, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add a7, a7, s4
	add a7, a7, t5
	add a7, a7, t5
	xor a0, a0, a7
	srli t5, a0, 63
	slli a0, a0, 1
	or a0, a0, t5
	slli t5, t1, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t1, t1, a1
	add t1, t1, t5
	add t1, t1, t5
	xor s1, s1, t1
	srli t5, s1, 32
	slli s1, s1, 32
	or s1, s1, t5
	slli t5, s0, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add s0, s0, s1
	add s0, s0, t5
	add s0, s0, t5
	xor a1, a1, s0
	srli t5, a1, 24
	slli a1, a1, 40
	or a1, a1, t5
	slli t5, t1, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t1, t1, a1
	add t1, t1, t5
	add t1, t1, t5
	xor s1, s1, t1
	srli t5, s1, 16
	slli s1, s1, 48
	or s1, s1, t5
	slli t5, s0, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add s0, s0, s1
	add s0, s0, t5
	add s0, s0, t5
	xor a1, a1, s0
	srli t5, a1, 63
	slli a1, a1, 1
	or a1, a1, t5
	slli t5, t2, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t2, t2, a4
	add t2, t2, t5
	add t2, t2, t5
	xor s2, s2, t2
	srli t5, s2, 32
	slli s2, s2, 32
	or s2, s2, t5
	slli t5, a5, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a5, a5, s2
	add a5, a5, t5
	add a5, a5, t5
	xor a4, a4, a5
	srli t5, a4, 24
	slli a4, a4, 40
	or a4, a4, t5
	slli t5, t2, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t2, t2, a4
	add t2, t2, t5
	add t2, t2, t5
	xor s2, s2, t2
	srli t5, s2, 16
	slli s2, s2, 48
	or s2, s2, t5
	slli t5, a5, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a5, a5, s2
	add a5, a5, t5
	add a5, a5, t5
	xor a4, a4, a5
	srli t5, a4, 63
	slli a4, a4, 1
	or a4, a4, t5
	slli t5, t3, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t3, t3, t4
	add t3, t3, t5
	add t3, t3, t5
	xor s3, s3, t3
	srli t5, s3, 32
	slli s3, s3, 32
	or s3, s3, t5
	slli t5, a6, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a6, a6, s3
	add a6, a6, t5
	add a6, a6, t5
	xor t4, t4, a6
	srli t5, t4, 24
	slli t4, t4, 40
	or t4, t4, t5
	slli t5, t3, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t3, t3, t4
	add t3, t3, t5
	add t3, t3, t5
	xor s3, s3, t3
	srli t5, s3, 16
	slli s3, s3, 48
	or s3, s3, t5
	slli t5, a6, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a6, a6, s3
	add a6, a6, t5
	add a6, a6, t5
	xor t4, t4, a6
	srli t5, t4, 63
	slli t4, t4, 1
	or t4, t4, t5
	sd t0, 1664(a3)
	sd t1, 1672(a3)
	sd t2, 1680(a3)
	sd t3, 1688(a3)
	sd t4, 1696(a3)
	sd a0, 1704(a3)
	sd a1, 1712(a3)
	sd a4, 1720(a3)
	sd a5, 1728(a3)
	sd a6, 1736(a3)
	sd a7, 1744(a3)
	sd s0, 1752(a3)
	sd s1, 1760(a3)
	sd s2, 1768(a3)
	sd s3, 1776(a3)
	sd s4, 1784(a3)
	ld t0, 1792(a3)
	ld t1, 1800(a3)
	ld t2, 1808(a3)
	ld t3, 1816(a3)
	ld t4, 1824(a3)
	ld a0, 1832(a3)
	ld a1, 1840(a3)
	ld a4, 1848(a3)
	ld a5, 1856(a3)
	ld a6, 1864(a3)
	ld a7, 1872(a3)
	ld s0, 1880(a3)
	ld s1, 1888(a3)
	ld s2, 1896(a3)
	ld s3, 1904(a3)
	ld s4, 1912(a3)
	slli t5, t0, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t0, t0, t4
	add t0, t0, t5
	add t0, t0, t5
	xor s1, s1, t0
	srli t5, s1, 32
	slli s1, s1, 32
	or s1, s1, t5
	slli t5, a5, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add a5, a5, s1
	add a5, a5, t5
	add a5, a5, t5
	xor t4, t4, a5
	srli t5, t4, 24
	slli t4, t4, 40
	or t4, t4, t5
	slli t5, t0, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t0, t0, t4
	add t0, t0, t5
	add t0, t0, t5
	xor s1, s1, t0
	srli t5, s1, 16
	slli s1, s1, 48
	or s1, s1, t5
	slli t5, a5, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add a5, a5, s1
	add a5, a5, t5
	add a5, a5, t5
	xor t4, t4, a5
	srli t5, t4, 63
	slli t4, t4, 1
	or t4, t4, t5
	slli t5, t1, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t1, t1, a0
	add t1, t1, t5
	add t1, t1, t5
	xor s2, s2, t1
	srli t5, s2, 32
	slli s2, s2, 32
	or s2, s2, t5
	slli t5, a6, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a6, a6, s2
	add a6, a6, t5
	add a6, a6, t5
	xor a0, a0, a6
	srli t5, a0, 24
	slli a0, a0, 40
	or a0, a0, t5
	slli t5, t1, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t1, t1, a0
	add t1, t1, t5
	add t1, t1, t5
	xor s2, s2, t1
	srli t5, s2, 16
	slli s2, s2, 48
	or s2, s2, t5
	slli t5, a6, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a6, a6, s2
	add a6, a6, t5
	add a6, a6, t5
	xor a0, a0, a6
	srli t5, a0, 63
	slli a0, a0, 1
	or a0, a0, t5
	slli t5, t2, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t2, t2, a1
	add t2, t2, t5
	add t2, t2, t5
	xor s3, s3, t2
	srli t5, s3, 32
	slli s3, s3, 32
	or s3, s3, t5
	slli t5, a7, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a7, a7, s3
	add a7, a7, t5
	add a7, a7, t5
	xor a1, a1, a7
	srli t5, a1, 24
	slli a1, a1, 40
	or a1, a1, t5
	slli t5, t2, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t2, t2, a1
	add t2, t2, t5
	add t2, t2, t5
	xor s3, s3, t2
	srli t5, s3, 16
	slli s3, s3, 48
	or s3, s3, t5
	slli t5, a7, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a7, a7, s3
	add a7, a7, t5
	add a7, a7, t5
	xor a1, a1, a7
	srli t5, a1, 63
	slli a1, a1, 1
	or a1, a1, t5
	slli t5, t3, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t3, t3, a4
	add t3, t3, t5
	add t3, t3, t5
	xor s4, s4, t3
	srli t5, s4, 32
	slli s4, s4, 32
	or s4, s4, t5
	slli t5, s0, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add s0, s0, s4
	add s0, s0, t5
	add s0, s0, t5
	xor a4, a4, s0
	srli t5, a4, 24
	slli a4, a4, 40
	or a4, a4, t5
	slli t5, t3, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t3, t3, a4
	add t3, t3, t5
	add t3, t3, t5
	xor s4, s4, t3
	srli t5, s4, 16
	slli s4, s4, 48
	or s4, s4, t5
	slli t5, s0, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add s0, s0, s4
	add s0, s0, t5
	add s0, s0, t5
	xor a4, a4, s0
	srli t5, a4, 63
	slli a4, a4, 1
	or a4, a4, t5
	slli t5, t0, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t0, t0, a0
	add t0, t0, t5
	add t0, t0, t5
	xor s4, s4, t0
	srli t5, s4, 32
	slli s4, s4, 32
	or s4, s4, t5
	slli t5, a7, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add a7, a7, s4
	add a7, a7, t5
	add a7, a7, t5
	xor a0, a0, a7
	srli t5, a0, 24
	slli a0, a0, 40
	or a0, a0, t5
	slli t5, t0, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t0, t0, a0
	add t0, t0, t5
	add t0, t0, t5
	xor s4, s4, t0
	srli t5, s4, 16
	slli s4, s4, 48
	or s4, s4, t5
	slli t5, a7, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add a7, a7, s4
	add a7, a7, t5
	add a7, a7, t5
	xor a0, a0, a7
	srli t5, a0, 63
	slli a0, a0, 1
	or a0, a0, t5
	slli t5, t1, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t1, t1, a1
	add t1, t1, t5
	add t1, t1, t5
	xor s1, s1, t1
	srli t5, s1, 32
	slli s1, s1, 32
	or s1, s1, t5
	slli t5, s0, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add s0, s0, s1
	add s0, s0, t5
	add s0, s0, t5
	xor a1, a1, s0
	srli t5, a1, 24
	slli a1, a1, 40
	or a1, a1, t5
	slli t5, t1, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t1, t1, a1
	add t1, t1, t5
	add t1, t1, t5
	xor s1, s1, t1
	srli t5, s1, 16
	slli s1, s1, 48
	or s1, s1, t5
	slli t5, s0, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add s0, s0, s1
	add s0, s0, t5
	add s0, s0, t5
	xor a1, a1, s0
	srli t5, a1, 63
	slli a1, a1, 1
	or a1, a1, t5
	slli t5, t2, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t2, t2, a4
	add t2, t2, t5
	add t2, t2, t5
	xor s2, s2, t2
	srli t5, s2, 32
	slli s2, s2, 32
	or s2, s2, t5
	slli t5, a5, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a5, a5, s2
	add a5, a5, t5
	add a5, a5, t5
	xor a4, a4, a5
	srli t5, a4, 24
	slli a4, a4, 40
	or a4, a4, t5
	slli t5, t2, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t2, t2, a4
	add t2, t2, t5
	add t2, t2, t5
	xor s2, s2, t2
	srli t5, s2, 16
	slli s2, s2, 48
	or s2, s2, t5
	slli t5, a5, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a5, a5, s2
	add a5, a5, t5
	add a5, a5, t5
	xor a4, a4, a5
	srli t5, a4, 63
	slli a4, a4, 1
	or a4, a4, t5
	slli t5, t3, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t3, t3, t4
	add t3, t3, t5
	add t3, t3, t5
	xor s3, s3, t3
	srli t5, s3, 32
	slli s3, s3, 32
	or s3, s3, t5
	slli t5, a6, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a6, a6, s3
	add a6, a6, t5
	add a6, a6, t5
	xor t4, t4, a6
	srli t5, t4, 24
	slli t4, t4, 40
	or t4, t4, t5
	slli t5, t3, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t3, t3, t4
	add t3, t3, t5
	add t3, t3, t5
	xor s3, s3, t3
	srli t5, s3, 16
	slli s3, s3, 48
	or s3, s3, t5
	slli t5, a6, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a6, a6, s3
	add a6, a6, t5
	add a6, a6, t5
	xor t4, t4, a6
	srli t5, t4, 63
	slli t4, t4, 1
	or t4, t4, t5
	sd t0, 1792(a3)
	sd t1, 1800(a3)
	sd t2, 1808(a3)
	sd t3, 1816(a3)
	sd t4, 1824(a3)
	sd a0, 1832(a3)
	sd a1, 1840(a3)
	sd a4, 1848(a3)
	sd a5, 1856(a3)
	sd a6, 1864(a3)
	sd a7, 1872(a3)
	sd s0, 1880(a3)
	sd s1, 1888(a3)
	sd s2, 1896(a3)
	sd s3, 1904(a3)
	sd s4, 1912(a3)
	ld t0, 1920(a3)
	ld t1, 1928(a3)
	ld t2, 1936(a3)
	ld t3, 1944(a3)
	ld t4, 1952(a3)
	ld a0, 1960(a3)
	ld a1, 1968(a3)
	ld a4, 1976(a3)
	ld a5, 1984(a3)
	ld a6, 1992(a3)
	ld a7, 2000(a3)
	ld s0, 2008(a3)
	ld s1, 2016(a3)
	ld s2, 2024(a3)
	ld s3, 2032(a3)
	ld s4, 2040(a3)
	slli t5, t0, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t0, t0, t4
	add t0, t0, t5
	add t0, t0, t5
	xor s1, s1, t0
	srli t5, s1, 32
	slli s1, s1, 32
	or s1, s1, t5
	slli t5, a5, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add a5, a5, s1
	add a5, a5, t5
	add a5, a5, t5
	xor t4, t4, a5
	srli t5, t4, 24
	slli t4, t4, 40
	or t4, t4, t5
	slli t5, t0, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t0, t0, t4
	add t0, t0, t5
	add t0, t0, t5
	xor s1, s1, t0
	srli t5, s1, 16
	slli s1, s1, 48
	or s1, s1, t5
	slli t5, a5, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add a5, a5, s1
	add a5, a5, t5
	add a5, a5, t5
	xor t4, t4, a5
	srli t5, t4, 63
	slli t4, t4, 1
	or t4, t4, t5
	slli t5, t1, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t1, t1, a0
	add t1, t1, t5
	add t1, t1, t5
	xor s2, s2, t1
	srli t5, s2, 32
	slli s2, s2, 32
	or s2, s2, t5
	slli t5, a6, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a6, a6, s2
	add a6, a6, t5
	add a6, a6, t5
	xor a0, a0, a6
	srli t5, a0, 24
	slli a0, a0, 40
	or a0, a0, t5
	slli t5, t1, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t1, t1, a0
	add t1, t1, t5
	add t1, t1, t5
	xor s2, s2, t1
	srli t5, s2, 16
	slli s2, s2, 48
	or s2, s2, t5
	slli t5, a6, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a6, a6, s2
	add a6, a6, t5
	add a6, a6, t5
	xor a0, a0, a6
	srli t5, a0, 63
	slli a0, a0, 1
	or a0, a0, t5
	slli t5, t2, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t2, t2, a1
	add t2, t2, t5
	add t2, t2, t5
	xor s3, s3, t2
	srli t5, s3, 32
	slli s3, s3, 32
	or s3, s3, t5
	slli t5, a7, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a7, a7, s3
	add a7, a7, t5
	add a7, a7, t5
	xor a1, a1, a7
	srli t5, a1, 24
	slli a1, a1, 40
	or a1, a1, t5
	slli t5, t2, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t2, t2, a1
	add t2, t2, t5
	add t2, t2, t5
	xor s3, s3, t2
	srli t5, s3, 16
	slli s3, s3, 48
	or s3, s3, t5
	slli t5, a7, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a7, a7, s3
	add a7, a7, t5
	add a7, a7, t5
	xor a1, a1, a7
	srli t5, a1, 63
	slli a1, a1, 1
	or a1, a1, t5
	slli t5, t3, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t3, t3, a4
	add t3, t3, t5
	add t3, t3, t5
	xor s4, s4, t3
	srli t5, s4, 32
	slli s4, s4, 32
	or s4, s4, t5
	slli t5, s0, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add s0, s0, s4
	add s0, s0, t5
	add s0, s0, t5
	xor a4, a4, s0
	srli t5, a4, 24
	slli a4, a4, 40
	or a4, a4, t5
	slli t5, t3, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t3, t3, a4
	add t3, t3, t5
	add t3, t3, t5
	xor s4, s4, t3
	srli t5, s4, 16
	slli s4, s4, 48
	or s4, s4, t5
	slli t5, s0, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add s0, s0, s4
	add s0, s0, t5
	add s0, s0, t5
	xor a4, a4, s0
	srli t5, a4, 63
	slli a4, a4, 1
	or a4, a4, t5
	slli t5, t0, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t0, t0, a0
	add t0, t0, t5
	add t0, t0, t5
	xor s4, s4, t0
	srli t5, s4, 32
	slli s4, s4, 32
	or s4, s4, t5
	slli t5, a7, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add a7, a7, s4
	add a7, a7, t5
	add a7, a7, t5
	xor a0, a0, a7
	srli t5, a0, 24
	slli a0, a0, 40
	or a0, a0, t5
	slli t5, t0, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t0, t0, a0
	add t0, t0, t5
	add t0, t0, t5
	xor s4, s4, t0
	srli t5, s4, 16
	slli s4, s4, 48
	or s4, s4, t5
	slli t5, a7, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add a7, a7, s4
	add a7, a7, t5
	add a7, a7, t5
	xor a0, a0, a7
	srli t5, a0, 63
	slli a0, a0, 1
	or a0, a0, t5
	slli t5, t1, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t1, t1, a1
	add t1, t1, t5
	add t1, t1, t5
	xor s1, s1, t1
	srli t5, s1, 32
	slli s1, s1, 32
	or s1, s1, t5
	slli t5, s0, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add s0, s0, s1
	add s0, s0, t5
	add s0, s0, t5
	xor a1, a1, s0
	srli t5, a1, 24
	slli a1, a1, 40
	or a1, a1, t5
	slli t5, t1, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t1, t1, a1
	add t1, t1, t5
	add t1, t1, t5
	xor s1, s1, t1
	srli t5, s1, 16
	slli s1, s1, 48
	or s1, s1, t5
	slli t5, s0, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add s0, s0, s1
	add s0, s0, t5
	add s0, s0, t5
	xor a1, a1, s0
	srli t5, a1, 63
	slli a1, a1, 1
	or a1, a1, t5
	slli t5, t2, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t2, t2, a4
	add t2, t2, t5
	add t2, t2, t5
	xor s2, s2, t2
	srli t5, s2, 32
	slli s2, s2, 32
	or s2, s2, t5
	slli t5, a5, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a5, a5, s2
	add a5, a5, t5
	add a5, a5, t5
	xor a4, a4, a5
	srli t5, a4, 24
	slli a4, a4, 40
	or a4, a4, t5
	slli t5, t2, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t2, t2, a4
	add t2, t2, t5
	add t2, t2, t5
	xor s2, s2, t2
	srli t5, s2, 16
	slli s2, s2, 48
	or s2, s2, t5
	slli t5, a5, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a5, a5, s2
	add a5, a5, t5
	add a5, a5, t5
	xor a4, a4, a5
	srli t5, a4, 63
	slli a4, a4, 1
	or a4, a4, t5
	slli t5, t3, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t3, t3, t4
	add t3, t3, t5
	add t3, t3, t5
	xor s3, s3, t3
	srli t5, s3, 32
	slli s3, s3, 32
	or s3, s3, t5
	slli t5, a6, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a6, a6, s3
	add a6, a6, t5
	add a6, a6, t5
	xor t4, t4, a6
	srli t5, t4, 24
	slli t4, t4, 40
	or t4, t4, t5
	slli t5, t3, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t3, t3, t4
	add t3, t3, t5
	add t3, t3, t5
	xor s3, s3, t3
	srli t5, s3, 16
	slli s3, s3, 48
	or s3, s3, t5
	slli t5, a6, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a6, a6, s3
	add a6, a6, t5
	add a6, a6, t5
	xor t4, t4, a6
	srli t5, t4, 63
	slli t4, t4, 1
	or t4, t4, t5
	sd t0, 1920(a3)
	sd t1, 1928(a3)
	sd t2, 1936(a3)
	sd t3, 1944(a3)
	sd t4, 1952(a3)
	sd a0, 1960(a3)
	sd a1, 1968(a3)
	sd a4, 1976(a3)
	sd a5, 1984(a3)
	sd a6, 1992(a3)
	sd a7, 2000(a3)
	sd s0, 2008(a3)
	sd s1, 2016(a3)
	sd s2, 2024(a3)
	sd s3, 2032(a3)
	sd s4, 2040(a3)
	ld t0, 1024(a3)
	ld t1, 1032(a3)
	ld t2, 1152(a3)
	ld t3, 1160(a3)
	ld t4, 1280(a3)
	ld a0, 1288(a3)
	ld a1, 1408(a3)
	ld a4, 1416(a3)
	ld a5, 1536(a3)
	ld a6, 1544(a3)
	ld a7, 1664(a3)
	ld s0, 1672(a3)
	ld s1, 1792(a3)
	ld s2, 1800(a3)
	ld s3, 1920(a3)
	ld s4, 1928(a3)
	slli t5, t0, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t0, t0, t4
	add t0, t0, t5
	add t0, t0, t5
	xor s1, s1, t0
	srli t5, s1, 32
	slli s1, s1, 32
	or s1, s1, t5
	slli t5, a5, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add a5, a5, s1
	add a5, a5, t5
	add a5, a5, t5
	xor t4, t4, a5
	srli t5, t4, 24
	slli t4, t4, 40
	or t4, t4, t5
	slli t5, t0, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t0, t0, t4
	add t0, t0, t5
	add t0, t0, t5
	xor s1, s1, t0
	srli t5, s1, 16
	slli s1, s1, 48
	or s1, s1, t5
	slli t5, a5, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add a5, a5, s1
	add a5, a5, t5
	add a5, a5, t5
	xor t4, t4, a5
	srli t5, t4, 63
	slli t4, t4, 1
	or t4, t4, t5
	slli t5, t1, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t1, t1, a0
	add t1, t1, t5
	add t1, t1, t5
	xor s2, s2, t1
	srli t5, s2, 32
	slli s2, s2, 32
	or s2, s2, t5
	slli t5, a6, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a6, a6, s2
	add a6, a6, t5
	add a6, a6, t5
	xor a0, a0, a6
	srli t5, a0, 24
	slli a0, a0, 40
	or a0, a0, t5
	slli t5, t1, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t1, t1, a0
	add t1, t1, t5
	add t1, t1, t5
	xor s2, s2, t1
	srli t5, s2, 16
	slli s2, s2, 48
	or s2, s2, t5
	slli t5, a6, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a6, a6, s2
	add a6, a6, t5
	add a6, a6, t5
	xor a0, a0, a6
	srli t5, a0, 63
	slli a0, a0, 1
	or a0, a0, t5
	slli t5, t2, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t2, t2, a1
	add t2, t2, t5
	add t2, t2, t5
	xor s3, s3, t2
	srli t5, s3, 32
	slli s3, s3, 32
	or s3, s3, t5
	slli t5, a7, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a7, a7, s3
	add a7, a7, t5
	add a7, a7, t5
	xor a1, a1, a7
	srli t5, a1, 24
	slli a1, a1, 40
	or a1, a1, t5
	slli t5, t2, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t2, t2, a1
	add t2, t2, t5
	add t2, t2, t5
	xor s3, s3, t2
	srli t5, s3, 16
	slli s3, s3, 48
	or s3, s3, t5
	slli t5, a7, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a7, a7, s3
	add a7, a7, t5
	add a7, a7, t5
	xor a1, a1, a7
	srli t5, a1, 63
	slli a1, a1, 1
	or a1, a1, t5
	slli t5, t3, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t3, t3, a4
	add t3, t3, t5
	add t3, t3, t5
	xor s4, s4, t3
	srli t5, s4, 32
	slli s4, s4, 32
	or s4, s4, t5
	slli t5, s0, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add s0, s0, s4
	add s0, s0, t5
	add s0, s0, t5
	xor a4, a4, s0
	srli t5, a4, 24
	slli a4, a4, 40
	or a4, a4, t5
	slli t5, t3, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t3, t3, a4
	add t3, t3, t5
	add t3, t3, t5
	xor s4, s4, t3
	srli t5, s4, 16
	slli s4, s4, 48
	or s4, s4, t5
	slli t5, s0, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add s0, s0, s4
	add s0, s0, t5
	add s0, s0, t5
	xor a4, a4, s0
	srli t5, a4, 63
	slli a4, a4, 1
	or a4, a4, t5
	slli t5, t0, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t0, t0, a0
	add t0, t0, t5
	add t0, t0, t5
	xor s4, s4, t0
	srli t5, s4, 32
	slli s4, s4, 32
	or s4, s4, t5
	slli t5, a7, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add a7, a7, s4
	add a7, a7, t5
	add a7, a7, t5
	xor a0, a0, a7
	srli t5, a0, 24
	slli a0, a0, 40
	or a0, a0, t5
	slli t5, t0, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t0, t0, a0
	add t0, t0, t5
	add t0, t0, t5
	xor s4, s4, t0
	srli t5, s4, 16
	slli s4, s4, 48
	or s4, s4, t5
	slli t5, a7, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add a7, a7, s4
	add a7, a7, t5
	add a7, a7, t5
	xor a0, a0, a7
	srli t5, a0, 63
	slli a0, a0, 1
	or a0, a0, t5
	slli t5, t1, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t1, t1, a1
	add t1, t1, t5
	add t1, t1, t5
	xor s1, s1, t1
	srli t5, s1, 32
	slli s1, s1, 32
	or s1, s1, t5
	slli t5, s0, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add s0, s0, s1
	add s0, s0, t5
	add s0, s0, t5
	xor a1, a1, s0
	srli t5, a1, 24
	slli a1, a1, 40
	or a1, a1, t5
	slli t5, t1, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t1, t1, a1
	add t1, t1, t5
	add t1, t1, t5
	xor s1, s1, t1
	srli t5, s1, 16
	slli s1, s1, 48
	or s1, s1, t5
	slli t5, s0, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add s0, s0, s1
	add s0, s0, t5
	add s0, s0, t5
	xor a1, a1, s0
	srli t5, a1, 63
	slli a1, a1, 1
	or a1, a1, t5
	slli t5, t2, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t2, t2, a4
	add t2, t2, t5
	add t2, t2, t5
	xor s2, s2, t2
	srli t5, s2, 32
	slli s2, s2, 32
	or s2, s2, t5
	slli t5, a5, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a5, a5, s2
	add a5, a5, t5
	add a5, a5, t5
	xor a4, a4, a5
	srli t5, a4, 24
	slli a4, a4, 40
	or a4, a4, t5
	slli t5, t2, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t2, t2, a4
	add t2, t2, t5
	add t2, t2, t5
	xor s2, s2, t2
	srli t5, s2, 16
	slli s2, s2, 48
	or s2, s2, t5
	slli t5, a5, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a5, a5, s2
	add a5, a5, t5
	add a5, a5, t5
	xor a4, a4, a5
	srli t5, a4, 63
	slli a4, a4, 1
	or a4, a4, t5
	slli t5, t3, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t3, t3, t4
	add t3, t3, t5
	add t3, t3, t5
	xor s3, s3, t3
	srli t5, s3, 32
	slli s3, s3, 32
	or s3, s3, t5
	slli t5, a6, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a6, a6, s3
	add a6, a6, t5
	add a6, a6, t5
	xor t4, t4, a6
	srli t5, t4, 24
	slli t4, t4, 40
	or t4, t4, t5
	slli t5, t3, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t3, t3, t4
	add t3, t3, t5
	add t3, t3, t5
	xor s3, s3, t3
	srli t5, s3, 16
	slli s3, s3, 48
	or s3, s3, t5
	slli t5, a6, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a6, a6, s3
	add a6, a6, t5
	add a6, a6, t5
	xor t4, t4, a6
	srli t5, t4, 63
	slli t4, t4, 1
	or t4, t4, t5
	sd t0, 1024(a3)
	sd t1, 1032(a3)
	sd t2, 1152(a3)
	sd t3, 1160(a3)
	sd t4, 1280(a3)
	sd a0, 1288(a3)
	sd a1, 1408(a3)
	sd a4, 1416(a3)
	sd a5, 1536(a3)
	sd a6, 1544(a3)
	sd a7, 1664(a3)
	sd s0, 1672(a3)
	sd s1, 1792(a3)
	sd s2, 1800(a3)
	sd s3, 1920(a3)
	sd s4, 1928(a3)
	ld t0, 1040(a3)
	ld t1, 1048(a3)
	ld t2, 1168(a3)
	ld t3, 1176(a3)
	ld t4, 1296(a3)
	ld a0, 1304(a3)
	ld a1, 1424(a3)
	ld a4, 1432(a3)
	ld a5, 1552(a3)
	ld a6, 1560(a3)
	ld a7, 1680(a3)
	ld s0, 1688(a3)
	ld s1, 1808(a3)
	ld s2, 1816(a3)
	ld s3, 1936(a3)
	ld s4, 1944(a3)
	slli t5, t0, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t0, t0, t4
	add t0, t0, t5
	add t0, t0, t5
	xor s1, s1, t0
	srli t5, s1, 32
	slli s1, s1, 32
	or s1, s1, t5
	slli t5, a5, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add a5, a5, s1
	add a5, a5, t5
	add a5, a5, t5
	xor t4, t4, a5
	srli t5, t4, 24
	slli t4, t4, 40
	or t4, t4, t5
	slli t5, t0, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t0, t0, t4
	add t0, t0, t5
	add t0, t0, t5
	xor s1, s1, t0
	srli t5, s1, 16
	slli s1, s1, 48
	or s1, s1, t5
	slli t5, a5, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add a5, a5, s1
	add a5, a5, t5
	add a5, a5, t5
	xor t4, t4, a5
	srli t5, t4, 63
	slli t4, t4, 1
	or t4, t4, t5
	slli t5, t1, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t1, t1, a0
	add t1, t1, t5
	add t1, t1, t5
	xor s2, s2, t1
	srli t5, s2, 32
	slli s2, s2, 32
	or s2, s2, t5
	slli t5, a6, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a6, a6, s2
	add a6, a6, t5
	add a6, a6, t5
	xor a0, a0, a6
	srli t5, a0, 24
	slli a0, a0, 40
	or a0, a0, t5
	slli t5, t1, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t1, t1, a0
	add t1, t1, t5
	add t1, t1, t5
	xor s2, s2, t1
	srli t5, s2, 16
	slli s2, s2, 48
	or s2, s2, t5
	slli t5, a6, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a6, a6, s2
	add a6, a6, t5
	add a6, a6, t5
	xor a0, a0, a6
	srli t5, a0, 63
	slli a0, a0, 1
	or a0, a0, t5
	slli t5, t2, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t2, t2, a1
	add t2, t2, t5
	add t2, t2, t5
	xor s3, s3, t2
	srli t5, s3, 32
	slli s3, s3, 32
	or s3, s3, t5
	slli t5, a7, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a7, a7, s3
	add a7, a7, t5
	add a7, a7, t5
	xor a1, a1, a7
	srli t5, a1, 24
	slli a1, a1, 40
	or a1, a1, t5
	slli t5, t2, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t2, t2, a1
	add t2, t2, t5
	add t2, t2, t5
	xor s3, s3, t2
	srli t5, s3, 16
	slli s3, s3, 48
	or s3, s3, t5
	slli t5, a7, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a7, a7, s3
	add a7, a7, t5
	add a7, a7, t5
	xor a1, a1, a7
	srli t5, a1, 63
	slli a1, a1, 1
	or a1, a1, t5
	slli t5, t3, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t3, t3, a4
	add t3, t3, t5
	add t3, t3, t5
	xor s4, s4, t3
	srli t5, s4, 32
	slli s4, s4, 32
	or s4, s4, t5
	slli t5, s0, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add s0, s0, s4
	add s0, s0, t5
	add s0, s0, t5
	xor a4, a4, s0
	srli t5, a4, 24
	slli a4, a4, 40
	or a4, a4, t5
	slli t5, t3, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t3, t3, a4
	add t3, t3, t5
	add t3, t3, t5
	xor s4, s4, t3
	srli t5, s4, 16
	slli s4, s4, 48
	or s4, s4, t5
	slli t5, s0, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add s0, s0, s4
	add s0, s0, t5
	add s0, s0, t5
	xor a4, a4, s0
	srli t5, a4, 63
	slli a4, a4, 1
	or a4, a4, t5
	slli t5, t0, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t0, t0, a0
	add t0, t0, t5
	add t0, t0, t5
	xor s4, s4, t0
	srli t5, s4, 32
	slli s4, s4, 32
	or s4, s4, t5
	slli t5, a7, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add a7, a7, s4
	add a7, a7, t5
	add a7, a7, t5
	xor a0, a0, a7
	srli t5, a0, 24
	slli a0, a0, 40
	or a0, a0, t5
	slli t5, t0, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t0, t0, a0
	add t0, t0, t5
	add t0, t0, t5
	xor s4, s4, t0
	srli t5, s4, 16
	slli s4, s4, 48
	or s4, s4, t5
	slli t5, a7, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add a7, a7, s4
	add a7, a7, t5
	add a7, a7, t5
	xor a0, a0, a7
	srli t5, a0, 63
	slli a0, a0, 1
	or a0, a0, t5
	slli t5, t1, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t1, t1, a1
	add t1, t1, t5
	add t1, t1, t5
	xor s1, s1, t1
	srli t5, s1, 32
	slli s1, s1, 32
	or s1, s1, t5
	slli t5, s0, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add s0, s0, s1
	add s0, s0, t5
	add s0, s0, t5
	xor a1, a1, s0
	srli t5, a1, 24
	slli a1, a1, 40
	or a1, a1, t5
	slli t5, t1, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t1, t1, a1
	add t1, t1, t5
	add t1, t1, t5
	xor s1, s1, t1
	srli t5, s1, 16
	slli s1, s1, 48
	or s1, s1, t5
	slli t5, s0, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add s0, s0, s1
	add s0, s0, t5
	add s0, s0, t5
	xor a1, a1, s0
	srli t5, a1, 63
	slli a1, a1, 1
	or a1, a1, t5
	slli t5, t2, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t2, t2, a4
	add t2, t2, t5
	add t2, t2, t5
	xor s2, s2, t2
	srli t5, s2, 32
	slli s2, s2, 32
	or s2, s2, t5
	slli t5, a5, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a5, a5, s2
	add a5, a5, t5
	add a5, a5, t5
	xor a4, a4, a5
	srli t5, a4, 24
	slli a4, a4, 40
	or a4, a4, t5
	slli t5, t2, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t2, t2, a4
	add t2, t2, t5
	add t2, t2, t5
	xor s2, s2, t2
	srli t5, s2, 16
	slli s2, s2, 48
	or s2, s2, t5
	slli t5, a5, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a5, a5, s2
	add a5, a5, t5
	add a5, a5, t5
	xor a4, a4, a5
	srli t5, a4, 63
	slli a4, a4, 1
	or a4, a4, t5
	slli t5, t3, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t3, t3, t4
	add t3, t3, t5
	add t3, t3, t5
	xor s3, s3, t3
	srli t5, s3, 32
	slli s3, s3, 32
	or s3, s3, t5
	slli t5, a6, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a6, a6, s3
	add a6, a6, t5
	add a6, a6, t5
	xor t4, t4, a6
	srli t5, t4, 24
	slli t4, t4, 40
	or t4, t4, t5
	slli t5, t3, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t3, t3, t4
	add t3, t3, t5
	add t3, t3, t5
	xor s3, s3, t3
	srli t5, s3, 16
	slli s3, s3, 48
	or s3, s3, t5
	slli t5, a6, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a6, a6, s3
	add a6, a6, t5
	add a6, a6, t5
	xor t4, t4, a6
	srli t5, t4, 63
	slli t4, t4, 1
	or t4, t4, t5
	sd t0, 1040(a3)
	sd t1, 1048(a3)
	sd t2, 1168(a3)
	sd t3, 1176(a3)
	sd t4, 1296(a3)
	sd a0, 1304(a3)
	sd a1, 1424(a3)
	sd a4, 1432(a3)
	sd a5, 1552(a3)
	sd a6, 1560(a3)
	sd a7, 1680(a3)
	sd s0, 1688(a3)
	sd s1, 1808(a3)
	sd s2, 1816(a3)
	sd s3, 1936(a3)
	sd s4, 1944(a3)
	ld t0, 1056(a3)
	ld t1, 1064(a3)
	ld t2, 1184(a3)
	ld t3, 1192(a3)
	ld t4, 1312(a3)
	ld a0, 1320(a3)
	ld a1, 1440(a3)
	ld a4, 1448(a3)
	ld a5, 1568(a3)
	ld a6, 1576(a3)
	ld a7, 1696(a3)
	ld s0, 1704(a3)
	ld s1, 1824(a3)
	ld s2, 1832(a3)
	ld s3, 1952(a3)
	ld s4, 1960(a3)
	slli t5, t0, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t0, t0, t4
	add t0, t0, t5
	add t0, t0, t5
	xor s1, s1, t0
	srli t5, s1, 32
	slli s1, s1, 32
	or s1, s1, t5
	slli t5, a5, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add a5, a5, s1
	add a5, a5, t5
	add a5, a5, t5
	xor t4, t4, a5
	srli t5, t4, 24
	slli t4, t4, 40
	or t4, t4, t5
	slli t5, t0, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t0, t0, t4
	add t0, t0, t5
	add t0, t0, t5
	xor s1, s1, t0
	srli t5, s1, 16
	slli s1, s1, 48
	or s1, s1, t5
	slli t5, a5, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add a5, a5, s1
	add a5, a5, t5
	add a5, a5, t5
	xor t4, t4, a5
	srli t5, t4, 63
	slli t4, t4, 1
	or t4, t4, t5
	slli t5, t1, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t1, t1, a0
	add t1, t1, t5
	add t1, t1, t5
	xor s2, s2, t1
	srli t5, s2, 32
	slli s2, s2, 32
	or s2, s2, t5
	slli t5, a6, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a6, a6, s2
	add a6, a6, t5
	add a6, a6, t5
	xor a0, a0, a6
	srli t5, a0, 24
	slli a0, a0, 40
	or a0, a0, t5
	slli t5, t1, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t1, t1, a0
	add t1, t1, t5
	add t1, t1, t5
	xor s2, s2, t1
	srli t5, s2, 16
	slli s2, s2, 48
	or s2, s2, t5
	slli t5, a6, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a6, a6, s2
	add a6, a6, t5
	add a6, a6, t5
	xor a0, a0, a6
	srli t5, a0, 63
	slli a0, a0, 1
	or a0, a0, t5
	slli t5, t2, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t2, t2, a1
	add t2, t2, t5
	add t2, t2, t5
	xor s3, s3, t2
	srli t5, s3, 32
	slli s3, s3, 32
	or s3, s3, t5
	slli t5, a7, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a7, a7, s3
	add a7, a7, t5
	add a7, a7, t5
	xor a1, a1, a7
	srli t5, a1, 24
	slli a1, a1, 40
	or a1, a1, t5
	slli t5, t2, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t2, t2, a1
	add t2, t2, t5
	add t2, t2, t5
	xor s3, s3, t2
	srli t5, s3, 16
	slli s3, s3, 48
	or s3, s3, t5
	slli t5, a7, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a7, a7, s3
	add a7, a7, t5
	add a7, a7, t5
	xor a1, a1, a7
	srli t5, a1, 63
	slli a1, a1, 1
	or a1, a1, t5
	slli t5, t3, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t3, t3, a4
	add t3, t3, t5
	add t3, t3, t5
	xor s4, s4, t3
	srli t5, s4, 32
	slli s4, s4, 32
	or s4, s4, t5
	slli t5, s0, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add s0, s0, s4
	add s0, s0, t5
	add s0, s0, t5
	xor a4, a4, s0
	srli t5, a4, 24
	slli a4, a4, 40
	or a4, a4, t5
	slli t5, t3, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t3, t3, a4
	add t3, t3, t5
	add t3, t3, t5
	xor s4, s4, t3
	srli t5, s4, 16
	slli s4, s4, 48
	or s4, s4, t5
	slli t5, s0, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add s0, s0, s4
	add s0, s0, t5
	add s0, s0, t5
	xor a4, a4, s0
	srli t5, a4, 63
	slli a4, a4, 1
	or a4, a4, t5
	slli t5, t0, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t0, t0, a0
	add t0, t0, t5
	add t0, t0, t5
	xor s4, s4, t0
	srli t5, s4, 32
	slli s4, s4, 32
	or s4, s4, t5
	slli t5, a7, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add a7, a7, s4
	add a7, a7, t5
	add a7, a7, t5
	xor a0, a0, a7
	srli t5, a0, 24
	slli a0, a0, 40
	or a0, a0, t5
	slli t5, t0, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t0, t0, a0
	add t0, t0, t5
	add t0, t0, t5
	xor s4, s4, t0
	srli t5, s4, 16
	slli s4, s4, 48
	or s4, s4, t5
	slli t5, a7, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add a7, a7, s4
	add a7, a7, t5
	add a7, a7, t5
	xor a0, a0, a7
	srli t5, a0, 63
	slli a0, a0, 1
	or a0, a0, t5
	slli t5, t1, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t1, t1, a1
	add t1, t1, t5
	add t1, t1, t5
	xor s1, s1, t1
	srli t5, s1, 32
	slli s1, s1, 32
	or s1, s1, t5
	slli t5, s0, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add s0, s0, s1
	add s0, s0, t5
	add s0, s0, t5
	xor a1, a1, s0
	srli t5, a1, 24
	slli a1, a1, 40
	or a1, a1, t5
	slli t5, t1, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t1, t1, a1
	add t1, t1, t5
	add t1, t1, t5
	xor s1, s1, t1
	srli t5, s1, 16
	slli s1, s1, 48
	or s1, s1, t5
	slli t5, s0, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add s0, s0, s1
	add s0, s0, t5
	add s0, s0, t5
	xor a1, a1, s0
	srli t5, a1, 63
	slli a1, a1, 1
	or a1, a1, t5
	slli t5, t2, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t2, t2, a4
	add t2, t2, t5
	add t2, t2, t5
	xor s2, s2, t2
	srli t5, s2, 32
	slli s2, s2, 32
	or s2, s2, t5
	slli t5, a5, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a5, a5, s2
	add a5, a5, t5
	add a5, a5, t5
	xor a4, a4, a5
	srli t5, a4, 24
	slli a4, a4, 40
	or a4, a4, t5
	slli t5, t2, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t2, t2, a4
	add t2, t2, t5
	add t2, t2, t5
	xor s2, s2, t2
	srli t5, s2, 16
	slli s2, s2, 48
	or s2, s2, t5
	slli t5, a5, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a5, a5, s2
	add a5, a5, t5
	add a5, a5, t5
	xor a4, a4, a5
	srli t5, a4, 63
	slli a4, a4, 1
	or a4, a4, t5
	slli t5, t3, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t3, t3, t4
	add t3, t3, t5
	add t3, t3, t5
	xor s3, s3, t3
	srli t5, s3, 32
	slli s3, s3, 32
	or s3, s3, t5
	slli t5, a6, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a6, a6, s3
	add a6, a6, t5
	add a6, a6, t5
	xor t4, t4, a6
	srli t5, t4, 24
	slli t4, t4, 40
	or t4, t4, t5
	slli t5, t3, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t3, t3, t4
	add t3, t3, t5
	add t3, t3, t5
	xor s3, s3, t3
	srli t5, s3, 16
	slli s3, s3, 48
	or s3, s3, t5
	slli t5, a6, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a6, a6, s3
	add a6, a6, t5
	add a6, a6, t5
	xor t4, t4, a6
	srli t5, t4, 63
	slli t4, t4, 1
	or t4, t4, t5
	sd t0, 1056(a3)
	sd t1, 1064(a3)
	sd t2, 1184(a3)
	sd t3, 1192(a3)
	sd t4, 1312(a3)
	sd a0, 1320(a3)
	sd a1, 1440(a3)
	sd a4, 1448(a3)
	sd a5, 1568(a3)
	sd a6, 1576(a3)
	sd a7, 1696(a3)
	sd s0, 1704(a3)
	sd s1, 1824(a3)
	sd s2, 1832(a3)
	sd s3, 1952(a3)
	sd s4, 1960(a3)
	ld t0, 1072(a3)
	ld t1, 1080(a3)
	ld t2, 1200(a3)
	ld t3, 1208(a3)
	ld t4, 1328(a3)
	ld a0, 1336(a3)
	ld a1, 1456(a3)
	ld a4, 1464(a3)
	ld a5, 1584(a3)
	ld a6, 1592(a3)
	ld a7, 1712(a3)
	ld s0, 1720(a3)
	ld s1, 1840(a3)
	ld s2, 1848(a3)
	ld s3, 1968(a3)
	ld s4, 1976(a3)
	slli t5, t0, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t0, t0, t4
	add t0, t0, t5
	add t0, t0, t5
	xor s1, s1, t0
	srli t5, s1, 32
	slli s1, s1, 32
	or s1, s1, t5
	slli t5, a5, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add a5, a5, s1
	add a5, a5, t5
	add a5, a5, t5
	xor t4, t4, a5
	srli t5, t4, 24
	slli t4, t4, 40
	or t4, t4, t5
	slli t5, t0, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t0, t0, t4
	add t0, t0, t5
	add t0, t0, t5
	xor s1, s1, t0
	srli t5, s1, 16
	slli s1, s1, 48
	or s1, s1, t5
	slli t5, a5, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add a5, a5, s1
	add a5, a5, t5
	add a5, a5, t5
	xor t4, t4, a5
	srli t5, t4, 63
	slli t4, t4, 1
	or t4, t4, t5
	slli t5, t1, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t1, t1, a0
	add t1, t1, t5
	add t1, t1, t5
	xor s2, s2, t1
	srli t5, s2, 32
	slli s2, s2, 32
	or s2, s2, t5
	slli t5, a6, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a6, a6, s2
	add a6, a6, t5
	add a6, a6, t5
	xor a0, a0, a6
	srli t5, a0, 24
	slli a0, a0, 40
	or a0, a0, t5
	slli t5, t1, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t1, t1, a0
	add t1, t1, t5
	add t1, t1, t5
	xor s2, s2, t1
	srli t5, s2, 16
	slli s2, s2, 48
	or s2, s2, t5
	slli t5, a6, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a6, a6, s2
	add a6, a6, t5
	add a6, a6, t5
	xor a0, a0, a6
	srli t5, a0, 63
	slli a0, a0, 1
	or a0, a0, t5
	slli t5, t2, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t2, t2, a1
	add t2, t2, t5
	add t2, t2, t5
	xor s3, s3, t2
	srli t5, s3, 32
	slli s3, s3, 32
	or s3, s3, t5
	slli t5, a7, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a7, a7, s3
	add a7, a7, t5
	add a7, a7, t5
	xor a1, a1, a7
	srli t5, a1, 24
	slli a1, a1, 40
	or a1, a1, t5
	slli t5, t2, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t2, t2, a1
	add t2, t2, t5
	add t2, t2, t5
	xor s3, s3, t2
	srli t5, s3, 16
	slli s3, s3, 48
	or s3, s3, t5
	slli t5, a7, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a7, a7, s3
	add a7, a7, t5
	add a7, a7, t5
	xor a1, a1, a7
	srli t5, a1, 63
	slli a1, a1, 1
	or a1, a1, t5
	slli t5, t3, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t3, t3, a4
	add t3, t3, t5
	add t3, t3, t5
	xor s4, s4, t3
	srli t5, s4, 32
	slli s4, s4, 32
	or s4, s4, t5
	slli t5, s0, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add s0, s0, s4
	add s0, s0, t5
	add s0, s0, t5
	xor a4, a4, s0
	srli t5, a4, 24
	slli a4, a4, 40
	or a4, a4, t5
	slli t5, t3, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t3, t3, a4
	add t3, t3, t5
	add t3, t3, t5
	xor s4, s4, t3
	srli t5, s4, 16
	slli s4, s4, 48
	or s4, s4, t5
	slli t5, s0, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add s0, s0, s4
	add s0, s0, t5
	add s0, s0, t5
	xor a4, a4, s0
	srli t5, a4, 63
	slli a4, a4, 1
	or a4, a4, t5
	slli t5, t0, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t0, t0, a0
	add t0, t0, t5
	add t0, t0, t5
	xor s4, s4, t0
	srli t5, s4, 32
	slli s4, s4, 32
	or s4, s4, t5
	slli t5, a7, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add a7, a7, s4
	add a7, a7, t5
	add a7, a7, t5
	xor a0, a0, a7
	srli t5, a0, 24
	slli a0, a0, 40
	or a0, a0, t5
	slli t5, t0, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t0, t0, a0
	add t0, t0, t5
	add t0, t0, t5
	xor s4, s4, t0
	srli t5, s4, 16
	slli s4, s4, 48
	or s4, s4, t5
	slli t5, a7, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add a7, a7, s4
	add a7, a7, t5
	add a7, a7, t5
	xor a0, a0, a7
	srli t5, a0, 63
	slli a0, a0, 1
	or a0, a0, t5
	slli t5, t1, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t1, t1, a1
	add t1, t1, t5
	add t1, t1, t5
	xor s1, s1, t1
	srli t5, s1, 32
	slli s1, s1, 32
	or s1, s1, t5
	slli t5, s0, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add s0, s0, s1
	add s0, s0, t5
	add s0, s0, t5
	xor a1, a1, s0
	srli t5, a1, 24
	slli a1, a1, 40
	or a1, a1, t5
	slli t5, t1, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t1, t1, a1
	add t1, t1, t5
	add t1, t1, t5
	xor s1, s1, t1
	srli t5, s1, 16
	slli s1, s1, 48
	or s1, s1, t5
	slli t5, s0, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add s0, s0, s1
	add s0, s0, t5
	add s0, s0, t5
	xor a1, a1, s0
	srli t5, a1, 63
	slli a1, a1, 1
	or a1, a1, t5
	slli t5, t2, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t2, t2, a4
	add t2, t2, t5
	add t2, t2, t5
	xor s2, s2, t2
	srli t5, s2, 32
	slli s2, s2, 32
	or s2, s2, t5
	slli t5, a5, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a5, a5, s2
	add a5, a5, t5
	add a5, a5, t5
	xor a4, a4, a5
	srli t5, a4, 24
	slli a4, a4, 40
	or a4, a4, t5
	slli t5, t2, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t2, t2, a4
	add t2, t2, t5
	add t2, t2, t5
	xor s2, s2, t2
	srli t5, s2, 16
	slli s2, s2, 48
	or s2, s2, t5
	slli t5, a5, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a5, a5, s2
	add a5, a5, t5
	add a5, a5, t5
	xor a4, a4, a5
	srli t5, a4, 63
	slli a4, a4, 1
	or a4, a4, t5
	slli t5, t3, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t3, t3, t4
	add t3, t3, t5
	add t3, t3, t5
	xor s3, s3, t3
	srli t5, s3, 32
	slli s3, s3, 32
	or s3, s3, t5
	slli t5, a6, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a6, a6, s3
	add a6, a6, t5
	add a6, a6, t5
	xor t4, t4, a6
	srli t5, t4, 24
	slli t4, t4, 40
	or t4, t4, t5
	slli t5, t3, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t3, t3, t4
	add t3, t3, t5
	add t3, t3, t5
	xor s3, s3, t3
	srli t5, s3, 16
	slli s3, s3, 48
	or s3, s3, t5
	slli t5, a6, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a6, a6, s3
	add a6, a6, t5
	add a6, a6, t5
	xor t4, t4, a6
	srli t5, t4, 63
	slli t4, t4, 1
	or t4, t4, t5
	sd t0, 1072(a3)
	sd t1, 1080(a3)
	sd t2, 1200(a3)
	sd t3, 1208(a3)
	sd t4, 1328(a3)
	sd a0, 1336(a3)
	sd a1, 1456(a3)
	sd a4, 1464(a3)
	sd a5, 1584(a3)
	sd a6, 1592(a3)
	sd a7, 1712(a3)
	sd s0, 1720(a3)
	sd s1, 1840(a3)
	sd s2, 1848(a3)
	sd s3, 1968(a3)
	sd s4, 1976(a3)
	ld t0, 1088(a3)
	ld t1, 1096(a3)
	ld t2, 1216(a3)
	ld t3, 1224(a3)
	ld t4, 1344(a3)
	ld a0, 1352(a3)
	ld a1, 1472(a3)
	ld a4, 1480(a3)
	ld a5, 1600(a3)
	ld a6, 1608(a3)
	ld a7, 1728(a3)
	ld s0, 1736(a3)
	ld s1, 1856(a3)
	ld s2, 1864(a3)
	ld s3, 1984(a3)
	ld s4, 1992(a3)
	slli t5, t0, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t0, t0, t4
	add t0, t0, t5
	add t0, t0, t5
	xor s1, s1, t0
	srli t5, s1, 32
	slli s1, s1, 32
	or s1, s1, t5
	slli t5, a5, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add a5, a5, s1
	add a5, a5, t5
	add a5, a5, t5
	xor t4, t4, a5
	srli t5, t4, 24
	slli t4, t4, 40
	or t4, t4, t5
	slli t5, t0, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t0, t0, t4
	add t0, t0, t5
	add t0, t0, t5
	xor s1, s1, t0
	srli t5, s1, 16
	slli s1, s1, 48
	or s1, s1, t5
	slli t5, a5, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add a5, a5, s1
	add a5, a5, t5
	add a5, a5, t5
	xor t4, t4, a5
	srli t5, t4, 63
	slli t4, t4, 1
	or t4, t4, t5
	slli t5, t1, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t1, t1, a0
	add t1, t1, t5
	add t1, t1, t5
	xor s2, s2, t1
	srli t5, s2, 32
	slli s2, s2, 32
	or s2, s2, t5
	slli t5, a6, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a6, a6, s2
	add a6, a6, t5
	add a6, a6, t5
	xor a0, a0, a6
	srli t5, a0, 24
	slli a0, a0, 40
	or a0, a0, t5
	slli t5, t1, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t1, t1, a0
	add t1, t1, t5
	add t1, t1, t5
	xor s2, s2, t1
	srli t5, s2, 16
	slli s2, s2, 48
	or s2, s2, t5
	slli t5, a6, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a6, a6, s2
	add a6, a6, t5
	add a6, a6, t5
	xor a0, a0, a6
	srli t5, a0, 63
	slli a0, a0, 1
	or a0, a0, t5
	slli t5, t2, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t2, t2, a1
	add t2, t2, t5
	add t2, t2, t5
	xor s3, s3, t2
	srli t5, s3, 32
	slli s3, s3, 32
	or s3, s3, t5
	slli t5, a7, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a7, a7, s3
	add a7, a7, t5
	add a7, a7, t5
	xor a1, a1, a7
	srli t5, a1, 24
	slli a1, a1, 40
	or a1, a1, t5
	slli t5, t2, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t2, t2, a1
	add t2, t2, t5
	add t2, t2, t5
	xor s3, s3, t2
	srli t5, s3, 16
	slli s3, s3, 48
	or s3, s3, t5
	slli t5, a7, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a7, a7, s3
	add a7, a7, t5
	add a7, a7, t5
	xor a1, a1, a7
	srli t5, a1, 63
	slli a1, a1, 1
	or a1, a1, t5
	slli t5, t3, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t3, t3, a4
	add t3, t3, t5
	add t3, t3, t5
	xor s4, s4, t3
	srli t5, s4, 32
	slli s4, s4, 32
	or s4, s4, t5
	slli t5, s0, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add s0, s0, s4
	add s0, s0, t5
	add s0, s0, t5
	xor a4, a4, s0
	srli t5, a4, 24
	slli a4, a4, 40
	or a4, a4, t5
	slli t5, t3, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t3, t3, a4
	add t3, t3, t5
	add t3, t3, t5
	xor s4, s4, t3
	srli t5, s4, 16
	slli s4, s4, 48
	or s4, s4, t5
	slli t5, s0, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add s0, s0, s4
	add s0, s0, t5
	add s0, s0, t5
	xor a4, a4, s0
	srli t5, a4, 63
	slli a4, a4, 1
	or a4, a4, t5
	slli t5, t0, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t0, t0, a0
	add t0, t0, t5
	add t0, t0, t5
	xor s4, s4, t0
	srli t5, s4, 32
	slli s4, s4, 32
	or s4, s4, t5
	slli t5, a7, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add a7, a7, s4
	add a7, a7, t5
	add a7, a7, t5
	xor a0, a0, a7
	srli t5, a0, 24
	slli a0, a0, 40
	or a0, a0, t5
	slli t5, t0, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t0, t0, a0
	add t0, t0, t5
	add t0, t0, t5
	xor s4, s4, t0
	srli t5, s4, 16
	slli s4, s4, 48
	or s4, s4, t5
	slli t5, a7, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add a7, a7, s4
	add a7, a7, t5
	add a7, a7, t5
	xor a0, a0, a7
	srli t5, a0, 63
	slli a0, a0, 1
	or a0, a0, t5
	slli t5, t1, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t1, t1, a1
	add t1, t1, t5
	add t1, t1, t5
	xor s1, s1, t1
	srli t5, s1, 32
	slli s1, s1, 32
	or s1, s1, t5
	slli t5, s0, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add s0, s0, s1
	add s0, s0, t5
	add s0, s0, t5
	xor a1, a1, s0
	srli t5, a1, 24
	slli a1, a1, 40
	or a1, a1, t5
	slli t5, t1, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t1, t1, a1
	add t1, t1, t5
	add t1, t1, t5
	xor s1, s1, t1
	srli t5, s1, 16
	slli s1, s1, 48
	or s1, s1, t5
	slli t5, s0, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add s0, s0, s1
	add s0, s0, t5
	add s0, s0, t5
	xor a1, a1, s0
	srli t5, a1, 63
	slli a1, a1, 1
	or a1, a1, t5
	slli t5, t2, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t2, t2, a4
	add t2, t2, t5
	add t2, t2, t5
	xor s2, s2, t2
	srli t5, s2, 32
	slli s2, s2, 32
	or s2, s2, t5
	slli t5, a5, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a5, a5, s2
	add a5, a5, t5
	add a5, a5, t5
	xor a4, a4, a5
	srli t5, a4, 24
	slli a4, a4, 40
	or a4, a4, t5
	slli t5, t2, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t2, t2, a4
	add t2, t2, t5
	add t2, t2, t5
	xor s2, s2, t2
	srli t5, s2, 16
	slli s2, s2, 48
	or s2, s2, t5
	slli t5, a5, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a5, a5, s2
	add a5, a5, t5
	add a5, a5, t5
	xor a4, a4, a5
	srli t5, a4, 63
	slli a4, a4, 1
	or a4, a4, t5
	slli t5, t3, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t3, t3, t4
	add t3, t3, t5
	add t3, t3, t5
	xor s3, s3, t3
	srli t5, s3, 32
	slli s3, s3, 32
	or s3, s3, t5
	slli t5, a6, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a6, a6, s3
	add a6, a6, t5
	add a6, a6, t5
	xor t4, t4, a6
	srli t5, t4, 24
	slli t4, t4, 40
	or t4, t4, t5
	slli t5, t3, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t3, t3, t4
	add t3, t3, t5
	add t3, t3, t5
	xor s3, s3, t3
	srli t5, s3, 16
	slli s3, s3, 48
	or s3, s3, t5
	slli t5, a6, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a6, a6, s3
	add a6, a6, t5
	add a6, a6, t5
	xor t4, t4, a6
	srli t5, t4, 63
	slli t4, t4, 1
	or t4, t4, t5
	sd t0, 1088(a3)
	sd t1, 1096(a3)
	sd t2, 1216(a3)
	sd t3, 1224(a3)
	sd t4, 1344(a3)
	sd a0, 1352(a3)
	sd a1, 1472(a3)
	sd a4, 1480(a3)
	sd a5, 1600(a3)
	sd a6, 1608(a3)
	sd a7, 1728(a3)
	sd s0, 1736(a3)
	sd s1, 1856(a3)
	sd s2, 1864(a3)
	sd s3, 1984(a3)
	sd s4, 1992(a3)
	ld t0, 1104(a3)
	ld t1, 1112(a3)
	ld t2, 1232(a3)
	ld t3, 1240(a3)
	ld t4, 1360(a3)
	ld a0, 1368(a3)
	ld a1, 1488(a3)
	ld a4, 1496(a3)
	ld a5, 1616(a3)
	ld a6, 1624(a3)
	ld a7, 1744(a3)
	ld s0, 1752(a3)
	ld s1, 1872(a3)
	ld s2, 1880(a3)
	ld s3, 2000(a3)
	ld s4, 2008(a3)
	slli t5, t0, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t0, t0, t4
	add t0, t0, t5
	add t0, t0, t5
	xor s1, s1, t0
	srli t5, s1, 32
	slli s1, s1, 32
	or s1, s1, t5
	slli t5, a5, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add a5, a5, s1
	add a5, a5, t5
	add a5, a5, t5
	xor t4, t4, a5
	srli t5, t4, 24
	slli t4, t4, 40
	or t4, t4, t5
	slli t5, t0, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t0, t0, t4
	add t0, t0, t5
	add t0, t0, t5
	xor s1, s1, t0
	srli t5, s1, 16
	slli s1, s1, 48
	or s1, s1, t5
	slli t5, a5, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add a5, a5, s1
	add a5, a5, t5
	add a5, a5, t5
	xor t4, t4, a5
	srli t5, t4, 63
	slli t4, t4, 1
	or t4, t4, t5
	slli t5, t1, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t1, t1, a0
	add t1, t1, t5
	add t1, t1, t5
	xor s2, s2, t1
	srli t5, s2, 32
	slli s2, s2, 32
	or s2, s2, t5
	slli t5, a6, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a6, a6, s2
	add a6, a6, t5
	add a6, a6, t5
	xor a0, a0, a6
	srli t5, a0, 24
	slli a0, a0, 40
	or a0, a0, t5
	slli t5, t1, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t1, t1, a0
	add t1, t1, t5
	add t1, t1, t5
	xor s2, s2, t1
	srli t5, s2, 16
	slli s2, s2, 48
	or s2, s2, t5
	slli t5, a6, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a6, a6, s2
	add a6, a6, t5
	add a6, a6, t5
	xor a0, a0, a6
	srli t5, a0, 63
	slli a0, a0, 1
	or a0, a0, t5
	slli t5, t2, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t2, t2, a1
	add t2, t2, t5
	add t2, t2, t5
	xor s3, s3, t2
	srli t5, s3, 32
	slli s3, s3, 32
	or s3, s3, t5
	slli t5, a7, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a7, a7, s3
	add a7, a7, t5
	add a7, a7, t5
	xor a1, a1, a7
	srli t5, a1, 24
	slli a1, a1, 40
	or a1, a1, t5
	slli t5, t2, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t2, t2, a1
	add t2, t2, t5
	add t2, t2, t5
	xor s3, s3, t2
	srli t5, s3, 16
	slli s3, s3, 48
	or s3, s3, t5
	slli t5, a7, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a7, a7, s3
	add a7, a7, t5
	add a7, a7, t5
	xor a1, a1, a7
	srli t5, a1, 63
	slli a1, a1, 1
	or a1, a1, t5
	slli t5, t3, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t3, t3, a4
	add t3, t3, t5
	add t3, t3, t5
	xor s4, s4, t3
	srli t5, s4, 32
	slli s4, s4, 32
	or s4, s4, t5
	slli t5, s0, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add s0, s0, s4
	add s0, s0, t5
	add s0, s0, t5
	xor a4, a4, s0
	srli t5, a4, 24
	slli a4, a4, 40
	or a4, a4, t5
	slli t5, t3, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t3, t3, a4
	add t3, t3, t5
	add t3, t3, t5
	xor s4, s4, t3
	srli t5, s4, 16
	slli s4, s4, 48
	or s4, s4, t5
	slli t5, s0, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add s0, s0, s4
	add s0, s0, t5
	add s0, s0, t5
	xor a4, a4, s0
	srli t5, a4, 63
	slli a4, a4, 1
	or a4, a4, t5
	slli t5, t0, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t0, t0, a0
	add t0, t0, t5
	add t0, t0, t5
	xor s4, s4, t0
	srli t5, s4, 32
	slli s4, s4, 32
	or s4, s4, t5
	slli t5, a7, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add a7, a7, s4
	add a7, a7, t5
	add a7, a7, t5
	xor a0, a0, a7
	srli t5, a0, 24
	slli a0, a0, 40
	or a0, a0, t5
	slli t5, t0, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t0, t0, a0
	add t0, t0, t5
	add t0, t0, t5
	xor s4, s4, t0
	srli t5, s4, 16
	slli s4, s4, 48
	or s4, s4, t5
	slli t5, a7, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add a7, a7, s4
	add a7, a7, t5
	add a7, a7, t5
	xor a0, a0, a7
	srli t5, a0, 63
	slli a0, a0, 1
	or a0, a0, t5
	slli t5, t1, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t1, t1, a1
	add t1, t1, t5
	add t1, t1, t5
	xor s1, s1, t1
	srli t5, s1, 32
	slli s1, s1, 32
	or s1, s1, t5
	slli t5, s0, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add s0, s0, s1
	add s0, s0, t5
	add s0, s0, t5
	xor a1, a1, s0
	srli t5, a1, 24
	slli a1, a1, 40
	or a1, a1, t5
	slli t5, t1, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t1, t1, a1
	add t1, t1, t5
	add t1, t1, t5
	xor s1, s1, t1
	srli t5, s1, 16
	slli s1, s1, 48
	or s1, s1, t5
	slli t5, s0, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add s0, s0, s1
	add s0, s0, t5
	add s0, s0, t5
	xor a1, a1, s0
	srli t5, a1, 63
	slli a1, a1, 1
	or a1, a1, t5
	slli t5, t2, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t2, t2, a4
	add t2, t2, t5
	add t2, t2, t5
	xor s2, s2, t2
	srli t5, s2, 32
	slli s2, s2, 32
	or s2, s2, t5
	slli t5, a5, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a5, a5, s2
	add a5, a5, t5
	add a5, a5, t5
	xor a4, a4, a5
	srli t5, a4, 24
	slli a4, a4, 40
	or a4, a4, t5
	slli t5, t2, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t2, t2, a4
	add t2, t2, t5
	add t2, t2, t5
	xor s2, s2, t2
	srli t5, s2, 16
	slli s2, s2, 48
	or s2, s2, t5
	slli t5, a5, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a5, a5, s2
	add a5, a5, t5
	add a5, a5, t5
	xor a4, a4, a5
	srli t5, a4, 63
	slli a4, a4, 1
	or a4, a4, t5
	slli t5, t3, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t3, t3, t4
	add t3, t3, t5
	add t3, t3, t5
	xor s3, s3, t3
	srli t5, s3, 32
	slli s3, s3, 32
	or s3, s3, t5
	slli t5, a6, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a6, a6, s3
	add a6, a6, t5
	add a6, a6, t5
	xor t4, t4, a6
	srli t5, t4, 24
	slli t4, t4, 40
	or t4, t4, t5
	slli t5, t3, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t3, t3, t4
	add t3, t3, t5
	add t3, t3, t5
	xor s3, s3, t3
	srli t5, s3, 16
	slli s3, s3, 48
	or s3, s3, t5
	slli t5, a6, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a6, a6, s3
	add a6, a6, t5
	add a6, a6, t5
	xor t4, t4, a6
	srli t5, t4, 63
	slli t4, t4, 1
	or t4, t4, t5
	sd t0, 1104(a3)
	sd t1, 1112(a3)
	sd t2, 1232(a3)
	sd t3, 1240(a3)
	sd t4, 1360(a3)
	sd a0, 1368(a3)
	sd a1, 1488(a3)
	sd a4, 1496(a3)
	sd a5, 1616(a3)
	sd a6, 1624(a3)
	sd a7, 1744(a3)
	sd s0, 1752(a3)
	sd s1, 1872(a3)
	sd s2, 1880(a3)
	sd s3, 2000(a3)
	sd s4, 2008(a3)
	ld t0, 1120(a3)
	ld t1, 1128(a3)
	ld t2, 1248(a3)
	ld t3, 1256(a3)
	ld t4, 1376(a3)
	ld a0, 1384(a3)
	ld a1, 1504(a3)
	ld a4, 1512(a3)
	ld a5, 1632(a3)
	ld a6, 1640(a3)
	ld a7, 1760(a3)
	ld s0, 1768(a3)
	ld s1, 1888(a3)
	ld s2, 1896(a3)
	ld s3, 2016(a3)
	ld s4, 2024(a3)
	slli t5, t0, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t0, t0, t4
	add t0, t0, t5
	add t0, t0, t5
	xor s1, s1, t0
	srli t5, s1, 32
	slli s1, s1, 32
	or s1, s1, t5
	slli t5, a5, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add a5, a5, s1
	add a5, a5, t5
	add a5, a5, t5
	xor t4, t4, a5
	srli t5, t4, 24
	slli t4, t4, 40
	or t4, t4, t5
	slli t5, t0, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t0, t0, t4
	add t0, t0, t5
	add t0, t0, t5
	xor s1, s1, t0
	srli t5, s1, 16
	slli s1, s1, 48
	or s1, s1, t5
	slli t5, a5, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add a5, a5, s1
	add a5, a5, t5
	add a5, a5, t5
	xor t4, t4, a5
	srli t5, t4, 63
	slli t4, t4, 1
	or t4, t4, t5
	slli t5, t1, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t1, t1, a0
	add t1, t1, t5
	add t1, t1, t5
	xor s2, s2, t1
	srli t5, s2, 32
	slli s2, s2, 32
	or s2, s2, t5
	slli t5, a6, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a6, a6, s2
	add a6, a6, t5
	add a6, a6, t5
	xor a0, a0, a6
	srli t5, a0, 24
	slli a0, a0, 40
	or a0, a0, t5
	slli t5, t1, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t1, t1, a0
	add t1, t1, t5
	add t1, t1, t5
	xor s2, s2, t1
	srli t5, s2, 16
	slli s2, s2, 48
	or s2, s2, t5
	slli t5, a6, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a6, a6, s2
	add a6, a6, t5
	add a6, a6, t5
	xor a0, a0, a6
	srli t5, a0, 63
	slli a0, a0, 1
	or a0, a0, t5
	slli t5, t2, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t2, t2, a1
	add t2, t2, t5
	add t2, t2, t5
	xor s3, s3, t2
	srli t5, s3, 32
	slli s3, s3, 32
	or s3, s3, t5
	slli t5, a7, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a7, a7, s3
	add a7, a7, t5
	add a7, a7, t5
	xor a1, a1, a7
	srli t5, a1, 24
	slli a1, a1, 40
	or a1, a1, t5
	slli t5, t2, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t2, t2, a1
	add t2, t2, t5
	add t2, t2, t5
	xor s3, s3, t2
	srli t5, s3, 16
	slli s3, s3, 48
	or s3, s3, t5
	slli t5, a7, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a7, a7, s3
	add a7, a7, t5
	add a7, a7, t5
	xor a1, a1, a7
	srli t5, a1, 63
	slli a1, a1, 1
	or a1, a1, t5
	slli t5, t3, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t3, t3, a4
	add t3, t3, t5
	add t3, t3, t5
	xor s4, s4, t3
	srli t5, s4, 32
	slli s4, s4, 32
	or s4, s4, t5
	slli t5, s0, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add s0, s0, s4
	add s0, s0, t5
	add s0, s0, t5
	xor a4, a4, s0
	srli t5, a4, 24
	slli a4, a4, 40
	or a4, a4, t5
	slli t5, t3, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t3, t3, a4
	add t3, t3, t5
	add t3, t3, t5
	xor s4, s4, t3
	srli t5, s4, 16
	slli s4, s4, 48
	or s4, s4, t5
	slli t5, s0, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add s0, s0, s4
	add s0, s0, t5
	add s0, s0, t5
	xor a4, a4, s0
	srli t5, a4, 63
	slli a4, a4, 1
	or a4, a4, t5
	slli t5, t0, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t0, t0, a0
	add t0, t0, t5
	add t0, t0, t5
	xor s4, s4, t0
	srli t5, s4, 32
	slli s4, s4, 32
	or s4, s4, t5
	slli t5, a7, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add a7, a7, s4
	add a7, a7, t5
	add a7, a7, t5
	xor a0, a0, a7
	srli t5, a0, 24
	slli a0, a0, 40
	or a0, a0, t5
	slli t5, t0, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t0, t0, a0
	add t0, t0, t5
	add t0, t0, t5
	xor s4, s4, t0
	srli t5, s4, 16
	slli s4, s4, 48
	or s4, s4, t5
	slli t5, a7, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add a7, a7, s4
	add a7, a7, t5
	add a7, a7, t5
	xor a0, a0, a7
	srli t5, a0, 63
	slli a0, a0, 1
	or a0, a0, t5
	slli t5, t1, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t1, t1, a1
	add t1, t1, t5
	add t1, t1, t5
	xor s1, s1, t1
	srli t5, s1, 32
	slli s1, s1, 32
	or s1, s1, t5
	slli t5, s0, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add s0, s0, s1
	add s0, s0, t5
	add s0, s0, t5
	xor a1, a1, s0
	srli t5, a1, 24
	slli a1, a1, 40
	or a1, a1, t5
	slli t5, t1, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t1, t1, a1
	add t1, t1, t5
	add t1, t1, t5
	xor s1, s1, t1
	srli t5, s1, 16
	slli s1, s1, 48
	or s1, s1, t5
	slli t5, s0, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add s0, s0, s1
	add s0, s0, t5
	add s0, s0, t5
	xor a1, a1, s0
	srli t5, a1, 63
	slli a1, a1, 1
	or a1, a1, t5
	slli t5, t2, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t2, t2, a4
	add t2, t2, t5
	add t2, t2, t5
	xor s2, s2, t2
	srli t5, s2, 32
	slli s2, s2, 32
	or s2, s2, t5
	slli t5, a5, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a5, a5, s2
	add a5, a5, t5
	add a5, a5, t5
	xor a4, a4, a5
	srli t5, a4, 24
	slli a4, a4, 40
	or a4, a4, t5
	slli t5, t2, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t2, t2, a4
	add t2, t2, t5
	add t2, t2, t5
	xor s2, s2, t2
	srli t5, s2, 16
	slli s2, s2, 48
	or s2, s2, t5
	slli t5, a5, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a5, a5, s2
	add a5, a5, t5
	add a5, a5, t5
	xor a4, a4, a5
	srli t5, a4, 63
	slli a4, a4, 1
	or a4, a4, t5
	slli t5, t3, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t3, t3, t4
	add t3, t3, t5
	add t3, t3, t5
	xor s3, s3, t3
	srli t5, s3, 32
	slli s3, s3, 32
	or s3, s3, t5
	slli t5, a6, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a6, a6, s3
	add a6, a6, t5
	add a6, a6, t5
	xor t4, t4, a6
	srli t5, t4, 24
	slli t4, t4, 40
	or t4, t4, t5
	slli t5, t3, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t3, t3, t4
	add t3, t3, t5
	add t3, t3, t5
	xor s3, s3, t3
	srli t5, s3, 16
	slli s3, s3, 48
	or s3, s3, t5
	slli t5, a6, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a6, a6, s3
	add a6, a6, t5
	add a6, a6, t5
	xor t4, t4, a6
	srli t5, t4, 63
	slli t4, t4, 1
	or t4, t4, t5
	sd t0, 1120(a3)
	sd t1, 1128(a3)
	sd t2, 1248(a3)
	sd t3, 1256(a3)
	sd t4, 1376(a3)
	sd a0, 1384(a3)
	sd a1, 1504(a3)
	sd a4, 1512(a3)
	sd a5, 1632(a3)
	sd a6, 1640(a3)
	sd a7, 1760(a3)
	sd s0, 1768(a3)
	sd s1, 1888(a3)
	sd s2, 1896(a3)
	sd s3, 2016(a3)
	sd s4, 2024(a3)
	ld t0, 1136(a3)
	ld t1, 1144(a3)
	ld t2, 1264(a3)
	ld t3, 1272(a3)
	ld t4, 1392(a3)
	ld a0, 1400(a3)
	ld a1, 1520(a3)
	ld a4, 1528(a3)
	ld a5, 1648(a3)
	ld a6, 1656(a3)
	ld a7, 1776(a3)
	ld s0, 1784(a3)
	ld s1, 1904(a3)
	ld s2, 1912(a3)
	ld s3, 2032(a3)
	ld s4, 2040(a3)
	slli t5, t0, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t0, t0, t4
	add t0, t0, t5
	add t0, t0, t5
	xor s1, s1, t0
	srli t5, s1, 32
	slli s1, s1, 32
	or s1, s1, t5
	slli t5, a5, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add a5, a5, s1
	add a5, a5, t5
	add a5, a5, t5
	xor t4, t4, a5
	srli t5, t4, 24
	slli t4, t4, 40
	or t4, t4, t5
	slli t5, t0, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t0, t0, t4
	add t0, t0, t5
	add t0, t0, t5
	xor s1, s1, t0
	srli t5, s1, 16
	slli s1, s1, 48
	or s1, s1, t5
	slli t5, a5, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add a5, a5, s1
	add a5, a5, t5
	add a5, a5, t5
	xor t4, t4, a5
	srli t5, t4, 63
	slli t4, t4, 1
	or t4, t4, t5
	slli t5, t1, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t1, t1, a0
	add t1, t1, t5
	add t1, t1, t5
	xor s2, s2, t1
	srli t5, s2, 32
	slli s2, s2, 32
	or s2, s2, t5
	slli t5, a6, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a6, a6, s2
	add a6, a6, t5
	add a6, a6, t5
	xor a0, a0, a6
	srli t5, a0, 24
	slli a0, a0, 40
	or a0, a0, t5
	slli t5, t1, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t1, t1, a0
	add t1, t1, t5
	add t1, t1, t5
	xor s2, s2, t1
	srli t5, s2, 16
	slli s2, s2, 48
	or s2, s2, t5
	slli t5, a6, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a6, a6, s2
	add a6, a6, t5
	add a6, a6, t5
	xor a0, a0, a6
	srli t5, a0, 63
	slli a0, a0, 1
	or a0, a0, t5
	slli t5, t2, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t2, t2, a1
	add t2, t2, t5
	add t2, t2, t5
	xor s3, s3, t2
	srli t5, s3, 32
	slli s3, s3, 32
	or s3, s3, t5
	slli t5, a7, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a7, a7, s3
	add a7, a7, t5
	add a7, a7, t5
	xor a1, a1, a7
	srli t5, a1, 24
	slli a1, a1, 40
	or a1, a1, t5
	slli t5, t2, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t2, t2, a1
	add t2, t2, t5
	add t2, t2, t5
	xor s3, s3, t2
	srli t5, s3, 16
	slli s3, s3, 48
	or s3, s3, t5
	slli t5, a7, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a7, a7, s3
	add a7, a7, t5
	add a7, a7, t5
	xor a1, a1, a7
	srli t5, a1, 63
	slli a1, a1, 1
	or a1, a1, t5
	slli t5, t3, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t3, t3, a4
	add t3, t3, t5
	add t3, t3, t5
	xor s4, s4, t3
	srli t5, s4, 32
	slli s4, s4, 32
	or s4, s4, t5
	slli t5, s0, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add s0, s0, s4
	add s0, s0, t5
	add s0, s0, t5
	xor a4, a4, s0
	srli t5, a4, 24
	slli a4, a4, 40
	or a4, a4, t5
	slli t5, t3, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t3, t3, a4
	add t3, t3, t5
	add t3, t3, t5
	xor s4, s4, t3
	srli t5, s4, 16
	slli s4, s4, 48
	or s4, s4, t5
	slli t5, s0, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add s0, s0, s4
	add s0, s0, t5
	add s0, s0, t5
	xor a4, a4, s0
	srli t5, a4, 63
	slli a4, a4, 1
	or a4, a4, t5
	slli t5, t0, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t0, t0, a0
	add t0, t0, t5
	add t0, t0, t5
	xor s4, s4, t0
	srli t5, s4, 32
	slli s4, s4, 32
	or s4, s4, t5
	slli t5, a7, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add a7, a7, s4
	add a7, a7, t5
	add a7, a7, t5
	xor a0, a0, a7
	srli t5, a0, 24
	slli a0, a0, 40
	or a0, a0, t5
	slli t5, t0, 32
	slli t6, a0, 32
	mulhu t5, t5, t6
	add t0, t0, a0
	add t0, t0, t5
	add t0, t0, t5
	xor s4, s4, t0
	srli t5, s4, 16
	slli s4, s4, 48
	or s4, s4, t5
	slli t5, a7, 32
	slli t6, s4, 32
	mulhu t5, t5, t6
	add a7, a7, s4
	add a7, a7, t5
	add a7, a7, t5
	xor a0, a0, a7
	srli t5, a0, 63
	slli a0, a0, 1
	or a0, a0, t5
	slli t5, t1, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t1, t1, a1
	add t1, t1, t5
	add t1, t1, t5
	xor s1, s1, t1
	srli t5, s1, 32
	slli s1, s1, 32
	or s1, s1, t5
	slli t5, s0, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add s0, s0, s1
	add s0, s0, t5
	add s0, s0, t5
	xor a1, a1, s0
	srli t5, a1, 24
	slli a1, a1, 40
	or a1, a1, t5
	slli t5, t1, 32
	slli t6, a1, 32
	mulhu t5, t5, t6
	add t1, t1, a1
	add t1, t1, t5
	add t1, t1, t5
	xor s1, s1, t1
	srli t5, s1, 16
	slli s1, s1, 48
	or s1, s1, t5
	slli t5, s0, 32
	slli t6, s1, 32
	mulhu t5, t5, t6
	add s0, s0, s1
	add s0, s0, t5
	add s0, s0, t5
	xor a1, a1, s0
	srli t5, a1, 63
	slli a1, a1, 1
	or a1, a1, t5
	slli t5, t2, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t2, t2, a4
	add t2, t2, t5
	add t2, t2, t5
	xor s2, s2, t2
	srli t5, s2, 32
	slli s2, s2, 32
	or s2, s2, t5
	slli t5, a5, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a5, a5, s2
	add a5, a5, t5
	add a5, a5, t5
	xor a4, a4, a5
	srli t5, a4, 24
	slli a4, a4, 40
	or a4, a4, t5
	slli t5, t2, 32
	slli t6, a4, 32
	mulhu t5, t5, t6
	add t2, t2, a4
	add t2, t2, t5
	add t2, t2, t5
	xor s2, s2, t2
	srli t5, s2, 16
	slli s2, s2, 48
	or s2, s2, t5
	slli t5, a5, 32
	slli t6, s2, 32
	mulhu t5, t5, t6
	add a5, a5, s2
	add a5, a5, t5
	add a5, a5, t5
	xor a4, a4, a5
	srli t5, a4, 63
	slli a4, a4, 1
	or a4, a4, t5
	slli t5, t3, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t3, t3, t4
	add t3, t3, t5
	add t3, t3, t5
	xor s3, s3, t3
	srli t5, s3, 32
	slli s3, s3, 32
	or s3, s3, t5
	slli t5, a6, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a6, a6, s3
	add a6, a6, t5
	add a6, a6, t5
	xor t4, t4, a6
	srli t5, t4, 24
	slli t4, t4, 40
	or t4, t4, t5
	slli t5, t3, 32
	slli t6, t4, 32
	mulhu t5, t5, t6
	add t3, t3, t4
	add t3, t3, t5
	add t3, t3, t5
	xor s3, s3, t3
	srli t5, s3, 16
	slli s3, s3, 48
	or s3, s3, t5
	slli t5, a6, 32
	slli t6, s3, 32
	mulhu t5, t5, t6
	add a6, a6, s3
	add a6, a6, t5
	add a6, a6, t5
	xor t4, t4, a6
	srli t5, t4, 63
	slli t4, t4, 1
	or t4, t4, t5
	sd t0, 1136(a3)
	sd t1, 1144(a3)
	sd t2, 1264(a3)
	sd t3, 1272(a3)
	sd t4, 1392(a3)
	sd a0, 1400(a3)
	sd a1, 1520(a3)
	sd a4, 1528(a3)
	sd a5, 1648(a3)
	sd a6, 1656(a3)
	sd a7, 1776(a3)
	sd s0, 1784(a3)
	sd s1, 1904(a3)
	sd s2, 1912(a3)
	sd s3, 2032(a3)
	sd s4, 2040(a3)
	ld t0, 1024(a3)
	ld t1, 0(a3)
	xor t0, t0, t1
	sd t0, 0(a2)
	ld t0, 1032(a3)
	ld t1, 8(a3)
	xor t0, t0, t1
	sd t0, 8(a2)
	ld t0, 1040(a3)
	ld t1, 16(a3)
	xor t0, t0, t1
	sd t0, 16(a2)
	ld t0, 1048(a3)
	ld t1, 24(a3)
	xor t0, t0, t1
	sd t0, 24(a2)
	ld t0, 1056(a3)
	ld t1, 32(a3)
	xor t0, t0, t1
	sd t0, 32(a2)
	ld t0, 1064(a3)
	ld t1, 40(a3)
	xor t0, t0, t1
	sd t0, 40(a2)
	ld t0, 1072(a3)
	ld t1, 48(a3)
	xor t0, t0, t1
	sd t0, 48(a2)
	ld t0, 1080(a3)
	ld t1, 56(a3)
	xor t0, t0, t1
	sd t0, 56(a2)
	ld t0, 1088(a3)
	ld t1, 64(a3)
	xor t0, t0, t1
	sd t0, 64(a2)
	ld t0, 1096(a3)
	ld t1, 72(a3)
	xor t0, t0, t1
	sd t0, 72(a2)
	ld t0, 1104(a3)
	ld t1, 80(a3)
	xor t0, t0, t1
	sd t0, 80(a2)
	ld t0, 1112(a3)
	ld t1, 88(a3)
	xor t0, t0, t1
	sd t0, 88(a2)
	ld t0, 1120(a3)
	ld t1, 96(a3)
	xor t0, t0, t1
	sd t0, 96(a2)
	ld t0, 1128(a3)
	ld t1, 104(a3)
	xor t0, t0, t1
	sd t0, 104(a2)
	ld t0, 1136(a3)
	ld t1, 112(a3)
	xor t0, t0, t1
	sd t0, 112(a2)
	ld t0, 1144(a3)
	ld t1, 120(a3)
	xor t0, t0, t1
	sd t0, 120(a2)
	ld t0, 1152(a3)
	ld t1, 128(a3)
	xor t0, t0, t1
	sd t0, 128(a2)
	ld t0, 1160(a3)
	ld t1, 136(a3)
	xor t0, t0, t1
	sd t0, 136(a2)
	ld t0, 1168(a3)
	ld t1, 144(a3)
	xor t0, t0, t1
	sd t0, 144(a2)
	ld t0, 1176(a3)
	ld t1, 152(a3)
	xor t0, t0, t1
	sd t0, 152(a2)
	ld t0, 1184(a3)
	ld t1, 160(a3)
	xor t0, t0, t1
	sd t0, 160(a2)
	ld t0, 1192(a3)
	ld t1, 168(a3)
	xor t0, t0, t1
	sd t0, 168(a2)
	ld t0, 1200(a3)
	ld t1, 176(a3)
	xor t0, t0, t1
	sd t0, 176(a2)
	ld t0, 1208(a3)
	ld t1, 184(a3)
	xor t0, t0, t1
	sd t0, 184(a2)
	ld t0, 1216(a3)
	ld t1, 192(a3)
	xor t0, t0, t1
	sd t0, 192(a2)
	ld t0, 1224(a3)
	ld t1, 200(a3)
	xor t0, t0, t1
	sd t0, 200(a2)
	ld t0, 1232(a3)
	ld t1, 208(a3)
	xor t0, t0, t1
	sd t0, 208(a2)
	ld t0, 1240(a3)
	ld t1, 216(a3)
	xor t0, t0, t1
	sd t0, 216(a2)
	ld t0, 1248(a3)
	ld t1, 224(a3)
	xor t0, t0, t1
	sd t0, 224(a2)
	ld t0, 1256(a3)
	ld t1, 232(a3)
	xor t0, t0, t1
	sd t0, 232(a2)
	ld t0, 1264(a3)
	ld t1, 240(a3)
	xor t0, t0, t1
	sd t0, 240(a2)
	ld t0, 1272(a3)
	ld t1, 248(a3)
	xor t0, t0, t1
	sd t0, 248(a2)
	ld t0, 1280(a3)
	ld t1, 256(a3)
	xor t0, t0, t1
	sd t0, 256(a2)
	ld t0, 1288(a3)
	ld t1, 264(a3)
	xor t0, t0, t1
	sd t0, 264(a2)
	ld t0, 1296(a3)
	ld t1, 272(a3)
	xor t0, t0, t1
	sd t0, 272(a2)
	ld t0, 1304(a3)
	ld t1, 280(a3)
	xor t0, t0, t1
	sd t0, 280(a2)
	ld t0, 1312(a3)
	ld t1, 288(a3)
	xor t0, t0, t1
	sd t0, 288(a2)
	ld t0, 1320(a3)
	ld t1, 296(a3)
	xor t0, t0, t1
	sd t0, 296(a2)
	ld t0, 1328(a3)
	ld t1, 304(a3)
	xor t0, t0, t1
	sd t0, 304(a2)
	ld t0, 1336(a3)
	ld t1, 312(a3)
	xor t0, t0, t1
	sd t0, 312(a2)
	ld t0, 1344(a3)
	ld t1, 320(a3)
	xor t0, t0, t1
	sd t0, 320(a2)
	ld t0, 1352(a3)
	ld t1, 328(a3)
	xor t0, t0, t1
	sd t0, 328(a2)
	ld t0, 1360(a3)
	ld t1, 336(a3)
	xor t0, t0, t1
	sd t0, 336(a2)
	ld t0, 1368(a3)
	ld t1, 344(a3)
	xor t0, t0, t1
	sd t0, 344(a2)
	ld t0, 1376(a3)
	ld t1, 352(a3)
	xor t0, t0, t1
	sd t0, 352(a2)
	ld t0, 1384(a3)
	ld t1, 360(a3)
	xor t0, t0, t1
	sd t0, 360(a2)
	ld t0, 1392(a3)
	ld t1, 368(a3)
	xor t0, t0, t1
	sd t0, 368(a2)
	ld t0, 1400(a3)
	ld t1, 376(a3)
	xor t0, t0, t1
	sd t0, 376(a2)
	ld t0, 1408(a3)
	ld t1, 384(a3)
	xor t0, t0, t1
	sd t0, 384(a2)
	ld t0, 1416(a3)
	ld t1, 392(a3)
	xor t0, t0, t1
	sd t0, 392(a2)
	ld t0, 1424(a3)
	ld t1, 400(a3)
	xor t0, t0, t1
	sd t0, 400(a2)
	ld t0, 1432(a3)
	ld t1, 408(a3)
	xor t0, t0, t1
	sd t0, 408(a2)
	ld t0, 1440(a3)
	ld t1, 416(a3)
	xor t0, t0, t1
	sd t0, 416(a2)
	ld t0, 1448(a3)
	ld t1, 424(a3)
	xor t0, t0, t1
	sd t0, 424(a2)
	ld t0, 1456(a3)
	ld t1, 432(a3)
	xor t0, t0, t1
	sd t0, 432(a2)
	ld t0, 1464(a3)
	ld t1, 440(a3)
	xor t0, t0, t1
	sd t0, 440(a2)
	ld t0, 1472(a3)
	ld t1, 448(a3)
	xor t0, t0, t1
	sd t0, 448(a2)
	ld t0, 1480(a3)
	ld t1, 456(a3)
	xor t0, t0, t1
	sd t0, 456(a2)
	ld t0, 1488(a3)
	ld t1, 464(a3)
	xor t0, t0, t1
	sd t0, 464(a2)
	ld t0, 1496(a3)
	ld t1, 472(a3)
	xor t0, t0, t1
	sd t0, 472(a2)
	ld t0, 1504(a3)
	ld t1, 480(a3)
	xor t0, t0, t1
	sd t0, 480(a2)
	ld t0, 1512(a3)
	ld t1, 488(a3)
	xor t0, t0, t1
	sd t0, 488(a2)
	ld t0, 1520(a3)
	ld t1, 496(a3)
	xor t0, t0, t1
	sd t0, 496(a2)
	ld t0, 1528(a3)
	ld t1, 504(a3)
	xor t0, t0, t1
	sd t0, 504(a2)
	ld t0, 1536(a3)
	ld t1, 512(a3)
	xor t0, t0, t1
	sd t0, 512(a2)
	ld t0, 1544(a3)
	ld t1, 520(a3)
	xor t0, t0, t1
	sd t0, 520(a2)
	ld t0, 1552(a3)
	ld t1, 528(a3)
	xor t0, t0, t1
	sd t0, 528(a2)
	ld t0, 1560(a3)
	ld t1, 536(a3)
	xor t0, t0, t1
	sd t0, 536(a2)
	ld t0, 1568(a3)
	ld t1, 544(a3)
	xor t0, t0, t1
	sd t0, 544(a2)
	ld t0, 1576(a3)
	ld t1, 552(a3)
	xor t0, t0, t1
	sd t0, 552(a2)
	ld t0, 1584(a3)
	ld t1, 560(a3)
	xor t0, t0, t1
	sd t0, 560(a2)
	ld t0, 1592(a3)
	ld t1, 568(a3)
	xor t0, t0, t1
	sd t0, 568(a2)
	ld t0, 1600(a3)
	ld t1, 576(a3)
	xor t0, t0, t1
	sd t0, 576(a2)
	ld t0, 1608(a3)
	ld t1, 584(a3)
	xor t0, t0, t1
	sd t0, 584(a2)
	ld t0, 1616(a3)
	ld t1, 592(a3)
	xor t0, t0, t1
	sd t0, 592(a2)
	ld t0, 1624(a3)
	ld t1, 600(a3)
	xor t0, t0, t1
	sd t0, 600(a2)
	ld t0, 1632(a3)
	ld t1, 608(a3)
	xor t0, t0, t1
	sd t0, 608(a2)
	ld t0, 1640(a3)
	ld t1, 616(a3)
	xor t0, t0, t1
	sd t0, 616(a2)
	ld t0, 1648(a3)
	ld t1, 624(a3)
	xor t0, t0, t1
	sd t0, 624(a2)
	ld t0, 1656(a3)
	ld t1, 632(a3)
	xor t0, t0, t1
	sd t0, 632(a2)
	ld t0, 1664(a3)
	ld t1, 640(a3)
	xor t0, t0, t1
	sd t0, 640(a2)
	ld t0, 1672(a3)
	ld t1, 648(a3)
	xor t0, t0, t1
	sd t0, 648(a2)
	ld t0, 1680(a3)
	ld t1, 656(a3)
	xor t0, t0, t1
	sd t0, 656(a2)
	ld t0, 1688(a3)
	ld t1, 664(a3)
	xor t0, t0, t1
	sd t0, 664(a2)
	ld t0, 1696(a3)
	ld t1, 672(a3)
	xor t0, t0, t1
	sd t0, 672(a2)
	ld t0, 1704(a3)
	ld t1, 680(a3)
	xor t0, t0, t1
	sd t0, 680(a2)
	ld t0, 1712(a3)
	ld t1, 688(a3)
	xor t0, t0, t1
	sd t0, 688(a2)
	ld t0, 1720(a3)
	ld t1, 696(a3)
	xor t0, t0, t1
	sd t0, 696(a2)
	ld t0, 1728(a3)
	ld t1, 704(a3)
	xor t0, t0, t1
	sd t0, 704(a2)
	ld t0, 1736(a3)
	ld t1, 712(a3)
	xor t0, t0, t1
	sd t0, 712(a2)
	ld t0, 1744(a3)
	ld t1, 720(a3)
	xor t0, t0, t1
	sd t0, 720(a2)
	ld t0, 1752(a3)
	ld t1, 728(a3)
	xor t0, t0, t1
	sd t0, 728(a2)
	ld t0, 1760(a3)
	ld t1, 736(a3)
	xor t0, t0, t1
	sd t0, 736(a2)
	ld t0, 1768(a3)
	ld t1, 744(a3)
	xor t0, t0, t1
	sd t0, 744(a2)
	ld t0, 1776(a3)
	ld t1, 752(a3)
	xor t0, t0, t1
	sd t0, 752(a2)
	ld t0, 1784(a3)
	ld t1, 760(a3)
	xor t0, t0, t1
	sd t0, 760(a2)
	ld t0, 1792(a3)
	ld t1, 768(a3)
	xor t0, t0, t1
	sd t0, 768(a2)
	ld t0, 1800(a3)
	ld t1, 776(a3)
	xor t0, t0, t1
	sd t0, 776(a2)
	ld t0, 1808(a3)
	ld t1, 784(a3)
	xor t0, t0, t1
	sd t0, 784(a2)
	ld t0, 1816(a3)
	ld t1, 792(a3)
	xor t0, t0, t1
	sd t0, 792(a2)
	ld t0, 1824(a3)
	ld t1, 800(a3)
	xor t0, t0, t1
	sd t0, 800(a2)
	ld t0, 1832(a3)
	ld t1, 808(a3)
	xor t0, t0, t1
	sd t0, 808(a2)
	ld t0, 1840(a3)
	ld t1, 816(a3)
	xor t0, t0, t1
	sd t0, 816(a2)
	ld t0, 1848(a3)
	ld t1, 824(a3)
	xor t0, t0, t1
	sd t0, 824(a2)
	ld t0, 1856(a3)
	ld t1, 832(a3)
	xor t0, t0, t1
	sd t0, 832(a2)
	ld t0, 1864(a3)
	ld t1, 840(a3)
	xor t0, t0, t1
	sd t0, 840(a2)
	ld t0, 1872(a3)
	ld t1, 848(a3)
	xor t0, t0, t1
	sd t0, 848(a2)
	ld t0, 1880(a3)
	ld t1, 856(a3)
	xor t0, t0, t1
	sd t0, 856(a2)
	ld t0, 1888(a3)
	ld t1, 864(a3)
	xor t0, t0, t1
	sd t0, 864(a2)
	ld t0, 1896(a3)
	ld t1, 872(a3)
	xor t0, t0, t1
	sd t0, 872(a2)
	ld t0, 1904(a3)
	ld t1, 880(a3)
	xor t0, t0, t1
	sd t0, 880(a2)
	ld t0, 1912(a3)
	ld t1, 888(a3)
	xor t0, t0, t1
	sd t0, 888(a2)
	ld t0, 1920(a3)
	ld t1, 896(a3)
	xor t0, t0, t1
	sd t0, 896(a2)
	ld t0, 1928(a3)
	ld t1, 904(a3)
	xor t0, t0, t1
	sd t0, 904(a2)
	ld t0, 1936(a3)
	ld t1, 912(a3)
	xor t0, t0, t1
	sd t0, 912(a2)
	ld t0, 1944(a3)
	ld t1, 920(a3)
	xor t0, t0, t1
	sd t0, 920(a2)
	ld t0, 1952(a3)
	ld t1, 928(a3)
	xor t0, t0, t1
	sd t0, 928(a2)
	ld t0, 1960(a3)
	ld t1, 936(a3)
	xor t0, t0, t1
	sd t0, 936(a2)
	ld t0, 1968(a3)
	ld t1, 944(a3)
	xor t0, t0, t1
	sd t0, 944(a2)
	ld t0, 1976(a3)
	ld t1, 952(a3)
	xor t0, t0, t1
	sd t0, 952(a2)
	ld t0, 1984(a3)
	ld t1, 960(a3)
	xor t0, t0, t1
	sd t0, 960(a2)
	ld t0, 1992(a3)
	ld t1, 968(a3)
	xor t0, t0, t1
	sd t0, 968(a2)
	ld t0, 2000(a3)
	ld t1, 976(a3)
	xor t0, t0, t1
	sd t0, 976(a2)
	ld t0, 2008(a3)
	ld t1, 984(a3)
	xor t0, t0, t1
	sd t0, 984(a2)
	ld t0, 2016(a3)
	ld t1, 992(a3)
	xor t0, t0, t1
	sd t0, 992(a2)
	ld t0, 2024(a3)
	ld t1, 1000(a3)
	xor t0, t0, t1
	sd t0, 1000(a2)
	ld t0, 2032(a3)
	ld t1, 1008(a3)
	xor t0, t0, t1
	sd t0, 1008(a2)
	ld t0, 2040(a3)
	ld t1, 1016(a3)
	xor t0, t0, t1
	sd t0, 1016(a2)
	addi t0, a3, 2040
	ld s0, 8(t0)
	ld s1, 16(t0)
	ld s2, 24(t0)
	ld s3, 32(t0)
	ld s4, 40(t0)
	ret
	.option pop
