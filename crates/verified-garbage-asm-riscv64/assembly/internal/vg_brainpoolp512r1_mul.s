// The functions of `src/internal/vg_brainpoolp512r1_mul.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_brainpoolp512r1_mul:
	.option push
	.option arch, +m, +c
	addi a0, a0, 2047
	sd s0, 897(a0)
	addi a0, a0, -2047
	addi a0, a0, 2047
	sd s1, 905(a0)
	addi a0, a0, -2047
	addi a0, a0, 2047
	sd ra, 913(a0)
	addi a0, a0, -2047
	addi s0, a0, 0
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 256(s0)
	sd t0, 0(a6)
	ld t0, 264(s0)
	sd t0, 8(a6)
	ld t0, 272(s0)
	sd t0, 16(a6)
	ld t0, 280(s0)
	sd t0, 24(a6)
	ld t0, 288(s0)
	sd t0, 32(a6)
	ld t0, 296(s0)
	sd t0, 40(a6)
	ld t0, 304(s0)
	sd t0, 48(a6)
	ld t0, 312(s0)
	sd t0, 56(a6)
	ld t0, 384(s0)
	sd t0, 64(a6)
	ld t0, 392(s0)
	sd t0, 72(a6)
	ld t0, 400(s0)
	sd t0, 80(a6)
	ld t0, 408(s0)
	sd t0, 88(a6)
	ld t0, 416(s0)
	sd t0, 96(a6)
	ld t0, 424(s0)
	sd t0, 104(a6)
	ld t0, 432(s0)
	sd t0, 112(a6)
	ld t0, 440(s0)
	sd t0, 120(a6)
	ld t0, 256(s0)
	sd t0, 128(a6)
	ld t0, 264(s0)
	sd t0, 136(a6)
	ld t0, 272(s0)
	sd t0, 144(a6)
	ld t0, 280(s0)
	sd t0, 152(a6)
	ld t0, 288(s0)
	sd t0, 160(a6)
	ld t0, 296(s0)
	sd t0, 168(a6)
	ld t0, 304(s0)
	sd t0, 176(a6)
	ld t0, 312(s0)
	sd t0, 184(a6)
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 960(s0)
	sd t0, 192(a6)
	ld t0, 968(s0)
	sd t0, 200(a6)
	ld t0, 976(s0)
	sd t0, 208(a6)
	ld t0, 984(s0)
	sd t0, 216(a6)
	ld t0, 992(s0)
	sd t0, 224(a6)
	ld t0, 1000(s0)
	sd t0, 232(a6)
	ld t0, 1008(s0)
	sd t0, 240(a6)
	ld t0, 1016(s0)
	sd t0, 248(a6)
	ld t0, 1024(s0)
	sd t0, 256(a6)
	ld t0, 1032(s0)
	sd t0, 264(a6)
	ld t0, 1040(s0)
	sd t0, 272(a6)
	ld t0, 1048(s0)
	sd t0, 280(a6)
	ld t0, 1056(s0)
	sd t0, 288(a6)
	ld t0, 1064(s0)
	sd t0, 296(a6)
	ld t0, 1072(s0)
	sd t0, 304(a6)
	ld t0, 1080(s0)
	sd t0, 312(a6)
	ld t0, 384(s0)
	sd t0, 320(a6)
	ld t0, 392(s0)
	sd t0, 328(a6)
	ld t0, 400(s0)
	sd t0, 336(a6)
	ld t0, 408(s0)
	sd t0, 344(a6)
	ld t0, 416(s0)
	sd t0, 352(a6)
	ld t0, 424(s0)
	sd t0, 360(a6)
	ld t0, 432(s0)
	sd t0, 368(a6)
	ld t0, 440(s0)
	sd t0, 376(a6)
	ld t0, 960(s0)
	sd t0, 1152(s0)
	ld t0, 968(s0)
	sd t0, 1160(s0)
	ld t0, 976(s0)
	sd t0, 1168(s0)
	ld t0, 984(s0)
	sd t0, 1176(s0)
	ld t0, 992(s0)
	sd t0, 1184(s0)
	ld t0, 1000(s0)
	sd t0, 1192(s0)
	ld t0, 1008(s0)
	sd t0, 1200(s0)
	ld t0, 1016(s0)
	sd t0, 1208(s0)
	ld t0, 1024(s0)
	sd t0, 1216(s0)
	ld t0, 1032(s0)
	sd t0, 1224(s0)
	ld t0, 1040(s0)
	sd t0, 1232(s0)
	ld t0, 1048(s0)
	sd t0, 1240(s0)
	ld t0, 1056(s0)
	sd t0, 1248(s0)
	ld t0, 1064(s0)
	sd t0, 1256(s0)
	ld t0, 1072(s0)
	sd t0, 1264(s0)
	ld t0, 1080(s0)
	sd t0, 1272(s0)
	ld t0, 384(s0)
	sd t0, 1280(s0)
	ld t0, 392(s0)
	sd t0, 1288(s0)
	ld t0, 400(s0)
	sd t0, 1296(s0)
	ld t0, 408(s0)
	sd t0, 1304(s0)
	ld t0, 416(s0)
	sd t0, 1312(s0)
	ld t0, 424(s0)
	sd t0, 1320(s0)
	ld t0, 432(s0)
	sd t0, 1328(s0)
	ld t0, 440(s0)
	sd t0, 1336(s0)
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1152
	addi a3, zero, 960
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1216
	addi a3, zero, 1024
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1280
	addi a3, zero, 384
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1152
	addi a3, zero, 1216
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 960
	addi a3, zero, 1024
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1728
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1536
	addi a3, zero, 1600
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1728
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1152
	addi a3, zero, 1280
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 960
	addi a3, zero, 384
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1856
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1536
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1856
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1216
	addi a3, zero, 1280
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1024
	addi a3, zero, 384
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1856
	addi a3, zero, 1344
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1600
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1856
	addi a3, zero, 1344
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 448
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 512
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1344
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1600
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1600
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1344
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1536
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1600
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 448
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 512
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1600
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1536
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 448
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1600
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1856
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1728
	addi a3, zero, 1344
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1344
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1728
	addi a3, zero, 1600
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1856
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1472
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 1344(s0)
	sd t0, 384(a6)
	ld t0, 1352(s0)
	sd t0, 392(a6)
	ld t0, 1360(s0)
	sd t0, 400(a6)
	ld t0, 1368(s0)
	sd t0, 408(a6)
	ld t0, 1376(s0)
	sd t0, 416(a6)
	ld t0, 1384(s0)
	sd t0, 424(a6)
	ld t0, 1392(s0)
	sd t0, 432(a6)
	ld t0, 1400(s0)
	sd t0, 440(a6)
	ld t0, 1408(s0)
	sd t0, 448(a6)
	ld t0, 1416(s0)
	sd t0, 456(a6)
	ld t0, 1424(s0)
	sd t0, 464(a6)
	ld t0, 1432(s0)
	sd t0, 472(a6)
	ld t0, 1440(s0)
	sd t0, 480(a6)
	ld t0, 1448(s0)
	sd t0, 488(a6)
	ld t0, 1456(s0)
	sd t0, 496(a6)
	ld t0, 1464(s0)
	sd t0, 504(a6)
	ld t0, 1472(s0)
	sd t0, 512(a6)
	ld t0, 1480(s0)
	sd t0, 520(a6)
	ld t0, 1488(s0)
	sd t0, 528(a6)
	ld t0, 1496(s0)
	sd t0, 536(a6)
	ld t0, 1504(s0)
	sd t0, 544(a6)
	ld t0, 1512(s0)
	sd t0, 552(a6)
	ld t0, 1520(s0)
	sd t0, 560(a6)
	ld t0, 1528(s0)
	sd t0, 568(a6)
	ld t0, 1344(s0)
	sd t0, 1152(s0)
	ld t0, 1352(s0)
	sd t0, 1160(s0)
	ld t0, 1360(s0)
	sd t0, 1168(s0)
	ld t0, 1368(s0)
	sd t0, 1176(s0)
	ld t0, 1376(s0)
	sd t0, 1184(s0)
	ld t0, 1384(s0)
	sd t0, 1192(s0)
	ld t0, 1392(s0)
	sd t0, 1200(s0)
	ld t0, 1400(s0)
	sd t0, 1208(s0)
	ld t0, 1408(s0)
	sd t0, 1216(s0)
	ld t0, 1416(s0)
	sd t0, 1224(s0)
	ld t0, 1424(s0)
	sd t0, 1232(s0)
	ld t0, 1432(s0)
	sd t0, 1240(s0)
	ld t0, 1440(s0)
	sd t0, 1248(s0)
	ld t0, 1448(s0)
	sd t0, 1256(s0)
	ld t0, 1456(s0)
	sd t0, 1264(s0)
	ld t0, 1464(s0)
	sd t0, 1272(s0)
	ld t0, 1472(s0)
	sd t0, 1280(s0)
	ld t0, 1480(s0)
	sd t0, 1288(s0)
	ld t0, 1488(s0)
	sd t0, 1296(s0)
	ld t0, 1496(s0)
	sd t0, 1304(s0)
	ld t0, 1504(s0)
	sd t0, 1312(s0)
	ld t0, 1512(s0)
	sd t0, 1320(s0)
	ld t0, 1520(s0)
	sd t0, 1328(s0)
	ld t0, 1528(s0)
	sd t0, 1336(s0)
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1152
	addi a3, zero, 960
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1216
	addi a3, zero, 1024
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1280
	addi a3, zero, 384
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1152
	addi a3, zero, 1216
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 960
	addi a3, zero, 1024
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1728
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1536
	addi a3, zero, 1600
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1728
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1152
	addi a3, zero, 1280
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 960
	addi a3, zero, 384
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1856
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1536
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1856
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1216
	addi a3, zero, 1280
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1024
	addi a3, zero, 384
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1856
	addi a3, zero, 1344
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1600
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1856
	addi a3, zero, 1344
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 448
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 512
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1344
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1600
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1600
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1344
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1536
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1600
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 448
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 512
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1600
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1536
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 448
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1600
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1856
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1728
	addi a3, zero, 1344
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1344
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1728
	addi a3, zero, 1600
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1856
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1472
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 1344(s0)
	sd t0, 576(a6)
	ld t0, 1352(s0)
	sd t0, 584(a6)
	ld t0, 1360(s0)
	sd t0, 592(a6)
	ld t0, 1368(s0)
	sd t0, 600(a6)
	ld t0, 1376(s0)
	sd t0, 608(a6)
	ld t0, 1384(s0)
	sd t0, 616(a6)
	ld t0, 1392(s0)
	sd t0, 624(a6)
	ld t0, 1400(s0)
	sd t0, 632(a6)
	ld t0, 1408(s0)
	sd t0, 640(a6)
	ld t0, 1416(s0)
	sd t0, 648(a6)
	ld t0, 1424(s0)
	sd t0, 656(a6)
	ld t0, 1432(s0)
	sd t0, 664(a6)
	ld t0, 1440(s0)
	sd t0, 672(a6)
	ld t0, 1448(s0)
	sd t0, 680(a6)
	ld t0, 1456(s0)
	sd t0, 688(a6)
	ld t0, 1464(s0)
	sd t0, 696(a6)
	ld t0, 1472(s0)
	sd t0, 704(a6)
	ld t0, 1480(s0)
	sd t0, 712(a6)
	ld t0, 1488(s0)
	sd t0, 720(a6)
	ld t0, 1496(s0)
	sd t0, 728(a6)
	ld t0, 1504(s0)
	sd t0, 736(a6)
	ld t0, 1512(s0)
	sd t0, 744(a6)
	ld t0, 1520(s0)
	sd t0, 752(a6)
	ld t0, 1528(s0)
	sd t0, 760(a6)
	ld t0, 1344(s0)
	sd t0, 1152(s0)
	ld t0, 1352(s0)
	sd t0, 1160(s0)
	ld t0, 1360(s0)
	sd t0, 1168(s0)
	ld t0, 1368(s0)
	sd t0, 1176(s0)
	ld t0, 1376(s0)
	sd t0, 1184(s0)
	ld t0, 1384(s0)
	sd t0, 1192(s0)
	ld t0, 1392(s0)
	sd t0, 1200(s0)
	ld t0, 1400(s0)
	sd t0, 1208(s0)
	ld t0, 1408(s0)
	sd t0, 1216(s0)
	ld t0, 1416(s0)
	sd t0, 1224(s0)
	ld t0, 1424(s0)
	sd t0, 1232(s0)
	ld t0, 1432(s0)
	sd t0, 1240(s0)
	ld t0, 1440(s0)
	sd t0, 1248(s0)
	ld t0, 1448(s0)
	sd t0, 1256(s0)
	ld t0, 1456(s0)
	sd t0, 1264(s0)
	ld t0, 1464(s0)
	sd t0, 1272(s0)
	ld t0, 1472(s0)
	sd t0, 1280(s0)
	ld t0, 1480(s0)
	sd t0, 1288(s0)
	ld t0, 1488(s0)
	sd t0, 1296(s0)
	ld t0, 1496(s0)
	sd t0, 1304(s0)
	ld t0, 1504(s0)
	sd t0, 1312(s0)
	ld t0, 1512(s0)
	sd t0, 1320(s0)
	ld t0, 1520(s0)
	sd t0, 1328(s0)
	ld t0, 1528(s0)
	sd t0, 1336(s0)
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1152
	addi a3, zero, 960
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1216
	addi a3, zero, 1024
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1280
	addi a3, zero, 384
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1152
	addi a3, zero, 1216
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 960
	addi a3, zero, 1024
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1728
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1536
	addi a3, zero, 1600
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1728
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1152
	addi a3, zero, 1280
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 960
	addi a3, zero, 384
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1856
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1536
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1856
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1216
	addi a3, zero, 1280
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1024
	addi a3, zero, 384
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1856
	addi a3, zero, 1344
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1600
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1856
	addi a3, zero, 1344
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 448
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 512
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1344
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1600
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1600
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1344
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1536
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1600
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 448
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 512
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1600
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1536
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 448
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1600
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1856
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1728
	addi a3, zero, 1344
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1344
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1728
	addi a3, zero, 1600
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1856
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1472
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 1344(s0)
	sd t0, 768(a6)
	ld t0, 1352(s0)
	sd t0, 776(a6)
	ld t0, 1360(s0)
	sd t0, 784(a6)
	ld t0, 1368(s0)
	sd t0, 792(a6)
	ld t0, 1376(s0)
	sd t0, 800(a6)
	ld t0, 1384(s0)
	sd t0, 808(a6)
	ld t0, 1392(s0)
	sd t0, 816(a6)
	ld t0, 1400(s0)
	sd t0, 824(a6)
	ld t0, 1408(s0)
	sd t0, 832(a6)
	ld t0, 1416(s0)
	sd t0, 840(a6)
	ld t0, 1424(s0)
	sd t0, 848(a6)
	ld t0, 1432(s0)
	sd t0, 856(a6)
	ld t0, 1440(s0)
	sd t0, 864(a6)
	ld t0, 1448(s0)
	sd t0, 872(a6)
	ld t0, 1456(s0)
	sd t0, 880(a6)
	ld t0, 1464(s0)
	sd t0, 888(a6)
	ld t0, 1472(s0)
	sd t0, 896(a6)
	ld t0, 1480(s0)
	sd t0, 904(a6)
	ld t0, 1488(s0)
	sd t0, 912(a6)
	ld t0, 1496(s0)
	sd t0, 920(a6)
	ld t0, 1504(s0)
	sd t0, 928(a6)
	ld t0, 1512(s0)
	sd t0, 936(a6)
	ld t0, 1520(s0)
	sd t0, 944(a6)
	ld t0, 1528(s0)
	sd t0, 952(a6)
	ld t0, 1344(s0)
	sd t0, 1152(s0)
	ld t0, 1352(s0)
	sd t0, 1160(s0)
	ld t0, 1360(s0)
	sd t0, 1168(s0)
	ld t0, 1368(s0)
	sd t0, 1176(s0)
	ld t0, 1376(s0)
	sd t0, 1184(s0)
	ld t0, 1384(s0)
	sd t0, 1192(s0)
	ld t0, 1392(s0)
	sd t0, 1200(s0)
	ld t0, 1400(s0)
	sd t0, 1208(s0)
	ld t0, 1408(s0)
	sd t0, 1216(s0)
	ld t0, 1416(s0)
	sd t0, 1224(s0)
	ld t0, 1424(s0)
	sd t0, 1232(s0)
	ld t0, 1432(s0)
	sd t0, 1240(s0)
	ld t0, 1440(s0)
	sd t0, 1248(s0)
	ld t0, 1448(s0)
	sd t0, 1256(s0)
	ld t0, 1456(s0)
	sd t0, 1264(s0)
	ld t0, 1464(s0)
	sd t0, 1272(s0)
	ld t0, 1472(s0)
	sd t0, 1280(s0)
	ld t0, 1480(s0)
	sd t0, 1288(s0)
	ld t0, 1488(s0)
	sd t0, 1296(s0)
	ld t0, 1496(s0)
	sd t0, 1304(s0)
	ld t0, 1504(s0)
	sd t0, 1312(s0)
	ld t0, 1512(s0)
	sd t0, 1320(s0)
	ld t0, 1520(s0)
	sd t0, 1328(s0)
	ld t0, 1528(s0)
	sd t0, 1336(s0)
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1152
	addi a3, zero, 960
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1216
	addi a3, zero, 1024
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1280
	addi a3, zero, 384
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1152
	addi a3, zero, 1216
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 960
	addi a3, zero, 1024
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1728
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1536
	addi a3, zero, 1600
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1728
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1152
	addi a3, zero, 1280
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 960
	addi a3, zero, 384
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1856
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1536
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1856
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1216
	addi a3, zero, 1280
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1024
	addi a3, zero, 384
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1856
	addi a3, zero, 1344
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1600
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1856
	addi a3, zero, 1344
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 448
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 512
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1344
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1600
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1600
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1344
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1536
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1600
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 448
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 512
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1600
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1536
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 448
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1600
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1856
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1728
	addi a3, zero, 1344
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1344
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1728
	addi a3, zero, 1600
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1856
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1472
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 1344(s0)
	sd t0, 960(a6)
	ld t0, 1352(s0)
	sd t0, 968(a6)
	ld t0, 1360(s0)
	sd t0, 976(a6)
	ld t0, 1368(s0)
	sd t0, 984(a6)
	ld t0, 1376(s0)
	sd t0, 992(a6)
	ld t0, 1384(s0)
	sd t0, 1000(a6)
	ld t0, 1392(s0)
	sd t0, 1008(a6)
	ld t0, 1400(s0)
	sd t0, 1016(a6)
	ld t0, 1408(s0)
	sd t0, 1024(a6)
	ld t0, 1416(s0)
	sd t0, 1032(a6)
	ld t0, 1424(s0)
	sd t0, 1040(a6)
	ld t0, 1432(s0)
	sd t0, 1048(a6)
	ld t0, 1440(s0)
	sd t0, 1056(a6)
	ld t0, 1448(s0)
	sd t0, 1064(a6)
	ld t0, 1456(s0)
	sd t0, 1072(a6)
	ld t0, 1464(s0)
	sd t0, 1080(a6)
	ld t0, 1472(s0)
	sd t0, 1088(a6)
	ld t0, 1480(s0)
	sd t0, 1096(a6)
	ld t0, 1488(s0)
	sd t0, 1104(a6)
	ld t0, 1496(s0)
	sd t0, 1112(a6)
	ld t0, 1504(s0)
	sd t0, 1120(a6)
	ld t0, 1512(s0)
	sd t0, 1128(a6)
	ld t0, 1520(s0)
	sd t0, 1136(a6)
	ld t0, 1528(s0)
	sd t0, 1144(a6)
	ld t0, 1344(s0)
	sd t0, 1152(s0)
	ld t0, 1352(s0)
	sd t0, 1160(s0)
	ld t0, 1360(s0)
	sd t0, 1168(s0)
	ld t0, 1368(s0)
	sd t0, 1176(s0)
	ld t0, 1376(s0)
	sd t0, 1184(s0)
	ld t0, 1384(s0)
	sd t0, 1192(s0)
	ld t0, 1392(s0)
	sd t0, 1200(s0)
	ld t0, 1400(s0)
	sd t0, 1208(s0)
	ld t0, 1408(s0)
	sd t0, 1216(s0)
	ld t0, 1416(s0)
	sd t0, 1224(s0)
	ld t0, 1424(s0)
	sd t0, 1232(s0)
	ld t0, 1432(s0)
	sd t0, 1240(s0)
	ld t0, 1440(s0)
	sd t0, 1248(s0)
	ld t0, 1448(s0)
	sd t0, 1256(s0)
	ld t0, 1456(s0)
	sd t0, 1264(s0)
	ld t0, 1464(s0)
	sd t0, 1272(s0)
	ld t0, 1472(s0)
	sd t0, 1280(s0)
	ld t0, 1480(s0)
	sd t0, 1288(s0)
	ld t0, 1488(s0)
	sd t0, 1296(s0)
	ld t0, 1496(s0)
	sd t0, 1304(s0)
	ld t0, 1504(s0)
	sd t0, 1312(s0)
	ld t0, 1512(s0)
	sd t0, 1320(s0)
	ld t0, 1520(s0)
	sd t0, 1328(s0)
	ld t0, 1528(s0)
	sd t0, 1336(s0)
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1152
	addi a3, zero, 960
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1216
	addi a3, zero, 1024
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1280
	addi a3, zero, 384
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1152
	addi a3, zero, 1216
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 960
	addi a3, zero, 1024
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1728
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1536
	addi a3, zero, 1600
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1728
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1152
	addi a3, zero, 1280
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 960
	addi a3, zero, 384
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1856
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1536
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1856
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1216
	addi a3, zero, 1280
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1024
	addi a3, zero, 384
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1856
	addi a3, zero, 1344
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1600
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1856
	addi a3, zero, 1344
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 448
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 512
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1344
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1600
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1600
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1344
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1536
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1600
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 448
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 512
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1600
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1536
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 448
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1600
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1856
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1728
	addi a3, zero, 1344
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1344
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1728
	addi a3, zero, 1600
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1856
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1472
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 1344(s0)
	sd t0, 1152(a6)
	ld t0, 1352(s0)
	sd t0, 1160(a6)
	ld t0, 1360(s0)
	sd t0, 1168(a6)
	ld t0, 1368(s0)
	sd t0, 1176(a6)
	ld t0, 1376(s0)
	sd t0, 1184(a6)
	ld t0, 1384(s0)
	sd t0, 1192(a6)
	ld t0, 1392(s0)
	sd t0, 1200(a6)
	ld t0, 1400(s0)
	sd t0, 1208(a6)
	ld t0, 1408(s0)
	sd t0, 1216(a6)
	ld t0, 1416(s0)
	sd t0, 1224(a6)
	ld t0, 1424(s0)
	sd t0, 1232(a6)
	ld t0, 1432(s0)
	sd t0, 1240(a6)
	ld t0, 1440(s0)
	sd t0, 1248(a6)
	ld t0, 1448(s0)
	sd t0, 1256(a6)
	ld t0, 1456(s0)
	sd t0, 1264(a6)
	ld t0, 1464(s0)
	sd t0, 1272(a6)
	ld t0, 1472(s0)
	sd t0, 1280(a6)
	ld t0, 1480(s0)
	sd t0, 1288(a6)
	ld t0, 1488(s0)
	sd t0, 1296(a6)
	ld t0, 1496(s0)
	sd t0, 1304(a6)
	ld t0, 1504(s0)
	sd t0, 1312(a6)
	ld t0, 1512(s0)
	sd t0, 1320(a6)
	ld t0, 1520(s0)
	sd t0, 1328(a6)
	ld t0, 1528(s0)
	sd t0, 1336(a6)
	ld t0, 1344(s0)
	sd t0, 1152(s0)
	ld t0, 1352(s0)
	sd t0, 1160(s0)
	ld t0, 1360(s0)
	sd t0, 1168(s0)
	ld t0, 1368(s0)
	sd t0, 1176(s0)
	ld t0, 1376(s0)
	sd t0, 1184(s0)
	ld t0, 1384(s0)
	sd t0, 1192(s0)
	ld t0, 1392(s0)
	sd t0, 1200(s0)
	ld t0, 1400(s0)
	sd t0, 1208(s0)
	ld t0, 1408(s0)
	sd t0, 1216(s0)
	ld t0, 1416(s0)
	sd t0, 1224(s0)
	ld t0, 1424(s0)
	sd t0, 1232(s0)
	ld t0, 1432(s0)
	sd t0, 1240(s0)
	ld t0, 1440(s0)
	sd t0, 1248(s0)
	ld t0, 1448(s0)
	sd t0, 1256(s0)
	ld t0, 1456(s0)
	sd t0, 1264(s0)
	ld t0, 1464(s0)
	sd t0, 1272(s0)
	ld t0, 1472(s0)
	sd t0, 1280(s0)
	ld t0, 1480(s0)
	sd t0, 1288(s0)
	ld t0, 1488(s0)
	sd t0, 1296(s0)
	ld t0, 1496(s0)
	sd t0, 1304(s0)
	ld t0, 1504(s0)
	sd t0, 1312(s0)
	ld t0, 1512(s0)
	sd t0, 1320(s0)
	ld t0, 1520(s0)
	sd t0, 1328(s0)
	ld t0, 1528(s0)
	sd t0, 1336(s0)
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1152
	addi a3, zero, 960
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1216
	addi a3, zero, 1024
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1280
	addi a3, zero, 384
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1152
	addi a3, zero, 1216
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 960
	addi a3, zero, 1024
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1728
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1536
	addi a3, zero, 1600
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1728
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1152
	addi a3, zero, 1280
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 960
	addi a3, zero, 384
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1856
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1536
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1856
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1216
	addi a3, zero, 1280
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1024
	addi a3, zero, 384
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1856
	addi a3, zero, 1344
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1600
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1856
	addi a3, zero, 1344
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 448
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 512
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1344
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1600
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1600
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1344
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1536
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1600
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 448
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 512
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1600
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1536
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 448
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1600
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1856
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1728
	addi a3, zero, 1344
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1344
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1728
	addi a3, zero, 1600
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1856
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1472
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 1344(s0)
	sd t0, 1344(a6)
	ld t0, 1352(s0)
	sd t0, 1352(a6)
	ld t0, 1360(s0)
	sd t0, 1360(a6)
	ld t0, 1368(s0)
	sd t0, 1368(a6)
	ld t0, 1376(s0)
	sd t0, 1376(a6)
	ld t0, 1384(s0)
	sd t0, 1384(a6)
	ld t0, 1392(s0)
	sd t0, 1392(a6)
	ld t0, 1400(s0)
	sd t0, 1400(a6)
	ld t0, 1408(s0)
	sd t0, 1408(a6)
	ld t0, 1416(s0)
	sd t0, 1416(a6)
	ld t0, 1424(s0)
	sd t0, 1424(a6)
	ld t0, 1432(s0)
	sd t0, 1432(a6)
	ld t0, 1440(s0)
	sd t0, 1440(a6)
	ld t0, 1448(s0)
	sd t0, 1448(a6)
	ld t0, 1456(s0)
	sd t0, 1456(a6)
	ld t0, 1464(s0)
	sd t0, 1464(a6)
	ld t0, 1472(s0)
	sd t0, 1472(a6)
	ld t0, 1480(s0)
	sd t0, 1480(a6)
	ld t0, 1488(s0)
	sd t0, 1488(a6)
	ld t0, 1496(s0)
	sd t0, 1496(a6)
	ld t0, 1504(s0)
	sd t0, 1504(a6)
	ld t0, 1512(s0)
	sd t0, 1512(a6)
	ld t0, 1520(s0)
	sd t0, 1520(a6)
	ld t0, 1528(s0)
	sd t0, 1528(a6)
	ld t0, 1344(s0)
	sd t0, 1152(s0)
	ld t0, 1352(s0)
	sd t0, 1160(s0)
	ld t0, 1360(s0)
	sd t0, 1168(s0)
	ld t0, 1368(s0)
	sd t0, 1176(s0)
	ld t0, 1376(s0)
	sd t0, 1184(s0)
	ld t0, 1384(s0)
	sd t0, 1192(s0)
	ld t0, 1392(s0)
	sd t0, 1200(s0)
	ld t0, 1400(s0)
	sd t0, 1208(s0)
	ld t0, 1408(s0)
	sd t0, 1216(s0)
	ld t0, 1416(s0)
	sd t0, 1224(s0)
	ld t0, 1424(s0)
	sd t0, 1232(s0)
	ld t0, 1432(s0)
	sd t0, 1240(s0)
	ld t0, 1440(s0)
	sd t0, 1248(s0)
	ld t0, 1448(s0)
	sd t0, 1256(s0)
	ld t0, 1456(s0)
	sd t0, 1264(s0)
	ld t0, 1464(s0)
	sd t0, 1272(s0)
	ld t0, 1472(s0)
	sd t0, 1280(s0)
	ld t0, 1480(s0)
	sd t0, 1288(s0)
	ld t0, 1488(s0)
	sd t0, 1296(s0)
	ld t0, 1496(s0)
	sd t0, 1304(s0)
	ld t0, 1504(s0)
	sd t0, 1312(s0)
	ld t0, 1512(s0)
	sd t0, 1320(s0)
	ld t0, 1520(s0)
	sd t0, 1328(s0)
	ld t0, 1528(s0)
	sd t0, 1336(s0)
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1152
	addi a3, zero, 960
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1216
	addi a3, zero, 1024
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1280
	addi a3, zero, 384
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1152
	addi a3, zero, 1216
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 960
	addi a3, zero, 1024
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1728
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1536
	addi a3, zero, 1600
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1728
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1152
	addi a3, zero, 1280
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 960
	addi a3, zero, 384
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1856
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1536
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1856
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1216
	addi a3, zero, 1280
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1024
	addi a3, zero, 384
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1856
	addi a3, zero, 1344
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1600
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1856
	addi a3, zero, 1344
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 448
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 512
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1344
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1600
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1600
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1344
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1536
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1600
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 448
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 512
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1600
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1536
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 448
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1600
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1856
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1728
	addi a3, zero, 1344
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1344
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1728
	addi a3, zero, 1600
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1856
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1472
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 1344(s0)
	sd t0, 1536(a6)
	ld t0, 1352(s0)
	sd t0, 1544(a6)
	ld t0, 1360(s0)
	sd t0, 1552(a6)
	ld t0, 1368(s0)
	sd t0, 1560(a6)
	ld t0, 1376(s0)
	sd t0, 1568(a6)
	ld t0, 1384(s0)
	sd t0, 1576(a6)
	ld t0, 1392(s0)
	sd t0, 1584(a6)
	ld t0, 1400(s0)
	sd t0, 1592(a6)
	ld t0, 1408(s0)
	sd t0, 1600(a6)
	ld t0, 1416(s0)
	sd t0, 1608(a6)
	ld t0, 1424(s0)
	sd t0, 1616(a6)
	ld t0, 1432(s0)
	sd t0, 1624(a6)
	ld t0, 1440(s0)
	sd t0, 1632(a6)
	ld t0, 1448(s0)
	sd t0, 1640(a6)
	ld t0, 1456(s0)
	sd t0, 1648(a6)
	ld t0, 1464(s0)
	sd t0, 1656(a6)
	ld t0, 1472(s0)
	sd t0, 1664(a6)
	ld t0, 1480(s0)
	sd t0, 1672(a6)
	ld t0, 1488(s0)
	sd t0, 1680(a6)
	ld t0, 1496(s0)
	sd t0, 1688(a6)
	ld t0, 1504(s0)
	sd t0, 1696(a6)
	ld t0, 1512(s0)
	sd t0, 1704(a6)
	ld t0, 1520(s0)
	sd t0, 1712(a6)
	ld t0, 1528(s0)
	sd t0, 1720(a6)
	ld t0, 1344(s0)
	sd t0, 1152(s0)
	ld t0, 1352(s0)
	sd t0, 1160(s0)
	ld t0, 1360(s0)
	sd t0, 1168(s0)
	ld t0, 1368(s0)
	sd t0, 1176(s0)
	ld t0, 1376(s0)
	sd t0, 1184(s0)
	ld t0, 1384(s0)
	sd t0, 1192(s0)
	ld t0, 1392(s0)
	sd t0, 1200(s0)
	ld t0, 1400(s0)
	sd t0, 1208(s0)
	ld t0, 1408(s0)
	sd t0, 1216(s0)
	ld t0, 1416(s0)
	sd t0, 1224(s0)
	ld t0, 1424(s0)
	sd t0, 1232(s0)
	ld t0, 1432(s0)
	sd t0, 1240(s0)
	ld t0, 1440(s0)
	sd t0, 1248(s0)
	ld t0, 1448(s0)
	sd t0, 1256(s0)
	ld t0, 1456(s0)
	sd t0, 1264(s0)
	ld t0, 1464(s0)
	sd t0, 1272(s0)
	ld t0, 1472(s0)
	sd t0, 1280(s0)
	ld t0, 1480(s0)
	sd t0, 1288(s0)
	ld t0, 1488(s0)
	sd t0, 1296(s0)
	ld t0, 1496(s0)
	sd t0, 1304(s0)
	ld t0, 1504(s0)
	sd t0, 1312(s0)
	ld t0, 1512(s0)
	sd t0, 1320(s0)
	ld t0, 1520(s0)
	sd t0, 1328(s0)
	ld t0, 1528(s0)
	sd t0, 1336(s0)
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1152
	addi a3, zero, 960
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1216
	addi a3, zero, 1024
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1280
	addi a3, zero, 384
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1152
	addi a3, zero, 1216
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 960
	addi a3, zero, 1024
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1728
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1536
	addi a3, zero, 1600
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1728
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1152
	addi a3, zero, 1280
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 960
	addi a3, zero, 384
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1856
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1536
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1856
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1216
	addi a3, zero, 1280
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1024
	addi a3, zero, 384
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1856
	addi a3, zero, 1344
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1600
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1856
	addi a3, zero, 1344
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 448
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 512
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1344
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1600
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1600
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1344
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1536
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1600
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 448
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 512
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1600
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1536
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 448
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1600
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1856
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1728
	addi a3, zero, 1344
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1344
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1728
	addi a3, zero, 1600
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1856
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1472
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 1344(s0)
	sd t0, 1728(a6)
	ld t0, 1352(s0)
	sd t0, 1736(a6)
	ld t0, 1360(s0)
	sd t0, 1744(a6)
	ld t0, 1368(s0)
	sd t0, 1752(a6)
	ld t0, 1376(s0)
	sd t0, 1760(a6)
	ld t0, 1384(s0)
	sd t0, 1768(a6)
	ld t0, 1392(s0)
	sd t0, 1776(a6)
	ld t0, 1400(s0)
	sd t0, 1784(a6)
	ld t0, 1408(s0)
	sd t0, 1792(a6)
	ld t0, 1416(s0)
	sd t0, 1800(a6)
	ld t0, 1424(s0)
	sd t0, 1808(a6)
	ld t0, 1432(s0)
	sd t0, 1816(a6)
	ld t0, 1440(s0)
	sd t0, 1824(a6)
	ld t0, 1448(s0)
	sd t0, 1832(a6)
	ld t0, 1456(s0)
	sd t0, 1840(a6)
	ld t0, 1464(s0)
	sd t0, 1848(a6)
	ld t0, 1472(s0)
	sd t0, 1856(a6)
	ld t0, 1480(s0)
	sd t0, 1864(a6)
	ld t0, 1488(s0)
	sd t0, 1872(a6)
	ld t0, 1496(s0)
	sd t0, 1880(a6)
	ld t0, 1504(s0)
	sd t0, 1888(a6)
	ld t0, 1512(s0)
	sd t0, 1896(a6)
	ld t0, 1520(s0)
	sd t0, 1904(a6)
	ld t0, 1528(s0)
	sd t0, 1912(a6)
	ld t0, 1344(s0)
	sd t0, 1152(s0)
	ld t0, 1352(s0)
	sd t0, 1160(s0)
	ld t0, 1360(s0)
	sd t0, 1168(s0)
	ld t0, 1368(s0)
	sd t0, 1176(s0)
	ld t0, 1376(s0)
	sd t0, 1184(s0)
	ld t0, 1384(s0)
	sd t0, 1192(s0)
	ld t0, 1392(s0)
	sd t0, 1200(s0)
	ld t0, 1400(s0)
	sd t0, 1208(s0)
	ld t0, 1408(s0)
	sd t0, 1216(s0)
	ld t0, 1416(s0)
	sd t0, 1224(s0)
	ld t0, 1424(s0)
	sd t0, 1232(s0)
	ld t0, 1432(s0)
	sd t0, 1240(s0)
	ld t0, 1440(s0)
	sd t0, 1248(s0)
	ld t0, 1448(s0)
	sd t0, 1256(s0)
	ld t0, 1456(s0)
	sd t0, 1264(s0)
	ld t0, 1464(s0)
	sd t0, 1272(s0)
	ld t0, 1472(s0)
	sd t0, 1280(s0)
	ld t0, 1480(s0)
	sd t0, 1288(s0)
	ld t0, 1488(s0)
	sd t0, 1296(s0)
	ld t0, 1496(s0)
	sd t0, 1304(s0)
	ld t0, 1504(s0)
	sd t0, 1312(s0)
	ld t0, 1512(s0)
	sd t0, 1320(s0)
	ld t0, 1520(s0)
	sd t0, 1328(s0)
	ld t0, 1528(s0)
	sd t0, 1336(s0)
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1152
	addi a3, zero, 960
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1216
	addi a3, zero, 1024
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1280
	addi a3, zero, 384
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1152
	addi a3, zero, 1216
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 960
	addi a3, zero, 1024
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1728
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1536
	addi a3, zero, 1600
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1728
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1152
	addi a3, zero, 1280
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 960
	addi a3, zero, 384
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1856
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1536
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1856
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1216
	addi a3, zero, 1280
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1024
	addi a3, zero, 384
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1856
	addi a3, zero, 1344
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1600
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1856
	addi a3, zero, 1344
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 448
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 512
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1344
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1600
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1600
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1344
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1536
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1600
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 448
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 512
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1600
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1536
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 448
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1600
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1856
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1728
	addi a3, zero, 1344
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1344
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1728
	addi a3, zero, 1600
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1856
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1472
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 1344(s0)
	sd t0, 1920(a6)
	ld t0, 1352(s0)
	sd t0, 1928(a6)
	ld t0, 1360(s0)
	sd t0, 1936(a6)
	ld t0, 1368(s0)
	sd t0, 1944(a6)
	ld t0, 1376(s0)
	sd t0, 1952(a6)
	ld t0, 1384(s0)
	sd t0, 1960(a6)
	ld t0, 1392(s0)
	sd t0, 1968(a6)
	ld t0, 1400(s0)
	sd t0, 1976(a6)
	ld t0, 1408(s0)
	sd t0, 1984(a6)
	ld t0, 1416(s0)
	sd t0, 1992(a6)
	ld t0, 1424(s0)
	sd t0, 2000(a6)
	ld t0, 1432(s0)
	sd t0, 2008(a6)
	ld t0, 1440(s0)
	sd t0, 2016(a6)
	ld t0, 1448(s0)
	sd t0, 2024(a6)
	ld t0, 1456(s0)
	sd t0, 2032(a6)
	ld t0, 1464(s0)
	sd t0, 2040(a6)
	ld t0, 1472(s0)
	addi a6, a6, 2047
	sd t0, 1(a6)
	addi a6, a6, -2047
	ld t0, 1480(s0)
	addi a6, a6, 2047
	sd t0, 9(a6)
	addi a6, a6, -2047
	ld t0, 1488(s0)
	addi a6, a6, 2047
	sd t0, 17(a6)
	addi a6, a6, -2047
	ld t0, 1496(s0)
	addi a6, a6, 2047
	sd t0, 25(a6)
	addi a6, a6, -2047
	ld t0, 1504(s0)
	addi a6, a6, 2047
	sd t0, 33(a6)
	addi a6, a6, -2047
	ld t0, 1512(s0)
	addi a6, a6, 2047
	sd t0, 41(a6)
	addi a6, a6, -2047
	ld t0, 1520(s0)
	addi a6, a6, 2047
	sd t0, 49(a6)
	addi a6, a6, -2047
	ld t0, 1528(s0)
	addi a6, a6, 2047
	sd t0, 57(a6)
	addi a6, a6, -2047
	ld t0, 1344(s0)
	sd t0, 1152(s0)
	ld t0, 1352(s0)
	sd t0, 1160(s0)
	ld t0, 1360(s0)
	sd t0, 1168(s0)
	ld t0, 1368(s0)
	sd t0, 1176(s0)
	ld t0, 1376(s0)
	sd t0, 1184(s0)
	ld t0, 1384(s0)
	sd t0, 1192(s0)
	ld t0, 1392(s0)
	sd t0, 1200(s0)
	ld t0, 1400(s0)
	sd t0, 1208(s0)
	ld t0, 1408(s0)
	sd t0, 1216(s0)
	ld t0, 1416(s0)
	sd t0, 1224(s0)
	ld t0, 1424(s0)
	sd t0, 1232(s0)
	ld t0, 1432(s0)
	sd t0, 1240(s0)
	ld t0, 1440(s0)
	sd t0, 1248(s0)
	ld t0, 1448(s0)
	sd t0, 1256(s0)
	ld t0, 1456(s0)
	sd t0, 1264(s0)
	ld t0, 1464(s0)
	sd t0, 1272(s0)
	ld t0, 1472(s0)
	sd t0, 1280(s0)
	ld t0, 1480(s0)
	sd t0, 1288(s0)
	ld t0, 1488(s0)
	sd t0, 1296(s0)
	ld t0, 1496(s0)
	sd t0, 1304(s0)
	ld t0, 1504(s0)
	sd t0, 1312(s0)
	ld t0, 1512(s0)
	sd t0, 1320(s0)
	ld t0, 1520(s0)
	sd t0, 1328(s0)
	ld t0, 1528(s0)
	sd t0, 1336(s0)
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1152
	addi a3, zero, 960
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1216
	addi a3, zero, 1024
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1280
	addi a3, zero, 384
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1152
	addi a3, zero, 1216
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 960
	addi a3, zero, 1024
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1728
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1536
	addi a3, zero, 1600
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1728
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1152
	addi a3, zero, 1280
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 960
	addi a3, zero, 384
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1856
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1536
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1856
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1216
	addi a3, zero, 1280
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1024
	addi a3, zero, 384
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1856
	addi a3, zero, 1344
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1600
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1856
	addi a3, zero, 1344
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 448
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 512
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1344
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1600
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1600
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1344
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1536
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1600
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 448
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 512
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1600
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1536
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 448
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1600
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1856
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1728
	addi a3, zero, 1344
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1344
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1728
	addi a3, zero, 1600
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1856
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1472
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 1344(s0)
	addi a6, a6, 2047
	sd t0, 65(a6)
	addi a6, a6, -2047
	ld t0, 1352(s0)
	addi a6, a6, 2047
	sd t0, 73(a6)
	addi a6, a6, -2047
	ld t0, 1360(s0)
	addi a6, a6, 2047
	sd t0, 81(a6)
	addi a6, a6, -2047
	ld t0, 1368(s0)
	addi a6, a6, 2047
	sd t0, 89(a6)
	addi a6, a6, -2047
	ld t0, 1376(s0)
	addi a6, a6, 2047
	sd t0, 97(a6)
	addi a6, a6, -2047
	ld t0, 1384(s0)
	addi a6, a6, 2047
	sd t0, 105(a6)
	addi a6, a6, -2047
	ld t0, 1392(s0)
	addi a6, a6, 2047
	sd t0, 113(a6)
	addi a6, a6, -2047
	ld t0, 1400(s0)
	addi a6, a6, 2047
	sd t0, 121(a6)
	addi a6, a6, -2047
	ld t0, 1408(s0)
	addi a6, a6, 2047
	sd t0, 129(a6)
	addi a6, a6, -2047
	ld t0, 1416(s0)
	addi a6, a6, 2047
	sd t0, 137(a6)
	addi a6, a6, -2047
	ld t0, 1424(s0)
	addi a6, a6, 2047
	sd t0, 145(a6)
	addi a6, a6, -2047
	ld t0, 1432(s0)
	addi a6, a6, 2047
	sd t0, 153(a6)
	addi a6, a6, -2047
	ld t0, 1440(s0)
	addi a6, a6, 2047
	sd t0, 161(a6)
	addi a6, a6, -2047
	ld t0, 1448(s0)
	addi a6, a6, 2047
	sd t0, 169(a6)
	addi a6, a6, -2047
	ld t0, 1456(s0)
	addi a6, a6, 2047
	sd t0, 177(a6)
	addi a6, a6, -2047
	ld t0, 1464(s0)
	addi a6, a6, 2047
	sd t0, 185(a6)
	addi a6, a6, -2047
	ld t0, 1472(s0)
	addi a6, a6, 2047
	sd t0, 193(a6)
	addi a6, a6, -2047
	ld t0, 1480(s0)
	addi a6, a6, 2047
	sd t0, 201(a6)
	addi a6, a6, -2047
	ld t0, 1488(s0)
	addi a6, a6, 2047
	sd t0, 209(a6)
	addi a6, a6, -2047
	ld t0, 1496(s0)
	addi a6, a6, 2047
	sd t0, 217(a6)
	addi a6, a6, -2047
	ld t0, 1504(s0)
	addi a6, a6, 2047
	sd t0, 225(a6)
	addi a6, a6, -2047
	ld t0, 1512(s0)
	addi a6, a6, 2047
	sd t0, 233(a6)
	addi a6, a6, -2047
	ld t0, 1520(s0)
	addi a6, a6, 2047
	sd t0, 241(a6)
	addi a6, a6, -2047
	ld t0, 1528(s0)
	addi a6, a6, 2047
	sd t0, 249(a6)
	addi a6, a6, -2047
	ld t0, 1344(s0)
	sd t0, 1152(s0)
	ld t0, 1352(s0)
	sd t0, 1160(s0)
	ld t0, 1360(s0)
	sd t0, 1168(s0)
	ld t0, 1368(s0)
	sd t0, 1176(s0)
	ld t0, 1376(s0)
	sd t0, 1184(s0)
	ld t0, 1384(s0)
	sd t0, 1192(s0)
	ld t0, 1392(s0)
	sd t0, 1200(s0)
	ld t0, 1400(s0)
	sd t0, 1208(s0)
	ld t0, 1408(s0)
	sd t0, 1216(s0)
	ld t0, 1416(s0)
	sd t0, 1224(s0)
	ld t0, 1424(s0)
	sd t0, 1232(s0)
	ld t0, 1432(s0)
	sd t0, 1240(s0)
	ld t0, 1440(s0)
	sd t0, 1248(s0)
	ld t0, 1448(s0)
	sd t0, 1256(s0)
	ld t0, 1456(s0)
	sd t0, 1264(s0)
	ld t0, 1464(s0)
	sd t0, 1272(s0)
	ld t0, 1472(s0)
	sd t0, 1280(s0)
	ld t0, 1480(s0)
	sd t0, 1288(s0)
	ld t0, 1488(s0)
	sd t0, 1296(s0)
	ld t0, 1496(s0)
	sd t0, 1304(s0)
	ld t0, 1504(s0)
	sd t0, 1312(s0)
	ld t0, 1512(s0)
	sd t0, 1320(s0)
	ld t0, 1520(s0)
	sd t0, 1328(s0)
	ld t0, 1528(s0)
	sd t0, 1336(s0)
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1152
	addi a3, zero, 960
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1216
	addi a3, zero, 1024
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1280
	addi a3, zero, 384
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1152
	addi a3, zero, 1216
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 960
	addi a3, zero, 1024
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1728
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1536
	addi a3, zero, 1600
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1728
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1152
	addi a3, zero, 1280
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 960
	addi a3, zero, 384
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1856
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1536
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1856
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1216
	addi a3, zero, 1280
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1024
	addi a3, zero, 384
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1856
	addi a3, zero, 1344
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1600
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1856
	addi a3, zero, 1344
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 448
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 512
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1344
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1600
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1600
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1344
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1536
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1600
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 448
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 512
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1600
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1536
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 448
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1600
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1856
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1728
	addi a3, zero, 1344
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1344
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1728
	addi a3, zero, 1600
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1856
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1472
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 1344(s0)
	addi a6, a6, 2047
	sd t0, 257(a6)
	addi a6, a6, -2047
	ld t0, 1352(s0)
	addi a6, a6, 2047
	sd t0, 265(a6)
	addi a6, a6, -2047
	ld t0, 1360(s0)
	addi a6, a6, 2047
	sd t0, 273(a6)
	addi a6, a6, -2047
	ld t0, 1368(s0)
	addi a6, a6, 2047
	sd t0, 281(a6)
	addi a6, a6, -2047
	ld t0, 1376(s0)
	addi a6, a6, 2047
	sd t0, 289(a6)
	addi a6, a6, -2047
	ld t0, 1384(s0)
	addi a6, a6, 2047
	sd t0, 297(a6)
	addi a6, a6, -2047
	ld t0, 1392(s0)
	addi a6, a6, 2047
	sd t0, 305(a6)
	addi a6, a6, -2047
	ld t0, 1400(s0)
	addi a6, a6, 2047
	sd t0, 313(a6)
	addi a6, a6, -2047
	ld t0, 1408(s0)
	addi a6, a6, 2047
	sd t0, 321(a6)
	addi a6, a6, -2047
	ld t0, 1416(s0)
	addi a6, a6, 2047
	sd t0, 329(a6)
	addi a6, a6, -2047
	ld t0, 1424(s0)
	addi a6, a6, 2047
	sd t0, 337(a6)
	addi a6, a6, -2047
	ld t0, 1432(s0)
	addi a6, a6, 2047
	sd t0, 345(a6)
	addi a6, a6, -2047
	ld t0, 1440(s0)
	addi a6, a6, 2047
	sd t0, 353(a6)
	addi a6, a6, -2047
	ld t0, 1448(s0)
	addi a6, a6, 2047
	sd t0, 361(a6)
	addi a6, a6, -2047
	ld t0, 1456(s0)
	addi a6, a6, 2047
	sd t0, 369(a6)
	addi a6, a6, -2047
	ld t0, 1464(s0)
	addi a6, a6, 2047
	sd t0, 377(a6)
	addi a6, a6, -2047
	ld t0, 1472(s0)
	addi a6, a6, 2047
	sd t0, 385(a6)
	addi a6, a6, -2047
	ld t0, 1480(s0)
	addi a6, a6, 2047
	sd t0, 393(a6)
	addi a6, a6, -2047
	ld t0, 1488(s0)
	addi a6, a6, 2047
	sd t0, 401(a6)
	addi a6, a6, -2047
	ld t0, 1496(s0)
	addi a6, a6, 2047
	sd t0, 409(a6)
	addi a6, a6, -2047
	ld t0, 1504(s0)
	addi a6, a6, 2047
	sd t0, 417(a6)
	addi a6, a6, -2047
	ld t0, 1512(s0)
	addi a6, a6, 2047
	sd t0, 425(a6)
	addi a6, a6, -2047
	ld t0, 1520(s0)
	addi a6, a6, 2047
	sd t0, 433(a6)
	addi a6, a6, -2047
	ld t0, 1528(s0)
	addi a6, a6, 2047
	sd t0, 441(a6)
	addi a6, a6, -2047
	ld t0, 1344(s0)
	sd t0, 1152(s0)
	ld t0, 1352(s0)
	sd t0, 1160(s0)
	ld t0, 1360(s0)
	sd t0, 1168(s0)
	ld t0, 1368(s0)
	sd t0, 1176(s0)
	ld t0, 1376(s0)
	sd t0, 1184(s0)
	ld t0, 1384(s0)
	sd t0, 1192(s0)
	ld t0, 1392(s0)
	sd t0, 1200(s0)
	ld t0, 1400(s0)
	sd t0, 1208(s0)
	ld t0, 1408(s0)
	sd t0, 1216(s0)
	ld t0, 1416(s0)
	sd t0, 1224(s0)
	ld t0, 1424(s0)
	sd t0, 1232(s0)
	ld t0, 1432(s0)
	sd t0, 1240(s0)
	ld t0, 1440(s0)
	sd t0, 1248(s0)
	ld t0, 1448(s0)
	sd t0, 1256(s0)
	ld t0, 1456(s0)
	sd t0, 1264(s0)
	ld t0, 1464(s0)
	sd t0, 1272(s0)
	ld t0, 1472(s0)
	sd t0, 1280(s0)
	ld t0, 1480(s0)
	sd t0, 1288(s0)
	ld t0, 1488(s0)
	sd t0, 1296(s0)
	ld t0, 1496(s0)
	sd t0, 1304(s0)
	ld t0, 1504(s0)
	sd t0, 1312(s0)
	ld t0, 1512(s0)
	sd t0, 1320(s0)
	ld t0, 1520(s0)
	sd t0, 1328(s0)
	ld t0, 1528(s0)
	sd t0, 1336(s0)
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1152
	addi a3, zero, 960
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1216
	addi a3, zero, 1024
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1280
	addi a3, zero, 384
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1152
	addi a3, zero, 1216
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 960
	addi a3, zero, 1024
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1728
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1536
	addi a3, zero, 1600
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1728
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1152
	addi a3, zero, 1280
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 960
	addi a3, zero, 384
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1856
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1536
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1856
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1216
	addi a3, zero, 1280
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1024
	addi a3, zero, 384
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1856
	addi a3, zero, 1344
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1600
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1856
	addi a3, zero, 1344
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 448
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 512
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1344
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1600
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1600
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1344
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1536
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1600
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 448
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 512
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1600
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1536
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 448
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1600
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1856
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1728
	addi a3, zero, 1344
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1344
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1728
	addi a3, zero, 1600
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1856
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1472
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 1344(s0)
	addi a6, a6, 2047
	sd t0, 449(a6)
	addi a6, a6, -2047
	ld t0, 1352(s0)
	addi a6, a6, 2047
	sd t0, 457(a6)
	addi a6, a6, -2047
	ld t0, 1360(s0)
	addi a6, a6, 2047
	sd t0, 465(a6)
	addi a6, a6, -2047
	ld t0, 1368(s0)
	addi a6, a6, 2047
	sd t0, 473(a6)
	addi a6, a6, -2047
	ld t0, 1376(s0)
	addi a6, a6, 2047
	sd t0, 481(a6)
	addi a6, a6, -2047
	ld t0, 1384(s0)
	addi a6, a6, 2047
	sd t0, 489(a6)
	addi a6, a6, -2047
	ld t0, 1392(s0)
	addi a6, a6, 2047
	sd t0, 497(a6)
	addi a6, a6, -2047
	ld t0, 1400(s0)
	addi a6, a6, 2047
	sd t0, 505(a6)
	addi a6, a6, -2047
	ld t0, 1408(s0)
	addi a6, a6, 2047
	sd t0, 513(a6)
	addi a6, a6, -2047
	ld t0, 1416(s0)
	addi a6, a6, 2047
	sd t0, 521(a6)
	addi a6, a6, -2047
	ld t0, 1424(s0)
	addi a6, a6, 2047
	sd t0, 529(a6)
	addi a6, a6, -2047
	ld t0, 1432(s0)
	addi a6, a6, 2047
	sd t0, 537(a6)
	addi a6, a6, -2047
	ld t0, 1440(s0)
	addi a6, a6, 2047
	sd t0, 545(a6)
	addi a6, a6, -2047
	ld t0, 1448(s0)
	addi a6, a6, 2047
	sd t0, 553(a6)
	addi a6, a6, -2047
	ld t0, 1456(s0)
	addi a6, a6, 2047
	sd t0, 561(a6)
	addi a6, a6, -2047
	ld t0, 1464(s0)
	addi a6, a6, 2047
	sd t0, 569(a6)
	addi a6, a6, -2047
	ld t0, 1472(s0)
	addi a6, a6, 2047
	sd t0, 577(a6)
	addi a6, a6, -2047
	ld t0, 1480(s0)
	addi a6, a6, 2047
	sd t0, 585(a6)
	addi a6, a6, -2047
	ld t0, 1488(s0)
	addi a6, a6, 2047
	sd t0, 593(a6)
	addi a6, a6, -2047
	ld t0, 1496(s0)
	addi a6, a6, 2047
	sd t0, 601(a6)
	addi a6, a6, -2047
	ld t0, 1504(s0)
	addi a6, a6, 2047
	sd t0, 609(a6)
	addi a6, a6, -2047
	ld t0, 1512(s0)
	addi a6, a6, 2047
	sd t0, 617(a6)
	addi a6, a6, -2047
	ld t0, 1520(s0)
	addi a6, a6, 2047
	sd t0, 625(a6)
	addi a6, a6, -2047
	ld t0, 1528(s0)
	addi a6, a6, 2047
	sd t0, 633(a6)
	addi a6, a6, -2047
	ld t0, 1344(s0)
	sd t0, 1152(s0)
	ld t0, 1352(s0)
	sd t0, 1160(s0)
	ld t0, 1360(s0)
	sd t0, 1168(s0)
	ld t0, 1368(s0)
	sd t0, 1176(s0)
	ld t0, 1376(s0)
	sd t0, 1184(s0)
	ld t0, 1384(s0)
	sd t0, 1192(s0)
	ld t0, 1392(s0)
	sd t0, 1200(s0)
	ld t0, 1400(s0)
	sd t0, 1208(s0)
	ld t0, 1408(s0)
	sd t0, 1216(s0)
	ld t0, 1416(s0)
	sd t0, 1224(s0)
	ld t0, 1424(s0)
	sd t0, 1232(s0)
	ld t0, 1432(s0)
	sd t0, 1240(s0)
	ld t0, 1440(s0)
	sd t0, 1248(s0)
	ld t0, 1448(s0)
	sd t0, 1256(s0)
	ld t0, 1456(s0)
	sd t0, 1264(s0)
	ld t0, 1464(s0)
	sd t0, 1272(s0)
	ld t0, 1472(s0)
	sd t0, 1280(s0)
	ld t0, 1480(s0)
	sd t0, 1288(s0)
	ld t0, 1488(s0)
	sd t0, 1296(s0)
	ld t0, 1496(s0)
	sd t0, 1304(s0)
	ld t0, 1504(s0)
	sd t0, 1312(s0)
	ld t0, 1512(s0)
	sd t0, 1320(s0)
	ld t0, 1520(s0)
	sd t0, 1328(s0)
	ld t0, 1528(s0)
	sd t0, 1336(s0)
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1152
	addi a3, zero, 960
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1216
	addi a3, zero, 1024
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1280
	addi a3, zero, 384
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1152
	addi a3, zero, 1216
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 960
	addi a3, zero, 1024
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1728
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1536
	addi a3, zero, 1600
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1728
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1152
	addi a3, zero, 1280
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 960
	addi a3, zero, 384
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1856
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1536
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1856
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1216
	addi a3, zero, 1280
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1024
	addi a3, zero, 384
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1856
	addi a3, zero, 1344
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1600
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1856
	addi a3, zero, 1344
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 448
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 512
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1344
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1600
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1600
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1344
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1536
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1600
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 448
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 512
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1600
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1536
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 448
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1600
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1856
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1728
	addi a3, zero, 1344
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1344
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1728
	addi a3, zero, 1600
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1856
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1472
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 1344(s0)
	addi a6, a6, 2047
	sd t0, 641(a6)
	addi a6, a6, -2047
	ld t0, 1352(s0)
	addi a6, a6, 2047
	sd t0, 649(a6)
	addi a6, a6, -2047
	ld t0, 1360(s0)
	addi a6, a6, 2047
	sd t0, 657(a6)
	addi a6, a6, -2047
	ld t0, 1368(s0)
	addi a6, a6, 2047
	sd t0, 665(a6)
	addi a6, a6, -2047
	ld t0, 1376(s0)
	addi a6, a6, 2047
	sd t0, 673(a6)
	addi a6, a6, -2047
	ld t0, 1384(s0)
	addi a6, a6, 2047
	sd t0, 681(a6)
	addi a6, a6, -2047
	ld t0, 1392(s0)
	addi a6, a6, 2047
	sd t0, 689(a6)
	addi a6, a6, -2047
	ld t0, 1400(s0)
	addi a6, a6, 2047
	sd t0, 697(a6)
	addi a6, a6, -2047
	ld t0, 1408(s0)
	addi a6, a6, 2047
	sd t0, 705(a6)
	addi a6, a6, -2047
	ld t0, 1416(s0)
	addi a6, a6, 2047
	sd t0, 713(a6)
	addi a6, a6, -2047
	ld t0, 1424(s0)
	addi a6, a6, 2047
	sd t0, 721(a6)
	addi a6, a6, -2047
	ld t0, 1432(s0)
	addi a6, a6, 2047
	sd t0, 729(a6)
	addi a6, a6, -2047
	ld t0, 1440(s0)
	addi a6, a6, 2047
	sd t0, 737(a6)
	addi a6, a6, -2047
	ld t0, 1448(s0)
	addi a6, a6, 2047
	sd t0, 745(a6)
	addi a6, a6, -2047
	ld t0, 1456(s0)
	addi a6, a6, 2047
	sd t0, 753(a6)
	addi a6, a6, -2047
	ld t0, 1464(s0)
	addi a6, a6, 2047
	sd t0, 761(a6)
	addi a6, a6, -2047
	ld t0, 1472(s0)
	addi a6, a6, 2047
	sd t0, 769(a6)
	addi a6, a6, -2047
	ld t0, 1480(s0)
	addi a6, a6, 2047
	sd t0, 777(a6)
	addi a6, a6, -2047
	ld t0, 1488(s0)
	addi a6, a6, 2047
	sd t0, 785(a6)
	addi a6, a6, -2047
	ld t0, 1496(s0)
	addi a6, a6, 2047
	sd t0, 793(a6)
	addi a6, a6, -2047
	ld t0, 1504(s0)
	addi a6, a6, 2047
	sd t0, 801(a6)
	addi a6, a6, -2047
	ld t0, 1512(s0)
	addi a6, a6, 2047
	sd t0, 809(a6)
	addi a6, a6, -2047
	ld t0, 1520(s0)
	addi a6, a6, 2047
	sd t0, 817(a6)
	addi a6, a6, -2047
	ld t0, 1528(s0)
	addi a6, a6, 2047
	sd t0, 825(a6)
	addi a6, a6, -2047
	ld t0, 1344(s0)
	sd t0, 1152(s0)
	ld t0, 1352(s0)
	sd t0, 1160(s0)
	ld t0, 1360(s0)
	sd t0, 1168(s0)
	ld t0, 1368(s0)
	sd t0, 1176(s0)
	ld t0, 1376(s0)
	sd t0, 1184(s0)
	ld t0, 1384(s0)
	sd t0, 1192(s0)
	ld t0, 1392(s0)
	sd t0, 1200(s0)
	ld t0, 1400(s0)
	sd t0, 1208(s0)
	ld t0, 1408(s0)
	sd t0, 1216(s0)
	ld t0, 1416(s0)
	sd t0, 1224(s0)
	ld t0, 1424(s0)
	sd t0, 1232(s0)
	ld t0, 1432(s0)
	sd t0, 1240(s0)
	ld t0, 1440(s0)
	sd t0, 1248(s0)
	ld t0, 1448(s0)
	sd t0, 1256(s0)
	ld t0, 1456(s0)
	sd t0, 1264(s0)
	ld t0, 1464(s0)
	sd t0, 1272(s0)
	ld t0, 1472(s0)
	sd t0, 1280(s0)
	ld t0, 1480(s0)
	sd t0, 1288(s0)
	ld t0, 1488(s0)
	sd t0, 1296(s0)
	ld t0, 1496(s0)
	sd t0, 1304(s0)
	ld t0, 1504(s0)
	sd t0, 1312(s0)
	ld t0, 1512(s0)
	sd t0, 1320(s0)
	ld t0, 1520(s0)
	sd t0, 1328(s0)
	ld t0, 1528(s0)
	sd t0, 1336(s0)
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1152
	addi a3, zero, 960
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1216
	addi a3, zero, 1024
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1280
	addi a3, zero, 384
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1152
	addi a3, zero, 1216
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 960
	addi a3, zero, 1024
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1728
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1536
	addi a3, zero, 1600
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1728
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1152
	addi a3, zero, 1280
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 960
	addi a3, zero, 384
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1856
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1536
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1856
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1216
	addi a3, zero, 1280
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1024
	addi a3, zero, 384
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1856
	addi a3, zero, 1344
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1600
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1856
	addi a3, zero, 1344
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 448
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 512
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1344
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1600
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1600
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1344
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1536
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1600
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 448
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 512
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1600
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1536
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 448
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1600
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1856
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1728
	addi a3, zero, 1344
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1344
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1728
	addi a3, zero, 1600
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1856
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1472
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 1344(s0)
	addi a6, a6, 2047
	sd t0, 833(a6)
	addi a6, a6, -2047
	ld t0, 1352(s0)
	addi a6, a6, 2047
	sd t0, 841(a6)
	addi a6, a6, -2047
	ld t0, 1360(s0)
	addi a6, a6, 2047
	sd t0, 849(a6)
	addi a6, a6, -2047
	ld t0, 1368(s0)
	addi a6, a6, 2047
	sd t0, 857(a6)
	addi a6, a6, -2047
	ld t0, 1376(s0)
	addi a6, a6, 2047
	sd t0, 865(a6)
	addi a6, a6, -2047
	ld t0, 1384(s0)
	addi a6, a6, 2047
	sd t0, 873(a6)
	addi a6, a6, -2047
	ld t0, 1392(s0)
	addi a6, a6, 2047
	sd t0, 881(a6)
	addi a6, a6, -2047
	ld t0, 1400(s0)
	addi a6, a6, 2047
	sd t0, 889(a6)
	addi a6, a6, -2047
	ld t0, 1408(s0)
	addi a6, a6, 2047
	sd t0, 897(a6)
	addi a6, a6, -2047
	ld t0, 1416(s0)
	addi a6, a6, 2047
	sd t0, 905(a6)
	addi a6, a6, -2047
	ld t0, 1424(s0)
	addi a6, a6, 2047
	sd t0, 913(a6)
	addi a6, a6, -2047
	ld t0, 1432(s0)
	addi a6, a6, 2047
	sd t0, 921(a6)
	addi a6, a6, -2047
	ld t0, 1440(s0)
	addi a6, a6, 2047
	sd t0, 929(a6)
	addi a6, a6, -2047
	ld t0, 1448(s0)
	addi a6, a6, 2047
	sd t0, 937(a6)
	addi a6, a6, -2047
	ld t0, 1456(s0)
	addi a6, a6, 2047
	sd t0, 945(a6)
	addi a6, a6, -2047
	ld t0, 1464(s0)
	addi a6, a6, 2047
	sd t0, 953(a6)
	addi a6, a6, -2047
	ld t0, 1472(s0)
	addi a6, a6, 2047
	sd t0, 961(a6)
	addi a6, a6, -2047
	ld t0, 1480(s0)
	addi a6, a6, 2047
	sd t0, 969(a6)
	addi a6, a6, -2047
	ld t0, 1488(s0)
	addi a6, a6, 2047
	sd t0, 977(a6)
	addi a6, a6, -2047
	ld t0, 1496(s0)
	addi a6, a6, 2047
	sd t0, 985(a6)
	addi a6, a6, -2047
	ld t0, 1504(s0)
	addi a6, a6, 2047
	sd t0, 993(a6)
	addi a6, a6, -2047
	ld t0, 1512(s0)
	addi a6, a6, 2047
	sd t0, 1001(a6)
	addi a6, a6, -2047
	ld t0, 1520(s0)
	addi a6, a6, 2047
	sd t0, 1009(a6)
	addi a6, a6, -2047
	ld t0, 1528(s0)
	addi a6, a6, 2047
	sd t0, 1017(a6)
	addi a6, a6, -2047
	ld t0, 1344(s0)
	sd t0, 1152(s0)
	ld t0, 1352(s0)
	sd t0, 1160(s0)
	ld t0, 1360(s0)
	sd t0, 1168(s0)
	ld t0, 1368(s0)
	sd t0, 1176(s0)
	ld t0, 1376(s0)
	sd t0, 1184(s0)
	ld t0, 1384(s0)
	sd t0, 1192(s0)
	ld t0, 1392(s0)
	sd t0, 1200(s0)
	ld t0, 1400(s0)
	sd t0, 1208(s0)
	ld t0, 1408(s0)
	sd t0, 1216(s0)
	ld t0, 1416(s0)
	sd t0, 1224(s0)
	ld t0, 1424(s0)
	sd t0, 1232(s0)
	ld t0, 1432(s0)
	sd t0, 1240(s0)
	ld t0, 1440(s0)
	sd t0, 1248(s0)
	ld t0, 1448(s0)
	sd t0, 1256(s0)
	ld t0, 1456(s0)
	sd t0, 1264(s0)
	ld t0, 1464(s0)
	sd t0, 1272(s0)
	ld t0, 1472(s0)
	sd t0, 1280(s0)
	ld t0, 1480(s0)
	sd t0, 1288(s0)
	ld t0, 1488(s0)
	sd t0, 1296(s0)
	ld t0, 1496(s0)
	sd t0, 1304(s0)
	ld t0, 1504(s0)
	sd t0, 1312(s0)
	ld t0, 1512(s0)
	sd t0, 1320(s0)
	ld t0, 1520(s0)
	sd t0, 1328(s0)
	ld t0, 1528(s0)
	sd t0, 1336(s0)
	ld t0, 256(s0)
	sd t0, 960(s0)
	ld t0, 264(s0)
	sd t0, 968(s0)
	ld t0, 272(s0)
	sd t0, 976(s0)
	ld t0, 280(s0)
	sd t0, 984(s0)
	ld t0, 288(s0)
	sd t0, 992(s0)
	ld t0, 296(s0)
	sd t0, 1000(s0)
	ld t0, 304(s0)
	sd t0, 1008(s0)
	ld t0, 312(s0)
	sd t0, 1016(s0)
	ld t0, 384(s0)
	sd t0, 1024(s0)
	ld t0, 392(s0)
	sd t0, 1032(s0)
	ld t0, 400(s0)
	sd t0, 1040(s0)
	ld t0, 408(s0)
	sd t0, 1048(s0)
	ld t0, 416(s0)
	sd t0, 1056(s0)
	ld t0, 424(s0)
	sd t0, 1064(s0)
	ld t0, 432(s0)
	sd t0, 1072(s0)
	ld t0, 440(s0)
	sd t0, 1080(s0)
	ld t0, 256(s0)
	sd t0, 1088(s0)
	ld t0, 264(s0)
	sd t0, 1096(s0)
	ld t0, 272(s0)
	sd t0, 1104(s0)
	ld t0, 280(s0)
	sd t0, 1112(s0)
	ld t0, 288(s0)
	sd t0, 1120(s0)
	ld t0, 296(s0)
	sd t0, 1128(s0)
	ld t0, 304(s0)
	sd t0, 1136(s0)
	ld t0, 312(s0)
	sd t0, 1144(s0)
	addi s1, zero, 128
20:
	addi s1, s1, -1
	srli t0, s1, 4
	slli t0, t0, 3
	add t0, t0, s0
	addi t2, t0, 2047
	ld t2, 1(t2)
	slli t1, s1, 2
	srl t2, t2, t1
	andi t2, t2, 15
	slli a1, t2, 63
	srai a1, a1, 63
	slli a2, t2, 62
	srai a2, a2, 63
	slli a3, t2, 61
	srai a3, a3, 63
	slli a4, t2, 60
	srai a4, a4, 63
	addi a0, s0, 2047
	addi a0, a0, 2047
	addi a0, a0, 2
	ld t0, 0(a0)
	ld t1, 192(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 384(a0)
	ld t2, 576(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 768(a0)
	ld t2, 960(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1152(a0)
	ld t3, 1344(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1536(a0)
	ld t2, 1728(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1920(a0)
	addi t3, a0, 2047
	ld t3, 65(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 257(t2)
	addi t3, a0, 2047
	ld t3, 449(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 641(t3)
	addi t4, a0, 2047
	ld t4, 833(t4)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 1729(s0)
	addi s0, s0, -2047
	ld t0, 8(a0)
	ld t1, 200(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 392(a0)
	ld t2, 584(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 776(a0)
	ld t2, 968(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1160(a0)
	ld t3, 1352(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1544(a0)
	ld t2, 1736(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1928(a0)
	addi t3, a0, 2047
	ld t3, 73(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 265(t2)
	addi t3, a0, 2047
	ld t3, 457(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 649(t3)
	addi t4, a0, 2047
	ld t4, 841(t4)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 1737(s0)
	addi s0, s0, -2047
	ld t0, 16(a0)
	ld t1, 208(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 400(a0)
	ld t2, 592(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 784(a0)
	ld t2, 976(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1168(a0)
	ld t3, 1360(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1552(a0)
	ld t2, 1744(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1936(a0)
	addi t3, a0, 2047
	ld t3, 81(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 273(t2)
	addi t3, a0, 2047
	ld t3, 465(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 657(t3)
	addi t4, a0, 2047
	ld t4, 849(t4)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 1745(s0)
	addi s0, s0, -2047
	ld t0, 24(a0)
	ld t1, 216(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 408(a0)
	ld t2, 600(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 792(a0)
	ld t2, 984(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1176(a0)
	ld t3, 1368(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1560(a0)
	ld t2, 1752(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1944(a0)
	addi t3, a0, 2047
	ld t3, 89(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 281(t2)
	addi t3, a0, 2047
	ld t3, 473(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 665(t3)
	addi t4, a0, 2047
	ld t4, 857(t4)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 1753(s0)
	addi s0, s0, -2047
	ld t0, 32(a0)
	ld t1, 224(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 416(a0)
	ld t2, 608(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 800(a0)
	ld t2, 992(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1184(a0)
	ld t3, 1376(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1568(a0)
	ld t2, 1760(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1952(a0)
	addi t3, a0, 2047
	ld t3, 97(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 289(t2)
	addi t3, a0, 2047
	ld t3, 481(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 673(t3)
	addi t4, a0, 2047
	ld t4, 865(t4)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 1761(s0)
	addi s0, s0, -2047
	ld t0, 40(a0)
	ld t1, 232(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 424(a0)
	ld t2, 616(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 808(a0)
	ld t2, 1000(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1192(a0)
	ld t3, 1384(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1576(a0)
	ld t2, 1768(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1960(a0)
	addi t3, a0, 2047
	ld t3, 105(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 297(t2)
	addi t3, a0, 2047
	ld t3, 489(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 681(t3)
	addi t4, a0, 2047
	ld t4, 873(t4)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 1769(s0)
	addi s0, s0, -2047
	ld t0, 48(a0)
	ld t1, 240(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 432(a0)
	ld t2, 624(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 816(a0)
	ld t2, 1008(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1200(a0)
	ld t3, 1392(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1584(a0)
	ld t2, 1776(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1968(a0)
	addi t3, a0, 2047
	ld t3, 113(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 305(t2)
	addi t3, a0, 2047
	ld t3, 497(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 689(t3)
	addi t4, a0, 2047
	ld t4, 881(t4)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 1777(s0)
	addi s0, s0, -2047
	ld t0, 56(a0)
	ld t1, 248(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 440(a0)
	ld t2, 632(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 824(a0)
	ld t2, 1016(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1208(a0)
	ld t3, 1400(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1592(a0)
	ld t2, 1784(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1976(a0)
	addi t3, a0, 2047
	ld t3, 121(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 313(t2)
	addi t3, a0, 2047
	ld t3, 505(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 697(t3)
	addi t4, a0, 2047
	ld t4, 889(t4)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 1785(s0)
	addi s0, s0, -2047
	ld t0, 64(a0)
	ld t1, 256(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 448(a0)
	ld t2, 640(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 832(a0)
	ld t2, 1024(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1216(a0)
	ld t3, 1408(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1600(a0)
	ld t2, 1792(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1984(a0)
	addi t3, a0, 2047
	ld t3, 129(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 321(t2)
	addi t3, a0, 2047
	ld t3, 513(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 705(t3)
	addi t4, a0, 2047
	ld t4, 897(t4)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 1793(s0)
	addi s0, s0, -2047
	ld t0, 72(a0)
	ld t1, 264(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 456(a0)
	ld t2, 648(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 840(a0)
	ld t2, 1032(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1224(a0)
	ld t3, 1416(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1608(a0)
	ld t2, 1800(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1992(a0)
	addi t3, a0, 2047
	ld t3, 137(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 329(t2)
	addi t3, a0, 2047
	ld t3, 521(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 713(t3)
	addi t4, a0, 2047
	ld t4, 905(t4)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 1801(s0)
	addi s0, s0, -2047
	ld t0, 80(a0)
	ld t1, 272(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 464(a0)
	ld t2, 656(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 848(a0)
	ld t2, 1040(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1232(a0)
	ld t3, 1424(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1616(a0)
	ld t2, 1808(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 2000(a0)
	addi t3, a0, 2047
	ld t3, 145(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 337(t2)
	addi t3, a0, 2047
	ld t3, 529(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 721(t3)
	addi t4, a0, 2047
	ld t4, 913(t4)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 1809(s0)
	addi s0, s0, -2047
	ld t0, 88(a0)
	ld t1, 280(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 472(a0)
	ld t2, 664(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 856(a0)
	ld t2, 1048(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1240(a0)
	ld t3, 1432(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1624(a0)
	ld t2, 1816(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 2008(a0)
	addi t3, a0, 2047
	ld t3, 153(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 345(t2)
	addi t3, a0, 2047
	ld t3, 537(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 729(t3)
	addi t4, a0, 2047
	ld t4, 921(t4)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 1817(s0)
	addi s0, s0, -2047
	ld t0, 96(a0)
	ld t1, 288(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 480(a0)
	ld t2, 672(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 864(a0)
	ld t2, 1056(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1248(a0)
	ld t3, 1440(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1632(a0)
	ld t2, 1824(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 2016(a0)
	addi t3, a0, 2047
	ld t3, 161(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 353(t2)
	addi t3, a0, 2047
	ld t3, 545(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 737(t3)
	addi t4, a0, 2047
	ld t4, 929(t4)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 1825(s0)
	addi s0, s0, -2047
	ld t0, 104(a0)
	ld t1, 296(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 488(a0)
	ld t2, 680(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 872(a0)
	ld t2, 1064(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1256(a0)
	ld t3, 1448(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1640(a0)
	ld t2, 1832(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 2024(a0)
	addi t3, a0, 2047
	ld t3, 169(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 361(t2)
	addi t3, a0, 2047
	ld t3, 553(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 745(t3)
	addi t4, a0, 2047
	ld t4, 937(t4)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 1833(s0)
	addi s0, s0, -2047
	ld t0, 112(a0)
	ld t1, 304(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 496(a0)
	ld t2, 688(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 880(a0)
	ld t2, 1072(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1264(a0)
	ld t3, 1456(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1648(a0)
	ld t2, 1840(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 2032(a0)
	addi t3, a0, 2047
	ld t3, 177(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 369(t2)
	addi t3, a0, 2047
	ld t3, 561(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 753(t3)
	addi t4, a0, 2047
	ld t4, 945(t4)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 1841(s0)
	addi s0, s0, -2047
	ld t0, 120(a0)
	ld t1, 312(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 504(a0)
	ld t2, 696(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 888(a0)
	ld t2, 1080(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1272(a0)
	ld t3, 1464(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1656(a0)
	ld t2, 1848(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 2040(a0)
	addi t3, a0, 2047
	ld t3, 185(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 377(t2)
	addi t3, a0, 2047
	ld t3, 569(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 761(t3)
	addi t4, a0, 2047
	ld t4, 953(t4)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 1849(s0)
	addi s0, s0, -2047
	ld t0, 128(a0)
	ld t1, 320(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 512(a0)
	ld t2, 704(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 896(a0)
	ld t2, 1088(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1280(a0)
	ld t3, 1472(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1664(a0)
	ld t2, 1856(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 1(t2)
	addi t3, a0, 2047
	ld t3, 193(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 385(t2)
	addi t3, a0, 2047
	ld t3, 577(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 769(t3)
	addi t4, a0, 2047
	ld t4, 961(t4)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 1857(s0)
	addi s0, s0, -2047
	ld t0, 136(a0)
	ld t1, 328(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 520(a0)
	ld t2, 712(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 904(a0)
	ld t2, 1096(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1288(a0)
	ld t3, 1480(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1672(a0)
	ld t2, 1864(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 9(t2)
	addi t3, a0, 2047
	ld t3, 201(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 393(t2)
	addi t3, a0, 2047
	ld t3, 585(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 777(t3)
	addi t4, a0, 2047
	ld t4, 969(t4)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 1865(s0)
	addi s0, s0, -2047
	ld t0, 144(a0)
	ld t1, 336(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 528(a0)
	ld t2, 720(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 912(a0)
	ld t2, 1104(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1296(a0)
	ld t3, 1488(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1680(a0)
	ld t2, 1872(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 17(t2)
	addi t3, a0, 2047
	ld t3, 209(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 401(t2)
	addi t3, a0, 2047
	ld t3, 593(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 785(t3)
	addi t4, a0, 2047
	ld t4, 977(t4)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 1873(s0)
	addi s0, s0, -2047
	ld t0, 152(a0)
	ld t1, 344(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 536(a0)
	ld t2, 728(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 920(a0)
	ld t2, 1112(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1304(a0)
	ld t3, 1496(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1688(a0)
	ld t2, 1880(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 25(t2)
	addi t3, a0, 2047
	ld t3, 217(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 409(t2)
	addi t3, a0, 2047
	ld t3, 601(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 793(t3)
	addi t4, a0, 2047
	ld t4, 985(t4)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 1881(s0)
	addi s0, s0, -2047
	ld t0, 160(a0)
	ld t1, 352(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 544(a0)
	ld t2, 736(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 928(a0)
	ld t2, 1120(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1312(a0)
	ld t3, 1504(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1696(a0)
	ld t2, 1888(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 33(t2)
	addi t3, a0, 2047
	ld t3, 225(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 417(t2)
	addi t3, a0, 2047
	ld t3, 609(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 801(t3)
	addi t4, a0, 2047
	ld t4, 993(t4)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 1889(s0)
	addi s0, s0, -2047
	ld t0, 168(a0)
	ld t1, 360(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 552(a0)
	ld t2, 744(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 936(a0)
	ld t2, 1128(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1320(a0)
	ld t3, 1512(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1704(a0)
	ld t2, 1896(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 41(t2)
	addi t3, a0, 2047
	ld t3, 233(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 425(t2)
	addi t3, a0, 2047
	ld t3, 617(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 809(t3)
	addi t4, a0, 2047
	ld t4, 1001(t4)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 1897(s0)
	addi s0, s0, -2047
	ld t0, 176(a0)
	ld t1, 368(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 560(a0)
	ld t2, 752(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 944(a0)
	ld t2, 1136(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1328(a0)
	ld t3, 1520(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1712(a0)
	ld t2, 1904(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 49(t2)
	addi t3, a0, 2047
	ld t3, 241(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 433(t2)
	addi t3, a0, 2047
	ld t3, 625(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 817(t3)
	addi t4, a0, 2047
	ld t4, 1009(t4)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 1905(s0)
	addi s0, s0, -2047
	ld t0, 184(a0)
	ld t1, 376(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 568(a0)
	ld t2, 760(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 952(a0)
	ld t2, 1144(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1336(a0)
	ld t3, 1528(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1720(a0)
	ld t2, 1912(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 57(t2)
	addi t3, a0, 2047
	ld t3, 249(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 441(t2)
	addi t3, a0, 2047
	ld t3, 633(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 825(t3)
	addi t4, a0, 2047
	ld t4, 1017(t4)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 1913(s0)
	addi s0, s0, -2047
	addi a0, s0, 0
	addi a1, zero, 1152
	addi a2, zero, 960
	addi a3, zero, 1088
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1088
	addi a3, zero, 1088
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1024
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1280
	addi a2, zero, 1088
	addi a3, zero, 256
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1152
	addi a3, zero, 1152
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1216
	addi a3, zero, 1216
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1600
	addi a3, zero, 1600
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1152
	addi a3, zero, 1600
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1728
	addi a3, zero, 1728
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1728
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1728
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1728
	addi a3, zero, 1728
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1280
	addi a3, zero, 1280
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 448
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1536
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1856
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1856
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1216
	addi a3, zero, 1280
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1472
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1792
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1344
	addi a3, zero, 1728
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1344
	addi a3, zero, 1728
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1728
	addi a3, zero, 1344
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1792
	addi a3, zero, 1408
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1664
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1664
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1664
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1344
	addi a3, zero, 1344
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1408
	addi a3, zero, 1408
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1600
	addi a3, zero, 1600
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1344
	addi a3, zero, 1600
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1728
	addi a3, zero, 1728
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1728
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1728
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1728
	addi a3, zero, 1728
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1472
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 448
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1536
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1856
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1856
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1280
	addi a2, zero, 1408
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1280
	addi a2, zero, 1280
	addi a3, zero, 1280
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1152
	addi a2, zero, 1792
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1152
	addi a2, zero, 1152
	addi a3, zero, 1728
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1152
	addi a2, zero, 1152
	addi a3, zero, 1728
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1728
	addi a3, zero, 1152
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1792
	addi a3, zero, 1216
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1664
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1664
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1664
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1152
	addi a3, zero, 1152
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1216
	addi a3, zero, 1216
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1600
	addi a3, zero, 1600
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1152
	addi a3, zero, 1600
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1728
	addi a3, zero, 1728
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1728
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1728
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1728
	addi a3, zero, 1728
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1280
	addi a3, zero, 1280
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 448
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1536
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1856
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1856
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1216
	addi a3, zero, 1280
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1472
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1792
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1344
	addi a3, zero, 1728
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1344
	addi a3, zero, 1728
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1728
	addi a3, zero, 1344
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1792
	addi a3, zero, 1408
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1664
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1664
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1664
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1344
	addi a3, zero, 1344
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1408
	addi a3, zero, 1408
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1600
	addi a3, zero, 1600
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1344
	addi a3, zero, 1600
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1728
	addi a3, zero, 1728
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1728
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1728
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1728
	addi a3, zero, 1728
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1472
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 448
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1536
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1856
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1856
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1280
	addi a2, zero, 1408
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1280
	addi a2, zero, 1280
	addi a3, zero, 1280
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1152
	addi a2, zero, 1792
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1152
	addi a2, zero, 1152
	addi a3, zero, 1728
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1152
	addi a2, zero, 1152
	addi a3, zero, 1728
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1728
	addi a3, zero, 1152
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1792
	addi a3, zero, 1216
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1664
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1664
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1664
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 960
	addi a2, zero, 1152
	addi a3, zero, 1280
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1280
	addi a3, zero, 1280
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1088
	addi a2, zero, 1536
	addi a3, zero, 1280
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1216
	addi a3, zero, 256
	call {vg_brainpoolp512r1_add_mod_p}
	addi t3, zero, 0
	ld t4, 1088(s0)
	or t3, t3, t4
	ld t4, 1096(s0)
	or t3, t3, t4
	ld t4, 1104(s0)
	or t3, t3, t4
	ld t4, 1112(s0)
	or t3, t3, t4
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
	ld t0, 1024(s0)
	ld t1, 384(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1024(s0)
	ld t0, 1032(s0)
	ld t1, 392(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1032(s0)
	ld t0, 1040(s0)
	ld t1, 400(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1040(s0)
	ld t0, 1048(s0)
	ld t1, 408(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1048(s0)
	ld t0, 1056(s0)
	ld t1, 416(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1056(s0)
	ld t0, 1064(s0)
	ld t1, 424(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1064(s0)
	ld t0, 1072(s0)
	ld t1, 432(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1072(s0)
	ld t0, 1080(s0)
	ld t1, 440(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1080(s0)
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 960
	addi a3, zero, 2047
	addi a3, a3, 1729
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1024
	addi a3, zero, 2047
	addi a3, a3, 1793
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1088
	addi a3, zero, 2047
	addi a3, a3, 1857
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 960
	addi a3, zero, 1024
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 2047
	addi a2, a2, 1729
	addi a3, zero, 2047
	addi a3, a3, 1793
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1728
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1536
	addi a3, zero, 1600
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1728
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 960
	addi a3, zero, 1088
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 2047
	addi a2, a2, 1729
	addi a3, zero, 2047
	addi a3, a3, 1857
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1856
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1536
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1856
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1024
	addi a3, zero, 1088
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 2047
	addi a2, a2, 1793
	addi a3, zero, 2047
	addi a3, a3, 1857
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1856
	addi a3, zero, 1344
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1600
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1856
	addi a3, zero, 1344
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 448
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 512
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1344
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1600
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1600
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1344
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1536
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1600
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 448
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 512
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1600
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1536
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 448
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1600
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1856
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1728
	addi a3, zero, 1344
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1344
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1728
	addi a3, zero, 1600
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1856
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1472
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	ld t0, 1344(s0)
	sd t0, 960(s0)
	ld t0, 1352(s0)
	sd t0, 968(s0)
	ld t0, 1360(s0)
	sd t0, 976(s0)
	ld t0, 1368(s0)
	sd t0, 984(s0)
	ld t0, 1376(s0)
	sd t0, 992(s0)
	ld t0, 1384(s0)
	sd t0, 1000(s0)
	ld t0, 1392(s0)
	sd t0, 1008(s0)
	ld t0, 1400(s0)
	sd t0, 1016(s0)
	ld t0, 1408(s0)
	sd t0, 1024(s0)
	ld t0, 1416(s0)
	sd t0, 1032(s0)
	ld t0, 1424(s0)
	sd t0, 1040(s0)
	ld t0, 1432(s0)
	sd t0, 1048(s0)
	ld t0, 1440(s0)
	sd t0, 1056(s0)
	ld t0, 1448(s0)
	sd t0, 1064(s0)
	ld t0, 1456(s0)
	sd t0, 1072(s0)
	ld t0, 1464(s0)
	sd t0, 1080(s0)
	ld t0, 1472(s0)
	sd t0, 1088(s0)
	ld t0, 1480(s0)
	sd t0, 1096(s0)
	ld t0, 1488(s0)
	sd t0, 1104(s0)
	ld t0, 1496(s0)
	sd t0, 1112(s0)
	ld t0, 1504(s0)
	sd t0, 1120(s0)
	ld t0, 1512(s0)
	sd t0, 1128(s0)
	ld t0, 1520(s0)
	sd t0, 1136(s0)
	ld t0, 1528(s0)
	sd t0, 1144(s0)
	bnez s1, 20b
	addi ra, s0, 2047
	ld ra, 913(ra)
	addi s1, s0, 2047
	ld s1, 905(s1)
	addi s0, s0, 2047
	ld s0, 897(s0)
	ret
	.option pop
