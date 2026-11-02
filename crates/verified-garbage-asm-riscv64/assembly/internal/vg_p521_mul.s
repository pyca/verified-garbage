// The functions of `src/internal/vg_p521_mul.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p521_mul:
	.option push
	.option arch, +m, +c
	addi a0, a0, 2047
	sd s0, 1257(a0)
	addi a0, a0, -2047
	addi a0, a0, 2047
	sd s1, 1265(a0)
	addi a0, a0, -2047
	addi a0, a0, 2047
	sd ra, 1273(a0)
	addi a0, a0, -2047
	addi s0, a0, 0
	ld t0, 1072(s0)
	addi s0, s0, 2047
	sd t0, 105(s0)
	addi s0, s0, -2047
	ld t0, 1080(s0)
	addi s0, s0, 2047
	sd t0, 113(s0)
	addi s0, s0, -2047
	ld t0, 1088(s0)
	addi s0, s0, 2047
	sd t0, 121(s0)
	addi s0, s0, -2047
	ld t0, 1096(s0)
	addi s0, s0, 2047
	sd t0, 129(s0)
	addi s0, s0, -2047
	ld t0, 1104(s0)
	addi s0, s0, 2047
	sd t0, 137(s0)
	addi s0, s0, -2047
	ld t0, 1112(s0)
	addi s0, s0, 2047
	sd t0, 145(s0)
	addi s0, s0, -2047
	ld t0, 1120(s0)
	addi s0, s0, 2047
	sd t0, 153(s0)
	addi s0, s0, -2047
	ld t0, 1128(s0)
	addi s0, s0, 2047
	sd t0, 161(s0)
	addi s0, s0, -2047
	ld t0, 1136(s0)
	addi s0, s0, 2047
	sd t0, 169(s0)
	addi s0, s0, -2047
	ld t0, 1144(s0)
	addi s0, s0, 2047
	sd t0, 177(s0)
	addi s0, s0, -2047
	ld t0, 1152(s0)
	addi s0, s0, 2047
	sd t0, 185(s0)
	addi s0, s0, -2047
	ld t0, 1160(s0)
	addi s0, s0, 2047
	sd t0, 193(s0)
	addi s0, s0, -2047
	ld t0, 1168(s0)
	addi s0, s0, 2047
	sd t0, 201(s0)
	addi s0, s0, -2047
	ld t0, 1176(s0)
	addi s0, s0, 2047
	sd t0, 209(s0)
	addi s0, s0, -2047
	ld t0, 1184(s0)
	addi s0, s0, 2047
	sd t0, 217(s0)
	addi s0, s0, -2047
	ld t0, 1192(s0)
	addi s0, s0, 2047
	sd t0, 225(s0)
	addi s0, s0, -2047
	ld t0, 1200(s0)
	addi s0, s0, 2047
	sd t0, 233(s0)
	addi s0, s0, -2047
	ld t0, 1208(s0)
	addi s0, s0, 2047
	sd t0, 241(s0)
	addi s0, s0, -2047
	ld t0, 280(s0)
	sd t0, 1072(s0)
	ld t0, 288(s0)
	sd t0, 1080(s0)
	ld t0, 296(s0)
	sd t0, 1088(s0)
	ld t0, 304(s0)
	sd t0, 1096(s0)
	ld t0, 312(s0)
	sd t0, 1104(s0)
	ld t0, 320(s0)
	sd t0, 1112(s0)
	ld t0, 328(s0)
	sd t0, 1120(s0)
	ld t0, 336(s0)
	sd t0, 1128(s0)
	ld t0, 344(s0)
	sd t0, 1136(s0)
	ld t0, 424(s0)
	sd t0, 1144(s0)
	ld t0, 432(s0)
	sd t0, 1152(s0)
	ld t0, 440(s0)
	sd t0, 1160(s0)
	ld t0, 448(s0)
	sd t0, 1168(s0)
	ld t0, 456(s0)
	sd t0, 1176(s0)
	ld t0, 464(s0)
	sd t0, 1184(s0)
	ld t0, 472(s0)
	sd t0, 1192(s0)
	ld t0, 480(s0)
	sd t0, 1200(s0)
	ld t0, 488(s0)
	sd t0, 1208(s0)
	ld t0, 280(s0)
	sd t0, 1216(s0)
	ld t0, 288(s0)
	sd t0, 1224(s0)
	ld t0, 296(s0)
	sd t0, 1232(s0)
	ld t0, 304(s0)
	sd t0, 1240(s0)
	ld t0, 312(s0)
	sd t0, 1248(s0)
	ld t0, 320(s0)
	sd t0, 1256(s0)
	ld t0, 328(s0)
	sd t0, 1264(s0)
	ld t0, 336(s0)
	sd t0, 1272(s0)
	ld t0, 344(s0)
	sd t0, 1280(s0)
	addi s1, zero, 576
20:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1720
	addi a2, zero, 1072
	addi a3, zero, 1072
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1144
	addi a3, zero, 1144
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1864
	addi a2, zero, 1216
	addi a3, zero, 1216
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1936
	addi a2, zero, 1072
	addi a3, zero, 1144
	call {vg_p521_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2008
	addi a2, zero, 1072
	addi a3, zero, 1144
	call {vg_p521_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1936
	addi a2, zero, 1936
	addi a3, zero, 2008
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2008
	addi a2, zero, 1720
	addi a3, zero, 1792
	call {vg_p521_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1936
	addi a2, zero, 1936
	addi a3, zero, 2008
	call {vg_p521_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2008
	addi a2, zero, 1072
	addi a3, zero, 1216
	call {vg_p521_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 33
	addi a2, zero, 1072
	addi a3, zero, 1216
	call {vg_p521_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2008
	addi a2, zero, 2008
	addi a3, zero, 2047
	addi a3, a3, 33
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 33
	addi a2, zero, 1720
	addi a3, zero, 1864
	call {vg_p521_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2008
	addi a2, zero, 2008
	addi a3, zero, 2047
	addi a3, a3, 33
	call {vg_p521_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 33
	addi a2, zero, 1144
	addi a3, zero, 1216
	call {vg_p521_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1288
	addi a2, zero, 1144
	addi a3, zero, 1216
	call {vg_p521_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 33
	addi a2, zero, 2047
	addi a2, a2, 33
	addi a3, zero, 1288
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1288
	addi a2, zero, 1792
	addi a3, zero, 1864
	call {vg_p521_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 33
	addi a2, zero, 2047
	addi a2, a2, 33
	addi a3, zero, 1288
	call {vg_p521_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1432
	addi a2, zero, 496
	addi a3, zero, 2008
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1288
	addi a2, zero, 568
	addi a3, zero, 1864
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1432
	addi a2, zero, 1288
	addi a3, zero, 1432
	call {vg_p521_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1288
	addi a2, zero, 1792
	addi a3, zero, 1432
	call {vg_p521_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1432
	addi a2, zero, 1792
	addi a3, zero, 1432
	call {vg_p521_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1288
	addi a3, zero, 1432
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1720
	addi a3, zero, 1720
	call {vg_p521_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1720
	call {vg_p521_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1864
	addi a2, zero, 496
	addi a3, zero, 1864
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2008
	addi a2, zero, 568
	addi a3, zero, 2008
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1864
	call {vg_p521_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1864
	addi a2, zero, 1720
	addi a3, zero, 1864
	call {vg_p521_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1864
	addi a2, zero, 496
	addi a3, zero, 1864
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2008
	addi a2, zero, 2008
	addi a3, zero, 1864
	call {vg_p521_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1720
	addi a2, zero, 1792
	addi a3, zero, 2008
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1720
	call {vg_p521_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1720
	addi a2, zero, 2047
	addi a2, a2, 33
	addi a3, zero, 2008
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1288
	addi a2, zero, 1936
	addi a3, zero, 1288
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1288
	addi a2, zero, 1288
	addi a3, zero, 1720
	call {vg_p521_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1720
	addi a2, zero, 1936
	addi a3, zero, 1792
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1432
	addi a2, zero, 2047
	addi a2, a2, 33
	addi a3, zero, 1432
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1432
	addi a2, zero, 1432
	addi a3, zero, 1720
	call {vg_p521_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1720
	addi a2, zero, 1288
	addi a3, zero, 2047
	addi a3, a3, 105
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1360
	addi a3, zero, 2047
	addi a3, a3, 177
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1864
	addi a2, zero, 1432
	addi a3, zero, 424
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1936
	addi a2, zero, 1288
	addi a3, zero, 1360
	call {vg_p521_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2008
	addi a2, zero, 2047
	addi a2, a2, 105
	addi a3, zero, 2047
	addi a3, a3, 177
	call {vg_p521_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1936
	addi a2, zero, 1936
	addi a3, zero, 2008
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2008
	addi a2, zero, 1720
	addi a3, zero, 1792
	call {vg_p521_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1936
	addi a2, zero, 1936
	addi a3, zero, 2008
	call {vg_p521_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2008
	addi a2, zero, 1288
	addi a3, zero, 1432
	call {vg_p521_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 33
	addi a2, zero, 2047
	addi a2, a2, 105
	addi a3, zero, 424
	call {vg_p521_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2008
	addi a2, zero, 2008
	addi a3, zero, 2047
	addi a3, a3, 33
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 33
	addi a2, zero, 1720
	addi a3, zero, 1864
	call {vg_p521_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2008
	addi a2, zero, 2008
	addi a3, zero, 2047
	addi a3, a3, 33
	call {vg_p521_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 33
	addi a2, zero, 1360
	addi a3, zero, 1432
	call {vg_p521_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1504
	addi a2, zero, 2047
	addi a2, a2, 177
	addi a3, zero, 424
	call {vg_p521_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 33
	addi a2, zero, 2047
	addi a2, a2, 33
	addi a3, zero, 1504
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1504
	addi a2, zero, 1792
	addi a3, zero, 1864
	call {vg_p521_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 33
	addi a2, zero, 2047
	addi a2, a2, 33
	addi a3, zero, 1504
	call {vg_p521_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1648
	addi a2, zero, 496
	addi a3, zero, 2008
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1504
	addi a2, zero, 568
	addi a3, zero, 1864
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1648
	addi a2, zero, 1504
	addi a3, zero, 1648
	call {vg_p521_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1504
	addi a2, zero, 1792
	addi a3, zero, 1648
	call {vg_p521_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1648
	addi a2, zero, 1792
	addi a3, zero, 1648
	call {vg_p521_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1576
	addi a2, zero, 1504
	addi a3, zero, 1648
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1720
	addi a3, zero, 1720
	call {vg_p521_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1720
	call {vg_p521_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1864
	addi a2, zero, 496
	addi a3, zero, 1864
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2008
	addi a2, zero, 568
	addi a3, zero, 2008
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1864
	call {vg_p521_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1864
	addi a2, zero, 1720
	addi a3, zero, 1864
	call {vg_p521_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1864
	addi a2, zero, 496
	addi a3, zero, 1864
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2008
	addi a2, zero, 2008
	addi a3, zero, 1864
	call {vg_p521_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1720
	addi a2, zero, 1792
	addi a3, zero, 2008
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1576
	addi a2, zero, 1576
	addi a3, zero, 1720
	call {vg_p521_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1720
	addi a2, zero, 2047
	addi a2, a2, 33
	addi a3, zero, 2008
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1504
	addi a2, zero, 1936
	addi a3, zero, 1504
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1504
	addi a2, zero, 1504
	addi a3, zero, 1720
	call {vg_p521_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1720
	addi a2, zero, 1936
	addi a3, zero, 1792
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1648
	addi a2, zero, 2047
	addi a2, a2, 33
	addi a3, zero, 1648
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1648
	addi a2, zero, 1648
	addi a3, zero, 1720
	call {vg_p521_add_mod_p}
	srli t0, s1, 6
	slli t0, t0, 3
	add t0, t0, s0
	addi t1, t0, 2047
	ld t1, 249(t1)
	srl t1, t1, s1
	andi t1, t1, 1
	addi t2, zero, 0
	sub a7, t2, t1
	ld t0, 1288(s0)
	ld t1, 1504(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1072(s0)
	ld t0, 1296(s0)
	ld t1, 1512(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1080(s0)
	ld t0, 1304(s0)
	ld t1, 1520(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1088(s0)
	ld t0, 1312(s0)
	ld t1, 1528(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1096(s0)
	ld t0, 1320(s0)
	ld t1, 1536(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1104(s0)
	ld t0, 1328(s0)
	ld t1, 1544(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1112(s0)
	ld t0, 1336(s0)
	ld t1, 1552(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1120(s0)
	ld t0, 1344(s0)
	ld t1, 1560(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1128(s0)
	ld t0, 1352(s0)
	ld t1, 1568(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1136(s0)
	ld t0, 1360(s0)
	ld t1, 1576(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1144(s0)
	ld t0, 1368(s0)
	ld t1, 1584(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1152(s0)
	ld t0, 1376(s0)
	ld t1, 1592(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1160(s0)
	ld t0, 1384(s0)
	ld t1, 1600(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1168(s0)
	ld t0, 1392(s0)
	ld t1, 1608(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1176(s0)
	ld t0, 1400(s0)
	ld t1, 1616(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1184(s0)
	ld t0, 1408(s0)
	ld t1, 1624(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1192(s0)
	ld t0, 1416(s0)
	ld t1, 1632(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1200(s0)
	ld t0, 1424(s0)
	ld t1, 1640(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1208(s0)
	ld t0, 1432(s0)
	ld t1, 1648(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1216(s0)
	ld t0, 1440(s0)
	ld t1, 1656(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1224(s0)
	ld t0, 1448(s0)
	ld t1, 1664(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1232(s0)
	ld t0, 1456(s0)
	ld t1, 1672(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1240(s0)
	ld t0, 1464(s0)
	ld t1, 1680(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1248(s0)
	ld t0, 1472(s0)
	ld t1, 1688(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1256(s0)
	ld t0, 1480(s0)
	ld t1, 1696(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1264(s0)
	ld t0, 1488(s0)
	ld t1, 1704(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1272(s0)
	ld t0, 1496(s0)
	ld t1, 1712(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1280(s0)
	bnez s1, 20b
	addi ra, s0, 2047
	ld ra, 1273(ra)
	addi s1, s0, 2047
	ld s1, 1265(s1)
	addi s0, s0, 2047
	ld s0, 1257(s0)
	ret
	.option pop
