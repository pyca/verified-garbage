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
	ld t0, 960(s0)
	sd t0, 1920(s0)
	ld t0, 968(s0)
	sd t0, 1928(s0)
	ld t0, 976(s0)
	sd t0, 1936(s0)
	ld t0, 984(s0)
	sd t0, 1944(s0)
	ld t0, 992(s0)
	sd t0, 1952(s0)
	ld t0, 1000(s0)
	sd t0, 1960(s0)
	ld t0, 1008(s0)
	sd t0, 1968(s0)
	ld t0, 1016(s0)
	sd t0, 1976(s0)
	ld t0, 1024(s0)
	sd t0, 1984(s0)
	ld t0, 1032(s0)
	sd t0, 1992(s0)
	ld t0, 1040(s0)
	sd t0, 2000(s0)
	ld t0, 1048(s0)
	sd t0, 2008(s0)
	ld t0, 1056(s0)
	sd t0, 2016(s0)
	ld t0, 1064(s0)
	sd t0, 2024(s0)
	ld t0, 1072(s0)
	sd t0, 2032(s0)
	ld t0, 1080(s0)
	sd t0, 2040(s0)
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
	addi s1, zero, 512
20:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 960
	addi a3, zero, 960
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1024
	addi a3, zero, 1024
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1088
	addi a3, zero, 1088
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 960
	addi a3, zero, 1024
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
	addi a2, zero, 960
	addi a3, zero, 1088
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 960
	addi a3, zero, 1088
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
	addi a1, zero, 1152
	addi a2, zero, 1024
	addi a3, zero, 1088
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1856
	addi a3, zero, 1152
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1152
	addi a2, zero, 1600
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1856
	addi a3, zero, 1152
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1280
	addi a2, zero, 448
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1152
	addi a2, zero, 512
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1280
	addi a2, zero, 1152
	addi a3, zero, 1280
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1152
	addi a2, zero, 1600
	addi a3, zero, 1280
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1280
	addi a2, zero, 1600
	addi a3, zero, 1280
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1152
	addi a3, zero, 1280
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
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1856
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1152
	addi a2, zero, 1728
	addi a3, zero, 1152
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1152
	addi a2, zero, 1152
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1728
	addi a3, zero, 1600
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1280
	addi a2, zero, 1856
	addi a3, zero, 1280
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1280
	addi a2, zero, 1280
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1152
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1216
	addi a3, zero, 1984
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
	addi a2, zero, 1920
	addi a3, zero, 1984
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
	addi a2, zero, 1920
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
	addi a2, zero, 1984
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
	srli t0, s1, 6
	slli t0, t0, 3
	add t0, t0, s0
	addi t1, t0, 2047
	ld t1, 1(t1)
	srl t1, t1, s1
	andi t1, t1, 1
	addi t2, zero, 0
	sub a7, t2, t1
	ld t0, 1152(s0)
	ld t1, 1344(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 960(s0)
	ld t0, 1160(s0)
	ld t1, 1352(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 968(s0)
	ld t0, 1168(s0)
	ld t1, 1360(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 976(s0)
	ld t0, 1176(s0)
	ld t1, 1368(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 984(s0)
	ld t0, 1184(s0)
	ld t1, 1376(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 992(s0)
	ld t0, 1192(s0)
	ld t1, 1384(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1000(s0)
	ld t0, 1200(s0)
	ld t1, 1392(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1008(s0)
	ld t0, 1208(s0)
	ld t1, 1400(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1016(s0)
	ld t0, 1216(s0)
	ld t1, 1408(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1024(s0)
	ld t0, 1224(s0)
	ld t1, 1416(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1032(s0)
	ld t0, 1232(s0)
	ld t1, 1424(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1040(s0)
	ld t0, 1240(s0)
	ld t1, 1432(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1048(s0)
	ld t0, 1248(s0)
	ld t1, 1440(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1056(s0)
	ld t0, 1256(s0)
	ld t1, 1448(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1064(s0)
	ld t0, 1264(s0)
	ld t1, 1456(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1072(s0)
	ld t0, 1272(s0)
	ld t1, 1464(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1080(s0)
	ld t0, 1280(s0)
	ld t1, 1472(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1088(s0)
	ld t0, 1288(s0)
	ld t1, 1480(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1096(s0)
	ld t0, 1296(s0)
	ld t1, 1488(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1104(s0)
	ld t0, 1304(s0)
	ld t1, 1496(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1112(s0)
	ld t0, 1312(s0)
	ld t1, 1504(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1120(s0)
	ld t0, 1320(s0)
	ld t1, 1512(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1128(s0)
	ld t0, 1328(s0)
	ld t1, 1520(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1136(s0)
	ld t0, 1336(s0)
	ld t1, 1528(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
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
