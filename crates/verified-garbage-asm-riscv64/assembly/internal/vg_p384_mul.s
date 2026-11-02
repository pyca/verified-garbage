// The functions of `src/internal/vg_p384_mul.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p384_mul:
	.option push
	.option arch, +m, +c
	addi a0, a0, 2047
	sd s0, 177(a0)
	addi a0, a0, -2047
	addi a0, a0, 2047
	sd s1, 185(a0)
	addi a0, a0, -2047
	addi a0, a0, 2047
	sd ra, 193(a0)
	addi a0, a0, -2047
	addi s0, a0, 0
	ld t0, 736(s0)
	sd t0, 1456(s0)
	ld t0, 744(s0)
	sd t0, 1464(s0)
	ld t0, 752(s0)
	sd t0, 1472(s0)
	ld t0, 760(s0)
	sd t0, 1480(s0)
	ld t0, 768(s0)
	sd t0, 1488(s0)
	ld t0, 776(s0)
	sd t0, 1496(s0)
	ld t0, 784(s0)
	sd t0, 1504(s0)
	ld t0, 792(s0)
	sd t0, 1512(s0)
	ld t0, 800(s0)
	sd t0, 1520(s0)
	ld t0, 808(s0)
	sd t0, 1528(s0)
	ld t0, 816(s0)
	sd t0, 1536(s0)
	ld t0, 824(s0)
	sd t0, 1544(s0)
	ld t0, 208(s0)
	sd t0, 736(s0)
	ld t0, 216(s0)
	sd t0, 744(s0)
	ld t0, 224(s0)
	sd t0, 752(s0)
	ld t0, 232(s0)
	sd t0, 760(s0)
	ld t0, 240(s0)
	sd t0, 768(s0)
	ld t0, 248(s0)
	sd t0, 776(s0)
	ld t0, 304(s0)
	sd t0, 784(s0)
	ld t0, 312(s0)
	sd t0, 792(s0)
	ld t0, 320(s0)
	sd t0, 800(s0)
	ld t0, 328(s0)
	sd t0, 808(s0)
	ld t0, 336(s0)
	sd t0, 816(s0)
	ld t0, 344(s0)
	sd t0, 824(s0)
	ld t0, 208(s0)
	sd t0, 832(s0)
	ld t0, 216(s0)
	sd t0, 840(s0)
	ld t0, 224(s0)
	sd t0, 848(s0)
	ld t0, 232(s0)
	sd t0, 856(s0)
	ld t0, 240(s0)
	sd t0, 864(s0)
	ld t0, 248(s0)
	sd t0, 872(s0)
	addi s1, zero, 384
20:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 736
	addi a3, zero, 736
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 784
	addi a3, zero, 784
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 832
	addi a3, zero, 832
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 736
	addi a3, zero, 784
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 736
	addi a3, zero, 784
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1168
	addi a3, zero, 1216
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_p384_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 736
	addi a3, zero, 832
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 736
	addi a3, zero, 832
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_p384_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 784
	addi a3, zero, 832
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 880
	addi a2, zero, 784
	addi a3, zero, 832
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 880
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 880
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 880
	call {vg_p384_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 976
	addi a2, zero, 352
	addi a3, zero, 1360
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 880
	addi a2, zero, 400
	addi a3, zero, 1264
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 976
	addi a2, zero, 880
	addi a3, zero, 976
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 880
	addi a2, zero, 1216
	addi a3, zero, 976
	call {vg_p384_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 976
	addi a2, zero, 1216
	addi a3, zero, 976
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 928
	addi a2, zero, 880
	addi a3, zero, 976
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1168
	addi a3, zero, 1168
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1168
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 400
	addi a3, zero, 1360
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_p384_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1264
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1216
	addi a3, zero, 1360
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 928
	addi a2, zero, 928
	addi a3, zero, 1168
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1408
	addi a3, zero, 1360
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 880
	addi a2, zero, 1312
	addi a3, zero, 880
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 880
	addi a2, zero, 880
	addi a3, zero, 1168
	call {vg_p384_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1312
	addi a3, zero, 1216
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 976
	addi a2, zero, 1408
	addi a3, zero, 976
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 976
	addi a2, zero, 976
	addi a3, zero, 1168
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 880
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 928
	addi a3, zero, 1504
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 976
	addi a3, zero, 304
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 880
	addi a3, zero, 928
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1456
	addi a3, zero, 1504
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1168
	addi a3, zero, 1216
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_p384_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 880
	addi a3, zero, 976
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1456
	addi a3, zero, 304
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_p384_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 928
	addi a3, zero, 976
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1504
	addi a3, zero, 304
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1024
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1024
	call {vg_p384_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 352
	addi a3, zero, 1360
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 400
	addi a3, zero, 1264
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1024
	addi a3, zero, 1120
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1216
	addi a3, zero, 1120
	call {vg_p384_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1216
	addi a3, zero, 1120
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1024
	addi a3, zero, 1120
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1168
	addi a3, zero, 1168
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1168
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 400
	addi a3, zero, 1360
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_p384_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1264
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1216
	addi a3, zero, 1360
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1072
	addi a3, zero, 1168
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1408
	addi a3, zero, 1360
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1312
	addi a3, zero, 1024
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1168
	call {vg_p384_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1312
	addi a3, zero, 1216
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1408
	addi a3, zero, 1120
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1120
	addi a3, zero, 1168
	call {vg_p384_add_mod_p}
	srli t0, s1, 6
	slli t0, t0, 3
	add t0, t0, s0
	ld t1, 1552(t0)
	srl t1, t1, s1
	andi t1, t1, 1
	addi t2, zero, 0
	sub a7, t2, t1
	ld t0, 880(s0)
	ld t1, 1024(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 736(s0)
	ld t0, 888(s0)
	ld t1, 1032(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 744(s0)
	ld t0, 896(s0)
	ld t1, 1040(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 752(s0)
	ld t0, 904(s0)
	ld t1, 1048(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 760(s0)
	ld t0, 912(s0)
	ld t1, 1056(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 768(s0)
	ld t0, 920(s0)
	ld t1, 1064(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 776(s0)
	ld t0, 928(s0)
	ld t1, 1072(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 784(s0)
	ld t0, 936(s0)
	ld t1, 1080(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 792(s0)
	ld t0, 944(s0)
	ld t1, 1088(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 800(s0)
	ld t0, 952(s0)
	ld t1, 1096(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 808(s0)
	ld t0, 960(s0)
	ld t1, 1104(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 816(s0)
	ld t0, 968(s0)
	ld t1, 1112(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 824(s0)
	ld t0, 976(s0)
	ld t1, 1120(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 832(s0)
	ld t0, 984(s0)
	ld t1, 1128(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 840(s0)
	ld t0, 992(s0)
	ld t1, 1136(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 848(s0)
	ld t0, 1000(s0)
	ld t1, 1144(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 856(s0)
	ld t0, 1008(s0)
	ld t1, 1152(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 864(s0)
	ld t0, 1016(s0)
	ld t1, 1160(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 872(s0)
	bnez s1, 20b
	addi ra, s0, 2047
	ld ra, 193(ra)
	addi s1, s0, 2047
	ld s1, 185(s1)
	addi s0, s0, 2047
	ld s0, 177(s0)
	ret
	.option pop
