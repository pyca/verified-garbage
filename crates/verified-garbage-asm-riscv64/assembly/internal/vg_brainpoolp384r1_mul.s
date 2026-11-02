// The functions of `src/internal/vg_brainpoolp384r1_mul.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_brainpoolp384r1_mul:
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
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 208(s0)
	sd t0, 0(a6)
	ld t0, 216(s0)
	sd t0, 8(a6)
	ld t0, 224(s0)
	sd t0, 16(a6)
	ld t0, 232(s0)
	sd t0, 24(a6)
	ld t0, 240(s0)
	sd t0, 32(a6)
	ld t0, 248(s0)
	sd t0, 40(a6)
	ld t0, 304(s0)
	sd t0, 48(a6)
	ld t0, 312(s0)
	sd t0, 56(a6)
	ld t0, 320(s0)
	sd t0, 64(a6)
	ld t0, 328(s0)
	sd t0, 72(a6)
	ld t0, 336(s0)
	sd t0, 80(a6)
	ld t0, 344(s0)
	sd t0, 88(a6)
	ld t0, 208(s0)
	sd t0, 96(a6)
	ld t0, 216(s0)
	sd t0, 104(a6)
	ld t0, 224(s0)
	sd t0, 112(a6)
	ld t0, 232(s0)
	sd t0, 120(a6)
	ld t0, 240(s0)
	sd t0, 128(a6)
	ld t0, 248(s0)
	sd t0, 136(a6)
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 736(s0)
	sd t0, 144(a6)
	ld t0, 744(s0)
	sd t0, 152(a6)
	ld t0, 752(s0)
	sd t0, 160(a6)
	ld t0, 760(s0)
	sd t0, 168(a6)
	ld t0, 768(s0)
	sd t0, 176(a6)
	ld t0, 776(s0)
	sd t0, 184(a6)
	ld t0, 784(s0)
	sd t0, 192(a6)
	ld t0, 792(s0)
	sd t0, 200(a6)
	ld t0, 800(s0)
	sd t0, 208(a6)
	ld t0, 808(s0)
	sd t0, 216(a6)
	ld t0, 816(s0)
	sd t0, 224(a6)
	ld t0, 824(s0)
	sd t0, 232(a6)
	ld t0, 304(s0)
	sd t0, 240(a6)
	ld t0, 312(s0)
	sd t0, 248(a6)
	ld t0, 320(s0)
	sd t0, 256(a6)
	ld t0, 328(s0)
	sd t0, 264(a6)
	ld t0, 336(s0)
	sd t0, 272(a6)
	ld t0, 344(s0)
	sd t0, 280(a6)
	ld t0, 736(s0)
	sd t0, 880(s0)
	ld t0, 744(s0)
	sd t0, 888(s0)
	ld t0, 752(s0)
	sd t0, 896(s0)
	ld t0, 760(s0)
	sd t0, 904(s0)
	ld t0, 768(s0)
	sd t0, 912(s0)
	ld t0, 776(s0)
	sd t0, 920(s0)
	ld t0, 784(s0)
	sd t0, 928(s0)
	ld t0, 792(s0)
	sd t0, 936(s0)
	ld t0, 800(s0)
	sd t0, 944(s0)
	ld t0, 808(s0)
	sd t0, 952(s0)
	ld t0, 816(s0)
	sd t0, 960(s0)
	ld t0, 824(s0)
	sd t0, 968(s0)
	ld t0, 304(s0)
	sd t0, 976(s0)
	ld t0, 312(s0)
	sd t0, 984(s0)
	ld t0, 320(s0)
	sd t0, 992(s0)
	ld t0, 328(s0)
	sd t0, 1000(s0)
	ld t0, 336(s0)
	sd t0, 1008(s0)
	ld t0, 344(s0)
	sd t0, 1016(s0)
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 880
	addi a3, zero, 736
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 928
	addi a3, zero, 784
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 976
	addi a3, zero, 304
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 880
	addi a3, zero, 928
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 736
	addi a3, zero, 784
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1168
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 880
	addi a3, zero, 976
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 736
	addi a3, zero, 304
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 928
	addi a3, zero, 976
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 784
	addi a3, zero, 304
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 352
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 400
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1024
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1216
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1216
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1024
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1168
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 400
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1216
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1072
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1408
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1312
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1312
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1408
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1120
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 1024(s0)
	sd t0, 288(a6)
	ld t0, 1032(s0)
	sd t0, 296(a6)
	ld t0, 1040(s0)
	sd t0, 304(a6)
	ld t0, 1048(s0)
	sd t0, 312(a6)
	ld t0, 1056(s0)
	sd t0, 320(a6)
	ld t0, 1064(s0)
	sd t0, 328(a6)
	ld t0, 1072(s0)
	sd t0, 336(a6)
	ld t0, 1080(s0)
	sd t0, 344(a6)
	ld t0, 1088(s0)
	sd t0, 352(a6)
	ld t0, 1096(s0)
	sd t0, 360(a6)
	ld t0, 1104(s0)
	sd t0, 368(a6)
	ld t0, 1112(s0)
	sd t0, 376(a6)
	ld t0, 1120(s0)
	sd t0, 384(a6)
	ld t0, 1128(s0)
	sd t0, 392(a6)
	ld t0, 1136(s0)
	sd t0, 400(a6)
	ld t0, 1144(s0)
	sd t0, 408(a6)
	ld t0, 1152(s0)
	sd t0, 416(a6)
	ld t0, 1160(s0)
	sd t0, 424(a6)
	ld t0, 1024(s0)
	sd t0, 880(s0)
	ld t0, 1032(s0)
	sd t0, 888(s0)
	ld t0, 1040(s0)
	sd t0, 896(s0)
	ld t0, 1048(s0)
	sd t0, 904(s0)
	ld t0, 1056(s0)
	sd t0, 912(s0)
	ld t0, 1064(s0)
	sd t0, 920(s0)
	ld t0, 1072(s0)
	sd t0, 928(s0)
	ld t0, 1080(s0)
	sd t0, 936(s0)
	ld t0, 1088(s0)
	sd t0, 944(s0)
	ld t0, 1096(s0)
	sd t0, 952(s0)
	ld t0, 1104(s0)
	sd t0, 960(s0)
	ld t0, 1112(s0)
	sd t0, 968(s0)
	ld t0, 1120(s0)
	sd t0, 976(s0)
	ld t0, 1128(s0)
	sd t0, 984(s0)
	ld t0, 1136(s0)
	sd t0, 992(s0)
	ld t0, 1144(s0)
	sd t0, 1000(s0)
	ld t0, 1152(s0)
	sd t0, 1008(s0)
	ld t0, 1160(s0)
	sd t0, 1016(s0)
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 880
	addi a3, zero, 736
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 928
	addi a3, zero, 784
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 976
	addi a3, zero, 304
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 880
	addi a3, zero, 928
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 736
	addi a3, zero, 784
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1168
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 880
	addi a3, zero, 976
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 736
	addi a3, zero, 304
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 928
	addi a3, zero, 976
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 784
	addi a3, zero, 304
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 352
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 400
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1024
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1216
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1216
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1024
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1168
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 400
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1216
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1072
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1408
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1312
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1312
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1408
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1120
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 1024(s0)
	sd t0, 432(a6)
	ld t0, 1032(s0)
	sd t0, 440(a6)
	ld t0, 1040(s0)
	sd t0, 448(a6)
	ld t0, 1048(s0)
	sd t0, 456(a6)
	ld t0, 1056(s0)
	sd t0, 464(a6)
	ld t0, 1064(s0)
	sd t0, 472(a6)
	ld t0, 1072(s0)
	sd t0, 480(a6)
	ld t0, 1080(s0)
	sd t0, 488(a6)
	ld t0, 1088(s0)
	sd t0, 496(a6)
	ld t0, 1096(s0)
	sd t0, 504(a6)
	ld t0, 1104(s0)
	sd t0, 512(a6)
	ld t0, 1112(s0)
	sd t0, 520(a6)
	ld t0, 1120(s0)
	sd t0, 528(a6)
	ld t0, 1128(s0)
	sd t0, 536(a6)
	ld t0, 1136(s0)
	sd t0, 544(a6)
	ld t0, 1144(s0)
	sd t0, 552(a6)
	ld t0, 1152(s0)
	sd t0, 560(a6)
	ld t0, 1160(s0)
	sd t0, 568(a6)
	ld t0, 1024(s0)
	sd t0, 880(s0)
	ld t0, 1032(s0)
	sd t0, 888(s0)
	ld t0, 1040(s0)
	sd t0, 896(s0)
	ld t0, 1048(s0)
	sd t0, 904(s0)
	ld t0, 1056(s0)
	sd t0, 912(s0)
	ld t0, 1064(s0)
	sd t0, 920(s0)
	ld t0, 1072(s0)
	sd t0, 928(s0)
	ld t0, 1080(s0)
	sd t0, 936(s0)
	ld t0, 1088(s0)
	sd t0, 944(s0)
	ld t0, 1096(s0)
	sd t0, 952(s0)
	ld t0, 1104(s0)
	sd t0, 960(s0)
	ld t0, 1112(s0)
	sd t0, 968(s0)
	ld t0, 1120(s0)
	sd t0, 976(s0)
	ld t0, 1128(s0)
	sd t0, 984(s0)
	ld t0, 1136(s0)
	sd t0, 992(s0)
	ld t0, 1144(s0)
	sd t0, 1000(s0)
	ld t0, 1152(s0)
	sd t0, 1008(s0)
	ld t0, 1160(s0)
	sd t0, 1016(s0)
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 880
	addi a3, zero, 736
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 928
	addi a3, zero, 784
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 976
	addi a3, zero, 304
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 880
	addi a3, zero, 928
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 736
	addi a3, zero, 784
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1168
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 880
	addi a3, zero, 976
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 736
	addi a3, zero, 304
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 928
	addi a3, zero, 976
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 784
	addi a3, zero, 304
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 352
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 400
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1024
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1216
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1216
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1024
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1168
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 400
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1216
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1072
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1408
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1312
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1312
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1408
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1120
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 1024(s0)
	sd t0, 576(a6)
	ld t0, 1032(s0)
	sd t0, 584(a6)
	ld t0, 1040(s0)
	sd t0, 592(a6)
	ld t0, 1048(s0)
	sd t0, 600(a6)
	ld t0, 1056(s0)
	sd t0, 608(a6)
	ld t0, 1064(s0)
	sd t0, 616(a6)
	ld t0, 1072(s0)
	sd t0, 624(a6)
	ld t0, 1080(s0)
	sd t0, 632(a6)
	ld t0, 1088(s0)
	sd t0, 640(a6)
	ld t0, 1096(s0)
	sd t0, 648(a6)
	ld t0, 1104(s0)
	sd t0, 656(a6)
	ld t0, 1112(s0)
	sd t0, 664(a6)
	ld t0, 1120(s0)
	sd t0, 672(a6)
	ld t0, 1128(s0)
	sd t0, 680(a6)
	ld t0, 1136(s0)
	sd t0, 688(a6)
	ld t0, 1144(s0)
	sd t0, 696(a6)
	ld t0, 1152(s0)
	sd t0, 704(a6)
	ld t0, 1160(s0)
	sd t0, 712(a6)
	ld t0, 1024(s0)
	sd t0, 880(s0)
	ld t0, 1032(s0)
	sd t0, 888(s0)
	ld t0, 1040(s0)
	sd t0, 896(s0)
	ld t0, 1048(s0)
	sd t0, 904(s0)
	ld t0, 1056(s0)
	sd t0, 912(s0)
	ld t0, 1064(s0)
	sd t0, 920(s0)
	ld t0, 1072(s0)
	sd t0, 928(s0)
	ld t0, 1080(s0)
	sd t0, 936(s0)
	ld t0, 1088(s0)
	sd t0, 944(s0)
	ld t0, 1096(s0)
	sd t0, 952(s0)
	ld t0, 1104(s0)
	sd t0, 960(s0)
	ld t0, 1112(s0)
	sd t0, 968(s0)
	ld t0, 1120(s0)
	sd t0, 976(s0)
	ld t0, 1128(s0)
	sd t0, 984(s0)
	ld t0, 1136(s0)
	sd t0, 992(s0)
	ld t0, 1144(s0)
	sd t0, 1000(s0)
	ld t0, 1152(s0)
	sd t0, 1008(s0)
	ld t0, 1160(s0)
	sd t0, 1016(s0)
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 880
	addi a3, zero, 736
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 928
	addi a3, zero, 784
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 976
	addi a3, zero, 304
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 880
	addi a3, zero, 928
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 736
	addi a3, zero, 784
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1168
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 880
	addi a3, zero, 976
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 736
	addi a3, zero, 304
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 928
	addi a3, zero, 976
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 784
	addi a3, zero, 304
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 352
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 400
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1024
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1216
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1216
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1024
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1168
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 400
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1216
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1072
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1408
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1312
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1312
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1408
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1120
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 1024(s0)
	sd t0, 720(a6)
	ld t0, 1032(s0)
	sd t0, 728(a6)
	ld t0, 1040(s0)
	sd t0, 736(a6)
	ld t0, 1048(s0)
	sd t0, 744(a6)
	ld t0, 1056(s0)
	sd t0, 752(a6)
	ld t0, 1064(s0)
	sd t0, 760(a6)
	ld t0, 1072(s0)
	sd t0, 768(a6)
	ld t0, 1080(s0)
	sd t0, 776(a6)
	ld t0, 1088(s0)
	sd t0, 784(a6)
	ld t0, 1096(s0)
	sd t0, 792(a6)
	ld t0, 1104(s0)
	sd t0, 800(a6)
	ld t0, 1112(s0)
	sd t0, 808(a6)
	ld t0, 1120(s0)
	sd t0, 816(a6)
	ld t0, 1128(s0)
	sd t0, 824(a6)
	ld t0, 1136(s0)
	sd t0, 832(a6)
	ld t0, 1144(s0)
	sd t0, 840(a6)
	ld t0, 1152(s0)
	sd t0, 848(a6)
	ld t0, 1160(s0)
	sd t0, 856(a6)
	ld t0, 1024(s0)
	sd t0, 880(s0)
	ld t0, 1032(s0)
	sd t0, 888(s0)
	ld t0, 1040(s0)
	sd t0, 896(s0)
	ld t0, 1048(s0)
	sd t0, 904(s0)
	ld t0, 1056(s0)
	sd t0, 912(s0)
	ld t0, 1064(s0)
	sd t0, 920(s0)
	ld t0, 1072(s0)
	sd t0, 928(s0)
	ld t0, 1080(s0)
	sd t0, 936(s0)
	ld t0, 1088(s0)
	sd t0, 944(s0)
	ld t0, 1096(s0)
	sd t0, 952(s0)
	ld t0, 1104(s0)
	sd t0, 960(s0)
	ld t0, 1112(s0)
	sd t0, 968(s0)
	ld t0, 1120(s0)
	sd t0, 976(s0)
	ld t0, 1128(s0)
	sd t0, 984(s0)
	ld t0, 1136(s0)
	sd t0, 992(s0)
	ld t0, 1144(s0)
	sd t0, 1000(s0)
	ld t0, 1152(s0)
	sd t0, 1008(s0)
	ld t0, 1160(s0)
	sd t0, 1016(s0)
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 880
	addi a3, zero, 736
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 928
	addi a3, zero, 784
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 976
	addi a3, zero, 304
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 880
	addi a3, zero, 928
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 736
	addi a3, zero, 784
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1168
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 880
	addi a3, zero, 976
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 736
	addi a3, zero, 304
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 928
	addi a3, zero, 976
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 784
	addi a3, zero, 304
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 352
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 400
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1024
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1216
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1216
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1024
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1168
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 400
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1216
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1072
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1408
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1312
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1312
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1408
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1120
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 1024(s0)
	sd t0, 864(a6)
	ld t0, 1032(s0)
	sd t0, 872(a6)
	ld t0, 1040(s0)
	sd t0, 880(a6)
	ld t0, 1048(s0)
	sd t0, 888(a6)
	ld t0, 1056(s0)
	sd t0, 896(a6)
	ld t0, 1064(s0)
	sd t0, 904(a6)
	ld t0, 1072(s0)
	sd t0, 912(a6)
	ld t0, 1080(s0)
	sd t0, 920(a6)
	ld t0, 1088(s0)
	sd t0, 928(a6)
	ld t0, 1096(s0)
	sd t0, 936(a6)
	ld t0, 1104(s0)
	sd t0, 944(a6)
	ld t0, 1112(s0)
	sd t0, 952(a6)
	ld t0, 1120(s0)
	sd t0, 960(a6)
	ld t0, 1128(s0)
	sd t0, 968(a6)
	ld t0, 1136(s0)
	sd t0, 976(a6)
	ld t0, 1144(s0)
	sd t0, 984(a6)
	ld t0, 1152(s0)
	sd t0, 992(a6)
	ld t0, 1160(s0)
	sd t0, 1000(a6)
	ld t0, 1024(s0)
	sd t0, 880(s0)
	ld t0, 1032(s0)
	sd t0, 888(s0)
	ld t0, 1040(s0)
	sd t0, 896(s0)
	ld t0, 1048(s0)
	sd t0, 904(s0)
	ld t0, 1056(s0)
	sd t0, 912(s0)
	ld t0, 1064(s0)
	sd t0, 920(s0)
	ld t0, 1072(s0)
	sd t0, 928(s0)
	ld t0, 1080(s0)
	sd t0, 936(s0)
	ld t0, 1088(s0)
	sd t0, 944(s0)
	ld t0, 1096(s0)
	sd t0, 952(s0)
	ld t0, 1104(s0)
	sd t0, 960(s0)
	ld t0, 1112(s0)
	sd t0, 968(s0)
	ld t0, 1120(s0)
	sd t0, 976(s0)
	ld t0, 1128(s0)
	sd t0, 984(s0)
	ld t0, 1136(s0)
	sd t0, 992(s0)
	ld t0, 1144(s0)
	sd t0, 1000(s0)
	ld t0, 1152(s0)
	sd t0, 1008(s0)
	ld t0, 1160(s0)
	sd t0, 1016(s0)
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 880
	addi a3, zero, 736
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 928
	addi a3, zero, 784
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 976
	addi a3, zero, 304
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 880
	addi a3, zero, 928
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 736
	addi a3, zero, 784
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1168
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 880
	addi a3, zero, 976
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 736
	addi a3, zero, 304
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 928
	addi a3, zero, 976
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 784
	addi a3, zero, 304
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 352
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 400
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1024
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1216
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1216
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1024
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1168
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 400
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1216
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1072
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1408
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1312
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1312
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1408
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1120
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 1024(s0)
	sd t0, 1008(a6)
	ld t0, 1032(s0)
	sd t0, 1016(a6)
	ld t0, 1040(s0)
	sd t0, 1024(a6)
	ld t0, 1048(s0)
	sd t0, 1032(a6)
	ld t0, 1056(s0)
	sd t0, 1040(a6)
	ld t0, 1064(s0)
	sd t0, 1048(a6)
	ld t0, 1072(s0)
	sd t0, 1056(a6)
	ld t0, 1080(s0)
	sd t0, 1064(a6)
	ld t0, 1088(s0)
	sd t0, 1072(a6)
	ld t0, 1096(s0)
	sd t0, 1080(a6)
	ld t0, 1104(s0)
	sd t0, 1088(a6)
	ld t0, 1112(s0)
	sd t0, 1096(a6)
	ld t0, 1120(s0)
	sd t0, 1104(a6)
	ld t0, 1128(s0)
	sd t0, 1112(a6)
	ld t0, 1136(s0)
	sd t0, 1120(a6)
	ld t0, 1144(s0)
	sd t0, 1128(a6)
	ld t0, 1152(s0)
	sd t0, 1136(a6)
	ld t0, 1160(s0)
	sd t0, 1144(a6)
	ld t0, 1024(s0)
	sd t0, 880(s0)
	ld t0, 1032(s0)
	sd t0, 888(s0)
	ld t0, 1040(s0)
	sd t0, 896(s0)
	ld t0, 1048(s0)
	sd t0, 904(s0)
	ld t0, 1056(s0)
	sd t0, 912(s0)
	ld t0, 1064(s0)
	sd t0, 920(s0)
	ld t0, 1072(s0)
	sd t0, 928(s0)
	ld t0, 1080(s0)
	sd t0, 936(s0)
	ld t0, 1088(s0)
	sd t0, 944(s0)
	ld t0, 1096(s0)
	sd t0, 952(s0)
	ld t0, 1104(s0)
	sd t0, 960(s0)
	ld t0, 1112(s0)
	sd t0, 968(s0)
	ld t0, 1120(s0)
	sd t0, 976(s0)
	ld t0, 1128(s0)
	sd t0, 984(s0)
	ld t0, 1136(s0)
	sd t0, 992(s0)
	ld t0, 1144(s0)
	sd t0, 1000(s0)
	ld t0, 1152(s0)
	sd t0, 1008(s0)
	ld t0, 1160(s0)
	sd t0, 1016(s0)
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 880
	addi a3, zero, 736
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 928
	addi a3, zero, 784
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 976
	addi a3, zero, 304
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 880
	addi a3, zero, 928
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 736
	addi a3, zero, 784
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1168
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 880
	addi a3, zero, 976
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 736
	addi a3, zero, 304
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 928
	addi a3, zero, 976
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 784
	addi a3, zero, 304
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 352
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 400
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1024
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1216
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1216
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1024
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1168
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 400
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1216
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1072
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1408
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1312
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1312
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1408
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1120
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 1024(s0)
	sd t0, 1152(a6)
	ld t0, 1032(s0)
	sd t0, 1160(a6)
	ld t0, 1040(s0)
	sd t0, 1168(a6)
	ld t0, 1048(s0)
	sd t0, 1176(a6)
	ld t0, 1056(s0)
	sd t0, 1184(a6)
	ld t0, 1064(s0)
	sd t0, 1192(a6)
	ld t0, 1072(s0)
	sd t0, 1200(a6)
	ld t0, 1080(s0)
	sd t0, 1208(a6)
	ld t0, 1088(s0)
	sd t0, 1216(a6)
	ld t0, 1096(s0)
	sd t0, 1224(a6)
	ld t0, 1104(s0)
	sd t0, 1232(a6)
	ld t0, 1112(s0)
	sd t0, 1240(a6)
	ld t0, 1120(s0)
	sd t0, 1248(a6)
	ld t0, 1128(s0)
	sd t0, 1256(a6)
	ld t0, 1136(s0)
	sd t0, 1264(a6)
	ld t0, 1144(s0)
	sd t0, 1272(a6)
	ld t0, 1152(s0)
	sd t0, 1280(a6)
	ld t0, 1160(s0)
	sd t0, 1288(a6)
	ld t0, 1024(s0)
	sd t0, 880(s0)
	ld t0, 1032(s0)
	sd t0, 888(s0)
	ld t0, 1040(s0)
	sd t0, 896(s0)
	ld t0, 1048(s0)
	sd t0, 904(s0)
	ld t0, 1056(s0)
	sd t0, 912(s0)
	ld t0, 1064(s0)
	sd t0, 920(s0)
	ld t0, 1072(s0)
	sd t0, 928(s0)
	ld t0, 1080(s0)
	sd t0, 936(s0)
	ld t0, 1088(s0)
	sd t0, 944(s0)
	ld t0, 1096(s0)
	sd t0, 952(s0)
	ld t0, 1104(s0)
	sd t0, 960(s0)
	ld t0, 1112(s0)
	sd t0, 968(s0)
	ld t0, 1120(s0)
	sd t0, 976(s0)
	ld t0, 1128(s0)
	sd t0, 984(s0)
	ld t0, 1136(s0)
	sd t0, 992(s0)
	ld t0, 1144(s0)
	sd t0, 1000(s0)
	ld t0, 1152(s0)
	sd t0, 1008(s0)
	ld t0, 1160(s0)
	sd t0, 1016(s0)
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 880
	addi a3, zero, 736
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 928
	addi a3, zero, 784
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 976
	addi a3, zero, 304
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 880
	addi a3, zero, 928
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 736
	addi a3, zero, 784
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1168
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 880
	addi a3, zero, 976
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 736
	addi a3, zero, 304
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 928
	addi a3, zero, 976
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 784
	addi a3, zero, 304
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 352
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 400
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1024
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1216
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1216
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1024
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1168
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 400
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1216
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1072
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1408
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1312
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1312
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1408
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1120
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 1024(s0)
	sd t0, 1296(a6)
	ld t0, 1032(s0)
	sd t0, 1304(a6)
	ld t0, 1040(s0)
	sd t0, 1312(a6)
	ld t0, 1048(s0)
	sd t0, 1320(a6)
	ld t0, 1056(s0)
	sd t0, 1328(a6)
	ld t0, 1064(s0)
	sd t0, 1336(a6)
	ld t0, 1072(s0)
	sd t0, 1344(a6)
	ld t0, 1080(s0)
	sd t0, 1352(a6)
	ld t0, 1088(s0)
	sd t0, 1360(a6)
	ld t0, 1096(s0)
	sd t0, 1368(a6)
	ld t0, 1104(s0)
	sd t0, 1376(a6)
	ld t0, 1112(s0)
	sd t0, 1384(a6)
	ld t0, 1120(s0)
	sd t0, 1392(a6)
	ld t0, 1128(s0)
	sd t0, 1400(a6)
	ld t0, 1136(s0)
	sd t0, 1408(a6)
	ld t0, 1144(s0)
	sd t0, 1416(a6)
	ld t0, 1152(s0)
	sd t0, 1424(a6)
	ld t0, 1160(s0)
	sd t0, 1432(a6)
	ld t0, 1024(s0)
	sd t0, 880(s0)
	ld t0, 1032(s0)
	sd t0, 888(s0)
	ld t0, 1040(s0)
	sd t0, 896(s0)
	ld t0, 1048(s0)
	sd t0, 904(s0)
	ld t0, 1056(s0)
	sd t0, 912(s0)
	ld t0, 1064(s0)
	sd t0, 920(s0)
	ld t0, 1072(s0)
	sd t0, 928(s0)
	ld t0, 1080(s0)
	sd t0, 936(s0)
	ld t0, 1088(s0)
	sd t0, 944(s0)
	ld t0, 1096(s0)
	sd t0, 952(s0)
	ld t0, 1104(s0)
	sd t0, 960(s0)
	ld t0, 1112(s0)
	sd t0, 968(s0)
	ld t0, 1120(s0)
	sd t0, 976(s0)
	ld t0, 1128(s0)
	sd t0, 984(s0)
	ld t0, 1136(s0)
	sd t0, 992(s0)
	ld t0, 1144(s0)
	sd t0, 1000(s0)
	ld t0, 1152(s0)
	sd t0, 1008(s0)
	ld t0, 1160(s0)
	sd t0, 1016(s0)
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 880
	addi a3, zero, 736
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 928
	addi a3, zero, 784
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 976
	addi a3, zero, 304
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 880
	addi a3, zero, 928
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 736
	addi a3, zero, 784
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1168
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 880
	addi a3, zero, 976
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 736
	addi a3, zero, 304
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 928
	addi a3, zero, 976
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 784
	addi a3, zero, 304
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 352
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 400
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1024
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1216
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1216
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1024
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1168
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 400
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1216
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1072
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1408
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1312
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1312
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1408
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1120
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 1024(s0)
	sd t0, 1440(a6)
	ld t0, 1032(s0)
	sd t0, 1448(a6)
	ld t0, 1040(s0)
	sd t0, 1456(a6)
	ld t0, 1048(s0)
	sd t0, 1464(a6)
	ld t0, 1056(s0)
	sd t0, 1472(a6)
	ld t0, 1064(s0)
	sd t0, 1480(a6)
	ld t0, 1072(s0)
	sd t0, 1488(a6)
	ld t0, 1080(s0)
	sd t0, 1496(a6)
	ld t0, 1088(s0)
	sd t0, 1504(a6)
	ld t0, 1096(s0)
	sd t0, 1512(a6)
	ld t0, 1104(s0)
	sd t0, 1520(a6)
	ld t0, 1112(s0)
	sd t0, 1528(a6)
	ld t0, 1120(s0)
	sd t0, 1536(a6)
	ld t0, 1128(s0)
	sd t0, 1544(a6)
	ld t0, 1136(s0)
	sd t0, 1552(a6)
	ld t0, 1144(s0)
	sd t0, 1560(a6)
	ld t0, 1152(s0)
	sd t0, 1568(a6)
	ld t0, 1160(s0)
	sd t0, 1576(a6)
	ld t0, 1024(s0)
	sd t0, 880(s0)
	ld t0, 1032(s0)
	sd t0, 888(s0)
	ld t0, 1040(s0)
	sd t0, 896(s0)
	ld t0, 1048(s0)
	sd t0, 904(s0)
	ld t0, 1056(s0)
	sd t0, 912(s0)
	ld t0, 1064(s0)
	sd t0, 920(s0)
	ld t0, 1072(s0)
	sd t0, 928(s0)
	ld t0, 1080(s0)
	sd t0, 936(s0)
	ld t0, 1088(s0)
	sd t0, 944(s0)
	ld t0, 1096(s0)
	sd t0, 952(s0)
	ld t0, 1104(s0)
	sd t0, 960(s0)
	ld t0, 1112(s0)
	sd t0, 968(s0)
	ld t0, 1120(s0)
	sd t0, 976(s0)
	ld t0, 1128(s0)
	sd t0, 984(s0)
	ld t0, 1136(s0)
	sd t0, 992(s0)
	ld t0, 1144(s0)
	sd t0, 1000(s0)
	ld t0, 1152(s0)
	sd t0, 1008(s0)
	ld t0, 1160(s0)
	sd t0, 1016(s0)
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 880
	addi a3, zero, 736
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 928
	addi a3, zero, 784
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 976
	addi a3, zero, 304
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 880
	addi a3, zero, 928
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 736
	addi a3, zero, 784
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1168
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 880
	addi a3, zero, 976
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 736
	addi a3, zero, 304
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 928
	addi a3, zero, 976
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 784
	addi a3, zero, 304
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 352
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 400
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1024
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1216
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1216
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1024
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1168
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 400
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1216
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1072
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1408
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1312
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1312
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1408
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1120
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 1024(s0)
	sd t0, 1584(a6)
	ld t0, 1032(s0)
	sd t0, 1592(a6)
	ld t0, 1040(s0)
	sd t0, 1600(a6)
	ld t0, 1048(s0)
	sd t0, 1608(a6)
	ld t0, 1056(s0)
	sd t0, 1616(a6)
	ld t0, 1064(s0)
	sd t0, 1624(a6)
	ld t0, 1072(s0)
	sd t0, 1632(a6)
	ld t0, 1080(s0)
	sd t0, 1640(a6)
	ld t0, 1088(s0)
	sd t0, 1648(a6)
	ld t0, 1096(s0)
	sd t0, 1656(a6)
	ld t0, 1104(s0)
	sd t0, 1664(a6)
	ld t0, 1112(s0)
	sd t0, 1672(a6)
	ld t0, 1120(s0)
	sd t0, 1680(a6)
	ld t0, 1128(s0)
	sd t0, 1688(a6)
	ld t0, 1136(s0)
	sd t0, 1696(a6)
	ld t0, 1144(s0)
	sd t0, 1704(a6)
	ld t0, 1152(s0)
	sd t0, 1712(a6)
	ld t0, 1160(s0)
	sd t0, 1720(a6)
	ld t0, 1024(s0)
	sd t0, 880(s0)
	ld t0, 1032(s0)
	sd t0, 888(s0)
	ld t0, 1040(s0)
	sd t0, 896(s0)
	ld t0, 1048(s0)
	sd t0, 904(s0)
	ld t0, 1056(s0)
	sd t0, 912(s0)
	ld t0, 1064(s0)
	sd t0, 920(s0)
	ld t0, 1072(s0)
	sd t0, 928(s0)
	ld t0, 1080(s0)
	sd t0, 936(s0)
	ld t0, 1088(s0)
	sd t0, 944(s0)
	ld t0, 1096(s0)
	sd t0, 952(s0)
	ld t0, 1104(s0)
	sd t0, 960(s0)
	ld t0, 1112(s0)
	sd t0, 968(s0)
	ld t0, 1120(s0)
	sd t0, 976(s0)
	ld t0, 1128(s0)
	sd t0, 984(s0)
	ld t0, 1136(s0)
	sd t0, 992(s0)
	ld t0, 1144(s0)
	sd t0, 1000(s0)
	ld t0, 1152(s0)
	sd t0, 1008(s0)
	ld t0, 1160(s0)
	sd t0, 1016(s0)
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 880
	addi a3, zero, 736
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 928
	addi a3, zero, 784
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 976
	addi a3, zero, 304
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 880
	addi a3, zero, 928
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 736
	addi a3, zero, 784
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1168
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 880
	addi a3, zero, 976
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 736
	addi a3, zero, 304
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 928
	addi a3, zero, 976
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 784
	addi a3, zero, 304
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 352
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 400
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1024
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1216
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1216
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1024
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1168
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 400
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1216
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1072
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1408
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1312
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1312
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1408
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1120
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 1024(s0)
	sd t0, 1728(a6)
	ld t0, 1032(s0)
	sd t0, 1736(a6)
	ld t0, 1040(s0)
	sd t0, 1744(a6)
	ld t0, 1048(s0)
	sd t0, 1752(a6)
	ld t0, 1056(s0)
	sd t0, 1760(a6)
	ld t0, 1064(s0)
	sd t0, 1768(a6)
	ld t0, 1072(s0)
	sd t0, 1776(a6)
	ld t0, 1080(s0)
	sd t0, 1784(a6)
	ld t0, 1088(s0)
	sd t0, 1792(a6)
	ld t0, 1096(s0)
	sd t0, 1800(a6)
	ld t0, 1104(s0)
	sd t0, 1808(a6)
	ld t0, 1112(s0)
	sd t0, 1816(a6)
	ld t0, 1120(s0)
	sd t0, 1824(a6)
	ld t0, 1128(s0)
	sd t0, 1832(a6)
	ld t0, 1136(s0)
	sd t0, 1840(a6)
	ld t0, 1144(s0)
	sd t0, 1848(a6)
	ld t0, 1152(s0)
	sd t0, 1856(a6)
	ld t0, 1160(s0)
	sd t0, 1864(a6)
	ld t0, 1024(s0)
	sd t0, 880(s0)
	ld t0, 1032(s0)
	sd t0, 888(s0)
	ld t0, 1040(s0)
	sd t0, 896(s0)
	ld t0, 1048(s0)
	sd t0, 904(s0)
	ld t0, 1056(s0)
	sd t0, 912(s0)
	ld t0, 1064(s0)
	sd t0, 920(s0)
	ld t0, 1072(s0)
	sd t0, 928(s0)
	ld t0, 1080(s0)
	sd t0, 936(s0)
	ld t0, 1088(s0)
	sd t0, 944(s0)
	ld t0, 1096(s0)
	sd t0, 952(s0)
	ld t0, 1104(s0)
	sd t0, 960(s0)
	ld t0, 1112(s0)
	sd t0, 968(s0)
	ld t0, 1120(s0)
	sd t0, 976(s0)
	ld t0, 1128(s0)
	sd t0, 984(s0)
	ld t0, 1136(s0)
	sd t0, 992(s0)
	ld t0, 1144(s0)
	sd t0, 1000(s0)
	ld t0, 1152(s0)
	sd t0, 1008(s0)
	ld t0, 1160(s0)
	sd t0, 1016(s0)
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 880
	addi a3, zero, 736
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 928
	addi a3, zero, 784
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 976
	addi a3, zero, 304
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 880
	addi a3, zero, 928
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 736
	addi a3, zero, 784
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1168
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 880
	addi a3, zero, 976
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 736
	addi a3, zero, 304
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 928
	addi a3, zero, 976
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 784
	addi a3, zero, 304
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 352
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 400
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1024
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1216
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1216
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1024
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1168
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 400
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1216
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1072
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1408
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1312
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1312
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1408
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1120
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 1024(s0)
	sd t0, 1872(a6)
	ld t0, 1032(s0)
	sd t0, 1880(a6)
	ld t0, 1040(s0)
	sd t0, 1888(a6)
	ld t0, 1048(s0)
	sd t0, 1896(a6)
	ld t0, 1056(s0)
	sd t0, 1904(a6)
	ld t0, 1064(s0)
	sd t0, 1912(a6)
	ld t0, 1072(s0)
	sd t0, 1920(a6)
	ld t0, 1080(s0)
	sd t0, 1928(a6)
	ld t0, 1088(s0)
	sd t0, 1936(a6)
	ld t0, 1096(s0)
	sd t0, 1944(a6)
	ld t0, 1104(s0)
	sd t0, 1952(a6)
	ld t0, 1112(s0)
	sd t0, 1960(a6)
	ld t0, 1120(s0)
	sd t0, 1968(a6)
	ld t0, 1128(s0)
	sd t0, 1976(a6)
	ld t0, 1136(s0)
	sd t0, 1984(a6)
	ld t0, 1144(s0)
	sd t0, 1992(a6)
	ld t0, 1152(s0)
	sd t0, 2000(a6)
	ld t0, 1160(s0)
	sd t0, 2008(a6)
	ld t0, 1024(s0)
	sd t0, 880(s0)
	ld t0, 1032(s0)
	sd t0, 888(s0)
	ld t0, 1040(s0)
	sd t0, 896(s0)
	ld t0, 1048(s0)
	sd t0, 904(s0)
	ld t0, 1056(s0)
	sd t0, 912(s0)
	ld t0, 1064(s0)
	sd t0, 920(s0)
	ld t0, 1072(s0)
	sd t0, 928(s0)
	ld t0, 1080(s0)
	sd t0, 936(s0)
	ld t0, 1088(s0)
	sd t0, 944(s0)
	ld t0, 1096(s0)
	sd t0, 952(s0)
	ld t0, 1104(s0)
	sd t0, 960(s0)
	ld t0, 1112(s0)
	sd t0, 968(s0)
	ld t0, 1120(s0)
	sd t0, 976(s0)
	ld t0, 1128(s0)
	sd t0, 984(s0)
	ld t0, 1136(s0)
	sd t0, 992(s0)
	ld t0, 1144(s0)
	sd t0, 1000(s0)
	ld t0, 1152(s0)
	sd t0, 1008(s0)
	ld t0, 1160(s0)
	sd t0, 1016(s0)
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 880
	addi a3, zero, 736
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 928
	addi a3, zero, 784
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 976
	addi a3, zero, 304
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 880
	addi a3, zero, 928
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 736
	addi a3, zero, 784
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1168
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 880
	addi a3, zero, 976
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 736
	addi a3, zero, 304
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 928
	addi a3, zero, 976
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 784
	addi a3, zero, 304
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 352
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 400
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1024
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1216
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1216
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1024
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1168
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 400
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1216
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1072
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1408
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1312
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1312
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1408
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1120
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 1024(s0)
	sd t0, 2016(a6)
	ld t0, 1032(s0)
	sd t0, 2024(a6)
	ld t0, 1040(s0)
	sd t0, 2032(a6)
	ld t0, 1048(s0)
	sd t0, 2040(a6)
	ld t0, 1056(s0)
	addi a6, a6, 2047
	sd t0, 1(a6)
	addi a6, a6, -2047
	ld t0, 1064(s0)
	addi a6, a6, 2047
	sd t0, 9(a6)
	addi a6, a6, -2047
	ld t0, 1072(s0)
	addi a6, a6, 2047
	sd t0, 17(a6)
	addi a6, a6, -2047
	ld t0, 1080(s0)
	addi a6, a6, 2047
	sd t0, 25(a6)
	addi a6, a6, -2047
	ld t0, 1088(s0)
	addi a6, a6, 2047
	sd t0, 33(a6)
	addi a6, a6, -2047
	ld t0, 1096(s0)
	addi a6, a6, 2047
	sd t0, 41(a6)
	addi a6, a6, -2047
	ld t0, 1104(s0)
	addi a6, a6, 2047
	sd t0, 49(a6)
	addi a6, a6, -2047
	ld t0, 1112(s0)
	addi a6, a6, 2047
	sd t0, 57(a6)
	addi a6, a6, -2047
	ld t0, 1120(s0)
	addi a6, a6, 2047
	sd t0, 65(a6)
	addi a6, a6, -2047
	ld t0, 1128(s0)
	addi a6, a6, 2047
	sd t0, 73(a6)
	addi a6, a6, -2047
	ld t0, 1136(s0)
	addi a6, a6, 2047
	sd t0, 81(a6)
	addi a6, a6, -2047
	ld t0, 1144(s0)
	addi a6, a6, 2047
	sd t0, 89(a6)
	addi a6, a6, -2047
	ld t0, 1152(s0)
	addi a6, a6, 2047
	sd t0, 97(a6)
	addi a6, a6, -2047
	ld t0, 1160(s0)
	addi a6, a6, 2047
	sd t0, 105(a6)
	addi a6, a6, -2047
	ld t0, 1024(s0)
	sd t0, 880(s0)
	ld t0, 1032(s0)
	sd t0, 888(s0)
	ld t0, 1040(s0)
	sd t0, 896(s0)
	ld t0, 1048(s0)
	sd t0, 904(s0)
	ld t0, 1056(s0)
	sd t0, 912(s0)
	ld t0, 1064(s0)
	sd t0, 920(s0)
	ld t0, 1072(s0)
	sd t0, 928(s0)
	ld t0, 1080(s0)
	sd t0, 936(s0)
	ld t0, 1088(s0)
	sd t0, 944(s0)
	ld t0, 1096(s0)
	sd t0, 952(s0)
	ld t0, 1104(s0)
	sd t0, 960(s0)
	ld t0, 1112(s0)
	sd t0, 968(s0)
	ld t0, 1120(s0)
	sd t0, 976(s0)
	ld t0, 1128(s0)
	sd t0, 984(s0)
	ld t0, 1136(s0)
	sd t0, 992(s0)
	ld t0, 1144(s0)
	sd t0, 1000(s0)
	ld t0, 1152(s0)
	sd t0, 1008(s0)
	ld t0, 1160(s0)
	sd t0, 1016(s0)
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 880
	addi a3, zero, 736
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 928
	addi a3, zero, 784
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 976
	addi a3, zero, 304
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 880
	addi a3, zero, 928
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 736
	addi a3, zero, 784
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1168
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 880
	addi a3, zero, 976
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 736
	addi a3, zero, 304
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 928
	addi a3, zero, 976
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 784
	addi a3, zero, 304
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 352
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 400
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1024
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1216
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1216
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1024
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1168
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 400
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1216
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1072
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1408
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1312
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1312
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1408
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1120
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 1024(s0)
	addi a6, a6, 2047
	sd t0, 113(a6)
	addi a6, a6, -2047
	ld t0, 1032(s0)
	addi a6, a6, 2047
	sd t0, 121(a6)
	addi a6, a6, -2047
	ld t0, 1040(s0)
	addi a6, a6, 2047
	sd t0, 129(a6)
	addi a6, a6, -2047
	ld t0, 1048(s0)
	addi a6, a6, 2047
	sd t0, 137(a6)
	addi a6, a6, -2047
	ld t0, 1056(s0)
	addi a6, a6, 2047
	sd t0, 145(a6)
	addi a6, a6, -2047
	ld t0, 1064(s0)
	addi a6, a6, 2047
	sd t0, 153(a6)
	addi a6, a6, -2047
	ld t0, 1072(s0)
	addi a6, a6, 2047
	sd t0, 161(a6)
	addi a6, a6, -2047
	ld t0, 1080(s0)
	addi a6, a6, 2047
	sd t0, 169(a6)
	addi a6, a6, -2047
	ld t0, 1088(s0)
	addi a6, a6, 2047
	sd t0, 177(a6)
	addi a6, a6, -2047
	ld t0, 1096(s0)
	addi a6, a6, 2047
	sd t0, 185(a6)
	addi a6, a6, -2047
	ld t0, 1104(s0)
	addi a6, a6, 2047
	sd t0, 193(a6)
	addi a6, a6, -2047
	ld t0, 1112(s0)
	addi a6, a6, 2047
	sd t0, 201(a6)
	addi a6, a6, -2047
	ld t0, 1120(s0)
	addi a6, a6, 2047
	sd t0, 209(a6)
	addi a6, a6, -2047
	ld t0, 1128(s0)
	addi a6, a6, 2047
	sd t0, 217(a6)
	addi a6, a6, -2047
	ld t0, 1136(s0)
	addi a6, a6, 2047
	sd t0, 225(a6)
	addi a6, a6, -2047
	ld t0, 1144(s0)
	addi a6, a6, 2047
	sd t0, 233(a6)
	addi a6, a6, -2047
	ld t0, 1152(s0)
	addi a6, a6, 2047
	sd t0, 241(a6)
	addi a6, a6, -2047
	ld t0, 1160(s0)
	addi a6, a6, 2047
	sd t0, 249(a6)
	addi a6, a6, -2047
	ld t0, 1024(s0)
	sd t0, 880(s0)
	ld t0, 1032(s0)
	sd t0, 888(s0)
	ld t0, 1040(s0)
	sd t0, 896(s0)
	ld t0, 1048(s0)
	sd t0, 904(s0)
	ld t0, 1056(s0)
	sd t0, 912(s0)
	ld t0, 1064(s0)
	sd t0, 920(s0)
	ld t0, 1072(s0)
	sd t0, 928(s0)
	ld t0, 1080(s0)
	sd t0, 936(s0)
	ld t0, 1088(s0)
	sd t0, 944(s0)
	ld t0, 1096(s0)
	sd t0, 952(s0)
	ld t0, 1104(s0)
	sd t0, 960(s0)
	ld t0, 1112(s0)
	sd t0, 968(s0)
	ld t0, 1120(s0)
	sd t0, 976(s0)
	ld t0, 1128(s0)
	sd t0, 984(s0)
	ld t0, 1136(s0)
	sd t0, 992(s0)
	ld t0, 1144(s0)
	sd t0, 1000(s0)
	ld t0, 1152(s0)
	sd t0, 1008(s0)
	ld t0, 1160(s0)
	sd t0, 1016(s0)
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
	addi s1, zero, 96
20:
	addi s1, s1, -1
	srli t0, s1, 4
	slli t0, t0, 3
	add t0, t0, s0
	ld t2, 1552(t0)
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
	ld t1, 144(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 288(a0)
	ld t2, 432(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 576(a0)
	ld t2, 720(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 864(a0)
	ld t3, 1008(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1152(a0)
	ld t2, 1296(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1440(a0)
	ld t3, 1584(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1728(a0)
	ld t3, 1872(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 2016(a0)
	addi t4, a0, 2047
	ld t4, 113(t4)
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
	sd t0, 801(s0)
	addi s0, s0, -2047
	ld t0, 8(a0)
	ld t1, 152(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 296(a0)
	ld t2, 440(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 584(a0)
	ld t2, 728(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 872(a0)
	ld t3, 1016(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1160(a0)
	ld t2, 1304(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1448(a0)
	ld t3, 1592(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1736(a0)
	ld t3, 1880(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 2024(a0)
	addi t4, a0, 2047
	ld t4, 121(t4)
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
	sd t0, 809(s0)
	addi s0, s0, -2047
	ld t0, 16(a0)
	ld t1, 160(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 304(a0)
	ld t2, 448(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 592(a0)
	ld t2, 736(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 880(a0)
	ld t3, 1024(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1168(a0)
	ld t2, 1312(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1456(a0)
	ld t3, 1600(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1744(a0)
	ld t3, 1888(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 2032(a0)
	addi t4, a0, 2047
	ld t4, 129(t4)
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
	sd t0, 817(s0)
	addi s0, s0, -2047
	ld t0, 24(a0)
	ld t1, 168(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 312(a0)
	ld t2, 456(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 600(a0)
	ld t2, 744(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 888(a0)
	ld t3, 1032(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1176(a0)
	ld t2, 1320(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1464(a0)
	ld t3, 1608(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1752(a0)
	ld t3, 1896(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 2040(a0)
	addi t4, a0, 2047
	ld t4, 137(t4)
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
	sd t0, 825(s0)
	addi s0, s0, -2047
	ld t0, 32(a0)
	ld t1, 176(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 320(a0)
	ld t2, 464(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 608(a0)
	ld t2, 752(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 896(a0)
	ld t3, 1040(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1184(a0)
	ld t2, 1328(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1472(a0)
	ld t3, 1616(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1760(a0)
	ld t3, 1904(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 1(t3)
	addi t4, a0, 2047
	ld t4, 145(t4)
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
	sd t0, 833(s0)
	addi s0, s0, -2047
	ld t0, 40(a0)
	ld t1, 184(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 328(a0)
	ld t2, 472(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 616(a0)
	ld t2, 760(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 904(a0)
	ld t3, 1048(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1192(a0)
	ld t2, 1336(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1480(a0)
	ld t3, 1624(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1768(a0)
	ld t3, 1912(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 9(t3)
	addi t4, a0, 2047
	ld t4, 153(t4)
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
	sd t0, 841(s0)
	addi s0, s0, -2047
	ld t0, 48(a0)
	ld t1, 192(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 336(a0)
	ld t2, 480(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 624(a0)
	ld t2, 768(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 912(a0)
	ld t3, 1056(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1200(a0)
	ld t2, 1344(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1488(a0)
	ld t3, 1632(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1776(a0)
	ld t3, 1920(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 17(t3)
	addi t4, a0, 2047
	ld t4, 161(t4)
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
	sd t0, 849(s0)
	addi s0, s0, -2047
	ld t0, 56(a0)
	ld t1, 200(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 344(a0)
	ld t2, 488(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 632(a0)
	ld t2, 776(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 920(a0)
	ld t3, 1064(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1208(a0)
	ld t2, 1352(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1496(a0)
	ld t3, 1640(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1784(a0)
	ld t3, 1928(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 25(t3)
	addi t4, a0, 2047
	ld t4, 169(t4)
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
	sd t0, 857(s0)
	addi s0, s0, -2047
	ld t0, 64(a0)
	ld t1, 208(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 352(a0)
	ld t2, 496(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 640(a0)
	ld t2, 784(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 928(a0)
	ld t3, 1072(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1216(a0)
	ld t2, 1360(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1504(a0)
	ld t3, 1648(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1792(a0)
	ld t3, 1936(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 33(t3)
	addi t4, a0, 2047
	ld t4, 177(t4)
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
	sd t0, 865(s0)
	addi s0, s0, -2047
	ld t0, 72(a0)
	ld t1, 216(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 360(a0)
	ld t2, 504(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 648(a0)
	ld t2, 792(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 936(a0)
	ld t3, 1080(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1224(a0)
	ld t2, 1368(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1512(a0)
	ld t3, 1656(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1800(a0)
	ld t3, 1944(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 41(t3)
	addi t4, a0, 2047
	ld t4, 185(t4)
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
	sd t0, 873(s0)
	addi s0, s0, -2047
	ld t0, 80(a0)
	ld t1, 224(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 368(a0)
	ld t2, 512(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 656(a0)
	ld t2, 800(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 944(a0)
	ld t3, 1088(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1232(a0)
	ld t2, 1376(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1520(a0)
	ld t3, 1664(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1808(a0)
	ld t3, 1952(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 49(t3)
	addi t4, a0, 2047
	ld t4, 193(t4)
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
	sd t0, 881(s0)
	addi s0, s0, -2047
	ld t0, 88(a0)
	ld t1, 232(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 376(a0)
	ld t2, 520(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 664(a0)
	ld t2, 808(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 952(a0)
	ld t3, 1096(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1240(a0)
	ld t2, 1384(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1528(a0)
	ld t3, 1672(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1816(a0)
	ld t3, 1960(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 57(t3)
	addi t4, a0, 2047
	ld t4, 201(t4)
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
	sd t0, 889(s0)
	addi s0, s0, -2047
	ld t0, 96(a0)
	ld t1, 240(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 384(a0)
	ld t2, 528(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 672(a0)
	ld t2, 816(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 960(a0)
	ld t3, 1104(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1248(a0)
	ld t2, 1392(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1536(a0)
	ld t3, 1680(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1824(a0)
	ld t3, 1968(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 65(t3)
	addi t4, a0, 2047
	ld t4, 209(t4)
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
	sd t0, 897(s0)
	addi s0, s0, -2047
	ld t0, 104(a0)
	ld t1, 248(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 392(a0)
	ld t2, 536(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 680(a0)
	ld t2, 824(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 968(a0)
	ld t3, 1112(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1256(a0)
	ld t2, 1400(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1544(a0)
	ld t3, 1688(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1832(a0)
	ld t3, 1976(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 73(t3)
	addi t4, a0, 2047
	ld t4, 217(t4)
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
	sd t0, 905(s0)
	addi s0, s0, -2047
	ld t0, 112(a0)
	ld t1, 256(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 400(a0)
	ld t2, 544(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 688(a0)
	ld t2, 832(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 976(a0)
	ld t3, 1120(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1264(a0)
	ld t2, 1408(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1552(a0)
	ld t3, 1696(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1840(a0)
	ld t3, 1984(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 81(t3)
	addi t4, a0, 2047
	ld t4, 225(t4)
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
	sd t0, 913(s0)
	addi s0, s0, -2047
	ld t0, 120(a0)
	ld t1, 264(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 408(a0)
	ld t2, 552(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 696(a0)
	ld t2, 840(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 984(a0)
	ld t3, 1128(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1272(a0)
	ld t2, 1416(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1560(a0)
	ld t3, 1704(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1848(a0)
	ld t3, 1992(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 89(t3)
	addi t4, a0, 2047
	ld t4, 233(t4)
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
	sd t0, 921(s0)
	addi s0, s0, -2047
	ld t0, 128(a0)
	ld t1, 272(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 416(a0)
	ld t2, 560(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 704(a0)
	ld t2, 848(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 992(a0)
	ld t3, 1136(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1280(a0)
	ld t2, 1424(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1568(a0)
	ld t3, 1712(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1856(a0)
	ld t3, 2000(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 97(t3)
	addi t4, a0, 2047
	ld t4, 241(t4)
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
	sd t0, 929(s0)
	addi s0, s0, -2047
	ld t0, 136(a0)
	ld t1, 280(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 424(a0)
	ld t2, 568(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 712(a0)
	ld t2, 856(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1000(a0)
	ld t3, 1144(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1288(a0)
	ld t2, 1432(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1576(a0)
	ld t3, 1720(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1864(a0)
	ld t3, 2008(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 105(t3)
	addi t4, a0, 2047
	ld t4, 249(t4)
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
	sd t0, 937(s0)
	addi s0, s0, -2047
	addi a0, s0, 0
	addi a1, zero, 880
	addi a2, zero, 736
	addi a3, zero, 832
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 832
	addi a3, zero, 832
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 928
	addi a2, zero, 784
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 976
	addi a2, zero, 832
	addi a3, zero, 208
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 880
	addi a3, zero, 880
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 928
	addi a3, zero, 928
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1216
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 880
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1312
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1312
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 976
	addi a3, zero, 976
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 352
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1168
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 928
	addi a3, zero, 976
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1120
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1360
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1312
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1312
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1312
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1360
	addi a3, zero, 1072
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1264
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1264
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1264
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1072
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1024
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1072
	addi a3, zero, 1072
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1216
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1024
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1312
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1312
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1120
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 352
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1168
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 976
	addi a2, zero, 1072
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 976
	addi a2, zero, 976
	addi a3, zero, 976
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 880
	addi a2, zero, 1360
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 880
	addi a2, zero, 880
	addi a3, zero, 1312
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 880
	addi a2, zero, 880
	addi a3, zero, 1312
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 928
	addi a2, zero, 1312
	addi a3, zero, 880
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 928
	addi a2, zero, 1360
	addi a3, zero, 928
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1264
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1264
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1264
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 928
	addi a2, zero, 928
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 880
	addi a3, zero, 880
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 928
	addi a3, zero, 928
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1216
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 880
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1312
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1312
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 976
	addi a3, zero, 976
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 352
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1168
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 928
	addi a3, zero, 976
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1120
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1360
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1312
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1312
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1312
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1360
	addi a3, zero, 1072
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1264
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1264
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1264
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1072
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1024
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1072
	addi a3, zero, 1072
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1216
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1024
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1312
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1312
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1120
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 352
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1168
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 976
	addi a2, zero, 1072
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 976
	addi a2, zero, 976
	addi a3, zero, 976
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 880
	addi a2, zero, 1360
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 880
	addi a2, zero, 880
	addi a3, zero, 1312
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 880
	addi a2, zero, 880
	addi a3, zero, 1312
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 928
	addi a2, zero, 1312
	addi a3, zero, 880
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 928
	addi a2, zero, 1360
	addi a3, zero, 928
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1264
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1264
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1264
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 928
	addi a2, zero, 928
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 736
	addi a2, zero, 880
	addi a3, zero, 976
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 976
	addi a3, zero, 976
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 832
	addi a2, zero, 1168
	addi a3, zero, 976
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 784
	addi a2, zero, 928
	addi a3, zero, 208
	call {vg_brainpoolp384r1_add_mod_p}
	addi t3, zero, 0
	ld t4, 832(s0)
	or t3, t3, t4
	ld t4, 840(s0)
	or t3, t3, t4
	ld t4, 848(s0)
	or t3, t3, t4
	ld t4, 856(s0)
	or t3, t3, t4
	ld t4, 864(s0)
	or t3, t3, t4
	ld t4, 872(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	ld t0, 784(s0)
	ld t1, 304(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 784(s0)
	ld t0, 792(s0)
	ld t1, 312(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 792(s0)
	ld t0, 800(s0)
	ld t1, 320(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 800(s0)
	ld t0, 808(s0)
	ld t1, 328(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 808(s0)
	ld t0, 816(s0)
	ld t1, 336(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 816(s0)
	ld t0, 824(s0)
	ld t1, 344(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 824(s0)
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 736
	addi a3, zero, 2047
	addi a3, a3, 801
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 784
	addi a3, zero, 2047
	addi a3, a3, 849
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 832
	addi a3, zero, 2047
	addi a3, a3, 897
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 736
	addi a3, zero, 784
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 2047
	addi a2, a2, 801
	addi a3, zero, 2047
	addi a3, a3, 849
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1168
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 736
	addi a3, zero, 832
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 2047
	addi a2, a2, 801
	addi a3, zero, 2047
	addi a3, a3, 897
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1408
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 784
	addi a3, zero, 832
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 2047
	addi a2, a2, 849
	addi a3, zero, 2047
	addi a3, a3, 897
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 352
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 400
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1024
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1216
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1216
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1024
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1168
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 400
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 352
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1264
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1216
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1072
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1408
	addi a3, zero, 1360
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1312
	addi a3, zero, 1024
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1312
	addi a3, zero, 1216
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1408
	addi a3, zero, 1120
	call {vg_brainpoolp384r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1120
	addi a3, zero, 1168
	call {vg_brainpoolp384r1_add_mod_p}
	ld t0, 1024(s0)
	sd t0, 736(s0)
	ld t0, 1032(s0)
	sd t0, 744(s0)
	ld t0, 1040(s0)
	sd t0, 752(s0)
	ld t0, 1048(s0)
	sd t0, 760(s0)
	ld t0, 1056(s0)
	sd t0, 768(s0)
	ld t0, 1064(s0)
	sd t0, 776(s0)
	ld t0, 1072(s0)
	sd t0, 784(s0)
	ld t0, 1080(s0)
	sd t0, 792(s0)
	ld t0, 1088(s0)
	sd t0, 800(s0)
	ld t0, 1096(s0)
	sd t0, 808(s0)
	ld t0, 1104(s0)
	sd t0, 816(s0)
	ld t0, 1112(s0)
	sd t0, 824(s0)
	ld t0, 1120(s0)
	sd t0, 832(s0)
	ld t0, 1128(s0)
	sd t0, 840(s0)
	ld t0, 1136(s0)
	sd t0, 848(s0)
	ld t0, 1144(s0)
	sd t0, 856(s0)
	ld t0, 1152(s0)
	sd t0, 864(s0)
	ld t0, 1160(s0)
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
