// The functions of `src/internal/vg_brainpoolp320r1_mul.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_brainpoolp320r1_mul:
	.option push
	.option arch, +m, +c
	sd s0, 1864(a0)
	sd s1, 1872(a0)
	sd ra, 1880(a0)
	addi s0, a0, 0
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 184(s0)
	sd t0, 0(a6)
	ld t0, 192(s0)
	sd t0, 8(a6)
	ld t0, 200(s0)
	sd t0, 16(a6)
	ld t0, 208(s0)
	sd t0, 24(a6)
	ld t0, 216(s0)
	sd t0, 32(a6)
	ld t0, 264(s0)
	sd t0, 40(a6)
	ld t0, 272(s0)
	sd t0, 48(a6)
	ld t0, 280(s0)
	sd t0, 56(a6)
	ld t0, 288(s0)
	sd t0, 64(a6)
	ld t0, 296(s0)
	sd t0, 72(a6)
	ld t0, 184(s0)
	sd t0, 80(a6)
	ld t0, 192(s0)
	sd t0, 88(a6)
	ld t0, 200(s0)
	sd t0, 96(a6)
	ld t0, 208(s0)
	sd t0, 104(a6)
	ld t0, 216(s0)
	sd t0, 112(a6)
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 624(s0)
	sd t0, 120(a6)
	ld t0, 632(s0)
	sd t0, 128(a6)
	ld t0, 640(s0)
	sd t0, 136(a6)
	ld t0, 648(s0)
	sd t0, 144(a6)
	ld t0, 656(s0)
	sd t0, 152(a6)
	ld t0, 664(s0)
	sd t0, 160(a6)
	ld t0, 672(s0)
	sd t0, 168(a6)
	ld t0, 680(s0)
	sd t0, 176(a6)
	ld t0, 688(s0)
	sd t0, 184(a6)
	ld t0, 696(s0)
	sd t0, 192(a6)
	ld t0, 264(s0)
	sd t0, 200(a6)
	ld t0, 272(s0)
	sd t0, 208(a6)
	ld t0, 280(s0)
	sd t0, 216(a6)
	ld t0, 288(s0)
	sd t0, 224(a6)
	ld t0, 296(s0)
	sd t0, 232(a6)
	ld t0, 624(s0)
	sd t0, 744(s0)
	ld t0, 632(s0)
	sd t0, 752(s0)
	ld t0, 640(s0)
	sd t0, 760(s0)
	ld t0, 648(s0)
	sd t0, 768(s0)
	ld t0, 656(s0)
	sd t0, 776(s0)
	ld t0, 664(s0)
	sd t0, 784(s0)
	ld t0, 672(s0)
	sd t0, 792(s0)
	ld t0, 680(s0)
	sd t0, 800(s0)
	ld t0, 688(s0)
	sd t0, 808(s0)
	ld t0, 696(s0)
	sd t0, 816(s0)
	ld t0, 264(s0)
	sd t0, 824(s0)
	ld t0, 272(s0)
	sd t0, 832(s0)
	ld t0, 280(s0)
	sd t0, 840(s0)
	ld t0, 288(s0)
	sd t0, 848(s0)
	ld t0, 296(s0)
	sd t0, 856(s0)
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 744
	addi a3, zero, 624
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 784
	addi a3, zero, 664
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 824
	addi a3, zero, 264
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 744
	addi a3, zero, 784
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 624
	addi a3, zero, 664
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 984
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 744
	addi a3, zero, 824
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 624
	addi a3, zero, 264
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 984
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 784
	addi a3, zero, 824
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 664
	addi a3, zero, 264
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 864
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1024
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 864
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 304
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 344
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 864
	addi a3, zero, 944
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1024
	addi a3, zero, 944
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 1024
	addi a3, zero, 944
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 904
	addi a2, zero, 864
	addi a3, zero, 944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 984
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 304
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 344
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 984
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 304
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1024
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 904
	addi a2, zero, 904
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1184
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1104
	addi a3, zero, 864
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 864
	addi a3, zero, 984
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1104
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 1184
	addi a3, zero, 944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 944
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 864(s0)
	sd t0, 240(a6)
	ld t0, 872(s0)
	sd t0, 248(a6)
	ld t0, 880(s0)
	sd t0, 256(a6)
	ld t0, 888(s0)
	sd t0, 264(a6)
	ld t0, 896(s0)
	sd t0, 272(a6)
	ld t0, 904(s0)
	sd t0, 280(a6)
	ld t0, 912(s0)
	sd t0, 288(a6)
	ld t0, 920(s0)
	sd t0, 296(a6)
	ld t0, 928(s0)
	sd t0, 304(a6)
	ld t0, 936(s0)
	sd t0, 312(a6)
	ld t0, 944(s0)
	sd t0, 320(a6)
	ld t0, 952(s0)
	sd t0, 328(a6)
	ld t0, 960(s0)
	sd t0, 336(a6)
	ld t0, 968(s0)
	sd t0, 344(a6)
	ld t0, 976(s0)
	sd t0, 352(a6)
	ld t0, 864(s0)
	sd t0, 744(s0)
	ld t0, 872(s0)
	sd t0, 752(s0)
	ld t0, 880(s0)
	sd t0, 760(s0)
	ld t0, 888(s0)
	sd t0, 768(s0)
	ld t0, 896(s0)
	sd t0, 776(s0)
	ld t0, 904(s0)
	sd t0, 784(s0)
	ld t0, 912(s0)
	sd t0, 792(s0)
	ld t0, 920(s0)
	sd t0, 800(s0)
	ld t0, 928(s0)
	sd t0, 808(s0)
	ld t0, 936(s0)
	sd t0, 816(s0)
	ld t0, 944(s0)
	sd t0, 824(s0)
	ld t0, 952(s0)
	sd t0, 832(s0)
	ld t0, 960(s0)
	sd t0, 840(s0)
	ld t0, 968(s0)
	sd t0, 848(s0)
	ld t0, 976(s0)
	sd t0, 856(s0)
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 744
	addi a3, zero, 624
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 784
	addi a3, zero, 664
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 824
	addi a3, zero, 264
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 744
	addi a3, zero, 784
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 624
	addi a3, zero, 664
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 984
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 744
	addi a3, zero, 824
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 624
	addi a3, zero, 264
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 984
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 784
	addi a3, zero, 824
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 664
	addi a3, zero, 264
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 864
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1024
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 864
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 304
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 344
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 864
	addi a3, zero, 944
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1024
	addi a3, zero, 944
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 1024
	addi a3, zero, 944
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 904
	addi a2, zero, 864
	addi a3, zero, 944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 984
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 304
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 344
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 984
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 304
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1024
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 904
	addi a2, zero, 904
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1184
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1104
	addi a3, zero, 864
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 864
	addi a3, zero, 984
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1104
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 1184
	addi a3, zero, 944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 944
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 864(s0)
	sd t0, 360(a6)
	ld t0, 872(s0)
	sd t0, 368(a6)
	ld t0, 880(s0)
	sd t0, 376(a6)
	ld t0, 888(s0)
	sd t0, 384(a6)
	ld t0, 896(s0)
	sd t0, 392(a6)
	ld t0, 904(s0)
	sd t0, 400(a6)
	ld t0, 912(s0)
	sd t0, 408(a6)
	ld t0, 920(s0)
	sd t0, 416(a6)
	ld t0, 928(s0)
	sd t0, 424(a6)
	ld t0, 936(s0)
	sd t0, 432(a6)
	ld t0, 944(s0)
	sd t0, 440(a6)
	ld t0, 952(s0)
	sd t0, 448(a6)
	ld t0, 960(s0)
	sd t0, 456(a6)
	ld t0, 968(s0)
	sd t0, 464(a6)
	ld t0, 976(s0)
	sd t0, 472(a6)
	ld t0, 864(s0)
	sd t0, 744(s0)
	ld t0, 872(s0)
	sd t0, 752(s0)
	ld t0, 880(s0)
	sd t0, 760(s0)
	ld t0, 888(s0)
	sd t0, 768(s0)
	ld t0, 896(s0)
	sd t0, 776(s0)
	ld t0, 904(s0)
	sd t0, 784(s0)
	ld t0, 912(s0)
	sd t0, 792(s0)
	ld t0, 920(s0)
	sd t0, 800(s0)
	ld t0, 928(s0)
	sd t0, 808(s0)
	ld t0, 936(s0)
	sd t0, 816(s0)
	ld t0, 944(s0)
	sd t0, 824(s0)
	ld t0, 952(s0)
	sd t0, 832(s0)
	ld t0, 960(s0)
	sd t0, 840(s0)
	ld t0, 968(s0)
	sd t0, 848(s0)
	ld t0, 976(s0)
	sd t0, 856(s0)
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 744
	addi a3, zero, 624
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 784
	addi a3, zero, 664
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 824
	addi a3, zero, 264
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 744
	addi a3, zero, 784
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 624
	addi a3, zero, 664
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 984
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 744
	addi a3, zero, 824
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 624
	addi a3, zero, 264
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 984
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 784
	addi a3, zero, 824
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 664
	addi a3, zero, 264
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 864
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1024
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 864
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 304
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 344
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 864
	addi a3, zero, 944
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1024
	addi a3, zero, 944
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 1024
	addi a3, zero, 944
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 904
	addi a2, zero, 864
	addi a3, zero, 944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 984
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 304
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 344
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 984
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 304
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1024
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 904
	addi a2, zero, 904
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1184
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1104
	addi a3, zero, 864
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 864
	addi a3, zero, 984
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1104
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 1184
	addi a3, zero, 944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 944
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 864(s0)
	sd t0, 480(a6)
	ld t0, 872(s0)
	sd t0, 488(a6)
	ld t0, 880(s0)
	sd t0, 496(a6)
	ld t0, 888(s0)
	sd t0, 504(a6)
	ld t0, 896(s0)
	sd t0, 512(a6)
	ld t0, 904(s0)
	sd t0, 520(a6)
	ld t0, 912(s0)
	sd t0, 528(a6)
	ld t0, 920(s0)
	sd t0, 536(a6)
	ld t0, 928(s0)
	sd t0, 544(a6)
	ld t0, 936(s0)
	sd t0, 552(a6)
	ld t0, 944(s0)
	sd t0, 560(a6)
	ld t0, 952(s0)
	sd t0, 568(a6)
	ld t0, 960(s0)
	sd t0, 576(a6)
	ld t0, 968(s0)
	sd t0, 584(a6)
	ld t0, 976(s0)
	sd t0, 592(a6)
	ld t0, 864(s0)
	sd t0, 744(s0)
	ld t0, 872(s0)
	sd t0, 752(s0)
	ld t0, 880(s0)
	sd t0, 760(s0)
	ld t0, 888(s0)
	sd t0, 768(s0)
	ld t0, 896(s0)
	sd t0, 776(s0)
	ld t0, 904(s0)
	sd t0, 784(s0)
	ld t0, 912(s0)
	sd t0, 792(s0)
	ld t0, 920(s0)
	sd t0, 800(s0)
	ld t0, 928(s0)
	sd t0, 808(s0)
	ld t0, 936(s0)
	sd t0, 816(s0)
	ld t0, 944(s0)
	sd t0, 824(s0)
	ld t0, 952(s0)
	sd t0, 832(s0)
	ld t0, 960(s0)
	sd t0, 840(s0)
	ld t0, 968(s0)
	sd t0, 848(s0)
	ld t0, 976(s0)
	sd t0, 856(s0)
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 744
	addi a3, zero, 624
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 784
	addi a3, zero, 664
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 824
	addi a3, zero, 264
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 744
	addi a3, zero, 784
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 624
	addi a3, zero, 664
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 984
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 744
	addi a3, zero, 824
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 624
	addi a3, zero, 264
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 984
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 784
	addi a3, zero, 824
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 664
	addi a3, zero, 264
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 864
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1024
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 864
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 304
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 344
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 864
	addi a3, zero, 944
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1024
	addi a3, zero, 944
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 1024
	addi a3, zero, 944
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 904
	addi a2, zero, 864
	addi a3, zero, 944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 984
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 304
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 344
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 984
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 304
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1024
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 904
	addi a2, zero, 904
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1184
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1104
	addi a3, zero, 864
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 864
	addi a3, zero, 984
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1104
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 1184
	addi a3, zero, 944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 944
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 864(s0)
	sd t0, 600(a6)
	ld t0, 872(s0)
	sd t0, 608(a6)
	ld t0, 880(s0)
	sd t0, 616(a6)
	ld t0, 888(s0)
	sd t0, 624(a6)
	ld t0, 896(s0)
	sd t0, 632(a6)
	ld t0, 904(s0)
	sd t0, 640(a6)
	ld t0, 912(s0)
	sd t0, 648(a6)
	ld t0, 920(s0)
	sd t0, 656(a6)
	ld t0, 928(s0)
	sd t0, 664(a6)
	ld t0, 936(s0)
	sd t0, 672(a6)
	ld t0, 944(s0)
	sd t0, 680(a6)
	ld t0, 952(s0)
	sd t0, 688(a6)
	ld t0, 960(s0)
	sd t0, 696(a6)
	ld t0, 968(s0)
	sd t0, 704(a6)
	ld t0, 976(s0)
	sd t0, 712(a6)
	ld t0, 864(s0)
	sd t0, 744(s0)
	ld t0, 872(s0)
	sd t0, 752(s0)
	ld t0, 880(s0)
	sd t0, 760(s0)
	ld t0, 888(s0)
	sd t0, 768(s0)
	ld t0, 896(s0)
	sd t0, 776(s0)
	ld t0, 904(s0)
	sd t0, 784(s0)
	ld t0, 912(s0)
	sd t0, 792(s0)
	ld t0, 920(s0)
	sd t0, 800(s0)
	ld t0, 928(s0)
	sd t0, 808(s0)
	ld t0, 936(s0)
	sd t0, 816(s0)
	ld t0, 944(s0)
	sd t0, 824(s0)
	ld t0, 952(s0)
	sd t0, 832(s0)
	ld t0, 960(s0)
	sd t0, 840(s0)
	ld t0, 968(s0)
	sd t0, 848(s0)
	ld t0, 976(s0)
	sd t0, 856(s0)
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 744
	addi a3, zero, 624
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 784
	addi a3, zero, 664
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 824
	addi a3, zero, 264
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 744
	addi a3, zero, 784
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 624
	addi a3, zero, 664
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 984
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 744
	addi a3, zero, 824
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 624
	addi a3, zero, 264
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 984
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 784
	addi a3, zero, 824
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 664
	addi a3, zero, 264
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 864
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1024
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 864
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 304
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 344
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 864
	addi a3, zero, 944
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1024
	addi a3, zero, 944
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 1024
	addi a3, zero, 944
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 904
	addi a2, zero, 864
	addi a3, zero, 944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 984
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 304
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 344
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 984
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 304
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1024
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 904
	addi a2, zero, 904
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1184
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1104
	addi a3, zero, 864
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 864
	addi a3, zero, 984
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1104
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 1184
	addi a3, zero, 944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 944
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 864(s0)
	sd t0, 720(a6)
	ld t0, 872(s0)
	sd t0, 728(a6)
	ld t0, 880(s0)
	sd t0, 736(a6)
	ld t0, 888(s0)
	sd t0, 744(a6)
	ld t0, 896(s0)
	sd t0, 752(a6)
	ld t0, 904(s0)
	sd t0, 760(a6)
	ld t0, 912(s0)
	sd t0, 768(a6)
	ld t0, 920(s0)
	sd t0, 776(a6)
	ld t0, 928(s0)
	sd t0, 784(a6)
	ld t0, 936(s0)
	sd t0, 792(a6)
	ld t0, 944(s0)
	sd t0, 800(a6)
	ld t0, 952(s0)
	sd t0, 808(a6)
	ld t0, 960(s0)
	sd t0, 816(a6)
	ld t0, 968(s0)
	sd t0, 824(a6)
	ld t0, 976(s0)
	sd t0, 832(a6)
	ld t0, 864(s0)
	sd t0, 744(s0)
	ld t0, 872(s0)
	sd t0, 752(s0)
	ld t0, 880(s0)
	sd t0, 760(s0)
	ld t0, 888(s0)
	sd t0, 768(s0)
	ld t0, 896(s0)
	sd t0, 776(s0)
	ld t0, 904(s0)
	sd t0, 784(s0)
	ld t0, 912(s0)
	sd t0, 792(s0)
	ld t0, 920(s0)
	sd t0, 800(s0)
	ld t0, 928(s0)
	sd t0, 808(s0)
	ld t0, 936(s0)
	sd t0, 816(s0)
	ld t0, 944(s0)
	sd t0, 824(s0)
	ld t0, 952(s0)
	sd t0, 832(s0)
	ld t0, 960(s0)
	sd t0, 840(s0)
	ld t0, 968(s0)
	sd t0, 848(s0)
	ld t0, 976(s0)
	sd t0, 856(s0)
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 744
	addi a3, zero, 624
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 784
	addi a3, zero, 664
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 824
	addi a3, zero, 264
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 744
	addi a3, zero, 784
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 624
	addi a3, zero, 664
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 984
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 744
	addi a3, zero, 824
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 624
	addi a3, zero, 264
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 984
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 784
	addi a3, zero, 824
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 664
	addi a3, zero, 264
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 864
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1024
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 864
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 304
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 344
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 864
	addi a3, zero, 944
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1024
	addi a3, zero, 944
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 1024
	addi a3, zero, 944
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 904
	addi a2, zero, 864
	addi a3, zero, 944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 984
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 304
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 344
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 984
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 304
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1024
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 904
	addi a2, zero, 904
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1184
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1104
	addi a3, zero, 864
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 864
	addi a3, zero, 984
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1104
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 1184
	addi a3, zero, 944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 944
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 864(s0)
	sd t0, 840(a6)
	ld t0, 872(s0)
	sd t0, 848(a6)
	ld t0, 880(s0)
	sd t0, 856(a6)
	ld t0, 888(s0)
	sd t0, 864(a6)
	ld t0, 896(s0)
	sd t0, 872(a6)
	ld t0, 904(s0)
	sd t0, 880(a6)
	ld t0, 912(s0)
	sd t0, 888(a6)
	ld t0, 920(s0)
	sd t0, 896(a6)
	ld t0, 928(s0)
	sd t0, 904(a6)
	ld t0, 936(s0)
	sd t0, 912(a6)
	ld t0, 944(s0)
	sd t0, 920(a6)
	ld t0, 952(s0)
	sd t0, 928(a6)
	ld t0, 960(s0)
	sd t0, 936(a6)
	ld t0, 968(s0)
	sd t0, 944(a6)
	ld t0, 976(s0)
	sd t0, 952(a6)
	ld t0, 864(s0)
	sd t0, 744(s0)
	ld t0, 872(s0)
	sd t0, 752(s0)
	ld t0, 880(s0)
	sd t0, 760(s0)
	ld t0, 888(s0)
	sd t0, 768(s0)
	ld t0, 896(s0)
	sd t0, 776(s0)
	ld t0, 904(s0)
	sd t0, 784(s0)
	ld t0, 912(s0)
	sd t0, 792(s0)
	ld t0, 920(s0)
	sd t0, 800(s0)
	ld t0, 928(s0)
	sd t0, 808(s0)
	ld t0, 936(s0)
	sd t0, 816(s0)
	ld t0, 944(s0)
	sd t0, 824(s0)
	ld t0, 952(s0)
	sd t0, 832(s0)
	ld t0, 960(s0)
	sd t0, 840(s0)
	ld t0, 968(s0)
	sd t0, 848(s0)
	ld t0, 976(s0)
	sd t0, 856(s0)
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 744
	addi a3, zero, 624
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 784
	addi a3, zero, 664
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 824
	addi a3, zero, 264
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 744
	addi a3, zero, 784
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 624
	addi a3, zero, 664
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 984
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 744
	addi a3, zero, 824
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 624
	addi a3, zero, 264
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 984
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 784
	addi a3, zero, 824
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 664
	addi a3, zero, 264
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 864
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1024
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 864
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 304
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 344
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 864
	addi a3, zero, 944
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1024
	addi a3, zero, 944
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 1024
	addi a3, zero, 944
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 904
	addi a2, zero, 864
	addi a3, zero, 944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 984
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 304
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 344
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 984
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 304
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1024
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 904
	addi a2, zero, 904
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1184
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1104
	addi a3, zero, 864
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 864
	addi a3, zero, 984
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1104
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 1184
	addi a3, zero, 944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 944
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 864(s0)
	sd t0, 960(a6)
	ld t0, 872(s0)
	sd t0, 968(a6)
	ld t0, 880(s0)
	sd t0, 976(a6)
	ld t0, 888(s0)
	sd t0, 984(a6)
	ld t0, 896(s0)
	sd t0, 992(a6)
	ld t0, 904(s0)
	sd t0, 1000(a6)
	ld t0, 912(s0)
	sd t0, 1008(a6)
	ld t0, 920(s0)
	sd t0, 1016(a6)
	ld t0, 928(s0)
	sd t0, 1024(a6)
	ld t0, 936(s0)
	sd t0, 1032(a6)
	ld t0, 944(s0)
	sd t0, 1040(a6)
	ld t0, 952(s0)
	sd t0, 1048(a6)
	ld t0, 960(s0)
	sd t0, 1056(a6)
	ld t0, 968(s0)
	sd t0, 1064(a6)
	ld t0, 976(s0)
	sd t0, 1072(a6)
	ld t0, 864(s0)
	sd t0, 744(s0)
	ld t0, 872(s0)
	sd t0, 752(s0)
	ld t0, 880(s0)
	sd t0, 760(s0)
	ld t0, 888(s0)
	sd t0, 768(s0)
	ld t0, 896(s0)
	sd t0, 776(s0)
	ld t0, 904(s0)
	sd t0, 784(s0)
	ld t0, 912(s0)
	sd t0, 792(s0)
	ld t0, 920(s0)
	sd t0, 800(s0)
	ld t0, 928(s0)
	sd t0, 808(s0)
	ld t0, 936(s0)
	sd t0, 816(s0)
	ld t0, 944(s0)
	sd t0, 824(s0)
	ld t0, 952(s0)
	sd t0, 832(s0)
	ld t0, 960(s0)
	sd t0, 840(s0)
	ld t0, 968(s0)
	sd t0, 848(s0)
	ld t0, 976(s0)
	sd t0, 856(s0)
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 744
	addi a3, zero, 624
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 784
	addi a3, zero, 664
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 824
	addi a3, zero, 264
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 744
	addi a3, zero, 784
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 624
	addi a3, zero, 664
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 984
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 744
	addi a3, zero, 824
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 624
	addi a3, zero, 264
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 984
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 784
	addi a3, zero, 824
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 664
	addi a3, zero, 264
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 864
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1024
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 864
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 304
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 344
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 864
	addi a3, zero, 944
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1024
	addi a3, zero, 944
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 1024
	addi a3, zero, 944
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 904
	addi a2, zero, 864
	addi a3, zero, 944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 984
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 304
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 344
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 984
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 304
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1024
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 904
	addi a2, zero, 904
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1184
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1104
	addi a3, zero, 864
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 864
	addi a3, zero, 984
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1104
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 1184
	addi a3, zero, 944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 944
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 864(s0)
	sd t0, 1080(a6)
	ld t0, 872(s0)
	sd t0, 1088(a6)
	ld t0, 880(s0)
	sd t0, 1096(a6)
	ld t0, 888(s0)
	sd t0, 1104(a6)
	ld t0, 896(s0)
	sd t0, 1112(a6)
	ld t0, 904(s0)
	sd t0, 1120(a6)
	ld t0, 912(s0)
	sd t0, 1128(a6)
	ld t0, 920(s0)
	sd t0, 1136(a6)
	ld t0, 928(s0)
	sd t0, 1144(a6)
	ld t0, 936(s0)
	sd t0, 1152(a6)
	ld t0, 944(s0)
	sd t0, 1160(a6)
	ld t0, 952(s0)
	sd t0, 1168(a6)
	ld t0, 960(s0)
	sd t0, 1176(a6)
	ld t0, 968(s0)
	sd t0, 1184(a6)
	ld t0, 976(s0)
	sd t0, 1192(a6)
	ld t0, 864(s0)
	sd t0, 744(s0)
	ld t0, 872(s0)
	sd t0, 752(s0)
	ld t0, 880(s0)
	sd t0, 760(s0)
	ld t0, 888(s0)
	sd t0, 768(s0)
	ld t0, 896(s0)
	sd t0, 776(s0)
	ld t0, 904(s0)
	sd t0, 784(s0)
	ld t0, 912(s0)
	sd t0, 792(s0)
	ld t0, 920(s0)
	sd t0, 800(s0)
	ld t0, 928(s0)
	sd t0, 808(s0)
	ld t0, 936(s0)
	sd t0, 816(s0)
	ld t0, 944(s0)
	sd t0, 824(s0)
	ld t0, 952(s0)
	sd t0, 832(s0)
	ld t0, 960(s0)
	sd t0, 840(s0)
	ld t0, 968(s0)
	sd t0, 848(s0)
	ld t0, 976(s0)
	sd t0, 856(s0)
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 744
	addi a3, zero, 624
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 784
	addi a3, zero, 664
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 824
	addi a3, zero, 264
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 744
	addi a3, zero, 784
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 624
	addi a3, zero, 664
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 984
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 744
	addi a3, zero, 824
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 624
	addi a3, zero, 264
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 984
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 784
	addi a3, zero, 824
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 664
	addi a3, zero, 264
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 864
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1024
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 864
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 304
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 344
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 864
	addi a3, zero, 944
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1024
	addi a3, zero, 944
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 1024
	addi a3, zero, 944
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 904
	addi a2, zero, 864
	addi a3, zero, 944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 984
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 304
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 344
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 984
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 304
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1024
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 904
	addi a2, zero, 904
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1184
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1104
	addi a3, zero, 864
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 864
	addi a3, zero, 984
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1104
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 1184
	addi a3, zero, 944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 944
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 864(s0)
	sd t0, 1200(a6)
	ld t0, 872(s0)
	sd t0, 1208(a6)
	ld t0, 880(s0)
	sd t0, 1216(a6)
	ld t0, 888(s0)
	sd t0, 1224(a6)
	ld t0, 896(s0)
	sd t0, 1232(a6)
	ld t0, 904(s0)
	sd t0, 1240(a6)
	ld t0, 912(s0)
	sd t0, 1248(a6)
	ld t0, 920(s0)
	sd t0, 1256(a6)
	ld t0, 928(s0)
	sd t0, 1264(a6)
	ld t0, 936(s0)
	sd t0, 1272(a6)
	ld t0, 944(s0)
	sd t0, 1280(a6)
	ld t0, 952(s0)
	sd t0, 1288(a6)
	ld t0, 960(s0)
	sd t0, 1296(a6)
	ld t0, 968(s0)
	sd t0, 1304(a6)
	ld t0, 976(s0)
	sd t0, 1312(a6)
	ld t0, 864(s0)
	sd t0, 744(s0)
	ld t0, 872(s0)
	sd t0, 752(s0)
	ld t0, 880(s0)
	sd t0, 760(s0)
	ld t0, 888(s0)
	sd t0, 768(s0)
	ld t0, 896(s0)
	sd t0, 776(s0)
	ld t0, 904(s0)
	sd t0, 784(s0)
	ld t0, 912(s0)
	sd t0, 792(s0)
	ld t0, 920(s0)
	sd t0, 800(s0)
	ld t0, 928(s0)
	sd t0, 808(s0)
	ld t0, 936(s0)
	sd t0, 816(s0)
	ld t0, 944(s0)
	sd t0, 824(s0)
	ld t0, 952(s0)
	sd t0, 832(s0)
	ld t0, 960(s0)
	sd t0, 840(s0)
	ld t0, 968(s0)
	sd t0, 848(s0)
	ld t0, 976(s0)
	sd t0, 856(s0)
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 744
	addi a3, zero, 624
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 784
	addi a3, zero, 664
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 824
	addi a3, zero, 264
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 744
	addi a3, zero, 784
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 624
	addi a3, zero, 664
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 984
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 744
	addi a3, zero, 824
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 624
	addi a3, zero, 264
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 984
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 784
	addi a3, zero, 824
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 664
	addi a3, zero, 264
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 864
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1024
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 864
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 304
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 344
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 864
	addi a3, zero, 944
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1024
	addi a3, zero, 944
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 1024
	addi a3, zero, 944
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 904
	addi a2, zero, 864
	addi a3, zero, 944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 984
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 304
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 344
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 984
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 304
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1024
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 904
	addi a2, zero, 904
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1184
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1104
	addi a3, zero, 864
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 864
	addi a3, zero, 984
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1104
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 1184
	addi a3, zero, 944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 944
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 864(s0)
	sd t0, 1320(a6)
	ld t0, 872(s0)
	sd t0, 1328(a6)
	ld t0, 880(s0)
	sd t0, 1336(a6)
	ld t0, 888(s0)
	sd t0, 1344(a6)
	ld t0, 896(s0)
	sd t0, 1352(a6)
	ld t0, 904(s0)
	sd t0, 1360(a6)
	ld t0, 912(s0)
	sd t0, 1368(a6)
	ld t0, 920(s0)
	sd t0, 1376(a6)
	ld t0, 928(s0)
	sd t0, 1384(a6)
	ld t0, 936(s0)
	sd t0, 1392(a6)
	ld t0, 944(s0)
	sd t0, 1400(a6)
	ld t0, 952(s0)
	sd t0, 1408(a6)
	ld t0, 960(s0)
	sd t0, 1416(a6)
	ld t0, 968(s0)
	sd t0, 1424(a6)
	ld t0, 976(s0)
	sd t0, 1432(a6)
	ld t0, 864(s0)
	sd t0, 744(s0)
	ld t0, 872(s0)
	sd t0, 752(s0)
	ld t0, 880(s0)
	sd t0, 760(s0)
	ld t0, 888(s0)
	sd t0, 768(s0)
	ld t0, 896(s0)
	sd t0, 776(s0)
	ld t0, 904(s0)
	sd t0, 784(s0)
	ld t0, 912(s0)
	sd t0, 792(s0)
	ld t0, 920(s0)
	sd t0, 800(s0)
	ld t0, 928(s0)
	sd t0, 808(s0)
	ld t0, 936(s0)
	sd t0, 816(s0)
	ld t0, 944(s0)
	sd t0, 824(s0)
	ld t0, 952(s0)
	sd t0, 832(s0)
	ld t0, 960(s0)
	sd t0, 840(s0)
	ld t0, 968(s0)
	sd t0, 848(s0)
	ld t0, 976(s0)
	sd t0, 856(s0)
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 744
	addi a3, zero, 624
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 784
	addi a3, zero, 664
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 824
	addi a3, zero, 264
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 744
	addi a3, zero, 784
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 624
	addi a3, zero, 664
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 984
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 744
	addi a3, zero, 824
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 624
	addi a3, zero, 264
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 984
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 784
	addi a3, zero, 824
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 664
	addi a3, zero, 264
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 864
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1024
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 864
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 304
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 344
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 864
	addi a3, zero, 944
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1024
	addi a3, zero, 944
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 1024
	addi a3, zero, 944
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 904
	addi a2, zero, 864
	addi a3, zero, 944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 984
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 304
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 344
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 984
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 304
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1024
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 904
	addi a2, zero, 904
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1184
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1104
	addi a3, zero, 864
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 864
	addi a3, zero, 984
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1104
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 1184
	addi a3, zero, 944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 944
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 864(s0)
	sd t0, 1440(a6)
	ld t0, 872(s0)
	sd t0, 1448(a6)
	ld t0, 880(s0)
	sd t0, 1456(a6)
	ld t0, 888(s0)
	sd t0, 1464(a6)
	ld t0, 896(s0)
	sd t0, 1472(a6)
	ld t0, 904(s0)
	sd t0, 1480(a6)
	ld t0, 912(s0)
	sd t0, 1488(a6)
	ld t0, 920(s0)
	sd t0, 1496(a6)
	ld t0, 928(s0)
	sd t0, 1504(a6)
	ld t0, 936(s0)
	sd t0, 1512(a6)
	ld t0, 944(s0)
	sd t0, 1520(a6)
	ld t0, 952(s0)
	sd t0, 1528(a6)
	ld t0, 960(s0)
	sd t0, 1536(a6)
	ld t0, 968(s0)
	sd t0, 1544(a6)
	ld t0, 976(s0)
	sd t0, 1552(a6)
	ld t0, 864(s0)
	sd t0, 744(s0)
	ld t0, 872(s0)
	sd t0, 752(s0)
	ld t0, 880(s0)
	sd t0, 760(s0)
	ld t0, 888(s0)
	sd t0, 768(s0)
	ld t0, 896(s0)
	sd t0, 776(s0)
	ld t0, 904(s0)
	sd t0, 784(s0)
	ld t0, 912(s0)
	sd t0, 792(s0)
	ld t0, 920(s0)
	sd t0, 800(s0)
	ld t0, 928(s0)
	sd t0, 808(s0)
	ld t0, 936(s0)
	sd t0, 816(s0)
	ld t0, 944(s0)
	sd t0, 824(s0)
	ld t0, 952(s0)
	sd t0, 832(s0)
	ld t0, 960(s0)
	sd t0, 840(s0)
	ld t0, 968(s0)
	sd t0, 848(s0)
	ld t0, 976(s0)
	sd t0, 856(s0)
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 744
	addi a3, zero, 624
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 784
	addi a3, zero, 664
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 824
	addi a3, zero, 264
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 744
	addi a3, zero, 784
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 624
	addi a3, zero, 664
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 984
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 744
	addi a3, zero, 824
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 624
	addi a3, zero, 264
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 984
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 784
	addi a3, zero, 824
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 664
	addi a3, zero, 264
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 864
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1024
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 864
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 304
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 344
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 864
	addi a3, zero, 944
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1024
	addi a3, zero, 944
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 1024
	addi a3, zero, 944
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 904
	addi a2, zero, 864
	addi a3, zero, 944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 984
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 304
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 344
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 984
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 304
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1024
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 904
	addi a2, zero, 904
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1184
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1104
	addi a3, zero, 864
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 864
	addi a3, zero, 984
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1104
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 1184
	addi a3, zero, 944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 944
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 864(s0)
	sd t0, 1560(a6)
	ld t0, 872(s0)
	sd t0, 1568(a6)
	ld t0, 880(s0)
	sd t0, 1576(a6)
	ld t0, 888(s0)
	sd t0, 1584(a6)
	ld t0, 896(s0)
	sd t0, 1592(a6)
	ld t0, 904(s0)
	sd t0, 1600(a6)
	ld t0, 912(s0)
	sd t0, 1608(a6)
	ld t0, 920(s0)
	sd t0, 1616(a6)
	ld t0, 928(s0)
	sd t0, 1624(a6)
	ld t0, 936(s0)
	sd t0, 1632(a6)
	ld t0, 944(s0)
	sd t0, 1640(a6)
	ld t0, 952(s0)
	sd t0, 1648(a6)
	ld t0, 960(s0)
	sd t0, 1656(a6)
	ld t0, 968(s0)
	sd t0, 1664(a6)
	ld t0, 976(s0)
	sd t0, 1672(a6)
	ld t0, 864(s0)
	sd t0, 744(s0)
	ld t0, 872(s0)
	sd t0, 752(s0)
	ld t0, 880(s0)
	sd t0, 760(s0)
	ld t0, 888(s0)
	sd t0, 768(s0)
	ld t0, 896(s0)
	sd t0, 776(s0)
	ld t0, 904(s0)
	sd t0, 784(s0)
	ld t0, 912(s0)
	sd t0, 792(s0)
	ld t0, 920(s0)
	sd t0, 800(s0)
	ld t0, 928(s0)
	sd t0, 808(s0)
	ld t0, 936(s0)
	sd t0, 816(s0)
	ld t0, 944(s0)
	sd t0, 824(s0)
	ld t0, 952(s0)
	sd t0, 832(s0)
	ld t0, 960(s0)
	sd t0, 840(s0)
	ld t0, 968(s0)
	sd t0, 848(s0)
	ld t0, 976(s0)
	sd t0, 856(s0)
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 744
	addi a3, zero, 624
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 784
	addi a3, zero, 664
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 824
	addi a3, zero, 264
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 744
	addi a3, zero, 784
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 624
	addi a3, zero, 664
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 984
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 744
	addi a3, zero, 824
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 624
	addi a3, zero, 264
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 984
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 784
	addi a3, zero, 824
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 664
	addi a3, zero, 264
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 864
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1024
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 864
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 304
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 344
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 864
	addi a3, zero, 944
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1024
	addi a3, zero, 944
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 1024
	addi a3, zero, 944
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 904
	addi a2, zero, 864
	addi a3, zero, 944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 984
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 304
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 344
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 984
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 304
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1024
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 904
	addi a2, zero, 904
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1184
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1104
	addi a3, zero, 864
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 864
	addi a3, zero, 984
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1104
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 1184
	addi a3, zero, 944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 944
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 864(s0)
	sd t0, 1680(a6)
	ld t0, 872(s0)
	sd t0, 1688(a6)
	ld t0, 880(s0)
	sd t0, 1696(a6)
	ld t0, 888(s0)
	sd t0, 1704(a6)
	ld t0, 896(s0)
	sd t0, 1712(a6)
	ld t0, 904(s0)
	sd t0, 1720(a6)
	ld t0, 912(s0)
	sd t0, 1728(a6)
	ld t0, 920(s0)
	sd t0, 1736(a6)
	ld t0, 928(s0)
	sd t0, 1744(a6)
	ld t0, 936(s0)
	sd t0, 1752(a6)
	ld t0, 944(s0)
	sd t0, 1760(a6)
	ld t0, 952(s0)
	sd t0, 1768(a6)
	ld t0, 960(s0)
	sd t0, 1776(a6)
	ld t0, 968(s0)
	sd t0, 1784(a6)
	ld t0, 976(s0)
	sd t0, 1792(a6)
	ld t0, 864(s0)
	sd t0, 744(s0)
	ld t0, 872(s0)
	sd t0, 752(s0)
	ld t0, 880(s0)
	sd t0, 760(s0)
	ld t0, 888(s0)
	sd t0, 768(s0)
	ld t0, 896(s0)
	sd t0, 776(s0)
	ld t0, 904(s0)
	sd t0, 784(s0)
	ld t0, 912(s0)
	sd t0, 792(s0)
	ld t0, 920(s0)
	sd t0, 800(s0)
	ld t0, 928(s0)
	sd t0, 808(s0)
	ld t0, 936(s0)
	sd t0, 816(s0)
	ld t0, 944(s0)
	sd t0, 824(s0)
	ld t0, 952(s0)
	sd t0, 832(s0)
	ld t0, 960(s0)
	sd t0, 840(s0)
	ld t0, 968(s0)
	sd t0, 848(s0)
	ld t0, 976(s0)
	sd t0, 856(s0)
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 744
	addi a3, zero, 624
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 784
	addi a3, zero, 664
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 824
	addi a3, zero, 264
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 744
	addi a3, zero, 784
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 624
	addi a3, zero, 664
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 984
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 744
	addi a3, zero, 824
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 624
	addi a3, zero, 264
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 984
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 784
	addi a3, zero, 824
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 664
	addi a3, zero, 264
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 864
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1024
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 864
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 304
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 344
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 864
	addi a3, zero, 944
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1024
	addi a3, zero, 944
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 1024
	addi a3, zero, 944
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 904
	addi a2, zero, 864
	addi a3, zero, 944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 984
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 304
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 344
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 984
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 304
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1024
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 904
	addi a2, zero, 904
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1184
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1104
	addi a3, zero, 864
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 864
	addi a3, zero, 984
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1104
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 1184
	addi a3, zero, 944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 944
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 864(s0)
	sd t0, 1800(a6)
	ld t0, 872(s0)
	sd t0, 1808(a6)
	ld t0, 880(s0)
	sd t0, 1816(a6)
	ld t0, 888(s0)
	sd t0, 1824(a6)
	ld t0, 896(s0)
	sd t0, 1832(a6)
	ld t0, 904(s0)
	sd t0, 1840(a6)
	ld t0, 912(s0)
	sd t0, 1848(a6)
	ld t0, 920(s0)
	sd t0, 1856(a6)
	ld t0, 928(s0)
	sd t0, 1864(a6)
	ld t0, 936(s0)
	sd t0, 1872(a6)
	ld t0, 944(s0)
	sd t0, 1880(a6)
	ld t0, 952(s0)
	sd t0, 1888(a6)
	ld t0, 960(s0)
	sd t0, 1896(a6)
	ld t0, 968(s0)
	sd t0, 1904(a6)
	ld t0, 976(s0)
	sd t0, 1912(a6)
	ld t0, 864(s0)
	sd t0, 744(s0)
	ld t0, 872(s0)
	sd t0, 752(s0)
	ld t0, 880(s0)
	sd t0, 760(s0)
	ld t0, 888(s0)
	sd t0, 768(s0)
	ld t0, 896(s0)
	sd t0, 776(s0)
	ld t0, 904(s0)
	sd t0, 784(s0)
	ld t0, 912(s0)
	sd t0, 792(s0)
	ld t0, 920(s0)
	sd t0, 800(s0)
	ld t0, 928(s0)
	sd t0, 808(s0)
	ld t0, 936(s0)
	sd t0, 816(s0)
	ld t0, 944(s0)
	sd t0, 824(s0)
	ld t0, 952(s0)
	sd t0, 832(s0)
	ld t0, 960(s0)
	sd t0, 840(s0)
	ld t0, 968(s0)
	sd t0, 848(s0)
	ld t0, 976(s0)
	sd t0, 856(s0)
	ld t0, 184(s0)
	sd t0, 624(s0)
	ld t0, 192(s0)
	sd t0, 632(s0)
	ld t0, 200(s0)
	sd t0, 640(s0)
	ld t0, 208(s0)
	sd t0, 648(s0)
	ld t0, 216(s0)
	sd t0, 656(s0)
	ld t0, 264(s0)
	sd t0, 664(s0)
	ld t0, 272(s0)
	sd t0, 672(s0)
	ld t0, 280(s0)
	sd t0, 680(s0)
	ld t0, 288(s0)
	sd t0, 688(s0)
	ld t0, 296(s0)
	sd t0, 696(s0)
	ld t0, 184(s0)
	sd t0, 704(s0)
	ld t0, 192(s0)
	sd t0, 712(s0)
	ld t0, 200(s0)
	sd t0, 720(s0)
	ld t0, 208(s0)
	sd t0, 728(s0)
	ld t0, 216(s0)
	sd t0, 736(s0)
	addi s1, zero, 80
20:
	addi s1, s1, -1
	srli t0, s1, 4
	slli t0, t0, 3
	add t0, t0, s0
	ld t2, 1304(t0)
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
	ld t1, 120(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 240(a0)
	ld t2, 360(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 480(a0)
	ld t2, 600(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 720(a0)
	ld t3, 840(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 960(a0)
	ld t2, 1080(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1200(a0)
	ld t3, 1320(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1440(a0)
	ld t3, 1560(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1680(a0)
	ld t4, 1800(a0)
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
	sd t0, 337(s0)
	addi s0, s0, -2047
	ld t0, 8(a0)
	ld t1, 128(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 248(a0)
	ld t2, 368(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 488(a0)
	ld t2, 608(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 728(a0)
	ld t3, 848(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 968(a0)
	ld t2, 1088(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1208(a0)
	ld t3, 1328(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1448(a0)
	ld t3, 1568(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1688(a0)
	ld t4, 1808(a0)
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
	sd t0, 345(s0)
	addi s0, s0, -2047
	ld t0, 16(a0)
	ld t1, 136(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 256(a0)
	ld t2, 376(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 496(a0)
	ld t2, 616(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 736(a0)
	ld t3, 856(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 976(a0)
	ld t2, 1096(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1216(a0)
	ld t3, 1336(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1456(a0)
	ld t3, 1576(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1696(a0)
	ld t4, 1816(a0)
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
	sd t0, 353(s0)
	addi s0, s0, -2047
	ld t0, 24(a0)
	ld t1, 144(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 264(a0)
	ld t2, 384(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 504(a0)
	ld t2, 624(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 744(a0)
	ld t3, 864(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 984(a0)
	ld t2, 1104(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1224(a0)
	ld t3, 1344(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1464(a0)
	ld t3, 1584(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1704(a0)
	ld t4, 1824(a0)
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
	sd t0, 361(s0)
	addi s0, s0, -2047
	ld t0, 32(a0)
	ld t1, 152(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 272(a0)
	ld t2, 392(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 512(a0)
	ld t2, 632(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 752(a0)
	ld t3, 872(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 992(a0)
	ld t2, 1112(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1232(a0)
	ld t3, 1352(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1472(a0)
	ld t3, 1592(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1712(a0)
	ld t4, 1832(a0)
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
	sd t0, 369(s0)
	addi s0, s0, -2047
	ld t0, 40(a0)
	ld t1, 160(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 280(a0)
	ld t2, 400(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 520(a0)
	ld t2, 640(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 760(a0)
	ld t3, 880(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1000(a0)
	ld t2, 1120(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1240(a0)
	ld t3, 1360(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1480(a0)
	ld t3, 1600(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1720(a0)
	ld t4, 1840(a0)
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
	sd t0, 377(s0)
	addi s0, s0, -2047
	ld t0, 48(a0)
	ld t1, 168(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 288(a0)
	ld t2, 408(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 528(a0)
	ld t2, 648(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 768(a0)
	ld t3, 888(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1008(a0)
	ld t2, 1128(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1248(a0)
	ld t3, 1368(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1488(a0)
	ld t3, 1608(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1728(a0)
	ld t4, 1848(a0)
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
	sd t0, 385(s0)
	addi s0, s0, -2047
	ld t0, 56(a0)
	ld t1, 176(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 296(a0)
	ld t2, 416(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 536(a0)
	ld t2, 656(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 776(a0)
	ld t3, 896(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1016(a0)
	ld t2, 1136(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1256(a0)
	ld t3, 1376(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1496(a0)
	ld t3, 1616(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1736(a0)
	ld t4, 1856(a0)
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
	sd t0, 393(s0)
	addi s0, s0, -2047
	ld t0, 64(a0)
	ld t1, 184(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 304(a0)
	ld t2, 424(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 544(a0)
	ld t2, 664(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 784(a0)
	ld t3, 904(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1024(a0)
	ld t2, 1144(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1264(a0)
	ld t3, 1384(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1504(a0)
	ld t3, 1624(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1744(a0)
	ld t4, 1864(a0)
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
	sd t0, 401(s0)
	addi s0, s0, -2047
	ld t0, 72(a0)
	ld t1, 192(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 312(a0)
	ld t2, 432(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 552(a0)
	ld t2, 672(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 792(a0)
	ld t3, 912(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1032(a0)
	ld t2, 1152(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1272(a0)
	ld t3, 1392(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1512(a0)
	ld t3, 1632(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1752(a0)
	ld t4, 1872(a0)
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
	sd t0, 409(s0)
	addi s0, s0, -2047
	ld t0, 80(a0)
	ld t1, 200(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 320(a0)
	ld t2, 440(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 560(a0)
	ld t2, 680(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 800(a0)
	ld t3, 920(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1040(a0)
	ld t2, 1160(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1280(a0)
	ld t3, 1400(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1520(a0)
	ld t3, 1640(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1760(a0)
	ld t4, 1880(a0)
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
	sd t0, 417(s0)
	addi s0, s0, -2047
	ld t0, 88(a0)
	ld t1, 208(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 328(a0)
	ld t2, 448(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 568(a0)
	ld t2, 688(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 808(a0)
	ld t3, 928(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1048(a0)
	ld t2, 1168(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1288(a0)
	ld t3, 1408(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1528(a0)
	ld t3, 1648(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1768(a0)
	ld t4, 1888(a0)
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
	sd t0, 425(s0)
	addi s0, s0, -2047
	ld t0, 96(a0)
	ld t1, 216(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 336(a0)
	ld t2, 456(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 576(a0)
	ld t2, 696(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 816(a0)
	ld t3, 936(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1056(a0)
	ld t2, 1176(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1296(a0)
	ld t3, 1416(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1536(a0)
	ld t3, 1656(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1776(a0)
	ld t4, 1896(a0)
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
	sd t0, 433(s0)
	addi s0, s0, -2047
	ld t0, 104(a0)
	ld t1, 224(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 344(a0)
	ld t2, 464(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 584(a0)
	ld t2, 704(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 824(a0)
	ld t3, 944(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1064(a0)
	ld t2, 1184(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1304(a0)
	ld t3, 1424(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1544(a0)
	ld t3, 1664(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1784(a0)
	ld t4, 1904(a0)
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
	sd t0, 441(s0)
	addi s0, s0, -2047
	ld t0, 112(a0)
	ld t1, 232(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 352(a0)
	ld t2, 472(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 592(a0)
	ld t2, 712(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 832(a0)
	ld t3, 952(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1072(a0)
	ld t2, 1192(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1312(a0)
	ld t3, 1432(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1552(a0)
	ld t3, 1672(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1792(a0)
	ld t4, 1912(a0)
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
	sd t0, 449(s0)
	addi s0, s0, -2047
	addi a0, s0, 0
	addi a1, zero, 744
	addi a2, zero, 624
	addi a3, zero, 704
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 704
	addi a3, zero, 704
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 784
	addi a2, zero, 664
	addi a3, zero, 984
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 824
	addi a2, zero, 704
	addi a3, zero, 184
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 744
	addi a3, zero, 744
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 784
	addi a3, zero, 784
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 1024
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 744
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1104
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 984
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1104
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 824
	addi a3, zero, 824
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 304
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 984
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 784
	addi a3, zero, 824
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 944
	addi a3, zero, 944
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1144
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 864
	addi a3, zero, 1104
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 864
	addi a3, zero, 1104
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 904
	addi a2, zero, 1104
	addi a3, zero, 864
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 904
	addi a2, zero, 1144
	addi a3, zero, 904
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 1064
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 1064
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 1064
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 904
	addi a2, zero, 904
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 864
	addi a3, zero, 864
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 904
	addi a3, zero, 904
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 1024
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 864
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1104
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 984
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1104
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 944
	addi a3, zero, 944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 304
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 984
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 824
	addi a2, zero, 904
	addi a3, zero, 944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 824
	addi a2, zero, 824
	addi a3, zero, 824
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 744
	addi a2, zero, 1144
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 744
	addi a2, zero, 744
	addi a3, zero, 1104
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 744
	addi a2, zero, 744
	addi a3, zero, 1104
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 784
	addi a2, zero, 1104
	addi a3, zero, 744
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 784
	addi a2, zero, 1144
	addi a3, zero, 784
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 1064
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 1064
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 1064
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 784
	addi a2, zero, 784
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 744
	addi a3, zero, 744
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 784
	addi a3, zero, 784
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 1024
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 744
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1104
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 984
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1104
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 824
	addi a3, zero, 824
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 304
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 984
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 784
	addi a3, zero, 824
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 944
	addi a3, zero, 944
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1144
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 864
	addi a3, zero, 1104
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 864
	addi a3, zero, 1104
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 904
	addi a2, zero, 1104
	addi a3, zero, 864
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 904
	addi a2, zero, 1144
	addi a3, zero, 904
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 1064
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 1064
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 1064
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 904
	addi a2, zero, 904
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 864
	addi a3, zero, 864
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 904
	addi a3, zero, 904
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 1024
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 864
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1104
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 984
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1104
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 944
	addi a3, zero, 944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 304
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 984
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 824
	addi a2, zero, 904
	addi a3, zero, 944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 824
	addi a2, zero, 824
	addi a3, zero, 824
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 744
	addi a2, zero, 1144
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 744
	addi a2, zero, 744
	addi a3, zero, 1104
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 744
	addi a2, zero, 744
	addi a3, zero, 1104
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 784
	addi a2, zero, 1104
	addi a3, zero, 744
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 784
	addi a2, zero, 1144
	addi a3, zero, 784
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 1064
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 1064
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 1064
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 784
	addi a2, zero, 784
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 624
	addi a2, zero, 744
	addi a3, zero, 824
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 824
	addi a3, zero, 824
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 704
	addi a2, zero, 984
	addi a3, zero, 824
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 664
	addi a2, zero, 784
	addi a3, zero, 184
	call {vg_brainpoolp320r1_add_mod_p}
	addi t3, zero, 0
	ld t4, 704(s0)
	or t3, t3, t4
	ld t4, 712(s0)
	or t3, t3, t4
	ld t4, 720(s0)
	or t3, t3, t4
	ld t4, 728(s0)
	or t3, t3, t4
	ld t4, 736(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	ld t0, 664(s0)
	ld t1, 264(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 664(s0)
	ld t0, 672(s0)
	ld t1, 272(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 672(s0)
	ld t0, 680(s0)
	ld t1, 280(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 680(s0)
	ld t0, 688(s0)
	ld t1, 288(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 688(s0)
	ld t0, 696(s0)
	ld t1, 296(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 696(s0)
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 624
	addi a3, zero, 2047
	addi a3, a3, 337
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 664
	addi a3, zero, 2047
	addi a3, a3, 377
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 704
	addi a3, zero, 2047
	addi a3, a3, 417
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 624
	addi a3, zero, 664
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 2047
	addi a2, a2, 337
	addi a3, zero, 2047
	addi a3, a3, 377
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 984
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1104
	addi a2, zero, 1104
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 624
	addi a3, zero, 704
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 2047
	addi a2, a2, 337
	addi a3, zero, 2047
	addi a3, a3, 417
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 984
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1184
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 664
	addi a3, zero, 704
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 2047
	addi a2, a2, 377
	addi a3, zero, 2047
	addi a3, a3, 417
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 864
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1024
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1184
	addi a3, zero, 864
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 304
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 344
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 864
	addi a3, zero, 944
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1024
	addi a3, zero, 944
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 1024
	addi a3, zero, 944
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 904
	addi a2, zero, 864
	addi a3, zero, 944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 984
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 304
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 344
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 984
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1064
	addi a2, zero, 304
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 1064
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1024
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 904
	addi a2, zero, 904
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1184
	addi a3, zero, 1144
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 1104
	addi a3, zero, 864
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 864
	addi a3, zero, 984
	call {vg_brainpoolp320r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 984
	addi a2, zero, 1104
	addi a3, zero, 1024
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 1184
	addi a3, zero, 944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 944
	addi a2, zero, 944
	addi a3, zero, 984
	call {vg_brainpoolp320r1_add_mod_p}
	ld t0, 864(s0)
	sd t0, 624(s0)
	ld t0, 872(s0)
	sd t0, 632(s0)
	ld t0, 880(s0)
	sd t0, 640(s0)
	ld t0, 888(s0)
	sd t0, 648(s0)
	ld t0, 896(s0)
	sd t0, 656(s0)
	ld t0, 904(s0)
	sd t0, 664(s0)
	ld t0, 912(s0)
	sd t0, 672(s0)
	ld t0, 920(s0)
	sd t0, 680(s0)
	ld t0, 928(s0)
	sd t0, 688(s0)
	ld t0, 936(s0)
	sd t0, 696(s0)
	ld t0, 944(s0)
	sd t0, 704(s0)
	ld t0, 952(s0)
	sd t0, 712(s0)
	ld t0, 960(s0)
	sd t0, 720(s0)
	ld t0, 968(s0)
	sd t0, 728(s0)
	ld t0, 976(s0)
	sd t0, 736(s0)
	bnez s1, 20b
	ld ra, 1880(s0)
	ld s1, 1872(s0)
	ld s0, 1864(s0)
	ret
	.option pop
