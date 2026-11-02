// The functions of `src/argon2.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_argon2:
	.option push
	.option arch, +m, +c
	addi sp, sp, -320
	addi t0, sp, 0
	sd ra, 72(t0)
	sd s0, 80(t0)
	sd s1, 88(t0)
	sd s2, 96(t0)
	sd s3, 104(t0)
	sd s4, 112(t0)
	sd a0, 120(t0)
	sd a1, 128(t0)
	sd a2, 136(t0)
	sd a3, 144(t0)
	sd a4, 152(t0)
	sd a5, 160(t0)
	sd a6, 168(t0)
	sd a7, 176(t0)
	addi s3, t0, 0
	ld s4, 376(s3)
	addi s0, s4, 1024
	addi s0, s0, 1024
	lwu a0, 176(s3)
	slli a2, a0, 2
	lwu a1, 168(s3)
	addi a3, zero, 0
	addi a4, zero, 0
	addi a6, zero, 1
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	sd a3, 240(s3)
	slli a3, a3, 2
	sd a3, 224(s3)
	slli a3, a3, 10
	sd a3, 232(s3)
	addi a1, zero, 64
	addi a0, s4, 0
	addi a2, s4, 832
	addi a3, zero, 0
	call {vg_blake2b_init}
	lwu a0, 176(s3)
	sw a0, 896(s4)
	lwu a0, 392(s3)
	sw a0, 900(s4)
	lwu a0, 168(s3)
	sw a0, 904(s4)
	lwu a0, 160(s3)
	sw a0, 908(s4)
	addi a0, zero, 19
	sw a0, 912(s4)
	lwu a0, 120(s3)
	sw a0, 916(s4)
	addi a1, zero, 0
	addi a2, s4, 896
	addi a3, zero, 24
	addi a0, s4, 0
	addi a4, s4, 192
	call {vg_blake2b_update_scratch}
	addi a0, zero, 24
	sd a0, 248(s3)
	ld a0, 136(s3)
	sw a0, 920(s4)
	ld a1, 248(s3)
	addi a2, s4, 920
	addi a3, zero, 4
	addi a0, s4, 0
	addi a4, s4, 192
	call {vg_blake2b_update_scratch}
	ld a1, 248(s3)
	addi a1, a1, 4
	sd a1, 248(s3)
	ld a2, 128(s3)
	ld a3, 136(s3)
	addi a0, s4, 0
	addi a4, s4, 192
	call {vg_blake2b_update_scratch}
	ld a1, 248(s3)
	ld a0, 136(s3)
	add a1, a1, a0
	sd a1, 248(s3)
	ld a0, 152(s3)
	sw a0, 920(s4)
	ld a1, 248(s3)
	addi a2, s4, 920
	addi a3, zero, 4
	addi a0, s4, 0
	addi a4, s4, 192
	call {vg_blake2b_update_scratch}
	ld a1, 248(s3)
	addi a1, a1, 4
	sd a1, 248(s3)
	ld a2, 144(s3)
	ld a3, 152(s3)
	addi a0, s4, 0
	addi a4, s4, 192
	call {vg_blake2b_update_scratch}
	ld a1, 248(s3)
	ld a0, 152(s3)
	add a1, a1, a0
	sd a1, 248(s3)
	ld a0, 336(s3)
	sw a0, 920(s4)
	ld a1, 248(s3)
	addi a2, s4, 920
	addi a3, zero, 4
	addi a0, s4, 0
	addi a4, s4, 192
	call {vg_blake2b_update_scratch}
	ld a1, 248(s3)
	addi a1, a1, 4
	sd a1, 248(s3)
	ld a2, 328(s3)
	ld a3, 336(s3)
	addi a0, s4, 0
	addi a4, s4, 192
	call {vg_blake2b_update_scratch}
	ld a1, 248(s3)
	ld a0, 336(s3)
	add a1, a1, a0
	sd a1, 248(s3)
	ld a0, 352(s3)
	sw a0, 920(s4)
	ld a1, 248(s3)
	addi a2, s4, 920
	addi a3, zero, 4
	addi a0, s4, 0
	addi a4, s4, 192
	call {vg_blake2b_update_scratch}
	ld a1, 248(s3)
	addi a1, a1, 4
	sd a1, 248(s3)
	ld a2, 344(s3)
	ld a3, 352(s3)
	addi a0, s4, 0
	addi a4, s4, 192
	call {vg_blake2b_update_scratch}
	ld a1, 248(s3)
	ld a0, 352(s3)
	add a1, a1, a0
	sd a1, 248(s3)
	ld a1, 248(s3)
	addi a0, s4, 0
	addi a2, s4, 768
	addi a3, s4, 192
	call {vg_blake2b_finalize_scratch}
	ld a0, 768(s4)
	sd a0, 0(s3)
	ld a0, 776(s4)
	sd a0, 8(s3)
	ld a0, 784(s4)
	sd a0, 16(s3)
	ld a0, 792(s4)
	sd a0, 24(s3)
	ld a0, 800(s4)
	sd a0, 32(s3)
	ld a0, 808(s4)
	sd a0, 40(s3)
	ld a0, 816(s4)
	sd a0, 48(s3)
	ld a0, 824(s4)
	sd a0, 56(s3)
	ld a2, 360(s3)
	ld a3, 368(s3)
	slli a3, a3, 7
	addi a4, zero, 0
20:
	sd a4, 0(a2)
	addi a2, a2, 8
	addi a3, a3, -1
	bnez a3, 20b
	ld s2, 360(s3)
	addi s1, zero, 0
21:
	addi a0, zero, 0
	sw a0, 64(s3)
	sw s1, 68(s3)
	addi a0, s3, 0
	addi a1, zero, 72
	addi a2, s2, 0
	addi a3, zero, 1024
	addi a4, s4, 0
	call {vg_argon2_hprime}
	addi s2, s2, 1024
	addi a0, zero, 1
	sw a0, 64(s3)
	sw s1, 68(s3)
	addi a0, s3, 0
	addi a1, zero, 72
	addi a2, s2, 0
	addi a3, zero, 1024
	addi a4, s4, 0
	call {vg_argon2_hprime}
	ld a0, 232(s3)
	add s2, s2, a0
	addi s2, s2, -1024
	addi s1, s1, 1
	lwu a0, 176(s3)
	sub a0, s1, a0
	bnez a0, 21b
	addi a0, zero, 0
	sd a0, 184(s3)
22:
	addi a0, zero, 0
	sd a0, 200(s3)
23:
	addi a0, zero, 0
	sd a0, 192(s3)
24:
	addi a0, zero, 0
	sd a0, 216(s3)
	ld a0, 184(s3)
	ld a1, 200(s3)
	or a0, a0, a1
	beqz a0, 25f
	addi a0, zero, 0
	sd a0, 208(s3)
	j 26f
25:
	addi a0, zero, 2
	sd a0, 208(s3)
26:
	ld a0, 208(s3)
	ld a1, 240(s3)
	sub a1, a0, a1
	beqz a1, 27f
29:
	lwu a0, 120(s3)
	addi a1, zero, 1
	xor a1, a0, a1
	addi a2, zero, 2
	xor a2, a0, a2
	ld a3, 184(s3)
	or a2, a2, a3
	ld a3, 200(s3)
	srli a3, a3, 1
	or a2, a2, a3
	addi a4, zero, 0
	sub a4, a4, a1
	or a4, a4, a1
	srli a5, a4, 63
	addi a4, zero, 0
	sub a4, a4, a2
	or a4, a4, a2
	srli a3, a4, 63
	and a5, a5, a3
	bnez a5, 210f
	ld a0, 208(s3)
	srli a0, a0, 7
	addi a0, a0, 1
	ld a1, 216(s3)
	sub a1, a0, a1
	beqz a1, 212f
	sd a0, 216(s3)
	addi a0, zero, 0
	sd a0, 1024(s4)
	sd a0, 1032(s4)
	sd a0, 1040(s4)
	sd a0, 1048(s4)
	sd a0, 1056(s4)
	sd a0, 1064(s4)
	sd a0, 1072(s4)
	sd a0, 1080(s4)
	sd a0, 1088(s4)
	sd a0, 1096(s4)
	sd a0, 1104(s4)
	sd a0, 1112(s4)
	sd a0, 1120(s4)
	sd a0, 1128(s4)
	sd a0, 1136(s4)
	sd a0, 1144(s4)
	sd a0, 1152(s4)
	sd a0, 1160(s4)
	sd a0, 1168(s4)
	sd a0, 1176(s4)
	sd a0, 1184(s4)
	sd a0, 1192(s4)
	sd a0, 1200(s4)
	sd a0, 1208(s4)
	sd a0, 1216(s4)
	sd a0, 1224(s4)
	sd a0, 1232(s4)
	sd a0, 1240(s4)
	sd a0, 1248(s4)
	sd a0, 1256(s4)
	sd a0, 1264(s4)
	sd a0, 1272(s4)
	sd a0, 1280(s4)
	sd a0, 1288(s4)
	sd a0, 1296(s4)
	sd a0, 1304(s4)
	sd a0, 1312(s4)
	sd a0, 1320(s4)
	sd a0, 1328(s4)
	sd a0, 1336(s4)
	sd a0, 1344(s4)
	sd a0, 1352(s4)
	sd a0, 1360(s4)
	sd a0, 1368(s4)
	sd a0, 1376(s4)
	sd a0, 1384(s4)
	sd a0, 1392(s4)
	sd a0, 1400(s4)
	sd a0, 1408(s4)
	sd a0, 1416(s4)
	sd a0, 1424(s4)
	sd a0, 1432(s4)
	sd a0, 1440(s4)
	sd a0, 1448(s4)
	sd a0, 1456(s4)
	sd a0, 1464(s4)
	sd a0, 1472(s4)
	sd a0, 1480(s4)
	sd a0, 1488(s4)
	sd a0, 1496(s4)
	sd a0, 1504(s4)
	sd a0, 1512(s4)
	sd a0, 1520(s4)
	sd a0, 1528(s4)
	sd a0, 1536(s4)
	sd a0, 1544(s4)
	sd a0, 1552(s4)
	sd a0, 1560(s4)
	sd a0, 1568(s4)
	sd a0, 1576(s4)
	sd a0, 1584(s4)
	sd a0, 1592(s4)
	sd a0, 1600(s4)
	sd a0, 1608(s4)
	sd a0, 1616(s4)
	sd a0, 1624(s4)
	sd a0, 1632(s4)
	sd a0, 1640(s4)
	sd a0, 1648(s4)
	sd a0, 1656(s4)
	sd a0, 1664(s4)
	sd a0, 1672(s4)
	sd a0, 1680(s4)
	sd a0, 1688(s4)
	sd a0, 1696(s4)
	sd a0, 1704(s4)
	sd a0, 1712(s4)
	sd a0, 1720(s4)
	sd a0, 1728(s4)
	sd a0, 1736(s4)
	sd a0, 1744(s4)
	sd a0, 1752(s4)
	sd a0, 1760(s4)
	sd a0, 1768(s4)
	sd a0, 1776(s4)
	sd a0, 1784(s4)
	sd a0, 1792(s4)
	sd a0, 1800(s4)
	sd a0, 1808(s4)
	sd a0, 1816(s4)
	sd a0, 1824(s4)
	sd a0, 1832(s4)
	sd a0, 1840(s4)
	sd a0, 1848(s4)
	sd a0, 1856(s4)
	sd a0, 1864(s4)
	sd a0, 1872(s4)
	sd a0, 1880(s4)
	sd a0, 1888(s4)
	sd a0, 1896(s4)
	sd a0, 1904(s4)
	sd a0, 1912(s4)
	sd a0, 1920(s4)
	sd a0, 1928(s4)
	sd a0, 1936(s4)
	sd a0, 1944(s4)
	sd a0, 1952(s4)
	sd a0, 1960(s4)
	sd a0, 1968(s4)
	sd a0, 1976(s4)
	sd a0, 1984(s4)
	sd a0, 1992(s4)
	sd a0, 2000(s4)
	sd a0, 2008(s4)
	sd a0, 2016(s4)
	sd a0, 2024(s4)
	sd a0, 2032(s4)
	sd a0, 2040(s4)
	addi a0, zero, 0
	sd a0, 1024(s0)
	sd a0, 1032(s0)
	sd a0, 1040(s0)
	sd a0, 1048(s0)
	sd a0, 1056(s0)
	sd a0, 1064(s0)
	sd a0, 1072(s0)
	sd a0, 1080(s0)
	sd a0, 1088(s0)
	sd a0, 1096(s0)
	sd a0, 1104(s0)
	sd a0, 1112(s0)
	sd a0, 1120(s0)
	sd a0, 1128(s0)
	sd a0, 1136(s0)
	sd a0, 1144(s0)
	sd a0, 1152(s0)
	sd a0, 1160(s0)
	sd a0, 1168(s0)
	sd a0, 1176(s0)
	sd a0, 1184(s0)
	sd a0, 1192(s0)
	sd a0, 1200(s0)
	sd a0, 1208(s0)
	sd a0, 1216(s0)
	sd a0, 1224(s0)
	sd a0, 1232(s0)
	sd a0, 1240(s0)
	sd a0, 1248(s0)
	sd a0, 1256(s0)
	sd a0, 1264(s0)
	sd a0, 1272(s0)
	sd a0, 1280(s0)
	sd a0, 1288(s0)
	sd a0, 1296(s0)
	sd a0, 1304(s0)
	sd a0, 1312(s0)
	sd a0, 1320(s0)
	sd a0, 1328(s0)
	sd a0, 1336(s0)
	sd a0, 1344(s0)
	sd a0, 1352(s0)
	sd a0, 1360(s0)
	sd a0, 1368(s0)
	sd a0, 1376(s0)
	sd a0, 1384(s0)
	sd a0, 1392(s0)
	sd a0, 1400(s0)
	sd a0, 1408(s0)
	sd a0, 1416(s0)
	sd a0, 1424(s0)
	sd a0, 1432(s0)
	sd a0, 1440(s0)
	sd a0, 1448(s0)
	sd a0, 1456(s0)
	sd a0, 1464(s0)
	sd a0, 1472(s0)
	sd a0, 1480(s0)
	sd a0, 1488(s0)
	sd a0, 1496(s0)
	sd a0, 1504(s0)
	sd a0, 1512(s0)
	sd a0, 1520(s0)
	sd a0, 1528(s0)
	sd a0, 1536(s0)
	sd a0, 1544(s0)
	sd a0, 1552(s0)
	sd a0, 1560(s0)
	sd a0, 1568(s0)
	sd a0, 1576(s0)
	sd a0, 1584(s0)
	sd a0, 1592(s0)
	sd a0, 1600(s0)
	sd a0, 1608(s0)
	sd a0, 1616(s0)
	sd a0, 1624(s0)
	sd a0, 1632(s0)
	sd a0, 1640(s0)
	sd a0, 1648(s0)
	sd a0, 1656(s0)
	sd a0, 1664(s0)
	sd a0, 1672(s0)
	sd a0, 1680(s0)
	sd a0, 1688(s0)
	sd a0, 1696(s0)
	sd a0, 1704(s0)
	sd a0, 1712(s0)
	sd a0, 1720(s0)
	sd a0, 1728(s0)
	sd a0, 1736(s0)
	sd a0, 1744(s0)
	sd a0, 1752(s0)
	sd a0, 1760(s0)
	sd a0, 1768(s0)
	sd a0, 1776(s0)
	sd a0, 1784(s0)
	sd a0, 1792(s0)
	sd a0, 1800(s0)
	sd a0, 1808(s0)
	sd a0, 1816(s0)
	sd a0, 1824(s0)
	sd a0, 1832(s0)
	sd a0, 1840(s0)
	sd a0, 1848(s0)
	sd a0, 1856(s0)
	sd a0, 1864(s0)
	sd a0, 1872(s0)
	sd a0, 1880(s0)
	sd a0, 1888(s0)
	sd a0, 1896(s0)
	sd a0, 1904(s0)
	sd a0, 1912(s0)
	sd a0, 1920(s0)
	sd a0, 1928(s0)
	sd a0, 1936(s0)
	sd a0, 1944(s0)
	sd a0, 1952(s0)
	sd a0, 1960(s0)
	sd a0, 1968(s0)
	sd a0, 1976(s0)
	sd a0, 1984(s0)
	sd a0, 1992(s0)
	sd a0, 2000(s0)
	sd a0, 2008(s0)
	sd a0, 2016(s0)
	sd a0, 2024(s0)
	sd a0, 2032(s0)
	sd a0, 2040(s0)
	ld a0, 184(s3)
	sd a0, 1024(s4)
	ld a0, 192(s3)
	sd a0, 1032(s4)
	ld a0, 200(s3)
	sd a0, 1040(s4)
	ld a0, 368(s3)
	sd a0, 1048(s4)
	lwu a0, 160(s3)
	sd a0, 1056(s4)
	lwu a0, 120(s3)
	sd a0, 1064(s4)
	ld a0, 216(s3)
	sd a0, 1072(s4)
	addi a0, s0, 1024
	addi a1, s4, 1024
	addi a2, s4, 0
	addi a3, s0, 1024
	addi a3, a3, 1024
	call {vg_argon2_compress}
	addi a0, s0, 1024
	addi a1, s4, 0
	addi a2, s0, 0
	addi a3, s0, 1024
	addi a3, a3, 1024
	call {vg_argon2_compress}
	j 213f
212:
213:
	ld a0, 208(s3)
	addi a1, zero, 127
	and a0, a0, a1
	slli a0, a0, 3
	add a0, s0, a0
	lwu a1, 0(a0)
	sd a1, 256(s3)
	lwu a1, 4(a0)
	sd a1, 264(s3)
	j 211f
210:
	ld a0, 200(s3)
	ld a2, 240(s3)
	mul a0, a0, a2
	ld a2, 208(s3)
	add a1, a0, a2
	beqz a1, 214f
	j 215f
214:
	ld a1, 224(s3)
215:
	addi a1, a1, -1
	ld a0, 192(s3)
	ld a2, 224(s3)
	mul a0, a0, a2
	add a0, a0, a1
	slli a0, a0, 10
	ld a2, 360(s3)
	add a0, a2, a0
	lwu a1, 0(a0)
	sd a1, 256(s3)
	lwu a1, 4(a0)
	sd a1, 264(s3)
211:
	ld a1, 264(s3)
	lwu a2, 176(s3)
	addi a3, zero, 0
	addi a4, zero, 0
	addi a6, zero, 1
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	srliw a5, a1, 31
	slli a1, a1, 1
	slli a4, a4, 1
	add a4, a4, a5
	sub a5, a4, a2
	srli a5, a5, 63
	sub a5, a6, a5
	slli a3, a3, 1
	add a3, a3, a5
	mul a5, a5, a2
	sub a4, a4, a5
	sd a4, 272(s3)
	ld a0, 184(s3)
	ld a1, 200(s3)
	or a0, a0, a1
	beqz a0, 216f
	j 217f
216:
	ld a0, 192(s3)
	sd a0, 272(s3)
217:
	addi a0, zero, 0
	sd a0, 280(s3)
	ld a1, 184(s3)
	beqz a1, 218f
	ld a1, 200(s3)
	addi a1, a1, -3
	beqz a1, 220f
	ld a0, 200(s3)
	addi a0, a0, 1
	ld a2, 240(s3)
	mul a0, a0, a2
	sd a0, 280(s3)
	j 221f
220:
221:
	j 219f
218:
219:
	ld a1, 184(s3)
	beqz a1, 222f
	ld a0, 224(s3)
	ld a2, 240(s3)
	sub a0, a0, a2
	j 223f
222:
	ld a0, 200(s3)
	ld a2, 240(s3)
	mul a0, a0, a2
223:
	ld a2, 208(s3)
	add a1, a0, a2
	addi a1, a1, -1
	addi a3, zero, 0
	sub a3, a3, a2
	or a3, a3, a2
	srli a3, a3, 63
	addi a3, a3, -1
	add a0, a0, a3
	ld a2, 272(s3)
	ld a3, 192(s3)
	xor a2, a2, a3
	addi a3, zero, 0
	sub a3, a3, a2
	or a3, a3, a2
	srli a3, a3, 63
	addi a2, a3, -1
	xor a1, a1, a0
	and a1, a1, a2
	xor a0, a0, a1
	sd a0, 296(s3)
	ld a1, 256(s3)
	mul a1, a1, a1
	srli a1, a1, 32
	ld a2, 296(s3)
	mul a1, a2, a1
	srli a1, a1, 32
	addi a0, a2, -1
	sub a0, a0, a1
	ld a1, 280(s3)
	add a0, a0, a1
	ld a1, 224(s3)
	sub a2, a0, a1
	srli a3, a2, 63
	mul a3, a3, a1
	add a0, a2, a3
	addi a1, a0, 0
	ld a0, 272(s3)
	ld a2, 224(s3)
	mul a0, a0, a2
	add a0, a0, a1
	slli a0, a0, 10
	ld a2, 360(s3)
	add a0, a2, a0
	sd a0, 304(s3)
	ld a0, 200(s3)
	ld a2, 240(s3)
	mul a0, a0, a2
	ld a2, 208(s3)
	add a1, a0, a2
	ld a0, 192(s3)
	ld a2, 224(s3)
	mul a0, a0, a2
	add a0, a0, a1
	slli a0, a0, 10
	ld a2, 360(s3)
	add a0, a2, a0
	sd a0, 288(s3)
	ld a0, 200(s3)
	ld a2, 240(s3)
	mul a0, a0, a2
	ld a2, 208(s3)
	add a1, a0, a2
	beqz a1, 224f
	j 225f
224:
	ld a1, 224(s3)
225:
	addi a1, a1, -1
	ld a0, 192(s3)
	ld a2, 224(s3)
	mul a0, a0, a2
	add a0, a0, a1
	slli a0, a0, 10
	ld a2, 360(s3)
	add a0, a2, a0
	ld a1, 304(s3)
	addi a2, s4, 0
	addi a3, s0, 1024
	addi a3, a3, 1024
	call {vg_argon2_compress}
	addi a1, s4, 0
	ld a3, 288(s3)
	ld a0, 184(s3)
	beqz a0, 226f
	ld a0, 0(a1)
	ld a2, 0(a3)
	xor a0, a0, a2
	sd a0, 0(a3)
	ld a0, 8(a1)
	ld a2, 8(a3)
	xor a0, a0, a2
	sd a0, 8(a3)
	ld a0, 16(a1)
	ld a2, 16(a3)
	xor a0, a0, a2
	sd a0, 16(a3)
	ld a0, 24(a1)
	ld a2, 24(a3)
	xor a0, a0, a2
	sd a0, 24(a3)
	ld a0, 32(a1)
	ld a2, 32(a3)
	xor a0, a0, a2
	sd a0, 32(a3)
	ld a0, 40(a1)
	ld a2, 40(a3)
	xor a0, a0, a2
	sd a0, 40(a3)
	ld a0, 48(a1)
	ld a2, 48(a3)
	xor a0, a0, a2
	sd a0, 48(a3)
	ld a0, 56(a1)
	ld a2, 56(a3)
	xor a0, a0, a2
	sd a0, 56(a3)
	ld a0, 64(a1)
	ld a2, 64(a3)
	xor a0, a0, a2
	sd a0, 64(a3)
	ld a0, 72(a1)
	ld a2, 72(a3)
	xor a0, a0, a2
	sd a0, 72(a3)
	ld a0, 80(a1)
	ld a2, 80(a3)
	xor a0, a0, a2
	sd a0, 80(a3)
	ld a0, 88(a1)
	ld a2, 88(a3)
	xor a0, a0, a2
	sd a0, 88(a3)
	ld a0, 96(a1)
	ld a2, 96(a3)
	xor a0, a0, a2
	sd a0, 96(a3)
	ld a0, 104(a1)
	ld a2, 104(a3)
	xor a0, a0, a2
	sd a0, 104(a3)
	ld a0, 112(a1)
	ld a2, 112(a3)
	xor a0, a0, a2
	sd a0, 112(a3)
	ld a0, 120(a1)
	ld a2, 120(a3)
	xor a0, a0, a2
	sd a0, 120(a3)
	ld a0, 128(a1)
	ld a2, 128(a3)
	xor a0, a0, a2
	sd a0, 128(a3)
	ld a0, 136(a1)
	ld a2, 136(a3)
	xor a0, a0, a2
	sd a0, 136(a3)
	ld a0, 144(a1)
	ld a2, 144(a3)
	xor a0, a0, a2
	sd a0, 144(a3)
	ld a0, 152(a1)
	ld a2, 152(a3)
	xor a0, a0, a2
	sd a0, 152(a3)
	ld a0, 160(a1)
	ld a2, 160(a3)
	xor a0, a0, a2
	sd a0, 160(a3)
	ld a0, 168(a1)
	ld a2, 168(a3)
	xor a0, a0, a2
	sd a0, 168(a3)
	ld a0, 176(a1)
	ld a2, 176(a3)
	xor a0, a0, a2
	sd a0, 176(a3)
	ld a0, 184(a1)
	ld a2, 184(a3)
	xor a0, a0, a2
	sd a0, 184(a3)
	ld a0, 192(a1)
	ld a2, 192(a3)
	xor a0, a0, a2
	sd a0, 192(a3)
	ld a0, 200(a1)
	ld a2, 200(a3)
	xor a0, a0, a2
	sd a0, 200(a3)
	ld a0, 208(a1)
	ld a2, 208(a3)
	xor a0, a0, a2
	sd a0, 208(a3)
	ld a0, 216(a1)
	ld a2, 216(a3)
	xor a0, a0, a2
	sd a0, 216(a3)
	ld a0, 224(a1)
	ld a2, 224(a3)
	xor a0, a0, a2
	sd a0, 224(a3)
	ld a0, 232(a1)
	ld a2, 232(a3)
	xor a0, a0, a2
	sd a0, 232(a3)
	ld a0, 240(a1)
	ld a2, 240(a3)
	xor a0, a0, a2
	sd a0, 240(a3)
	ld a0, 248(a1)
	ld a2, 248(a3)
	xor a0, a0, a2
	sd a0, 248(a3)
	ld a0, 256(a1)
	ld a2, 256(a3)
	xor a0, a0, a2
	sd a0, 256(a3)
	ld a0, 264(a1)
	ld a2, 264(a3)
	xor a0, a0, a2
	sd a0, 264(a3)
	ld a0, 272(a1)
	ld a2, 272(a3)
	xor a0, a0, a2
	sd a0, 272(a3)
	ld a0, 280(a1)
	ld a2, 280(a3)
	xor a0, a0, a2
	sd a0, 280(a3)
	ld a0, 288(a1)
	ld a2, 288(a3)
	xor a0, a0, a2
	sd a0, 288(a3)
	ld a0, 296(a1)
	ld a2, 296(a3)
	xor a0, a0, a2
	sd a0, 296(a3)
	ld a0, 304(a1)
	ld a2, 304(a3)
	xor a0, a0, a2
	sd a0, 304(a3)
	ld a0, 312(a1)
	ld a2, 312(a3)
	xor a0, a0, a2
	sd a0, 312(a3)
	ld a0, 320(a1)
	ld a2, 320(a3)
	xor a0, a0, a2
	sd a0, 320(a3)
	ld a0, 328(a1)
	ld a2, 328(a3)
	xor a0, a0, a2
	sd a0, 328(a3)
	ld a0, 336(a1)
	ld a2, 336(a3)
	xor a0, a0, a2
	sd a0, 336(a3)
	ld a0, 344(a1)
	ld a2, 344(a3)
	xor a0, a0, a2
	sd a0, 344(a3)
	ld a0, 352(a1)
	ld a2, 352(a3)
	xor a0, a0, a2
	sd a0, 352(a3)
	ld a0, 360(a1)
	ld a2, 360(a3)
	xor a0, a0, a2
	sd a0, 360(a3)
	ld a0, 368(a1)
	ld a2, 368(a3)
	xor a0, a0, a2
	sd a0, 368(a3)
	ld a0, 376(a1)
	ld a2, 376(a3)
	xor a0, a0, a2
	sd a0, 376(a3)
	ld a0, 384(a1)
	ld a2, 384(a3)
	xor a0, a0, a2
	sd a0, 384(a3)
	ld a0, 392(a1)
	ld a2, 392(a3)
	xor a0, a0, a2
	sd a0, 392(a3)
	ld a0, 400(a1)
	ld a2, 400(a3)
	xor a0, a0, a2
	sd a0, 400(a3)
	ld a0, 408(a1)
	ld a2, 408(a3)
	xor a0, a0, a2
	sd a0, 408(a3)
	ld a0, 416(a1)
	ld a2, 416(a3)
	xor a0, a0, a2
	sd a0, 416(a3)
	ld a0, 424(a1)
	ld a2, 424(a3)
	xor a0, a0, a2
	sd a0, 424(a3)
	ld a0, 432(a1)
	ld a2, 432(a3)
	xor a0, a0, a2
	sd a0, 432(a3)
	ld a0, 440(a1)
	ld a2, 440(a3)
	xor a0, a0, a2
	sd a0, 440(a3)
	ld a0, 448(a1)
	ld a2, 448(a3)
	xor a0, a0, a2
	sd a0, 448(a3)
	ld a0, 456(a1)
	ld a2, 456(a3)
	xor a0, a0, a2
	sd a0, 456(a3)
	ld a0, 464(a1)
	ld a2, 464(a3)
	xor a0, a0, a2
	sd a0, 464(a3)
	ld a0, 472(a1)
	ld a2, 472(a3)
	xor a0, a0, a2
	sd a0, 472(a3)
	ld a0, 480(a1)
	ld a2, 480(a3)
	xor a0, a0, a2
	sd a0, 480(a3)
	ld a0, 488(a1)
	ld a2, 488(a3)
	xor a0, a0, a2
	sd a0, 488(a3)
	ld a0, 496(a1)
	ld a2, 496(a3)
	xor a0, a0, a2
	sd a0, 496(a3)
	ld a0, 504(a1)
	ld a2, 504(a3)
	xor a0, a0, a2
	sd a0, 504(a3)
	ld a0, 512(a1)
	ld a2, 512(a3)
	xor a0, a0, a2
	sd a0, 512(a3)
	ld a0, 520(a1)
	ld a2, 520(a3)
	xor a0, a0, a2
	sd a0, 520(a3)
	ld a0, 528(a1)
	ld a2, 528(a3)
	xor a0, a0, a2
	sd a0, 528(a3)
	ld a0, 536(a1)
	ld a2, 536(a3)
	xor a0, a0, a2
	sd a0, 536(a3)
	ld a0, 544(a1)
	ld a2, 544(a3)
	xor a0, a0, a2
	sd a0, 544(a3)
	ld a0, 552(a1)
	ld a2, 552(a3)
	xor a0, a0, a2
	sd a0, 552(a3)
	ld a0, 560(a1)
	ld a2, 560(a3)
	xor a0, a0, a2
	sd a0, 560(a3)
	ld a0, 568(a1)
	ld a2, 568(a3)
	xor a0, a0, a2
	sd a0, 568(a3)
	ld a0, 576(a1)
	ld a2, 576(a3)
	xor a0, a0, a2
	sd a0, 576(a3)
	ld a0, 584(a1)
	ld a2, 584(a3)
	xor a0, a0, a2
	sd a0, 584(a3)
	ld a0, 592(a1)
	ld a2, 592(a3)
	xor a0, a0, a2
	sd a0, 592(a3)
	ld a0, 600(a1)
	ld a2, 600(a3)
	xor a0, a0, a2
	sd a0, 600(a3)
	ld a0, 608(a1)
	ld a2, 608(a3)
	xor a0, a0, a2
	sd a0, 608(a3)
	ld a0, 616(a1)
	ld a2, 616(a3)
	xor a0, a0, a2
	sd a0, 616(a3)
	ld a0, 624(a1)
	ld a2, 624(a3)
	xor a0, a0, a2
	sd a0, 624(a3)
	ld a0, 632(a1)
	ld a2, 632(a3)
	xor a0, a0, a2
	sd a0, 632(a3)
	ld a0, 640(a1)
	ld a2, 640(a3)
	xor a0, a0, a2
	sd a0, 640(a3)
	ld a0, 648(a1)
	ld a2, 648(a3)
	xor a0, a0, a2
	sd a0, 648(a3)
	ld a0, 656(a1)
	ld a2, 656(a3)
	xor a0, a0, a2
	sd a0, 656(a3)
	ld a0, 664(a1)
	ld a2, 664(a3)
	xor a0, a0, a2
	sd a0, 664(a3)
	ld a0, 672(a1)
	ld a2, 672(a3)
	xor a0, a0, a2
	sd a0, 672(a3)
	ld a0, 680(a1)
	ld a2, 680(a3)
	xor a0, a0, a2
	sd a0, 680(a3)
	ld a0, 688(a1)
	ld a2, 688(a3)
	xor a0, a0, a2
	sd a0, 688(a3)
	ld a0, 696(a1)
	ld a2, 696(a3)
	xor a0, a0, a2
	sd a0, 696(a3)
	ld a0, 704(a1)
	ld a2, 704(a3)
	xor a0, a0, a2
	sd a0, 704(a3)
	ld a0, 712(a1)
	ld a2, 712(a3)
	xor a0, a0, a2
	sd a0, 712(a3)
	ld a0, 720(a1)
	ld a2, 720(a3)
	xor a0, a0, a2
	sd a0, 720(a3)
	ld a0, 728(a1)
	ld a2, 728(a3)
	xor a0, a0, a2
	sd a0, 728(a3)
	ld a0, 736(a1)
	ld a2, 736(a3)
	xor a0, a0, a2
	sd a0, 736(a3)
	ld a0, 744(a1)
	ld a2, 744(a3)
	xor a0, a0, a2
	sd a0, 744(a3)
	ld a0, 752(a1)
	ld a2, 752(a3)
	xor a0, a0, a2
	sd a0, 752(a3)
	ld a0, 760(a1)
	ld a2, 760(a3)
	xor a0, a0, a2
	sd a0, 760(a3)
	ld a0, 768(a1)
	ld a2, 768(a3)
	xor a0, a0, a2
	sd a0, 768(a3)
	ld a0, 776(a1)
	ld a2, 776(a3)
	xor a0, a0, a2
	sd a0, 776(a3)
	ld a0, 784(a1)
	ld a2, 784(a3)
	xor a0, a0, a2
	sd a0, 784(a3)
	ld a0, 792(a1)
	ld a2, 792(a3)
	xor a0, a0, a2
	sd a0, 792(a3)
	ld a0, 800(a1)
	ld a2, 800(a3)
	xor a0, a0, a2
	sd a0, 800(a3)
	ld a0, 808(a1)
	ld a2, 808(a3)
	xor a0, a0, a2
	sd a0, 808(a3)
	ld a0, 816(a1)
	ld a2, 816(a3)
	xor a0, a0, a2
	sd a0, 816(a3)
	ld a0, 824(a1)
	ld a2, 824(a3)
	xor a0, a0, a2
	sd a0, 824(a3)
	ld a0, 832(a1)
	ld a2, 832(a3)
	xor a0, a0, a2
	sd a0, 832(a3)
	ld a0, 840(a1)
	ld a2, 840(a3)
	xor a0, a0, a2
	sd a0, 840(a3)
	ld a0, 848(a1)
	ld a2, 848(a3)
	xor a0, a0, a2
	sd a0, 848(a3)
	ld a0, 856(a1)
	ld a2, 856(a3)
	xor a0, a0, a2
	sd a0, 856(a3)
	ld a0, 864(a1)
	ld a2, 864(a3)
	xor a0, a0, a2
	sd a0, 864(a3)
	ld a0, 872(a1)
	ld a2, 872(a3)
	xor a0, a0, a2
	sd a0, 872(a3)
	ld a0, 880(a1)
	ld a2, 880(a3)
	xor a0, a0, a2
	sd a0, 880(a3)
	ld a0, 888(a1)
	ld a2, 888(a3)
	xor a0, a0, a2
	sd a0, 888(a3)
	ld a0, 896(a1)
	ld a2, 896(a3)
	xor a0, a0, a2
	sd a0, 896(a3)
	ld a0, 904(a1)
	ld a2, 904(a3)
	xor a0, a0, a2
	sd a0, 904(a3)
	ld a0, 912(a1)
	ld a2, 912(a3)
	xor a0, a0, a2
	sd a0, 912(a3)
	ld a0, 920(a1)
	ld a2, 920(a3)
	xor a0, a0, a2
	sd a0, 920(a3)
	ld a0, 928(a1)
	ld a2, 928(a3)
	xor a0, a0, a2
	sd a0, 928(a3)
	ld a0, 936(a1)
	ld a2, 936(a3)
	xor a0, a0, a2
	sd a0, 936(a3)
	ld a0, 944(a1)
	ld a2, 944(a3)
	xor a0, a0, a2
	sd a0, 944(a3)
	ld a0, 952(a1)
	ld a2, 952(a3)
	xor a0, a0, a2
	sd a0, 952(a3)
	ld a0, 960(a1)
	ld a2, 960(a3)
	xor a0, a0, a2
	sd a0, 960(a3)
	ld a0, 968(a1)
	ld a2, 968(a3)
	xor a0, a0, a2
	sd a0, 968(a3)
	ld a0, 976(a1)
	ld a2, 976(a3)
	xor a0, a0, a2
	sd a0, 976(a3)
	ld a0, 984(a1)
	ld a2, 984(a3)
	xor a0, a0, a2
	sd a0, 984(a3)
	ld a0, 992(a1)
	ld a2, 992(a3)
	xor a0, a0, a2
	sd a0, 992(a3)
	ld a0, 1000(a1)
	ld a2, 1000(a3)
	xor a0, a0, a2
	sd a0, 1000(a3)
	ld a0, 1008(a1)
	ld a2, 1008(a3)
	xor a0, a0, a2
	sd a0, 1008(a3)
	ld a0, 1016(a1)
	ld a2, 1016(a3)
	xor a0, a0, a2
	sd a0, 1016(a3)
	j 227f
226:
	ld a0, 0(a1)
	sd a0, 0(a3)
	ld a0, 8(a1)
	sd a0, 8(a3)
	ld a0, 16(a1)
	sd a0, 16(a3)
	ld a0, 24(a1)
	sd a0, 24(a3)
	ld a0, 32(a1)
	sd a0, 32(a3)
	ld a0, 40(a1)
	sd a0, 40(a3)
	ld a0, 48(a1)
	sd a0, 48(a3)
	ld a0, 56(a1)
	sd a0, 56(a3)
	ld a0, 64(a1)
	sd a0, 64(a3)
	ld a0, 72(a1)
	sd a0, 72(a3)
	ld a0, 80(a1)
	sd a0, 80(a3)
	ld a0, 88(a1)
	sd a0, 88(a3)
	ld a0, 96(a1)
	sd a0, 96(a3)
	ld a0, 104(a1)
	sd a0, 104(a3)
	ld a0, 112(a1)
	sd a0, 112(a3)
	ld a0, 120(a1)
	sd a0, 120(a3)
	ld a0, 128(a1)
	sd a0, 128(a3)
	ld a0, 136(a1)
	sd a0, 136(a3)
	ld a0, 144(a1)
	sd a0, 144(a3)
	ld a0, 152(a1)
	sd a0, 152(a3)
	ld a0, 160(a1)
	sd a0, 160(a3)
	ld a0, 168(a1)
	sd a0, 168(a3)
	ld a0, 176(a1)
	sd a0, 176(a3)
	ld a0, 184(a1)
	sd a0, 184(a3)
	ld a0, 192(a1)
	sd a0, 192(a3)
	ld a0, 200(a1)
	sd a0, 200(a3)
	ld a0, 208(a1)
	sd a0, 208(a3)
	ld a0, 216(a1)
	sd a0, 216(a3)
	ld a0, 224(a1)
	sd a0, 224(a3)
	ld a0, 232(a1)
	sd a0, 232(a3)
	ld a0, 240(a1)
	sd a0, 240(a3)
	ld a0, 248(a1)
	sd a0, 248(a3)
	ld a0, 256(a1)
	sd a0, 256(a3)
	ld a0, 264(a1)
	sd a0, 264(a3)
	ld a0, 272(a1)
	sd a0, 272(a3)
	ld a0, 280(a1)
	sd a0, 280(a3)
	ld a0, 288(a1)
	sd a0, 288(a3)
	ld a0, 296(a1)
	sd a0, 296(a3)
	ld a0, 304(a1)
	sd a0, 304(a3)
	ld a0, 312(a1)
	sd a0, 312(a3)
	ld a0, 320(a1)
	sd a0, 320(a3)
	ld a0, 328(a1)
	sd a0, 328(a3)
	ld a0, 336(a1)
	sd a0, 336(a3)
	ld a0, 344(a1)
	sd a0, 344(a3)
	ld a0, 352(a1)
	sd a0, 352(a3)
	ld a0, 360(a1)
	sd a0, 360(a3)
	ld a0, 368(a1)
	sd a0, 368(a3)
	ld a0, 376(a1)
	sd a0, 376(a3)
	ld a0, 384(a1)
	sd a0, 384(a3)
	ld a0, 392(a1)
	sd a0, 392(a3)
	ld a0, 400(a1)
	sd a0, 400(a3)
	ld a0, 408(a1)
	sd a0, 408(a3)
	ld a0, 416(a1)
	sd a0, 416(a3)
	ld a0, 424(a1)
	sd a0, 424(a3)
	ld a0, 432(a1)
	sd a0, 432(a3)
	ld a0, 440(a1)
	sd a0, 440(a3)
	ld a0, 448(a1)
	sd a0, 448(a3)
	ld a0, 456(a1)
	sd a0, 456(a3)
	ld a0, 464(a1)
	sd a0, 464(a3)
	ld a0, 472(a1)
	sd a0, 472(a3)
	ld a0, 480(a1)
	sd a0, 480(a3)
	ld a0, 488(a1)
	sd a0, 488(a3)
	ld a0, 496(a1)
	sd a0, 496(a3)
	ld a0, 504(a1)
	sd a0, 504(a3)
	ld a0, 512(a1)
	sd a0, 512(a3)
	ld a0, 520(a1)
	sd a0, 520(a3)
	ld a0, 528(a1)
	sd a0, 528(a3)
	ld a0, 536(a1)
	sd a0, 536(a3)
	ld a0, 544(a1)
	sd a0, 544(a3)
	ld a0, 552(a1)
	sd a0, 552(a3)
	ld a0, 560(a1)
	sd a0, 560(a3)
	ld a0, 568(a1)
	sd a0, 568(a3)
	ld a0, 576(a1)
	sd a0, 576(a3)
	ld a0, 584(a1)
	sd a0, 584(a3)
	ld a0, 592(a1)
	sd a0, 592(a3)
	ld a0, 600(a1)
	sd a0, 600(a3)
	ld a0, 608(a1)
	sd a0, 608(a3)
	ld a0, 616(a1)
	sd a0, 616(a3)
	ld a0, 624(a1)
	sd a0, 624(a3)
	ld a0, 632(a1)
	sd a0, 632(a3)
	ld a0, 640(a1)
	sd a0, 640(a3)
	ld a0, 648(a1)
	sd a0, 648(a3)
	ld a0, 656(a1)
	sd a0, 656(a3)
	ld a0, 664(a1)
	sd a0, 664(a3)
	ld a0, 672(a1)
	sd a0, 672(a3)
	ld a0, 680(a1)
	sd a0, 680(a3)
	ld a0, 688(a1)
	sd a0, 688(a3)
	ld a0, 696(a1)
	sd a0, 696(a3)
	ld a0, 704(a1)
	sd a0, 704(a3)
	ld a0, 712(a1)
	sd a0, 712(a3)
	ld a0, 720(a1)
	sd a0, 720(a3)
	ld a0, 728(a1)
	sd a0, 728(a3)
	ld a0, 736(a1)
	sd a0, 736(a3)
	ld a0, 744(a1)
	sd a0, 744(a3)
	ld a0, 752(a1)
	sd a0, 752(a3)
	ld a0, 760(a1)
	sd a0, 760(a3)
	ld a0, 768(a1)
	sd a0, 768(a3)
	ld a0, 776(a1)
	sd a0, 776(a3)
	ld a0, 784(a1)
	sd a0, 784(a3)
	ld a0, 792(a1)
	sd a0, 792(a3)
	ld a0, 800(a1)
	sd a0, 800(a3)
	ld a0, 808(a1)
	sd a0, 808(a3)
	ld a0, 816(a1)
	sd a0, 816(a3)
	ld a0, 824(a1)
	sd a0, 824(a3)
	ld a0, 832(a1)
	sd a0, 832(a3)
	ld a0, 840(a1)
	sd a0, 840(a3)
	ld a0, 848(a1)
	sd a0, 848(a3)
	ld a0, 856(a1)
	sd a0, 856(a3)
	ld a0, 864(a1)
	sd a0, 864(a3)
	ld a0, 872(a1)
	sd a0, 872(a3)
	ld a0, 880(a1)
	sd a0, 880(a3)
	ld a0, 888(a1)
	sd a0, 888(a3)
	ld a0, 896(a1)
	sd a0, 896(a3)
	ld a0, 904(a1)
	sd a0, 904(a3)
	ld a0, 912(a1)
	sd a0, 912(a3)
	ld a0, 920(a1)
	sd a0, 920(a3)
	ld a0, 928(a1)
	sd a0, 928(a3)
	ld a0, 936(a1)
	sd a0, 936(a3)
	ld a0, 944(a1)
	sd a0, 944(a3)
	ld a0, 952(a1)
	sd a0, 952(a3)
	ld a0, 960(a1)
	sd a0, 960(a3)
	ld a0, 968(a1)
	sd a0, 968(a3)
	ld a0, 976(a1)
	sd a0, 976(a3)
	ld a0, 984(a1)
	sd a0, 984(a3)
	ld a0, 992(a1)
	sd a0, 992(a3)
	ld a0, 1000(a1)
	sd a0, 1000(a3)
	ld a0, 1008(a1)
	sd a0, 1008(a3)
	ld a0, 1016(a1)
	sd a0, 1016(a3)
227:
	ld a0, 208(s3)
	addi a0, a0, 1
	sd a0, 208(s3)
	ld a1, 240(s3)
	sub a1, a0, a1
	bnez a1, 29b
	j 28f
27:
28:
	ld a0, 192(s3)
	addi a0, a0, 1
	sd a0, 192(s3)
	lwu a1, 176(s3)
	sub a1, a0, a1
	bnez a1, 24b
	ld a0, 200(s3)
	addi a0, a0, 1
	sd a0, 200(s3)
	addi a1, a0, -4
	bnez a1, 23b
	ld a0, 184(s3)
	addi a0, a0, 1
	sd a0, 184(s3)
	lwu a1, 160(s3)
	sub a1, a0, a1
	bnez a1, 22b
	ld a3, 360(s3)
	addi a0, zero, 0
	sd a0, 0(a3)
	sd a0, 8(a3)
	sd a0, 16(a3)
	sd a0, 24(a3)
	sd a0, 32(a3)
	sd a0, 40(a3)
	sd a0, 48(a3)
	sd a0, 56(a3)
	sd a0, 64(a3)
	sd a0, 72(a3)
	sd a0, 80(a3)
	sd a0, 88(a3)
	sd a0, 96(a3)
	sd a0, 104(a3)
	sd a0, 112(a3)
	sd a0, 120(a3)
	sd a0, 128(a3)
	sd a0, 136(a3)
	sd a0, 144(a3)
	sd a0, 152(a3)
	sd a0, 160(a3)
	sd a0, 168(a3)
	sd a0, 176(a3)
	sd a0, 184(a3)
	sd a0, 192(a3)
	sd a0, 200(a3)
	sd a0, 208(a3)
	sd a0, 216(a3)
	sd a0, 224(a3)
	sd a0, 232(a3)
	sd a0, 240(a3)
	sd a0, 248(a3)
	sd a0, 256(a3)
	sd a0, 264(a3)
	sd a0, 272(a3)
	sd a0, 280(a3)
	sd a0, 288(a3)
	sd a0, 296(a3)
	sd a0, 304(a3)
	sd a0, 312(a3)
	sd a0, 320(a3)
	sd a0, 328(a3)
	sd a0, 336(a3)
	sd a0, 344(a3)
	sd a0, 352(a3)
	sd a0, 360(a3)
	sd a0, 368(a3)
	sd a0, 376(a3)
	sd a0, 384(a3)
	sd a0, 392(a3)
	sd a0, 400(a3)
	sd a0, 408(a3)
	sd a0, 416(a3)
	sd a0, 424(a3)
	sd a0, 432(a3)
	sd a0, 440(a3)
	sd a0, 448(a3)
	sd a0, 456(a3)
	sd a0, 464(a3)
	sd a0, 472(a3)
	sd a0, 480(a3)
	sd a0, 488(a3)
	sd a0, 496(a3)
	sd a0, 504(a3)
	sd a0, 512(a3)
	sd a0, 520(a3)
	sd a0, 528(a3)
	sd a0, 536(a3)
	sd a0, 544(a3)
	sd a0, 552(a3)
	sd a0, 560(a3)
	sd a0, 568(a3)
	sd a0, 576(a3)
	sd a0, 584(a3)
	sd a0, 592(a3)
	sd a0, 600(a3)
	sd a0, 608(a3)
	sd a0, 616(a3)
	sd a0, 624(a3)
	sd a0, 632(a3)
	sd a0, 640(a3)
	sd a0, 648(a3)
	sd a0, 656(a3)
	sd a0, 664(a3)
	sd a0, 672(a3)
	sd a0, 680(a3)
	sd a0, 688(a3)
	sd a0, 696(a3)
	sd a0, 704(a3)
	sd a0, 712(a3)
	sd a0, 720(a3)
	sd a0, 728(a3)
	sd a0, 736(a3)
	sd a0, 744(a3)
	sd a0, 752(a3)
	sd a0, 760(a3)
	sd a0, 768(a3)
	sd a0, 776(a3)
	sd a0, 784(a3)
	sd a0, 792(a3)
	sd a0, 800(a3)
	sd a0, 808(a3)
	sd a0, 816(a3)
	sd a0, 824(a3)
	sd a0, 832(a3)
	sd a0, 840(a3)
	sd a0, 848(a3)
	sd a0, 856(a3)
	sd a0, 864(a3)
	sd a0, 872(a3)
	sd a0, 880(a3)
	sd a0, 888(a3)
	sd a0, 896(a3)
	sd a0, 904(a3)
	sd a0, 912(a3)
	sd a0, 920(a3)
	sd a0, 928(a3)
	sd a0, 936(a3)
	sd a0, 944(a3)
	sd a0, 952(a3)
	sd a0, 960(a3)
	sd a0, 968(a3)
	sd a0, 976(a3)
	sd a0, 984(a3)
	sd a0, 992(a3)
	sd a0, 1000(a3)
	sd a0, 1008(a3)
	sd a0, 1016(a3)
	addi a0, zero, 0
	sd a0, 192(s3)
228:
	ld a0, 192(s3)
	ld a1, 224(s3)
	addi a1, a1, -1
	ld a2, 224(s3)
	mul a0, a0, a2
	add a0, a0, a1
	slli a0, a0, 10
	ld a2, 360(s3)
	add a0, a2, a0
	addi a1, a0, 0
	ld a3, 360(s3)
	ld a0, 0(a1)
	ld a2, 0(a3)
	xor a0, a0, a2
	sd a0, 0(a3)
	ld a0, 8(a1)
	ld a2, 8(a3)
	xor a0, a0, a2
	sd a0, 8(a3)
	ld a0, 16(a1)
	ld a2, 16(a3)
	xor a0, a0, a2
	sd a0, 16(a3)
	ld a0, 24(a1)
	ld a2, 24(a3)
	xor a0, a0, a2
	sd a0, 24(a3)
	ld a0, 32(a1)
	ld a2, 32(a3)
	xor a0, a0, a2
	sd a0, 32(a3)
	ld a0, 40(a1)
	ld a2, 40(a3)
	xor a0, a0, a2
	sd a0, 40(a3)
	ld a0, 48(a1)
	ld a2, 48(a3)
	xor a0, a0, a2
	sd a0, 48(a3)
	ld a0, 56(a1)
	ld a2, 56(a3)
	xor a0, a0, a2
	sd a0, 56(a3)
	ld a0, 64(a1)
	ld a2, 64(a3)
	xor a0, a0, a2
	sd a0, 64(a3)
	ld a0, 72(a1)
	ld a2, 72(a3)
	xor a0, a0, a2
	sd a0, 72(a3)
	ld a0, 80(a1)
	ld a2, 80(a3)
	xor a0, a0, a2
	sd a0, 80(a3)
	ld a0, 88(a1)
	ld a2, 88(a3)
	xor a0, a0, a2
	sd a0, 88(a3)
	ld a0, 96(a1)
	ld a2, 96(a3)
	xor a0, a0, a2
	sd a0, 96(a3)
	ld a0, 104(a1)
	ld a2, 104(a3)
	xor a0, a0, a2
	sd a0, 104(a3)
	ld a0, 112(a1)
	ld a2, 112(a3)
	xor a0, a0, a2
	sd a0, 112(a3)
	ld a0, 120(a1)
	ld a2, 120(a3)
	xor a0, a0, a2
	sd a0, 120(a3)
	ld a0, 128(a1)
	ld a2, 128(a3)
	xor a0, a0, a2
	sd a0, 128(a3)
	ld a0, 136(a1)
	ld a2, 136(a3)
	xor a0, a0, a2
	sd a0, 136(a3)
	ld a0, 144(a1)
	ld a2, 144(a3)
	xor a0, a0, a2
	sd a0, 144(a3)
	ld a0, 152(a1)
	ld a2, 152(a3)
	xor a0, a0, a2
	sd a0, 152(a3)
	ld a0, 160(a1)
	ld a2, 160(a3)
	xor a0, a0, a2
	sd a0, 160(a3)
	ld a0, 168(a1)
	ld a2, 168(a3)
	xor a0, a0, a2
	sd a0, 168(a3)
	ld a0, 176(a1)
	ld a2, 176(a3)
	xor a0, a0, a2
	sd a0, 176(a3)
	ld a0, 184(a1)
	ld a2, 184(a3)
	xor a0, a0, a2
	sd a0, 184(a3)
	ld a0, 192(a1)
	ld a2, 192(a3)
	xor a0, a0, a2
	sd a0, 192(a3)
	ld a0, 200(a1)
	ld a2, 200(a3)
	xor a0, a0, a2
	sd a0, 200(a3)
	ld a0, 208(a1)
	ld a2, 208(a3)
	xor a0, a0, a2
	sd a0, 208(a3)
	ld a0, 216(a1)
	ld a2, 216(a3)
	xor a0, a0, a2
	sd a0, 216(a3)
	ld a0, 224(a1)
	ld a2, 224(a3)
	xor a0, a0, a2
	sd a0, 224(a3)
	ld a0, 232(a1)
	ld a2, 232(a3)
	xor a0, a0, a2
	sd a0, 232(a3)
	ld a0, 240(a1)
	ld a2, 240(a3)
	xor a0, a0, a2
	sd a0, 240(a3)
	ld a0, 248(a1)
	ld a2, 248(a3)
	xor a0, a0, a2
	sd a0, 248(a3)
	ld a0, 256(a1)
	ld a2, 256(a3)
	xor a0, a0, a2
	sd a0, 256(a3)
	ld a0, 264(a1)
	ld a2, 264(a3)
	xor a0, a0, a2
	sd a0, 264(a3)
	ld a0, 272(a1)
	ld a2, 272(a3)
	xor a0, a0, a2
	sd a0, 272(a3)
	ld a0, 280(a1)
	ld a2, 280(a3)
	xor a0, a0, a2
	sd a0, 280(a3)
	ld a0, 288(a1)
	ld a2, 288(a3)
	xor a0, a0, a2
	sd a0, 288(a3)
	ld a0, 296(a1)
	ld a2, 296(a3)
	xor a0, a0, a2
	sd a0, 296(a3)
	ld a0, 304(a1)
	ld a2, 304(a3)
	xor a0, a0, a2
	sd a0, 304(a3)
	ld a0, 312(a1)
	ld a2, 312(a3)
	xor a0, a0, a2
	sd a0, 312(a3)
	ld a0, 320(a1)
	ld a2, 320(a3)
	xor a0, a0, a2
	sd a0, 320(a3)
	ld a0, 328(a1)
	ld a2, 328(a3)
	xor a0, a0, a2
	sd a0, 328(a3)
	ld a0, 336(a1)
	ld a2, 336(a3)
	xor a0, a0, a2
	sd a0, 336(a3)
	ld a0, 344(a1)
	ld a2, 344(a3)
	xor a0, a0, a2
	sd a0, 344(a3)
	ld a0, 352(a1)
	ld a2, 352(a3)
	xor a0, a0, a2
	sd a0, 352(a3)
	ld a0, 360(a1)
	ld a2, 360(a3)
	xor a0, a0, a2
	sd a0, 360(a3)
	ld a0, 368(a1)
	ld a2, 368(a3)
	xor a0, a0, a2
	sd a0, 368(a3)
	ld a0, 376(a1)
	ld a2, 376(a3)
	xor a0, a0, a2
	sd a0, 376(a3)
	ld a0, 384(a1)
	ld a2, 384(a3)
	xor a0, a0, a2
	sd a0, 384(a3)
	ld a0, 392(a1)
	ld a2, 392(a3)
	xor a0, a0, a2
	sd a0, 392(a3)
	ld a0, 400(a1)
	ld a2, 400(a3)
	xor a0, a0, a2
	sd a0, 400(a3)
	ld a0, 408(a1)
	ld a2, 408(a3)
	xor a0, a0, a2
	sd a0, 408(a3)
	ld a0, 416(a1)
	ld a2, 416(a3)
	xor a0, a0, a2
	sd a0, 416(a3)
	ld a0, 424(a1)
	ld a2, 424(a3)
	xor a0, a0, a2
	sd a0, 424(a3)
	ld a0, 432(a1)
	ld a2, 432(a3)
	xor a0, a0, a2
	sd a0, 432(a3)
	ld a0, 440(a1)
	ld a2, 440(a3)
	xor a0, a0, a2
	sd a0, 440(a3)
	ld a0, 448(a1)
	ld a2, 448(a3)
	xor a0, a0, a2
	sd a0, 448(a3)
	ld a0, 456(a1)
	ld a2, 456(a3)
	xor a0, a0, a2
	sd a0, 456(a3)
	ld a0, 464(a1)
	ld a2, 464(a3)
	xor a0, a0, a2
	sd a0, 464(a3)
	ld a0, 472(a1)
	ld a2, 472(a3)
	xor a0, a0, a2
	sd a0, 472(a3)
	ld a0, 480(a1)
	ld a2, 480(a3)
	xor a0, a0, a2
	sd a0, 480(a3)
	ld a0, 488(a1)
	ld a2, 488(a3)
	xor a0, a0, a2
	sd a0, 488(a3)
	ld a0, 496(a1)
	ld a2, 496(a3)
	xor a0, a0, a2
	sd a0, 496(a3)
	ld a0, 504(a1)
	ld a2, 504(a3)
	xor a0, a0, a2
	sd a0, 504(a3)
	ld a0, 512(a1)
	ld a2, 512(a3)
	xor a0, a0, a2
	sd a0, 512(a3)
	ld a0, 520(a1)
	ld a2, 520(a3)
	xor a0, a0, a2
	sd a0, 520(a3)
	ld a0, 528(a1)
	ld a2, 528(a3)
	xor a0, a0, a2
	sd a0, 528(a3)
	ld a0, 536(a1)
	ld a2, 536(a3)
	xor a0, a0, a2
	sd a0, 536(a3)
	ld a0, 544(a1)
	ld a2, 544(a3)
	xor a0, a0, a2
	sd a0, 544(a3)
	ld a0, 552(a1)
	ld a2, 552(a3)
	xor a0, a0, a2
	sd a0, 552(a3)
	ld a0, 560(a1)
	ld a2, 560(a3)
	xor a0, a0, a2
	sd a0, 560(a3)
	ld a0, 568(a1)
	ld a2, 568(a3)
	xor a0, a0, a2
	sd a0, 568(a3)
	ld a0, 576(a1)
	ld a2, 576(a3)
	xor a0, a0, a2
	sd a0, 576(a3)
	ld a0, 584(a1)
	ld a2, 584(a3)
	xor a0, a0, a2
	sd a0, 584(a3)
	ld a0, 592(a1)
	ld a2, 592(a3)
	xor a0, a0, a2
	sd a0, 592(a3)
	ld a0, 600(a1)
	ld a2, 600(a3)
	xor a0, a0, a2
	sd a0, 600(a3)
	ld a0, 608(a1)
	ld a2, 608(a3)
	xor a0, a0, a2
	sd a0, 608(a3)
	ld a0, 616(a1)
	ld a2, 616(a3)
	xor a0, a0, a2
	sd a0, 616(a3)
	ld a0, 624(a1)
	ld a2, 624(a3)
	xor a0, a0, a2
	sd a0, 624(a3)
	ld a0, 632(a1)
	ld a2, 632(a3)
	xor a0, a0, a2
	sd a0, 632(a3)
	ld a0, 640(a1)
	ld a2, 640(a3)
	xor a0, a0, a2
	sd a0, 640(a3)
	ld a0, 648(a1)
	ld a2, 648(a3)
	xor a0, a0, a2
	sd a0, 648(a3)
	ld a0, 656(a1)
	ld a2, 656(a3)
	xor a0, a0, a2
	sd a0, 656(a3)
	ld a0, 664(a1)
	ld a2, 664(a3)
	xor a0, a0, a2
	sd a0, 664(a3)
	ld a0, 672(a1)
	ld a2, 672(a3)
	xor a0, a0, a2
	sd a0, 672(a3)
	ld a0, 680(a1)
	ld a2, 680(a3)
	xor a0, a0, a2
	sd a0, 680(a3)
	ld a0, 688(a1)
	ld a2, 688(a3)
	xor a0, a0, a2
	sd a0, 688(a3)
	ld a0, 696(a1)
	ld a2, 696(a3)
	xor a0, a0, a2
	sd a0, 696(a3)
	ld a0, 704(a1)
	ld a2, 704(a3)
	xor a0, a0, a2
	sd a0, 704(a3)
	ld a0, 712(a1)
	ld a2, 712(a3)
	xor a0, a0, a2
	sd a0, 712(a3)
	ld a0, 720(a1)
	ld a2, 720(a3)
	xor a0, a0, a2
	sd a0, 720(a3)
	ld a0, 728(a1)
	ld a2, 728(a3)
	xor a0, a0, a2
	sd a0, 728(a3)
	ld a0, 736(a1)
	ld a2, 736(a3)
	xor a0, a0, a2
	sd a0, 736(a3)
	ld a0, 744(a1)
	ld a2, 744(a3)
	xor a0, a0, a2
	sd a0, 744(a3)
	ld a0, 752(a1)
	ld a2, 752(a3)
	xor a0, a0, a2
	sd a0, 752(a3)
	ld a0, 760(a1)
	ld a2, 760(a3)
	xor a0, a0, a2
	sd a0, 760(a3)
	ld a0, 768(a1)
	ld a2, 768(a3)
	xor a0, a0, a2
	sd a0, 768(a3)
	ld a0, 776(a1)
	ld a2, 776(a3)
	xor a0, a0, a2
	sd a0, 776(a3)
	ld a0, 784(a1)
	ld a2, 784(a3)
	xor a0, a0, a2
	sd a0, 784(a3)
	ld a0, 792(a1)
	ld a2, 792(a3)
	xor a0, a0, a2
	sd a0, 792(a3)
	ld a0, 800(a1)
	ld a2, 800(a3)
	xor a0, a0, a2
	sd a0, 800(a3)
	ld a0, 808(a1)
	ld a2, 808(a3)
	xor a0, a0, a2
	sd a0, 808(a3)
	ld a0, 816(a1)
	ld a2, 816(a3)
	xor a0, a0, a2
	sd a0, 816(a3)
	ld a0, 824(a1)
	ld a2, 824(a3)
	xor a0, a0, a2
	sd a0, 824(a3)
	ld a0, 832(a1)
	ld a2, 832(a3)
	xor a0, a0, a2
	sd a0, 832(a3)
	ld a0, 840(a1)
	ld a2, 840(a3)
	xor a0, a0, a2
	sd a0, 840(a3)
	ld a0, 848(a1)
	ld a2, 848(a3)
	xor a0, a0, a2
	sd a0, 848(a3)
	ld a0, 856(a1)
	ld a2, 856(a3)
	xor a0, a0, a2
	sd a0, 856(a3)
	ld a0, 864(a1)
	ld a2, 864(a3)
	xor a0, a0, a2
	sd a0, 864(a3)
	ld a0, 872(a1)
	ld a2, 872(a3)
	xor a0, a0, a2
	sd a0, 872(a3)
	ld a0, 880(a1)
	ld a2, 880(a3)
	xor a0, a0, a2
	sd a0, 880(a3)
	ld a0, 888(a1)
	ld a2, 888(a3)
	xor a0, a0, a2
	sd a0, 888(a3)
	ld a0, 896(a1)
	ld a2, 896(a3)
	xor a0, a0, a2
	sd a0, 896(a3)
	ld a0, 904(a1)
	ld a2, 904(a3)
	xor a0, a0, a2
	sd a0, 904(a3)
	ld a0, 912(a1)
	ld a2, 912(a3)
	xor a0, a0, a2
	sd a0, 912(a3)
	ld a0, 920(a1)
	ld a2, 920(a3)
	xor a0, a0, a2
	sd a0, 920(a3)
	ld a0, 928(a1)
	ld a2, 928(a3)
	xor a0, a0, a2
	sd a0, 928(a3)
	ld a0, 936(a1)
	ld a2, 936(a3)
	xor a0, a0, a2
	sd a0, 936(a3)
	ld a0, 944(a1)
	ld a2, 944(a3)
	xor a0, a0, a2
	sd a0, 944(a3)
	ld a0, 952(a1)
	ld a2, 952(a3)
	xor a0, a0, a2
	sd a0, 952(a3)
	ld a0, 960(a1)
	ld a2, 960(a3)
	xor a0, a0, a2
	sd a0, 960(a3)
	ld a0, 968(a1)
	ld a2, 968(a3)
	xor a0, a0, a2
	sd a0, 968(a3)
	ld a0, 976(a1)
	ld a2, 976(a3)
	xor a0, a0, a2
	sd a0, 976(a3)
	ld a0, 984(a1)
	ld a2, 984(a3)
	xor a0, a0, a2
	sd a0, 984(a3)
	ld a0, 992(a1)
	ld a2, 992(a3)
	xor a0, a0, a2
	sd a0, 992(a3)
	ld a0, 1000(a1)
	ld a2, 1000(a3)
	xor a0, a0, a2
	sd a0, 1000(a3)
	ld a0, 1008(a1)
	ld a2, 1008(a3)
	xor a0, a0, a2
	sd a0, 1008(a3)
	ld a0, 1016(a1)
	ld a2, 1016(a3)
	xor a0, a0, a2
	sd a0, 1016(a3)
	ld a0, 192(s3)
	addi a0, a0, 1
	sd a0, 192(s3)
	lwu a1, 176(s3)
	sub a1, a0, a1
	bnez a1, 228b
	ld a0, 360(s3)
	addi a1, zero, 1024
	ld a2, 384(s3)
	ld a3, 392(s3)
	addi a4, s4, 0
	call {vg_argon2_hprime}
	ld ra, 72(s3)
	ld s0, 80(s3)
	ld s1, 88(s3)
	ld s2, 96(s3)
	ld s4, 112(s3)
	ld s3, 104(s3)
	addi sp, sp, 320
	ret
	.option pop
