// The functions of `src/ecdsa_p224.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_p224_verify:
	.option push
	.option arch, +m, +c
	sd s0, 0(a3)
	sd s1, 8(a3)
	sd s2, 16(a3)
	sd ra, 24(a3)
	sd s3, 32(a3)
	addi s0, a3, 0
	addi s3, a3, 0
	addi s2, a0, 0
	lbu t0, 1(a0)
	slli t0, t0, 24
	lbu t1, 2(a0)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 3(a0)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 4(a0)
	or t0, t0, t1
	sd t0, 1144(s0)
	lbu t0, 5(a0)
	slli t0, t0, 8
	lbu t1, 6(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 7(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 8(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 9(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 10(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 11(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 12(a0)
	or t0, t0, t1
	sd t0, 1136(s0)
	lbu t0, 13(a0)
	slli t0, t0, 8
	lbu t1, 14(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 15(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 16(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 17(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 18(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 19(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 20(a0)
	or t0, t0, t1
	sd t0, 1128(s0)
	lbu t0, 21(a0)
	slli t0, t0, 8
	lbu t1, 22(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 23(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 24(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 25(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 26(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 27(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 28(a0)
	or t0, t0, t1
	sd t0, 1120(s0)
	lbu t0, 29(a0)
	slli t0, t0, 24
	lbu t1, 30(a0)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 31(a0)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 32(a0)
	or t0, t0, t1
	sd t0, 1240(s0)
	lbu t0, 33(a0)
	slli t0, t0, 8
	lbu t1, 34(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 35(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 36(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 37(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 38(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 39(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 40(a0)
	or t0, t0, t1
	sd t0, 1232(s0)
	lbu t0, 41(a0)
	slli t0, t0, 8
	lbu t1, 42(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 43(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 44(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 45(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 46(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 47(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 48(a0)
	or t0, t0, t1
	sd t0, 1224(s0)
	lbu t0, 49(a0)
	slli t0, t0, 8
	lbu t1, 50(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 51(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 52(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 53(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 54(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 55(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 56(a0)
	or t0, t0, t1
	sd t0, 1216(s0)
	lbu t0, 0(a0)
	xori t0, t0, 4
	addi t0, t0, -1
	srli t0, t0, 63
	addi t1, zero, 0
	sub a7, t1, t0
	sd a7, 1472(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 1
	add t0, t0, t1
	sd t0, 64(s0)
	lui t0, 0
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 72(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 80(s0)
	lui t0, 0
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 88(s0)
	lui t0, 81363
	addiw t0, t0, -1723
	slli t0, t0, 32
	lui t1, 378307
	addiw t1, t1, -1475
	add t0, t0, t1
	sd t0, 96(s0)
	lui t0, 1048561
	addiw t0, t0, 1699
	slli t0, t0, 32
	lui t1, 920463
	addiw t1, t1, 62
	add t0, t0, t1
	sd t0, 104(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 112(s0)
	lui t0, 0
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 120(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 160(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 168(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 176(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 184(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 1
	add t0, t0, t1
	sd t0, 192(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 200(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 208(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 216(s0)
	lui t0, 0
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 224(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 232(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 240(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 248(s0)
	lui t0, 0
	addiw t0, t0, 3
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 1
	add t0, t0, t1
	sd t0, 256(s0)
	lui t0, 0
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 264(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -4
	add t0, t0, t1
	sd t0, 272(s0)
	lui t0, 0
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 280(s0)
	lui t0, 746407
	addiw t0, t0, -1565
	slli t0, t0, 32
	lui t1, 177169
	addiw t1, t1, -666
	add t0, t0, t1
	sd t0, 288(s0)
	lui t0, 202501
	addiw t0, t0, -1828
	slli t0, t0, 32
	lui t1, 421124
	addiw t1, t1, -1742
	add t0, t0, t1
	sd t0, 296(s0)
	lui t0, 759491
	addiw t0, t0, -54
	slli t0, t0, 32
	lui t1, 364408
	addiw t1, t1, 1011
	add t0, t0, t1
	sd t0, 304(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 521225
	addiw t1, t1, -327
	add t0, t0, t1
	sd t0, 312(s0)
	lui t0, 772357
	addiw t0, t0, 550
	slli t0, t0, 32
	lui t1, 446629
	addiw t1, t1, -1302
	add t0, t0, t1
	sd t0, 320(s0)
	lui t0, 545369
	addiw t0, t0, 1846
	slli t0, t0, 32
	lui t1, 393612
	addiw t1, t1, -86
	add t0, t0, t1
	sd t0, 328(s0)
	lui t0, 449851
	addiw t0, t0, -100
	slli t0, t0, 32
	lui t1, 1021631
	addiw t1, t1, -1019
	add t0, t0, t1
	sd t0, 336(s0)
	lui t0, 0
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 663990
	addiw t1, t1, -416
	add t0, t0, t1
	sd t0, 344(s0)
	lui t0, 191946
	addiw t0, t0, 486
	slli t0, t0, 32
	lui t1, 982847
	addiw t1, t1, -536
	add t0, t0, t1
	sd t0, 352(s0)
	lui t0, 1019094
	addiw t0, t0, 1835
	slli t0, t0, 32
	lui t1, 21302
	addiw t1, t1, -1429
	add t0, t0, t1
	sd t0, 360(s0)
	lui t0, 715420
	addiw t0, t0, 1454
	slli t0, t0, 32
	lui t1, 15871
	addiw t1, t1, -1928
	add t0, t0, t1
	sd t0, 368(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 398456
	addiw t1, t1, 1777
	add t0, t0, t1
	sd t0, 376(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 448(s0)
	lui t0, 0
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 456(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 464(s0)
	lui t0, 0
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 472(s0)
	lui t0, 0
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 1
	add t0, t0, t1
	sd t0, 1312(s0)
	lui t0, 0
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1320(s0)
	lui t0, 0
	addiw t0, t0, -2
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1328(s0)
	lui t0, 0
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 1336(s0)
	lui t0, 947853
	addiw t0, t0, -522
	slli t0, t0, 32
	lui t1, 408582
	addiw t1, t1, -1587
	add t0, t0, t1
	sd t0, 1344(s0)
	lui t0, 67500
	addiw t0, t0, 756
	slli t0, t0, 32
	lui t1, 839425
	addiw t1, t1, 784
	add t0, t0, t1
	sd t0, 1352(s0)
	lui t0, 253164
	addiw t0, t0, -1383
	slli t0, t0, 32
	lui t1, 820520
	addiw t1, t1, 337
	add t0, t0, t1
	sd t0, 1360(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 523267
	addiw t1, t1, -109
	add t0, t0, t1
	sd t0, 1368(s0)
	lbu t0, 0(a2)
	slli t0, t0, 24
	lbu t1, 1(a2)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 2(a2)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 3(a2)
	or t0, t0, t1
	sd t0, 408(s0)
	lbu t0, 4(a2)
	slli t0, t0, 8
	lbu t1, 5(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 6(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 7(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 8(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 9(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 10(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 11(a2)
	or t0, t0, t1
	sd t0, 400(s0)
	lbu t0, 12(a2)
	slli t0, t0, 8
	lbu t1, 13(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 14(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 15(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 16(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 17(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 18(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 19(a2)
	or t0, t0, t1
	sd t0, 392(s0)
	lbu t0, 20(a2)
	slli t0, t0, 8
	lbu t1, 21(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 22(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 23(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 24(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 25(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 26(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 27(a2)
	or t0, t0, t1
	sd t0, 384(s0)
	lbu t0, 28(a2)
	slli t0, t0, 24
	lbu t1, 29(a2)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 30(a2)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 31(a2)
	or t0, t0, t1
	sd t0, 440(s0)
	lbu t0, 32(a2)
	slli t0, t0, 8
	lbu t1, 33(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 34(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 35(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 36(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 37(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 38(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 39(a2)
	or t0, t0, t1
	sd t0, 432(s0)
	lbu t0, 40(a2)
	slli t0, t0, 8
	lbu t1, 41(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 42(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 43(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 44(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 45(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 46(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 47(a2)
	or t0, t0, t1
	sd t0, 424(s0)
	lbu t0, 48(a2)
	slli t0, t0, 8
	lbu t1, 49(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 50(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 51(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 52(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 53(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 54(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 55(a2)
	or t0, t0, t1
	sd t0, 416(s0)
	lbu t0, 0(a1)
	slli t0, t0, 24
	lbu t1, 1(a1)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 2(a1)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 3(a1)
	or t0, t0, t1
	sd t0, 1112(s0)
	lbu t0, 4(a1)
	slli t0, t0, 8
	lbu t1, 5(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 6(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 7(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 8(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 9(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 10(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 11(a1)
	or t0, t0, t1
	sd t0, 1104(s0)
	lbu t0, 12(a1)
	slli t0, t0, 8
	lbu t1, 13(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 14(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 15(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 16(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 17(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 18(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 19(a1)
	or t0, t0, t1
	sd t0, 1096(s0)
	lbu t0, 20(a1)
	slli t0, t0, 8
	lbu t1, 21(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 22(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 23(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 24(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 25(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 26(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 27(a1)
	or t0, t0, t1
	sd t0, 1088(s0)
	addi t5, zero, 0
	ld t3, 384(s0)
	ld t4, 96(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 392(s0)
	ld t4, 104(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 400(s0)
	ld t4, 112(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 408(s0)
	ld t4, 120(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t6, zero, 0
	sub a7, t6, t5
	ld t0, 1472(s0)
	and t0, t0, a7
	sd t0, 1472(s0)
	addi t3, zero, 0
	ld t4, 384(s0)
	or t3, t3, t4
	ld t4, 392(s0)
	or t3, t3, t4
	ld t4, 400(s0)
	or t3, t3, t4
	ld t4, 408(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	xori a7, a7, -1
	ld t0, 1472(s0)
	and t0, t0, a7
	sd t0, 1472(s0)
	addi t5, zero, 0
	ld t3, 416(s0)
	ld t4, 96(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 424(s0)
	ld t4, 104(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 432(s0)
	ld t4, 112(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 440(s0)
	ld t4, 120(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t6, zero, 0
	sub a7, t6, t5
	ld t0, 1472(s0)
	and t0, t0, a7
	sd t0, 1472(s0)
	addi t3, zero, 0
	ld t4, 416(s0)
	or t3, t3, t4
	ld t4, 424(s0)
	or t3, t3, t4
	ld t4, 432(s0)
	or t3, t3, t4
	ld t4, 440(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	xori a7, a7, -1
	ld t0, 1472(s0)
	and t0, t0, a7
	sd t0, 1472(s0)
	addi a0, s0, 0
	call {vg_p224_check_point}
	addi s0, s3, 0
	lui t0, 170312
	addiw t0, t0, -1431
	slli t0, t0, 32
	lui t1, 390424
	addiw t1, t1, -747
	add t0, t0, t1
	sd t0, 1184(s0)
	lui t0, 703632
	addiw t0, t0, -167
	slli t0, t0, 32
	lui t1, 204132
	addiw t1, t1, -181
	add t0, t0, t1
	sd t0, 1192(s0)
	lui t0, 437526
	addiw t0, t0, -131
	slli t0, t0, 32
	lui t1, 890645
	addiw t1, t1, -1962
	add t0, t0, t1
	sd t0, 1200(s0)
	lui t0, 0
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 728728
	addiw t1, t1, -1695
	add t0, t0, t1
	sd t0, 1208(s0)
	lui t0, 670269
	addiw t0, t0, 1475
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1216(s0)
	lui t0, 128113
	addiw t0, t0, -62
	slli t0, t0, 32
	lui t1, 967213
	addiw t1, t1, 1722
	add t0, t0, t1
	sd t0, 1224(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 15
	addiw t1, t1, -1699
	add t0, t0, t1
	sd t0, 1232(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1240(s0)
	lui t0, 81363
	addiw t0, t0, -1723
	slli t0, t0, 32
	lui t1, 378307
	addiw t1, t1, -1477
	add t0, t0, t1
	sd t0, 1248(s0)
	lui t0, 1048561
	addiw t0, t0, 1699
	slli t0, t0, 32
	lui t1, 920463
	addiw t1, t1, 62
	add t0, t0, t1
	sd t0, 1256(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 1264(s0)
	lui t0, 0
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 1272(s0)
	addi a0, s0, 0
	addi a1, zero, 704
	addi a2, zero, 416
	addi a3, zero, 1184
	call {vg_p224_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 704
	addi a3, zero, 1216
	call {vg_p224_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1536
	addi a3, zero, 1536
	call {vg_p224_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1568
	addi a2, zero, 1536
	addi a3, zero, 1792
	call {vg_p224_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1568
	addi a3, zero, 1792
	call {vg_p224_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1632
	addi a2, zero, 1600
	addi a3, zero, 1792
	call {vg_p224_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1632
	addi a3, zero, 1792
	call {vg_p224_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1696
	addi a2, zero, 1664
	addi a3, zero, 1792
	call {vg_p224_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1696
	addi a3, zero, 1792
	call {vg_p224_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1760
	addi a2, zero, 1728
	addi a3, zero, 1792
	call {vg_p224_mul_mod_n}
	ld t0, 1760(s0)
	sd t0, 992(s0)
	ld t0, 1768(s0)
	sd t0, 1000(s0)
	ld t0, 1776(s0)
	sd t0, 1008(s0)
	ld t0, 1784(s0)
	sd t0, 1016(s0)
	addi s1, zero, 4
20:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_n}
	bnez s1, 20b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_n}
	addi s1, zero, 4
21:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_n}
	bnez s1, 21b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_n}
	addi s1, zero, 4
22:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_n}
	bnez s1, 22b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_n}
	addi s1, zero, 4
23:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_n}
	bnez s1, 23b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_n}
	addi s1, zero, 4
24:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_n}
	bnez s1, 24b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_n}
	addi s1, zero, 4
25:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_n}
	bnez s1, 25b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_n}
	addi s1, zero, 4
26:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_n}
	bnez s1, 26b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_n}
	addi s1, zero, 4
27:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_n}
	bnez s1, 27b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_n}
	addi s1, zero, 4
28:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_n}
	bnez s1, 28b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_n}
	addi s1, zero, 4
29:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_n}
	bnez s1, 29b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_n}
	addi s1, zero, 4
210:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_n}
	bnez s1, 210b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_n}
	addi s1, zero, 4
211:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_n}
	bnez s1, 211b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_n}
	addi s1, zero, 4
212:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_n}
	bnez s1, 212b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_n}
	addi s1, zero, 4
213:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_n}
	bnez s1, 213b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_n}
	addi s1, zero, 4
214:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_n}
	bnez s1, 214b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_n}
	addi s1, zero, 4
215:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_n}
	bnez s1, 215b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_n}
	addi s1, zero, 4
216:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_n}
	bnez s1, 216b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_n}
	addi s1, zero, 4
217:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_n}
	bnez s1, 217b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_n}
	addi s1, zero, 4
218:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_n}
	bnez s1, 218b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_n}
	addi s1, zero, 4
219:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_n}
	bnez s1, 219b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_n}
	addi s1, zero, 4
220:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_n}
	bnez s1, 220b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_n}
	addi s1, zero, 4
221:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_n}
	bnez s1, 221b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_n}
	addi s1, zero, 4
222:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_n}
	bnez s1, 222b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_n}
	addi s1, zero, 4
223:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_n}
	bnez s1, 223b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_n}
	addi s1, zero, 4
224:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_n}
	bnez s1, 224b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_n}
	addi s1, zero, 4
225:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_n}
	bnez s1, 225b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_n}
	addi s1, zero, 4
226:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_n}
	bnez s1, 226b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_n}
	addi s1, zero, 7
227:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_n}
	bnez s1, 227b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1696
	call {vg_p224_mul_mod_n}
	addi s1, zero, 4
228:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_n}
	bnez s1, 228b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1600
	call {vg_p224_mul_mod_n}
	addi s1, zero, 7
229:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_n}
	bnez s1, 229b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1696
	call {vg_p224_mul_mod_n}
	addi s1, zero, 1
230:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_n}
	bnez s1, 230b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1536
	call {vg_p224_mul_mod_n}
	addi s1, zero, 9
231:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_n}
	bnez s1, 231b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1696
	call {vg_p224_mul_mod_n}
	addi s1, zero, 1
232:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_n}
	bnez s1, 232b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1536
	call {vg_p224_mul_mod_n}
	addi s1, zero, 7
233:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_n}
	bnez s1, 233b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_n}
	addi s1, zero, 10
234:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_n}
	bnez s1, 234b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_n}
	addi s1, zero, 1
235:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_n}
	bnez s1, 235b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1536
	call {vg_p224_mul_mod_n}
	addi s1, zero, 8
236:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_n}
	bnez s1, 236b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1664
	call {vg_p224_mul_mod_n}
	addi s1, zero, 3
237:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_n}
	bnez s1, 237b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1632
	call {vg_p224_mul_mod_n}
	addi s1, zero, 4
238:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_n}
	bnez s1, 238b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1632
	call {vg_p224_mul_mod_n}
	addi s1, zero, 5
239:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_n}
	bnez s1, 239b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1664
	call {vg_p224_mul_mod_n}
	addi s1, zero, 5
240:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_n}
	bnez s1, 240b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1664
	call {vg_p224_mul_mod_n}
	addi s1, zero, 2
241:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_n}
	bnez s1, 241b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1536
	call {vg_p224_mul_mod_n}
	addi s1, zero, 6
242:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_n}
	bnez s1, 242b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1600
	call {vg_p224_mul_mod_n}
	addi s1, zero, 5
243:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_n}
	bnez s1, 243b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1696
	call {vg_p224_mul_mod_n}
	addi s1, zero, 1
244:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_n}
	bnez s1, 244b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1536
	call {vg_p224_mul_mod_n}
	addi s1, zero, 7
245:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_n}
	bnez s1, 245b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1696
	call {vg_p224_mul_mod_n}
	addi s1, zero, 1
246:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_n}
	bnez s1, 246b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1536
	call {vg_p224_mul_mod_n}
	addi s1, zero, 7
247:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_n}
	bnez s1, 247b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1600
	call {vg_p224_mul_mod_n}
	addi s1, zero, 2
248:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_n}
	bnez s1, 248b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1536
	call {vg_p224_mul_mod_n}
	addi s1, zero, 6
249:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_n}
	bnez s1, 249b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1632
	call {vg_p224_mul_mod_n}
	addi s1, zero, 3
250:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_n}
	bnez s1, 250b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1568
	call {vg_p224_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 736
	addi a2, zero, 1088
	addi a3, zero, 1184
	call {vg_p224_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 768
	addi a2, zero, 736
	addi a3, zero, 992
	call {vg_p224_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 768
	addi a3, zero, 192
	call {vg_p224_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 768
	addi a2, zero, 384
	addi a3, zero, 1184
	call {vg_p224_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 832
	addi a2, zero, 768
	addi a3, zero, 992
	call {vg_p224_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 832
	addi a3, zero, 192
	call {vg_p224_mul_mod_n}
	ld t0, 1216(s0)
	sd t0, 1056(s0)
	ld t0, 1224(s0)
	sd t0, 1064(s0)
	ld t0, 1232(s0)
	sd t0, 1072(s0)
	ld t0, 1240(s0)
	sd t0, 1080(s0)
	ld t0, 1280(s0)
	sd t0, 512(s0)
	ld t0, 1288(s0)
	sd t0, 520(s0)
	ld t0, 1296(s0)
	sd t0, 528(s0)
	ld t0, 1304(s0)
	sd t0, 536(s0)
	ld t0, 1440(s0)
	sd t0, 544(s0)
	ld t0, 1448(s0)
	sd t0, 552(s0)
	ld t0, 1456(s0)
	sd t0, 560(s0)
	ld t0, 1464(s0)
	sd t0, 568(s0)
	addi a0, s0, 0
	call {vg_p224_mul}
	addi s0, s3, 0
	addi t3, zero, 0
	ld t4, 1216(s0)
	or t3, t3, t4
	ld t4, 1224(s0)
	or t3, t3, t4
	ld t4, 1232(s0)
	or t3, t3, t4
	ld t4, 1240(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	ld t0, 512(s0)
	ld t1, 160(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 512(s0)
	ld t0, 520(s0)
	ld t1, 168(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 520(s0)
	ld t0, 528(s0)
	ld t1, 176(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 528(s0)
	ld t0, 536(s0)
	ld t1, 184(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 536(s0)
	ld t0, 544(s0)
	ld t1, 224(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 544(s0)
	ld t0, 552(s0)
	ld t1, 232(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 552(s0)
	ld t0, 560(s0)
	ld t1, 240(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 560(s0)
	ld t0, 568(s0)
	ld t1, 248(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 568(s0)
	ld t0, 576(s0)
	ld t1, 160(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 576(s0)
	ld t0, 584(s0)
	ld t1, 168(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 584(s0)
	ld t0, 592(s0)
	ld t1, 176(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 592(s0)
	ld t0, 600(s0)
	ld t1, 184(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 600(s0)
	lui t0, 947853
	addiw t0, t0, -522
	slli t0, t0, 32
	lui t1, 408582
	addiw t1, t1, -1587
	add t0, t0, t1
	sd t0, 1344(s0)
	lui t0, 67500
	addiw t0, t0, 756
	slli t0, t0, 32
	lui t1, 839425
	addiw t1, t1, 784
	add t0, t0, t1
	sd t0, 1352(s0)
	lui t0, 253164
	addiw t0, t0, -1383
	slli t0, t0, 32
	lui t1, 820520
	addiw t1, t1, 337
	add t0, t0, t1
	sd t0, 1360(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 523267
	addiw t1, t1, -109
	add t0, t0, t1
	sd t0, 1368(s0)
	ld t0, 512(s0)
	sd t0, 320(s0)
	ld t0, 520(s0)
	sd t0, 328(s0)
	ld t0, 528(s0)
	sd t0, 336(s0)
	ld t0, 536(s0)
	sd t0, 344(s0)
	ld t0, 544(s0)
	sd t0, 1280(s0)
	ld t0, 552(s0)
	sd t0, 1288(s0)
	ld t0, 560(s0)
	sd t0, 1296(s0)
	ld t0, 568(s0)
	sd t0, 1304(s0)
	ld t0, 576(s0)
	sd t0, 1440(s0)
	ld t0, 584(s0)
	sd t0, 1448(s0)
	ld t0, 592(s0)
	sd t0, 1456(s0)
	ld t0, 600(s0)
	sd t0, 1464(s0)
	ld t0, 1120(s0)
	sd t0, 1056(s0)
	ld t0, 1128(s0)
	sd t0, 1064(s0)
	ld t0, 1136(s0)
	sd t0, 1072(s0)
	ld t0, 1144(s0)
	sd t0, 1080(s0)
	addi a0, s0, 0
	call {vg_p224_mul_g}
	addi s0, s3, 0
	addi t3, zero, 0
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
	ld t0, 512(s0)
	ld t1, 160(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 512(s0)
	ld t0, 520(s0)
	ld t1, 168(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 520(s0)
	ld t0, 528(s0)
	ld t1, 176(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 528(s0)
	ld t0, 536(s0)
	ld t1, 184(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 536(s0)
	ld t0, 544(s0)
	ld t1, 224(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 544(s0)
	ld t0, 552(s0)
	ld t1, 232(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 552(s0)
	ld t0, 560(s0)
	ld t1, 240(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 560(s0)
	ld t0, 568(s0)
	ld t1, 248(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 568(s0)
	ld t0, 576(s0)
	ld t1, 160(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 576(s0)
	ld t0, 584(s0)
	ld t1, 168(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 584(s0)
	ld t0, 592(s0)
	ld t1, 176(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 592(s0)
	ld t0, 600(s0)
	ld t1, 184(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 600(s0)
	lui t0, 947853
	addiw t0, t0, -522
	slli t0, t0, 32
	lui t1, 408582
	addiw t1, t1, -1587
	add t0, t0, t1
	sd t0, 1344(s0)
	lui t0, 67500
	addiw t0, t0, 756
	slli t0, t0, 32
	lui t1, 839425
	addiw t1, t1, 784
	add t0, t0, t1
	sd t0, 1352(s0)
	lui t0, 253164
	addiw t0, t0, -1383
	slli t0, t0, 32
	lui t1, 820520
	addiw t1, t1, 337
	add t0, t0, t1
	sd t0, 1360(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 523267
	addiw t1, t1, -109
	add t0, t0, t1
	sd t0, 1368(s0)
	addi a0, s0, 0
	addi a1, zero, 800
	addi a2, zero, 512
	addi a3, zero, 320
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 832
	addi a2, zero, 544
	addi a3, zero, 1280
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 576
	addi a3, zero, 1440
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 896
	addi a2, zero, 512
	addi a3, zero, 544
	call {vg_p224_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 928
	addi a2, zero, 320
	addi a3, zero, 1280
	call {vg_p224_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 896
	addi a2, zero, 896
	addi a3, zero, 928
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 928
	addi a2, zero, 800
	addi a3, zero, 832
	call {vg_p224_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 896
	addi a2, zero, 896
	addi a3, zero, 928
	call {vg_p224_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 928
	addi a2, zero, 544
	addi a3, zero, 576
	call {vg_p224_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 704
	addi a2, zero, 1280
	addi a3, zero, 1440
	call {vg_p224_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 928
	addi a2, zero, 928
	addi a3, zero, 704
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 704
	addi a2, zero, 832
	addi a3, zero, 864
	call {vg_p224_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 928
	addi a2, zero, 928
	addi a3, zero, 704
	call {vg_p224_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 704
	addi a2, zero, 512
	addi a3, zero, 576
	call {vg_p224_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 736
	addi a2, zero, 320
	addi a3, zero, 1440
	call {vg_p224_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 704
	addi a2, zero, 704
	addi a3, zero, 736
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 736
	addi a2, zero, 800
	addi a3, zero, 864
	call {vg_p224_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 736
	addi a2, zero, 704
	addi a3, zero, 736
	call {vg_p224_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 768
	addi a2, zero, 1344
	addi a3, zero, 864
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 704
	addi a2, zero, 736
	addi a3, zero, 768
	call {vg_p224_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 768
	addi a2, zero, 704
	addi a3, zero, 704
	call {vg_p224_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 704
	addi a2, zero, 704
	addi a3, zero, 768
	call {vg_p224_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 768
	addi a2, zero, 832
	addi a3, zero, 704
	call {vg_p224_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 704
	addi a2, zero, 832
	addi a3, zero, 704
	call {vg_p224_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 736
	addi a2, zero, 1344
	addi a3, zero, 736
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 832
	addi a2, zero, 864
	addi a3, zero, 864
	call {vg_p224_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 832
	addi a3, zero, 864
	call {vg_p224_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 736
	addi a2, zero, 736
	addi a3, zero, 864
	call {vg_p224_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 736
	addi a2, zero, 736
	addi a3, zero, 800
	call {vg_p224_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 832
	addi a2, zero, 736
	addi a3, zero, 736
	call {vg_p224_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 736
	addi a2, zero, 832
	addi a3, zero, 736
	call {vg_p224_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 832
	addi a2, zero, 800
	addi a3, zero, 800
	call {vg_p224_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 800
	addi a2, zero, 832
	addi a3, zero, 800
	call {vg_p224_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 800
	addi a2, zero, 800
	addi a3, zero, 864
	call {vg_p224_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 832
	addi a2, zero, 928
	addi a3, zero, 736
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 800
	addi a3, zero, 736
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 736
	addi a2, zero, 704
	addi a3, zero, 768
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 736
	addi a2, zero, 736
	addi a3, zero, 864
	call {vg_p224_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 704
	addi a2, zero, 896
	addi a3, zero, 704
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 704
	addi a2, zero, 704
	addi a3, zero, 832
	call {vg_p224_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 768
	addi a2, zero, 928
	addi a3, zero, 768
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 832
	addi a2, zero, 896
	addi a3, zero, 800
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 768
	addi a2, zero, 768
	addi a3, zero, 832
	call {vg_p224_add_mod_p}
	ld t0, 704(s0)
	sd t0, 512(s0)
	ld t0, 712(s0)
	sd t0, 520(s0)
	ld t0, 720(s0)
	sd t0, 528(s0)
	ld t0, 728(s0)
	sd t0, 536(s0)
	ld t0, 736(s0)
	sd t0, 544(s0)
	ld t0, 744(s0)
	sd t0, 552(s0)
	ld t0, 752(s0)
	sd t0, 560(s0)
	ld t0, 760(s0)
	sd t0, 568(s0)
	ld t0, 768(s0)
	sd t0, 576(s0)
	ld t0, 776(s0)
	sd t0, 584(s0)
	ld t0, 784(s0)
	sd t0, 592(s0)
	ld t0, 792(s0)
	sd t0, 600(s0)
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 576
	addi a3, zero, 224
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1536
	addi a3, zero, 1536
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1568
	addi a2, zero, 1536
	addi a3, zero, 1792
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1568
	addi a3, zero, 1792
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1632
	addi a2, zero, 1600
	addi a3, zero, 1792
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1632
	addi a3, zero, 1792
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1696
	addi a2, zero, 1664
	addi a3, zero, 1792
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1696
	addi a3, zero, 1792
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1760
	addi a2, zero, 1728
	addi a3, zero, 1792
	call {vg_p224_mul_mod_p}
	ld t0, 1760(s0)
	sd t0, 992(s0)
	ld t0, 1768(s0)
	sd t0, 1000(s0)
	ld t0, 1776(s0)
	sd t0, 1008(s0)
	ld t0, 1784(s0)
	sd t0, 1016(s0)
	addi s1, zero, 4
251:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 251b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
252:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 252b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
253:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 253b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
254:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 254b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
255:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 255b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
256:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 256b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
257:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 257b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
258:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 258b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
259:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 259b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
260:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 260b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
261:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 261b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
262:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 262b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
263:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 263b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
264:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 264b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
265:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 265b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
266:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 266b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
267:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 267b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
268:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 268b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
269:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 269b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
270:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 270b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
271:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 271b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
272:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 272b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
273:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 273b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
274:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 274b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
275:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 275b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
276:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 276b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
277:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 277b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
278:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 278b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
279:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 279b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
280:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 280b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 3
281:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 281b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1632
	call {vg_p224_mul_mod_p}
	addi s1, zero, 5
282:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 282b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
283:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 283b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
284:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 284b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
285:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 285b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
286:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 286b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
287:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 287b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
288:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 288b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
289:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 289b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
290:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 290b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
291:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 291b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
292:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 292b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
293:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 293b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
294:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 294b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
295:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 295b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
296:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 296b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
297:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 297b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
298:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 298b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
299:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 299b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
2100:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 2100b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
2101:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 2101b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
2102:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 2102b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
2103:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 2103b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
2104:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 2104b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
2105:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 2105b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 608
	addi a2, zero, 512
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 640
	addi a2, zero, 608
	addi a3, zero, 192
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 672
	addi a2, zero, 640
	addi a3, zero, 160
	call {vg_p224_add_mod_n}
	addi a0, s0, 0
	addi a1, zero, 704
	addi a2, zero, 384
	addi a3, zero, 160
	call {vg_p224_add_mod_n}
	addi a0, s0, 0
	addi a1, zero, 736
	addi a2, zero, 672
	addi a3, zero, 704
	call {vg_p224_sub_mod_n}
	addi t3, zero, 0
	ld t4, 576(s0)
	or t3, t3, t4
	ld t4, 584(s0)
	or t3, t3, t4
	ld t4, 592(s0)
	or t3, t3, t4
	ld t4, 600(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	xori a7, a7, -1
	ld t0, 1472(s0)
	and t0, t0, a7
	sd t0, 1472(s0)
	addi t3, zero, 0
	ld t4, 736(s0)
	or t3, t3, t4
	ld t4, 744(s0)
	or t3, t3, t4
	ld t4, 752(s0)
	or t3, t3, t4
	ld t4, 760(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	ld t0, 1472(s0)
	and t0, t0, a7
	sd t0, 1472(s0)
	ld a0, 1472(s0)
	andi a0, a0, 1
	ld ra, 24(s0)
	ld s2, 16(s0)
	ld s1, 8(s0)
	ld s3, 32(s0)
	ld s0, 0(s0)
	ret
	.option pop

vg_ecdsa_p224_sign:
	.option push
	.option arch, +m, +c
	addi sp, sp, -512
	addi t0, sp, 0
	sd ra, 0(t0)
	sd s0, 8(t0)
	sd s1, 16(t0)
	sd s2, 24(t0)
	sd s3, 32(t0)
	sd s4, 40(t0)
	sd s5, 48(t0)
	sd s6, 56(t0)
	sd s7, 64(t0)
	sd s8, 72(t0)
	sd s9, 80(t0)
	addi s1, t0, 0
	addi s2, a0, 0
	addi s3, a1, 0
	addi s4, a2, 0
	addi s0, a4, 0
	addi s6, a5, 0
	ld s7, 32(a5)
	ld s8, 40(a5)
	addi t0, zero, 0
	sd t0, 232(s1)
	sd t0, 240(s1)
	sd t0, 248(s1)
	sd t0, 256(s1)
	sd t0, 264(s1)
	sd t0, 272(s1)
	sd t0, 280(s1)
	sd t0, 288(s1)
	sd t0, 296(s1)
	addi t1, zero, 28
	sub t2, s7, t1
	srli t3, t2, 63
	addi t4, zero, 0
	sub t3, t4, t3
	and t2, t2, t3
	add a6, t1, t2
	addi a4, s4, 0
	addi a5, s1, 260
	sub a5, a5, a6
20:
	lbu t1, 0(a4)
	sb t1, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 20b
	lbu t0, 232(s1)
	slli t0, t0, 24
	lbu t1, 233(s1)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 234(s1)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 235(s1)
	or t0, t0, t1
	sd t0, 24(s0)
	lbu t0, 236(s1)
	slli t0, t0, 8
	lbu t1, 237(s1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 238(s1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 239(s1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 240(s1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 241(s1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 242(s1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 243(s1)
	or t0, t0, t1
	sd t0, 16(s0)
	lbu t0, 244(s1)
	slli t0, t0, 8
	lbu t1, 245(s1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 246(s1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 247(s1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 248(s1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 249(s1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 250(s1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 251(s1)
	or t0, t0, t1
	sd t0, 8(s0)
	lbu t0, 252(s1)
	slli t0, t0, 8
	lbu t1, 253(s1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 254(s1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 255(s1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 256(s1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 257(s1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 258(s1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 259(s1)
	or t0, t0, t1
	sd t0, 0(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 32(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 40(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 48(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 56(s0)
	addi a0, s0, 0
	addi a1, zero, 64
	addi a2, zero, 0
	addi a3, zero, 32
	call {vg_p224_add_mod_n}
	addi a7, zero, -1
	ld t0, 88(s0)
	and t0, t0, a7
	srli t1, t0, 24
	sb t1, 304(s1)
	srli t1, t0, 16
	sb t1, 305(s1)
	srli t1, t0, 8
	sb t1, 306(s1)
	srli t1, t0, 0
	sb t1, 307(s1)
	ld t0, 80(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 308(s1)
	srli t1, t0, 48
	sb t1, 309(s1)
	srli t1, t0, 40
	sb t1, 310(s1)
	srli t1, t0, 32
	sb t1, 311(s1)
	srli t1, t0, 24
	sb t1, 312(s1)
	srli t1, t0, 16
	sb t1, 313(s1)
	srli t1, t0, 8
	sb t1, 314(s1)
	srli t1, t0, 0
	sb t1, 315(s1)
	ld t0, 72(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 316(s1)
	srli t1, t0, 48
	sb t1, 317(s1)
	srli t1, t0, 40
	sb t1, 318(s1)
	srli t1, t0, 32
	sb t1, 319(s1)
	srli t1, t0, 24
	sb t1, 320(s1)
	srli t1, t0, 16
	sb t1, 321(s1)
	srli t1, t0, 8
	sb t1, 322(s1)
	srli t1, t0, 0
	sb t1, 323(s1)
	ld t0, 64(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 324(s1)
	srli t1, t0, 48
	sb t1, 325(s1)
	srli t1, t0, 40
	sb t1, 326(s1)
	srli t1, t0, 32
	sb t1, 327(s1)
	srli t1, t0, 24
	sb t1, 328(s1)
	srli t1, t0, 16
	sb t1, 329(s1)
	srli t1, t0, 8
	sb t1, 330(s1)
	srli t1, t0, 0
	sb t1, 331(s1)
	addi t0, zero, 257
	slli t1, t0, 16
	or t0, t0, t1
	slli t1, t0, 32
	or t0, t0, t1
	addi t1, zero, 0
	sd t1, 96(s1)
	sd t0, 160(s1)
	sd t1, 104(s1)
	sd t0, 168(s1)
	sd t1, 112(s1)
	sd t0, 176(s1)
	sd t1, 120(s1)
	sd t0, 184(s1)
	sd t1, 128(s1)
	sd t0, 192(s1)
	sd t1, 136(s1)
	sd t0, 200(s1)
	sd t1, 144(s1)
	sd t0, 208(s1)
	sd t1, 152(s1)
	sd t0, 216(s1)
	add t0, s1, s7
	addi t1, zero, 0
	sb t1, 160(t0)
	addi a0, s0, 0
	addi a1, s0, 192
	addi a2, s1, 96
	addi a3, s7, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, s8, 0
	addi a2, s1, 160
	addi a3, s7, 1
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	add a1, s8, s7
	addi a1, a1, 1
	addi a2, s3, 0
	addi a3, zero, 28
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	add a1, s8, s7
	addi a1, a1, 29
	addi a2, s1, 304
	addi a3, zero, 28
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, s0, 192
	add a2, s8, s7
	addi a2, a2, 57
	addi a3, s1, 96
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, s0, 192
	addi a2, s1, 96
	addi a3, s7, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, s8, 0
	addi a2, s1, 160
	addi a3, s7, 0
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, s0, 192
	add a2, s8, s7
	addi a2, a2, 0
	addi a3, s1, 160
	ld t1, 16(s6)
	jalr ra, 0(t1)
	add t0, s1, s7
	addi t1, zero, 1
	sb t1, 160(t0)
	addi a0, s0, 0
	addi a1, s0, 192
	addi a2, s1, 96
	addi a3, s7, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, s8, 0
	addi a2, s1, 160
	addi a3, s7, 1
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	add a1, s8, s7
	addi a1, a1, 1
	addi a2, s3, 0
	addi a3, zero, 28
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	add a1, s8, s7
	addi a1, a1, 29
	addi a2, s1, 304
	addi a3, zero, 28
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, s0, 192
	add a2, s8, s7
	addi a2, a2, 57
	addi a3, s1, 96
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, s0, 192
	addi a2, s1, 96
	addi a3, s7, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, s8, 0
	addi a2, s1, 160
	addi a3, s7, 0
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, s0, 192
	add a2, s8, s7
	addi a2, a2, 0
	addi a3, s1, 160
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi s5, zero, 8
21:
	addi s9, zero, 0
22:
	addi a0, s0, 0
	addi a1, s0, 192
	addi a2, s1, 96
	addi a3, s7, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, s8, 0
	addi a2, s1, 160
	addi a3, s7, 0
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, s0, 192
	add a2, s8, s7
	addi a2, a2, 0
	addi a3, s1, 160
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a4, s1, 160
	addi a5, s1, 368
	add a5, a5, s9
	addi a6, s7, 0
23:
	lbu t1, 0(a4)
	sb t1, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 23b
	add s9, s9, s7
	addi t0, zero, 28
	sltu t6, s9, t0
	bnez t6, 22b
	addi a0, s2, 0
	addi a1, s3, 0
	addi a2, s1, 232
	addi a3, s1, 368
	addi a4, s0, 0
	call {vg_ecdsa_p224_sign_k}
	addi s5, s5, -1
	andi t0, a0, 1
	addi t0, t0, -1
	and t6, t0, s5
	bnez t6, 24f
	addi t6, zero, 0
	j 25f
24:
	add t0, s1, s7
	addi t1, zero, 0
	sb t1, 160(t0)
	addi a0, s0, 0
	addi a1, s0, 192
	addi a2, s1, 96
	addi a3, s7, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, s8, 0
	addi a2, s1, 160
	addi a3, s7, 1
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, s0, 192
	add a2, s8, s7
	addi a2, a2, 1
	addi a3, s1, 96
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, s0, 192
	addi a2, s1, 96
	addi a3, s7, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, s8, 0
	addi a2, s1, 160
	addi a3, s7, 0
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, s0, 192
	add a2, s8, s7
	addi a2, a2, 0
	addi a3, s1, 160
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi t6, zero, 1
25:
	bnez t6, 21b
	addi t0, zero, 0
	sd t0, 96(s1)
	sd t0, 104(s1)
	sd t0, 112(s1)
	sd t0, 120(s1)
	sd t0, 128(s1)
	sd t0, 136(s1)
	sd t0, 144(s1)
	sd t0, 152(s1)
	sd t0, 160(s1)
	sd t0, 168(s1)
	sd t0, 176(s1)
	sd t0, 184(s1)
	sd t0, 192(s1)
	sd t0, 200(s1)
	sd t0, 208(s1)
	sd t0, 216(s1)
	sd t0, 224(s1)
	sd t0, 232(s1)
	sd t0, 240(s1)
	sd t0, 248(s1)
	sd t0, 256(s1)
	sd t0, 264(s1)
	sd t0, 272(s1)
	sd t0, 280(s1)
	sd t0, 288(s1)
	sd t0, 296(s1)
	sd t0, 304(s1)
	sd t0, 312(s1)
	sd t0, 320(s1)
	sd t0, 328(s1)
	sd t0, 336(s1)
	sd t0, 344(s1)
	sd t0, 352(s1)
	sd t0, 360(s1)
	sd t0, 368(s1)
	sd t0, 376(s1)
	sd t0, 384(s1)
	sd t0, 392(s1)
	sd t0, 400(s1)
	sd t0, 408(s1)
	sd t0, 416(s1)
	sd t0, 424(s1)
	sd t0, 432(s1)
	sd t0, 440(s1)
	sd t0, 448(s1)
	sd t0, 456(s1)
	sd t0, 464(s1)
	sd t0, 472(s1)
	sd t0, 480(s1)
	sd t0, 488(s1)
	sd t0, 496(s1)
	ld ra, 0(s1)
	ld s0, 8(s1)
	ld s2, 24(s1)
	ld s3, 32(s1)
	ld s4, 40(s1)
	ld s5, 48(s1)
	ld s6, 56(s1)
	ld s7, 64(s1)
	ld s8, 72(s1)
	ld s9, 80(s1)
	ld s1, 16(s1)
	addi sp, sp, 512
	ret
	.option pop
