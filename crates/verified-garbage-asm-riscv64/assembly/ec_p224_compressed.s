// The functions of `src/ec_p224_compressed.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ec_p224_compress_public_key:
	.option push
	.option arch, +m, +c
	sd s0, 0(a2)
	sd s1, 8(a2)
	sd s2, 16(a2)
	sd ra, 24(a2)
	sd s3, 32(a2)
	addi s0, a2, 0
	addi s3, a2, 0
	addi s2, a0, 0
	lbu t0, 1(a1)
	slli t0, t0, 24
	lbu t1, 2(a1)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 3(a1)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 4(a1)
	or t0, t0, t1
	sd t0, 1144(s0)
	lbu t0, 5(a1)
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
	slli t0, t0, 8
	lbu t1, 12(a1)
	or t0, t0, t1
	sd t0, 1136(s0)
	lbu t0, 13(a1)
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
	slli t0, t0, 8
	lbu t1, 20(a1)
	or t0, t0, t1
	sd t0, 1128(s0)
	lbu t0, 21(a1)
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
	slli t0, t0, 8
	lbu t1, 28(a1)
	or t0, t0, t1
	sd t0, 1120(s0)
	lbu t0, 29(a1)
	slli t0, t0, 24
	lbu t1, 30(a1)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 31(a1)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 32(a1)
	or t0, t0, t1
	sd t0, 1240(s0)
	lbu t0, 33(a1)
	slli t0, t0, 8
	lbu t1, 34(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 35(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 36(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 37(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 38(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 39(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 40(a1)
	or t0, t0, t1
	sd t0, 1232(s0)
	lbu t0, 41(a1)
	slli t0, t0, 8
	lbu t1, 42(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 43(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 44(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 45(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 46(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 47(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 48(a1)
	or t0, t0, t1
	sd t0, 1224(s0)
	lbu t0, 49(a1)
	slli t0, t0, 8
	lbu t1, 50(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 51(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 52(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 53(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 54(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 55(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 56(a1)
	or t0, t0, t1
	sd t0, 1216(s0)
	lbu t0, 0(a1)
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
	addi a0, s0, 0
	call {vg_p224_check_point}
	addi s0, s3, 0
	ld a7, 1472(s0)
	ld t0, 1216(s0)
	andi t0, t0, 1
	addi t0, t0, 2
	and t0, t0, a7
	sb t0, 0(s2)
	ld t0, 1144(s0)
	and t0, t0, a7
	srli t1, t0, 24
	sb t1, 1(s2)
	srli t1, t0, 16
	sb t1, 2(s2)
	srli t1, t0, 8
	sb t1, 3(s2)
	srli t1, t0, 0
	sb t1, 4(s2)
	ld t0, 1136(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 5(s2)
	srli t1, t0, 48
	sb t1, 6(s2)
	srli t1, t0, 40
	sb t1, 7(s2)
	srli t1, t0, 32
	sb t1, 8(s2)
	srli t1, t0, 24
	sb t1, 9(s2)
	srli t1, t0, 16
	sb t1, 10(s2)
	srli t1, t0, 8
	sb t1, 11(s2)
	srli t1, t0, 0
	sb t1, 12(s2)
	ld t0, 1128(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 13(s2)
	srli t1, t0, 48
	sb t1, 14(s2)
	srli t1, t0, 40
	sb t1, 15(s2)
	srli t1, t0, 32
	sb t1, 16(s2)
	srli t1, t0, 24
	sb t1, 17(s2)
	srli t1, t0, 16
	sb t1, 18(s2)
	srli t1, t0, 8
	sb t1, 19(s2)
	srli t1, t0, 0
	sb t1, 20(s2)
	ld t0, 1120(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 21(s2)
	srli t1, t0, 48
	sb t1, 22(s2)
	srli t1, t0, 40
	sb t1, 23(s2)
	srli t1, t0, 32
	sb t1, 24(s2)
	srli t1, t0, 24
	sb t1, 25(s2)
	srli t1, t0, 16
	sb t1, 26(s2)
	srli t1, t0, 8
	sb t1, 27(s2)
	srli t1, t0, 0
	sb t1, 28(s2)
	ld a0, 1472(s0)
	andi a0, a0, 1
	ld ra, 24(s0)
	ld s2, 16(s0)
	ld s1, 8(s0)
	ld s3, 32(s0)
	ld s0, 0(s0)
	addi t0, zero, 0
	slli a0, a0, 32
	srli a0, a0, 32
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
	ret
	.option pop

vg_ec_p224_decompress_public_key:
	.option push
	.option arch, +m, +c
	sd s0, 0(a2)
	sd s1, 8(a2)
	sd s2, 16(a2)
	sd ra, 24(a2)
	sd s3, 32(a2)
	addi s0, a2, 0
	addi s3, a2, 0
	addi s2, a0, 0
	lbu t0, 1(a1)
	slli t0, t0, 24
	lbu t1, 2(a1)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 3(a1)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 4(a1)
	or t0, t0, t1
	sd t0, 1144(s0)
	lbu t0, 5(a1)
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
	slli t0, t0, 8
	lbu t1, 12(a1)
	or t0, t0, t1
	sd t0, 1136(s0)
	lbu t0, 13(a1)
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
	slli t0, t0, 8
	lbu t1, 20(a1)
	or t0, t0, t1
	sd t0, 1128(s0)
	lbu t0, 21(a1)
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
	slli t0, t0, 8
	lbu t1, 28(a1)
	or t0, t0, t1
	sd t0, 1120(s0)
	lbu t0, 0(a1)
	andi t0, t0, 1
	sd t0, 384(s0)
	lbu t0, 0(a1)
	xori t0, t0, 2
	srli t0, t0, 1
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
	addi t5, zero, 0
	ld t3, 1120(s0)
	ld t4, 64(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1128(s0)
	ld t4, 72(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1136(s0)
	ld t4, 80(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1144(s0)
	ld t4, 88(s0)
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
	addi a0, s0, 0
	addi a1, zero, 1152
	addi a2, zero, 1120
	addi a3, zero, 1312
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 800
	addi a2, zero, 1152
	addi a3, zero, 1152
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 800
	addi a2, zero, 800
	addi a3, zero, 1152
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 832
	addi a2, zero, 256
	addi a3, zero, 1152
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 800
	addi a2, zero, 800
	addi a3, zero, 832
	call {vg_p224_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 800
	addi a2, zero, 800
	addi a3, zero, 1344
	call {vg_p224_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 800
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
20:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 20b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
21:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 21b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
22:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 22b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
23:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 23b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
24:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 24b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
25:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 25b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
26:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 26b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
27:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 27b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
28:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 28b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
29:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 29b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
210:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 210b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
211:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 211b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
212:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 212b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
213:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 213b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
214:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 214b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
215:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 215b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
216:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 216b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
217:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 217b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
218:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 218b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
219:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 219b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
220:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 220b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
221:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 221b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
222:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 222b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
223:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 223b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
224:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 224b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
225:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 225b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
226:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 226b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
227:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 227b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
228:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 228b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 4
229:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 229b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p224_mul_mod_p}
	addi s1, zero, 3
230:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	bnez s1, 230b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1632
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 480
	addi a2, zero, 992
	addi a3, zero, 800
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1824
	addi a2, zero, 992
	addi a3, zero, 480
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1824
	addi a3, zero, 1824
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1856
	addi a3, zero, 1856
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1856
	addi a3, zero, 1856
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1856
	addi a3, zero, 1856
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1888
	addi a2, zero, 1856
	addi a3, zero, 1856
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1888
	addi a2, zero, 1888
	addi a3, zero, 1888
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1888
	addi a2, zero, 1888
	addi a3, zero, 1888
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1888
	addi a2, zero, 1888
	addi a3, zero, 1888
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1888
	addi a3, zero, 1888
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1952
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1952
	addi a2, zero, 1952
	addi a3, zero, 1952
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1952
	addi a2, zero, 1952
	addi a3, zero, 1952
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1952
	addi a2, zero, 1952
	addi a3, zero, 1952
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1984
	addi a2, zero, 1952
	addi a3, zero, 1952
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1984
	addi a2, zero, 1984
	addi a3, zero, 1984
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1984
	addi a2, zero, 1984
	addi a3, zero, 1984
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1984
	addi a2, zero, 1984
	addi a3, zero, 1984
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2016
	addi a2, zero, 1984
	addi a3, zero, 1984
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2016
	addi a2, zero, 2016
	addi a3, zero, 2016
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2016
	addi a2, zero, 2016
	addi a3, zero, 2016
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2016
	addi a2, zero, 2016
	addi a3, zero, 2016
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1
	addi a2, zero, 2016
	addi a3, zero, 2016
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1
	addi a2, zero, 2047
	addi a2, a2, 1
	addi a3, zero, 2047
	addi a3, a3, 1
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1
	addi a2, zero, 2047
	addi a2, a2, 1
	addi a3, zero, 2047
	addi a3, a3, 1
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1
	addi a2, zero, 2047
	addi a2, a2, 1
	addi a3, zero, 2047
	addi a3, a3, 1
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 33
	addi a2, zero, 2047
	addi a2, a2, 1
	addi a3, zero, 2047
	addi a3, a3, 1
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 33
	addi a2, zero, 2047
	addi a2, a2, 33
	addi a3, zero, 2047
	addi a3, a3, 33
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 33
	addi a2, zero, 2047
	addi a2, a2, 33
	addi a3, zero, 2047
	addi a3, a3, 33
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 33
	addi a2, zero, 2047
	addi a2, a2, 33
	addi a3, zero, 2047
	addi a3, a3, 33
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 65
	addi a2, zero, 2047
	addi a2, a2, 33
	addi a3, zero, 2047
	addi a3, a3, 33
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 65
	addi a2, zero, 2047
	addi a2, a2, 65
	addi a3, zero, 2047
	addi a3, a3, 65
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 65
	addi a2, zero, 2047
	addi a2, a2, 65
	addi a3, zero, 2047
	addi a3, a3, 65
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 65
	addi a2, zero, 2047
	addi a2, a2, 65
	addi a3, zero, 2047
	addi a3, a3, 65
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 97
	addi a2, zero, 2047
	addi a2, a2, 65
	addi a3, zero, 2047
	addi a3, a3, 65
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 97
	addi a2, zero, 2047
	addi a2, a2, 97
	addi a3, zero, 2047
	addi a3, a3, 97
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 97
	addi a2, zero, 2047
	addi a2, a2, 97
	addi a3, zero, 2047
	addi a3, a3, 97
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 97
	addi a2, zero, 2047
	addi a2, a2, 97
	addi a3, zero, 2047
	addi a3, a3, 97
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 129
	addi a2, zero, 2047
	addi a2, a2, 97
	addi a3, zero, 2047
	addi a3, a3, 97
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 129
	addi a2, zero, 2047
	addi a2, a2, 129
	addi a3, zero, 2047
	addi a3, a3, 129
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 129
	addi a2, zero, 2047
	addi a2, a2, 129
	addi a3, zero, 2047
	addi a3, a3, 129
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 129
	addi a2, zero, 2047
	addi a2, a2, 129
	addi a3, zero, 2047
	addi a3, a3, 129
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 161
	addi a2, zero, 2047
	addi a2, a2, 129
	addi a3, zero, 2047
	addi a3, a3, 129
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 161
	addi a2, zero, 2047
	addi a2, a2, 161
	addi a3, zero, 2047
	addi a3, a3, 161
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 161
	addi a2, zero, 2047
	addi a2, a2, 161
	addi a3, zero, 2047
	addi a3, a3, 161
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 161
	addi a2, zero, 2047
	addi a2, a2, 161
	addi a3, zero, 2047
	addi a3, a3, 161
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 193
	addi a2, zero, 2047
	addi a2, a2, 161
	addi a3, zero, 2047
	addi a3, a3, 161
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 193
	addi a2, zero, 2047
	addi a2, a2, 193
	addi a3, zero, 2047
	addi a3, a3, 193
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 193
	addi a2, zero, 2047
	addi a2, a2, 193
	addi a3, zero, 2047
	addi a3, a3, 193
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 193
	addi a2, zero, 2047
	addi a2, a2, 193
	addi a3, zero, 2047
	addi a3, a3, 193
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 225
	addi a2, zero, 2047
	addi a2, a2, 193
	addi a3, zero, 2047
	addi a3, a3, 193
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 225
	addi a2, zero, 2047
	addi a2, a2, 225
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 225
	addi a2, zero, 2047
	addi a2, a2, 225
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 225
	addi a2, zero, 2047
	addi a2, a2, 225
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 257
	addi a2, zero, 2047
	addi a2, a2, 225
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 257
	addi a2, zero, 2047
	addi a2, a2, 257
	addi a3, zero, 2047
	addi a3, a3, 257
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 257
	addi a2, zero, 2047
	addi a2, a2, 257
	addi a3, zero, 2047
	addi a3, a3, 257
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 257
	addi a2, zero, 2047
	addi a2, a2, 257
	addi a3, zero, 2047
	addi a3, a3, 257
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 289
	addi a2, zero, 2047
	addi a2, a2, 257
	addi a3, zero, 2047
	addi a3, a3, 257
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 289
	addi a2, zero, 2047
	addi a2, a2, 289
	addi a3, zero, 2047
	addi a3, a3, 289
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 289
	addi a2, zero, 2047
	addi a2, a2, 289
	addi a3, zero, 2047
	addi a3, a3, 289
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 289
	addi a2, zero, 2047
	addi a2, a2, 289
	addi a3, zero, 2047
	addi a3, a3, 289
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 321
	addi a2, zero, 2047
	addi a2, a2, 289
	addi a3, zero, 2047
	addi a3, a3, 289
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 321
	addi a2, zero, 2047
	addi a2, a2, 321
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 321
	addi a2, zero, 2047
	addi a2, a2, 321
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 321
	addi a2, zero, 2047
	addi a2, a2, 321
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 353
	addi a2, zero, 2047
	addi a2, a2, 321
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 353
	addi a2, zero, 2047
	addi a2, a2, 353
	addi a3, zero, 2047
	addi a3, a3, 353
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 353
	addi a2, zero, 2047
	addi a2, a2, 353
	addi a3, zero, 2047
	addi a3, a3, 353
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 353
	addi a2, zero, 2047
	addi a2, a2, 353
	addi a3, zero, 2047
	addi a3, a3, 353
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 385
	addi a2, zero, 2047
	addi a2, a2, 353
	addi a3, zero, 2047
	addi a3, a3, 353
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 385
	addi a2, zero, 2047
	addi a2, a2, 385
	addi a3, zero, 2047
	addi a3, a3, 385
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 385
	addi a2, zero, 2047
	addi a2, a2, 385
	addi a3, zero, 2047
	addi a3, a3, 385
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 385
	addi a2, zero, 2047
	addi a2, a2, 385
	addi a3, zero, 2047
	addi a3, a3, 385
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 417
	addi a2, zero, 2047
	addi a2, a2, 385
	addi a3, zero, 2047
	addi a3, a3, 385
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 417
	addi a2, zero, 2047
	addi a2, a2, 417
	addi a3, zero, 2047
	addi a3, a3, 417
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 417
	addi a2, zero, 2047
	addi a2, a2, 417
	addi a3, zero, 2047
	addi a3, a3, 417
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 417
	addi a2, zero, 2047
	addi a2, a2, 417
	addi a3, zero, 2047
	addi a3, a3, 417
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 449
	addi a2, zero, 2047
	addi a2, a2, 417
	addi a3, zero, 2047
	addi a3, a3, 417
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 449
	addi a2, zero, 2047
	addi a2, a2, 449
	addi a3, zero, 2047
	addi a3, a3, 449
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 449
	addi a2, zero, 2047
	addi a2, a2, 449
	addi a3, zero, 2047
	addi a3, a3, 449
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 449
	addi a2, zero, 2047
	addi a2, a2, 449
	addi a3, zero, 2047
	addi a3, a3, 449
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 481
	addi a2, zero, 2047
	addi a2, a2, 449
	addi a3, zero, 2047
	addi a3, a3, 449
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 481
	addi a2, zero, 2047
	addi a2, a2, 481
	addi a3, zero, 2047
	addi a3, a3, 481
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 481
	addi a2, zero, 2047
	addi a2, a2, 481
	addi a3, zero, 2047
	addi a3, a3, 481
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 481
	addi a2, zero, 2047
	addi a2, a2, 481
	addi a3, zero, 2047
	addi a3, a3, 481
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 513
	addi a2, zero, 2047
	addi a2, a2, 481
	addi a3, zero, 2047
	addi a3, a3, 481
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 513
	addi a2, zero, 2047
	addi a2, a2, 513
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 513
	addi a2, zero, 2047
	addi a2, a2, 513
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 513
	addi a2, zero, 2047
	addi a2, a2, 513
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_p224_mul_mod_p}
	sd s4, 40(s0)
	sd s5, 48(s0)
	sd s6, 56(s0)
	lla t0, {VG_P224_SQRT}
	addi t1, zero, 23
	slli t1, t1, 9
	add t0, t0, t1
	ld t3, 0(t0)
	addi s0, s0, 2047
	sd t3, 545(s0)
	addi s0, s0, -2047
	ld t3, 8(t0)
	addi s0, s0, 2047
	sd t3, 553(s0)
	addi s0, s0, -2047
	ld t3, 16(t0)
	addi s0, s0, 2047
	sd t3, 561(s0)
	addi s0, s0, -2047
	ld t3, 24(t0)
	addi s0, s0, 2047
	sd t3, 569(s0)
	addi s0, s0, -2047
	ld t3, 32(t0)
	addi s0, s0, 2047
	sd t3, 577(s0)
	addi s0, s0, -2047
	ld t3, 40(t0)
	addi s0, s0, 2047
	sd t3, 585(s0)
	addi s0, s0, -2047
	ld t3, 48(t0)
	addi s0, s0, 2047
	sd t3, 593(s0)
	addi s0, s0, -2047
	ld t3, 56(t0)
	addi s0, s0, 2047
	sd t3, 601(s0)
	addi s0, s0, -2047
	ld t3, 64(t0)
	addi s0, s0, 2047
	sd t3, 609(s0)
	addi s0, s0, -2047
	ld t3, 72(t0)
	addi s0, s0, 2047
	sd t3, 617(s0)
	addi s0, s0, -2047
	ld t3, 80(t0)
	addi s0, s0, 2047
	sd t3, 625(s0)
	addi s0, s0, -2047
	ld t3, 88(t0)
	addi s0, s0, 2047
	sd t3, 633(s0)
	addi s0, s0, -2047
	ld t3, 96(t0)
	addi s0, s0, 2047
	sd t3, 641(s0)
	addi s0, s0, -2047
	ld t3, 104(t0)
	addi s0, s0, 2047
	sd t3, 649(s0)
	addi s0, s0, -2047
	ld t3, 112(t0)
	addi s0, s0, 2047
	sd t3, 657(s0)
	addi s0, s0, -2047
	ld t3, 120(t0)
	addi s0, s0, 2047
	sd t3, 665(s0)
	addi s0, s0, -2047
	ld t3, 128(t0)
	addi s0, s0, 2047
	sd t3, 673(s0)
	addi s0, s0, -2047
	ld t3, 136(t0)
	addi s0, s0, 2047
	sd t3, 681(s0)
	addi s0, s0, -2047
	ld t3, 144(t0)
	addi s0, s0, 2047
	sd t3, 689(s0)
	addi s0, s0, -2047
	ld t3, 152(t0)
	addi s0, s0, 2047
	sd t3, 697(s0)
	addi s0, s0, -2047
	ld t3, 160(t0)
	addi s0, s0, 2047
	sd t3, 705(s0)
	addi s0, s0, -2047
	ld t3, 168(t0)
	addi s0, s0, 2047
	sd t3, 713(s0)
	addi s0, s0, -2047
	ld t3, 176(t0)
	addi s0, s0, 2047
	sd t3, 721(s0)
	addi s0, s0, -2047
	ld t3, 184(t0)
	addi s0, s0, 2047
	sd t3, 729(s0)
	addi s0, s0, -2047
	ld t3, 192(t0)
	addi s0, s0, 2047
	sd t3, 737(s0)
	addi s0, s0, -2047
	ld t3, 200(t0)
	addi s0, s0, 2047
	sd t3, 745(s0)
	addi s0, s0, -2047
	ld t3, 208(t0)
	addi s0, s0, 2047
	sd t3, 753(s0)
	addi s0, s0, -2047
	ld t3, 216(t0)
	addi s0, s0, 2047
	sd t3, 761(s0)
	addi s0, s0, -2047
	ld t3, 224(t0)
	addi s0, s0, 2047
	sd t3, 769(s0)
	addi s0, s0, -2047
	ld t3, 232(t0)
	addi s0, s0, 2047
	sd t3, 777(s0)
	addi s0, s0, -2047
	ld t3, 240(t0)
	addi s0, s0, 2047
	sd t3, 785(s0)
	addi s0, s0, -2047
	ld t3, 248(t0)
	addi s0, s0, 2047
	sd t3, 793(s0)
	addi s0, s0, -2047
	ld t3, 256(t0)
	addi s0, s0, 2047
	sd t3, 801(s0)
	addi s0, s0, -2047
	ld t3, 264(t0)
	addi s0, s0, 2047
	sd t3, 809(s0)
	addi s0, s0, -2047
	ld t3, 272(t0)
	addi s0, s0, 2047
	sd t3, 817(s0)
	addi s0, s0, -2047
	ld t3, 280(t0)
	addi s0, s0, 2047
	sd t3, 825(s0)
	addi s0, s0, -2047
	ld t3, 288(t0)
	addi s0, s0, 2047
	sd t3, 833(s0)
	addi s0, s0, -2047
	ld t3, 296(t0)
	addi s0, s0, 2047
	sd t3, 841(s0)
	addi s0, s0, -2047
	ld t3, 304(t0)
	addi s0, s0, 2047
	sd t3, 849(s0)
	addi s0, s0, -2047
	ld t3, 312(t0)
	addi s0, s0, 2047
	sd t3, 857(s0)
	addi s0, s0, -2047
	ld t3, 320(t0)
	addi s0, s0, 2047
	sd t3, 865(s0)
	addi s0, s0, -2047
	ld t3, 328(t0)
	addi s0, s0, 2047
	sd t3, 873(s0)
	addi s0, s0, -2047
	ld t3, 336(t0)
	addi s0, s0, 2047
	sd t3, 881(s0)
	addi s0, s0, -2047
	ld t3, 344(t0)
	addi s0, s0, 2047
	sd t3, 889(s0)
	addi s0, s0, -2047
	ld t3, 352(t0)
	addi s0, s0, 2047
	sd t3, 897(s0)
	addi s0, s0, -2047
	ld t3, 360(t0)
	addi s0, s0, 2047
	sd t3, 905(s0)
	addi s0, s0, -2047
	ld t3, 368(t0)
	addi s0, s0, 2047
	sd t3, 913(s0)
	addi s0, s0, -2047
	ld t3, 376(t0)
	addi s0, s0, 2047
	sd t3, 921(s0)
	addi s0, s0, -2047
	ld t3, 384(t0)
	addi s0, s0, 2047
	sd t3, 929(s0)
	addi s0, s0, -2047
	ld t3, 392(t0)
	addi s0, s0, 2047
	sd t3, 937(s0)
	addi s0, s0, -2047
	ld t3, 400(t0)
	addi s0, s0, 2047
	sd t3, 945(s0)
	addi s0, s0, -2047
	ld t3, 408(t0)
	addi s0, s0, 2047
	sd t3, 953(s0)
	addi s0, s0, -2047
	ld t3, 416(t0)
	addi s0, s0, 2047
	sd t3, 961(s0)
	addi s0, s0, -2047
	ld t3, 424(t0)
	addi s0, s0, 2047
	sd t3, 969(s0)
	addi s0, s0, -2047
	ld t3, 432(t0)
	addi s0, s0, 2047
	sd t3, 977(s0)
	addi s0, s0, -2047
	ld t3, 440(t0)
	addi s0, s0, 2047
	sd t3, 985(s0)
	addi s0, s0, -2047
	ld t3, 448(t0)
	addi s0, s0, 2047
	sd t3, 993(s0)
	addi s0, s0, -2047
	ld t3, 456(t0)
	addi s0, s0, 2047
	sd t3, 1001(s0)
	addi s0, s0, -2047
	ld t3, 464(t0)
	addi s0, s0, 2047
	sd t3, 1009(s0)
	addi s0, s0, -2047
	ld t3, 472(t0)
	addi s0, s0, 2047
	sd t3, 1017(s0)
	addi s0, s0, -2047
	ld t3, 480(t0)
	addi s0, s0, 2047
	sd t3, 1025(s0)
	addi s0, s0, -2047
	ld t3, 488(t0)
	addi s0, s0, 2047
	sd t3, 1033(s0)
	addi s0, s0, -2047
	ld t3, 496(t0)
	addi s0, s0, 2047
	sd t3, 1041(s0)
	addi s0, s0, -2047
	ld t3, 504(t0)
	addi s0, s0, 2047
	sd t3, 1049(s0)
	addi s0, s0, -2047
	addi s4, zero, 0
	addi s5, zero, 0
	addi t0, s0, 2047
	ld t0, 513(t0)
	sd t0, 544(s0)
	addi t0, s0, 2047
	ld t0, 521(t0)
	sd t0, 552(s0)
	addi t0, s0, 2047
	ld t0, 529(t0)
	sd t0, 560(s0)
	addi t0, s0, 2047
	ld t0, 537(t0)
	sd t0, 568(s0)
	addi s6, zero, 0
	addi s1, zero, 0
231:
	slli t0, s1, 5
	add t0, t0, s0
	addi t0, t0, 2047
	addi t0, t0, 545
	ld t3, 0(t0)
	sd t3, 608(s0)
	ld t3, 8(t0)
	sd t3, 616(s0)
	ld t3, 16(t0)
	sd t3, 624(s0)
	ld t3, 24(t0)
	sd t3, 632(s0)
	addi a0, s0, 0
	addi a1, zero, 768
	addi a2, zero, 544
	addi a3, zero, 608
	call {vg_p224_sub_mod_p}
	addi t3, zero, 0
	ld t4, 768(s0)
	or t3, t3, t4
	ld t4, 776(s0)
	or t3, t3, t4
	ld t4, 784(s0)
	or t3, t3, t4
	ld t4, 792(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	addi t0, zero, 16
	sub t0, t0, s1
	andi t0, t0, 15
	and a7, a7, t0
	add s6, s6, a7
	addi s1, s1, 1
	addi t0, zero, 16
	bne s1, t0, 231b
	andi s6, s6, 15
	slli s6, s6, 0
	or s4, s4, s6
	addi t0, s0, 2047
	ld t0, 481(t0)
	sd t0, 544(s0)
	addi t0, s0, 2047
	ld t0, 489(t0)
	sd t0, 552(s0)
	addi t0, s0, 2047
	ld t0, 497(t0)
	sd t0, 560(s0)
	addi t0, s0, 2047
	ld t0, 505(t0)
	sd t0, 568(s0)
	addi s6, zero, 0
232:
	lla t0, {VG_P224_SQRT}
	addi t1, s6, 22
	slli t1, t1, 9
	add t0, t0, t1
	slli t2, s6, 2
	addi t3, zero, 16
	bltu s6, t3, 233f
	srl t2, s5, t2
	j 234f
233:
	srl t2, s4, t2
234:
	andi t2, t2, 15
	slli t2, t2, 5
	add t0, t0, t2
	ld t3, 0(t0)
	sd t3, 608(s0)
	ld t3, 8(t0)
	sd t3, 616(s0)
	ld t3, 16(t0)
	sd t3, 624(s0)
	ld t3, 24(t0)
	sd t3, 632(s0)
	addi a0, s0, 0
	addi a1, zero, 544
	addi a2, zero, 544
	addi a3, zero, 608
	call {vg_p224_mul_mod_p}
	addi s6, s6, 1
	addi t0, zero, 1
	bne s6, t0, 232b
	addi s6, zero, 0
	addi s1, zero, 0
235:
	slli t0, s1, 5
	add t0, t0, s0
	addi t0, t0, 2047
	addi t0, t0, 545
	ld t3, 0(t0)
	sd t3, 608(s0)
	ld t3, 8(t0)
	sd t3, 616(s0)
	ld t3, 16(t0)
	sd t3, 624(s0)
	ld t3, 24(t0)
	sd t3, 632(s0)
	addi a0, s0, 0
	addi a1, zero, 768
	addi a2, zero, 544
	addi a3, zero, 608
	call {vg_p224_sub_mod_p}
	addi t3, zero, 0
	ld t4, 768(s0)
	or t3, t3, t4
	ld t4, 776(s0)
	or t3, t3, t4
	ld t4, 784(s0)
	or t3, t3, t4
	ld t4, 792(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	addi t0, zero, 16
	sub t0, t0, s1
	andi t0, t0, 15
	and a7, a7, t0
	add s6, s6, a7
	addi s1, s1, 1
	addi t0, zero, 16
	bne s1, t0, 235b
	andi s6, s6, 15
	slli s6, s6, 4
	or s4, s4, s6
	addi t0, s0, 2047
	ld t0, 449(t0)
	sd t0, 544(s0)
	addi t0, s0, 2047
	ld t0, 457(t0)
	sd t0, 552(s0)
	addi t0, s0, 2047
	ld t0, 465(t0)
	sd t0, 560(s0)
	addi t0, s0, 2047
	ld t0, 473(t0)
	sd t0, 568(s0)
	addi s6, zero, 0
236:
	lla t0, {VG_P224_SQRT}
	addi t1, s6, 21
	slli t1, t1, 9
	add t0, t0, t1
	slli t2, s6, 2
	addi t3, zero, 16
	bltu s6, t3, 237f
	srl t2, s5, t2
	j 238f
237:
	srl t2, s4, t2
238:
	andi t2, t2, 15
	slli t2, t2, 5
	add t0, t0, t2
	ld t3, 0(t0)
	sd t3, 608(s0)
	ld t3, 8(t0)
	sd t3, 616(s0)
	ld t3, 16(t0)
	sd t3, 624(s0)
	ld t3, 24(t0)
	sd t3, 632(s0)
	addi a0, s0, 0
	addi a1, zero, 544
	addi a2, zero, 544
	addi a3, zero, 608
	call {vg_p224_mul_mod_p}
	addi s6, s6, 1
	addi t0, zero, 2
	bne s6, t0, 236b
	addi s6, zero, 0
	addi s1, zero, 0
239:
	slli t0, s1, 5
	add t0, t0, s0
	addi t0, t0, 2047
	addi t0, t0, 545
	ld t3, 0(t0)
	sd t3, 608(s0)
	ld t3, 8(t0)
	sd t3, 616(s0)
	ld t3, 16(t0)
	sd t3, 624(s0)
	ld t3, 24(t0)
	sd t3, 632(s0)
	addi a0, s0, 0
	addi a1, zero, 768
	addi a2, zero, 544
	addi a3, zero, 608
	call {vg_p224_sub_mod_p}
	addi t3, zero, 0
	ld t4, 768(s0)
	or t3, t3, t4
	ld t4, 776(s0)
	or t3, t3, t4
	ld t4, 784(s0)
	or t3, t3, t4
	ld t4, 792(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	addi t0, zero, 16
	sub t0, t0, s1
	andi t0, t0, 15
	and a7, a7, t0
	add s6, s6, a7
	addi s1, s1, 1
	addi t0, zero, 16
	bne s1, t0, 239b
	andi s6, s6, 15
	slli s6, s6, 8
	or s4, s4, s6
	addi t0, s0, 2047
	ld t0, 417(t0)
	sd t0, 544(s0)
	addi t0, s0, 2047
	ld t0, 425(t0)
	sd t0, 552(s0)
	addi t0, s0, 2047
	ld t0, 433(t0)
	sd t0, 560(s0)
	addi t0, s0, 2047
	ld t0, 441(t0)
	sd t0, 568(s0)
	addi s6, zero, 0
240:
	lla t0, {VG_P224_SQRT}
	addi t1, s6, 20
	slli t1, t1, 9
	add t0, t0, t1
	slli t2, s6, 2
	addi t3, zero, 16
	bltu s6, t3, 241f
	srl t2, s5, t2
	j 242f
241:
	srl t2, s4, t2
242:
	andi t2, t2, 15
	slli t2, t2, 5
	add t0, t0, t2
	ld t3, 0(t0)
	sd t3, 608(s0)
	ld t3, 8(t0)
	sd t3, 616(s0)
	ld t3, 16(t0)
	sd t3, 624(s0)
	ld t3, 24(t0)
	sd t3, 632(s0)
	addi a0, s0, 0
	addi a1, zero, 544
	addi a2, zero, 544
	addi a3, zero, 608
	call {vg_p224_mul_mod_p}
	addi s6, s6, 1
	addi t0, zero, 3
	bne s6, t0, 240b
	addi s6, zero, 0
	addi s1, zero, 0
243:
	slli t0, s1, 5
	add t0, t0, s0
	addi t0, t0, 2047
	addi t0, t0, 545
	ld t3, 0(t0)
	sd t3, 608(s0)
	ld t3, 8(t0)
	sd t3, 616(s0)
	ld t3, 16(t0)
	sd t3, 624(s0)
	ld t3, 24(t0)
	sd t3, 632(s0)
	addi a0, s0, 0
	addi a1, zero, 768
	addi a2, zero, 544
	addi a3, zero, 608
	call {vg_p224_sub_mod_p}
	addi t3, zero, 0
	ld t4, 768(s0)
	or t3, t3, t4
	ld t4, 776(s0)
	or t3, t3, t4
	ld t4, 784(s0)
	or t3, t3, t4
	ld t4, 792(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	addi t0, zero, 16
	sub t0, t0, s1
	andi t0, t0, 15
	and a7, a7, t0
	add s6, s6, a7
	addi s1, s1, 1
	addi t0, zero, 16
	bne s1, t0, 243b
	andi s6, s6, 15
	slli s6, s6, 12
	or s4, s4, s6
	addi t0, s0, 2047
	ld t0, 385(t0)
	sd t0, 544(s0)
	addi t0, s0, 2047
	ld t0, 393(t0)
	sd t0, 552(s0)
	addi t0, s0, 2047
	ld t0, 401(t0)
	sd t0, 560(s0)
	addi t0, s0, 2047
	ld t0, 409(t0)
	sd t0, 568(s0)
	addi s6, zero, 0
244:
	lla t0, {VG_P224_SQRT}
	addi t1, s6, 19
	slli t1, t1, 9
	add t0, t0, t1
	slli t2, s6, 2
	addi t3, zero, 16
	bltu s6, t3, 245f
	srl t2, s5, t2
	j 246f
245:
	srl t2, s4, t2
246:
	andi t2, t2, 15
	slli t2, t2, 5
	add t0, t0, t2
	ld t3, 0(t0)
	sd t3, 608(s0)
	ld t3, 8(t0)
	sd t3, 616(s0)
	ld t3, 16(t0)
	sd t3, 624(s0)
	ld t3, 24(t0)
	sd t3, 632(s0)
	addi a0, s0, 0
	addi a1, zero, 544
	addi a2, zero, 544
	addi a3, zero, 608
	call {vg_p224_mul_mod_p}
	addi s6, s6, 1
	addi t0, zero, 4
	bne s6, t0, 244b
	addi s6, zero, 0
	addi s1, zero, 0
247:
	slli t0, s1, 5
	add t0, t0, s0
	addi t0, t0, 2047
	addi t0, t0, 545
	ld t3, 0(t0)
	sd t3, 608(s0)
	ld t3, 8(t0)
	sd t3, 616(s0)
	ld t3, 16(t0)
	sd t3, 624(s0)
	ld t3, 24(t0)
	sd t3, 632(s0)
	addi a0, s0, 0
	addi a1, zero, 768
	addi a2, zero, 544
	addi a3, zero, 608
	call {vg_p224_sub_mod_p}
	addi t3, zero, 0
	ld t4, 768(s0)
	or t3, t3, t4
	ld t4, 776(s0)
	or t3, t3, t4
	ld t4, 784(s0)
	or t3, t3, t4
	ld t4, 792(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	addi t0, zero, 16
	sub t0, t0, s1
	andi t0, t0, 15
	and a7, a7, t0
	add s6, s6, a7
	addi s1, s1, 1
	addi t0, zero, 16
	bne s1, t0, 247b
	andi s6, s6, 15
	slli s6, s6, 16
	or s4, s4, s6
	addi t0, s0, 2047
	ld t0, 353(t0)
	sd t0, 544(s0)
	addi t0, s0, 2047
	ld t0, 361(t0)
	sd t0, 552(s0)
	addi t0, s0, 2047
	ld t0, 369(t0)
	sd t0, 560(s0)
	addi t0, s0, 2047
	ld t0, 377(t0)
	sd t0, 568(s0)
	addi s6, zero, 0
248:
	lla t0, {VG_P224_SQRT}
	addi t1, s6, 18
	slli t1, t1, 9
	add t0, t0, t1
	slli t2, s6, 2
	addi t3, zero, 16
	bltu s6, t3, 249f
	srl t2, s5, t2
	j 250f
249:
	srl t2, s4, t2
250:
	andi t2, t2, 15
	slli t2, t2, 5
	add t0, t0, t2
	ld t3, 0(t0)
	sd t3, 608(s0)
	ld t3, 8(t0)
	sd t3, 616(s0)
	ld t3, 16(t0)
	sd t3, 624(s0)
	ld t3, 24(t0)
	sd t3, 632(s0)
	addi a0, s0, 0
	addi a1, zero, 544
	addi a2, zero, 544
	addi a3, zero, 608
	call {vg_p224_mul_mod_p}
	addi s6, s6, 1
	addi t0, zero, 5
	bne s6, t0, 248b
	addi s6, zero, 0
	addi s1, zero, 0
251:
	slli t0, s1, 5
	add t0, t0, s0
	addi t0, t0, 2047
	addi t0, t0, 545
	ld t3, 0(t0)
	sd t3, 608(s0)
	ld t3, 8(t0)
	sd t3, 616(s0)
	ld t3, 16(t0)
	sd t3, 624(s0)
	ld t3, 24(t0)
	sd t3, 632(s0)
	addi a0, s0, 0
	addi a1, zero, 768
	addi a2, zero, 544
	addi a3, zero, 608
	call {vg_p224_sub_mod_p}
	addi t3, zero, 0
	ld t4, 768(s0)
	or t3, t3, t4
	ld t4, 776(s0)
	or t3, t3, t4
	ld t4, 784(s0)
	or t3, t3, t4
	ld t4, 792(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	addi t0, zero, 16
	sub t0, t0, s1
	andi t0, t0, 15
	and a7, a7, t0
	add s6, s6, a7
	addi s1, s1, 1
	addi t0, zero, 16
	bne s1, t0, 251b
	andi s6, s6, 15
	slli s6, s6, 20
	or s4, s4, s6
	addi t0, s0, 2047
	ld t0, 321(t0)
	sd t0, 544(s0)
	addi t0, s0, 2047
	ld t0, 329(t0)
	sd t0, 552(s0)
	addi t0, s0, 2047
	ld t0, 337(t0)
	sd t0, 560(s0)
	addi t0, s0, 2047
	ld t0, 345(t0)
	sd t0, 568(s0)
	addi s6, zero, 0
252:
	lla t0, {VG_P224_SQRT}
	addi t1, s6, 17
	slli t1, t1, 9
	add t0, t0, t1
	slli t2, s6, 2
	addi t3, zero, 16
	bltu s6, t3, 253f
	srl t2, s5, t2
	j 254f
253:
	srl t2, s4, t2
254:
	andi t2, t2, 15
	slli t2, t2, 5
	add t0, t0, t2
	ld t3, 0(t0)
	sd t3, 608(s0)
	ld t3, 8(t0)
	sd t3, 616(s0)
	ld t3, 16(t0)
	sd t3, 624(s0)
	ld t3, 24(t0)
	sd t3, 632(s0)
	addi a0, s0, 0
	addi a1, zero, 544
	addi a2, zero, 544
	addi a3, zero, 608
	call {vg_p224_mul_mod_p}
	addi s6, s6, 1
	addi t0, zero, 6
	bne s6, t0, 252b
	addi s6, zero, 0
	addi s1, zero, 0
255:
	slli t0, s1, 5
	add t0, t0, s0
	addi t0, t0, 2047
	addi t0, t0, 545
	ld t3, 0(t0)
	sd t3, 608(s0)
	ld t3, 8(t0)
	sd t3, 616(s0)
	ld t3, 16(t0)
	sd t3, 624(s0)
	ld t3, 24(t0)
	sd t3, 632(s0)
	addi a0, s0, 0
	addi a1, zero, 768
	addi a2, zero, 544
	addi a3, zero, 608
	call {vg_p224_sub_mod_p}
	addi t3, zero, 0
	ld t4, 768(s0)
	or t3, t3, t4
	ld t4, 776(s0)
	or t3, t3, t4
	ld t4, 784(s0)
	or t3, t3, t4
	ld t4, 792(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	addi t0, zero, 16
	sub t0, t0, s1
	andi t0, t0, 15
	and a7, a7, t0
	add s6, s6, a7
	addi s1, s1, 1
	addi t0, zero, 16
	bne s1, t0, 255b
	andi s6, s6, 15
	slli s6, s6, 24
	or s4, s4, s6
	addi t0, s0, 2047
	ld t0, 289(t0)
	sd t0, 544(s0)
	addi t0, s0, 2047
	ld t0, 297(t0)
	sd t0, 552(s0)
	addi t0, s0, 2047
	ld t0, 305(t0)
	sd t0, 560(s0)
	addi t0, s0, 2047
	ld t0, 313(t0)
	sd t0, 568(s0)
	addi s6, zero, 0
256:
	lla t0, {VG_P224_SQRT}
	addi t1, s6, 16
	slli t1, t1, 9
	add t0, t0, t1
	slli t2, s6, 2
	addi t3, zero, 16
	bltu s6, t3, 257f
	srl t2, s5, t2
	j 258f
257:
	srl t2, s4, t2
258:
	andi t2, t2, 15
	slli t2, t2, 5
	add t0, t0, t2
	ld t3, 0(t0)
	sd t3, 608(s0)
	ld t3, 8(t0)
	sd t3, 616(s0)
	ld t3, 16(t0)
	sd t3, 624(s0)
	ld t3, 24(t0)
	sd t3, 632(s0)
	addi a0, s0, 0
	addi a1, zero, 544
	addi a2, zero, 544
	addi a3, zero, 608
	call {vg_p224_mul_mod_p}
	addi s6, s6, 1
	addi t0, zero, 7
	bne s6, t0, 256b
	addi s6, zero, 0
	addi s1, zero, 0
259:
	slli t0, s1, 5
	add t0, t0, s0
	addi t0, t0, 2047
	addi t0, t0, 545
	ld t3, 0(t0)
	sd t3, 608(s0)
	ld t3, 8(t0)
	sd t3, 616(s0)
	ld t3, 16(t0)
	sd t3, 624(s0)
	ld t3, 24(t0)
	sd t3, 632(s0)
	addi a0, s0, 0
	addi a1, zero, 768
	addi a2, zero, 544
	addi a3, zero, 608
	call {vg_p224_sub_mod_p}
	addi t3, zero, 0
	ld t4, 768(s0)
	or t3, t3, t4
	ld t4, 776(s0)
	or t3, t3, t4
	ld t4, 784(s0)
	or t3, t3, t4
	ld t4, 792(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	addi t0, zero, 16
	sub t0, t0, s1
	andi t0, t0, 15
	and a7, a7, t0
	add s6, s6, a7
	addi s1, s1, 1
	addi t0, zero, 16
	bne s1, t0, 259b
	andi s6, s6, 15
	slli s6, s6, 28
	or s4, s4, s6
	addi t0, s0, 2047
	ld t0, 257(t0)
	sd t0, 544(s0)
	addi t0, s0, 2047
	ld t0, 265(t0)
	sd t0, 552(s0)
	addi t0, s0, 2047
	ld t0, 273(t0)
	sd t0, 560(s0)
	addi t0, s0, 2047
	ld t0, 281(t0)
	sd t0, 568(s0)
	addi s6, zero, 0
260:
	lla t0, {VG_P224_SQRT}
	addi t1, s6, 15
	slli t1, t1, 9
	add t0, t0, t1
	slli t2, s6, 2
	addi t3, zero, 16
	bltu s6, t3, 261f
	srl t2, s5, t2
	j 262f
261:
	srl t2, s4, t2
262:
	andi t2, t2, 15
	slli t2, t2, 5
	add t0, t0, t2
	ld t3, 0(t0)
	sd t3, 608(s0)
	ld t3, 8(t0)
	sd t3, 616(s0)
	ld t3, 16(t0)
	sd t3, 624(s0)
	ld t3, 24(t0)
	sd t3, 632(s0)
	addi a0, s0, 0
	addi a1, zero, 544
	addi a2, zero, 544
	addi a3, zero, 608
	call {vg_p224_mul_mod_p}
	addi s6, s6, 1
	addi t0, zero, 8
	bne s6, t0, 260b
	addi s6, zero, 0
	addi s1, zero, 0
263:
	slli t0, s1, 5
	add t0, t0, s0
	addi t0, t0, 2047
	addi t0, t0, 545
	ld t3, 0(t0)
	sd t3, 608(s0)
	ld t3, 8(t0)
	sd t3, 616(s0)
	ld t3, 16(t0)
	sd t3, 624(s0)
	ld t3, 24(t0)
	sd t3, 632(s0)
	addi a0, s0, 0
	addi a1, zero, 768
	addi a2, zero, 544
	addi a3, zero, 608
	call {vg_p224_sub_mod_p}
	addi t3, zero, 0
	ld t4, 768(s0)
	or t3, t3, t4
	ld t4, 776(s0)
	or t3, t3, t4
	ld t4, 784(s0)
	or t3, t3, t4
	ld t4, 792(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	addi t0, zero, 16
	sub t0, t0, s1
	andi t0, t0, 15
	and a7, a7, t0
	add s6, s6, a7
	addi s1, s1, 1
	addi t0, zero, 16
	bne s1, t0, 263b
	andi s6, s6, 15
	slli s6, s6, 32
	or s4, s4, s6
	addi t0, s0, 2047
	ld t0, 225(t0)
	sd t0, 544(s0)
	addi t0, s0, 2047
	ld t0, 233(t0)
	sd t0, 552(s0)
	addi t0, s0, 2047
	ld t0, 241(t0)
	sd t0, 560(s0)
	addi t0, s0, 2047
	ld t0, 249(t0)
	sd t0, 568(s0)
	addi s6, zero, 0
264:
	lla t0, {VG_P224_SQRT}
	addi t1, s6, 14
	slli t1, t1, 9
	add t0, t0, t1
	slli t2, s6, 2
	addi t3, zero, 16
	bltu s6, t3, 265f
	srl t2, s5, t2
	j 266f
265:
	srl t2, s4, t2
266:
	andi t2, t2, 15
	slli t2, t2, 5
	add t0, t0, t2
	ld t3, 0(t0)
	sd t3, 608(s0)
	ld t3, 8(t0)
	sd t3, 616(s0)
	ld t3, 16(t0)
	sd t3, 624(s0)
	ld t3, 24(t0)
	sd t3, 632(s0)
	addi a0, s0, 0
	addi a1, zero, 544
	addi a2, zero, 544
	addi a3, zero, 608
	call {vg_p224_mul_mod_p}
	addi s6, s6, 1
	addi t0, zero, 9
	bne s6, t0, 264b
	addi s6, zero, 0
	addi s1, zero, 0
267:
	slli t0, s1, 5
	add t0, t0, s0
	addi t0, t0, 2047
	addi t0, t0, 545
	ld t3, 0(t0)
	sd t3, 608(s0)
	ld t3, 8(t0)
	sd t3, 616(s0)
	ld t3, 16(t0)
	sd t3, 624(s0)
	ld t3, 24(t0)
	sd t3, 632(s0)
	addi a0, s0, 0
	addi a1, zero, 768
	addi a2, zero, 544
	addi a3, zero, 608
	call {vg_p224_sub_mod_p}
	addi t3, zero, 0
	ld t4, 768(s0)
	or t3, t3, t4
	ld t4, 776(s0)
	or t3, t3, t4
	ld t4, 784(s0)
	or t3, t3, t4
	ld t4, 792(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	addi t0, zero, 16
	sub t0, t0, s1
	andi t0, t0, 15
	and a7, a7, t0
	add s6, s6, a7
	addi s1, s1, 1
	addi t0, zero, 16
	bne s1, t0, 267b
	andi s6, s6, 15
	slli s6, s6, 36
	or s4, s4, s6
	addi t0, s0, 2047
	ld t0, 193(t0)
	sd t0, 544(s0)
	addi t0, s0, 2047
	ld t0, 201(t0)
	sd t0, 552(s0)
	addi t0, s0, 2047
	ld t0, 209(t0)
	sd t0, 560(s0)
	addi t0, s0, 2047
	ld t0, 217(t0)
	sd t0, 568(s0)
	addi s6, zero, 0
268:
	lla t0, {VG_P224_SQRT}
	addi t1, s6, 13
	slli t1, t1, 9
	add t0, t0, t1
	slli t2, s6, 2
	addi t3, zero, 16
	bltu s6, t3, 269f
	srl t2, s5, t2
	j 270f
269:
	srl t2, s4, t2
270:
	andi t2, t2, 15
	slli t2, t2, 5
	add t0, t0, t2
	ld t3, 0(t0)
	sd t3, 608(s0)
	ld t3, 8(t0)
	sd t3, 616(s0)
	ld t3, 16(t0)
	sd t3, 624(s0)
	ld t3, 24(t0)
	sd t3, 632(s0)
	addi a0, s0, 0
	addi a1, zero, 544
	addi a2, zero, 544
	addi a3, zero, 608
	call {vg_p224_mul_mod_p}
	addi s6, s6, 1
	addi t0, zero, 10
	bne s6, t0, 268b
	addi s6, zero, 0
	addi s1, zero, 0
271:
	slli t0, s1, 5
	add t0, t0, s0
	addi t0, t0, 2047
	addi t0, t0, 545
	ld t3, 0(t0)
	sd t3, 608(s0)
	ld t3, 8(t0)
	sd t3, 616(s0)
	ld t3, 16(t0)
	sd t3, 624(s0)
	ld t3, 24(t0)
	sd t3, 632(s0)
	addi a0, s0, 0
	addi a1, zero, 768
	addi a2, zero, 544
	addi a3, zero, 608
	call {vg_p224_sub_mod_p}
	addi t3, zero, 0
	ld t4, 768(s0)
	or t3, t3, t4
	ld t4, 776(s0)
	or t3, t3, t4
	ld t4, 784(s0)
	or t3, t3, t4
	ld t4, 792(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	addi t0, zero, 16
	sub t0, t0, s1
	andi t0, t0, 15
	and a7, a7, t0
	add s6, s6, a7
	addi s1, s1, 1
	addi t0, zero, 16
	bne s1, t0, 271b
	andi s6, s6, 15
	slli s6, s6, 40
	or s4, s4, s6
	addi t0, s0, 2047
	ld t0, 161(t0)
	sd t0, 544(s0)
	addi t0, s0, 2047
	ld t0, 169(t0)
	sd t0, 552(s0)
	addi t0, s0, 2047
	ld t0, 177(t0)
	sd t0, 560(s0)
	addi t0, s0, 2047
	ld t0, 185(t0)
	sd t0, 568(s0)
	addi s6, zero, 0
272:
	lla t0, {VG_P224_SQRT}
	addi t1, s6, 12
	slli t1, t1, 9
	add t0, t0, t1
	slli t2, s6, 2
	addi t3, zero, 16
	bltu s6, t3, 273f
	srl t2, s5, t2
	j 274f
273:
	srl t2, s4, t2
274:
	andi t2, t2, 15
	slli t2, t2, 5
	add t0, t0, t2
	ld t3, 0(t0)
	sd t3, 608(s0)
	ld t3, 8(t0)
	sd t3, 616(s0)
	ld t3, 16(t0)
	sd t3, 624(s0)
	ld t3, 24(t0)
	sd t3, 632(s0)
	addi a0, s0, 0
	addi a1, zero, 544
	addi a2, zero, 544
	addi a3, zero, 608
	call {vg_p224_mul_mod_p}
	addi s6, s6, 1
	addi t0, zero, 11
	bne s6, t0, 272b
	addi s6, zero, 0
	addi s1, zero, 0
275:
	slli t0, s1, 5
	add t0, t0, s0
	addi t0, t0, 2047
	addi t0, t0, 545
	ld t3, 0(t0)
	sd t3, 608(s0)
	ld t3, 8(t0)
	sd t3, 616(s0)
	ld t3, 16(t0)
	sd t3, 624(s0)
	ld t3, 24(t0)
	sd t3, 632(s0)
	addi a0, s0, 0
	addi a1, zero, 768
	addi a2, zero, 544
	addi a3, zero, 608
	call {vg_p224_sub_mod_p}
	addi t3, zero, 0
	ld t4, 768(s0)
	or t3, t3, t4
	ld t4, 776(s0)
	or t3, t3, t4
	ld t4, 784(s0)
	or t3, t3, t4
	ld t4, 792(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	addi t0, zero, 16
	sub t0, t0, s1
	andi t0, t0, 15
	and a7, a7, t0
	add s6, s6, a7
	addi s1, s1, 1
	addi t0, zero, 16
	bne s1, t0, 275b
	andi s6, s6, 15
	slli s6, s6, 44
	or s4, s4, s6
	addi t0, s0, 2047
	ld t0, 129(t0)
	sd t0, 544(s0)
	addi t0, s0, 2047
	ld t0, 137(t0)
	sd t0, 552(s0)
	addi t0, s0, 2047
	ld t0, 145(t0)
	sd t0, 560(s0)
	addi t0, s0, 2047
	ld t0, 153(t0)
	sd t0, 568(s0)
	addi s6, zero, 0
276:
	lla t0, {VG_P224_SQRT}
	addi t1, s6, 11
	slli t1, t1, 9
	add t0, t0, t1
	slli t2, s6, 2
	addi t3, zero, 16
	bltu s6, t3, 277f
	srl t2, s5, t2
	j 278f
277:
	srl t2, s4, t2
278:
	andi t2, t2, 15
	slli t2, t2, 5
	add t0, t0, t2
	ld t3, 0(t0)
	sd t3, 608(s0)
	ld t3, 8(t0)
	sd t3, 616(s0)
	ld t3, 16(t0)
	sd t3, 624(s0)
	ld t3, 24(t0)
	sd t3, 632(s0)
	addi a0, s0, 0
	addi a1, zero, 544
	addi a2, zero, 544
	addi a3, zero, 608
	call {vg_p224_mul_mod_p}
	addi s6, s6, 1
	addi t0, zero, 12
	bne s6, t0, 276b
	addi s6, zero, 0
	addi s1, zero, 0
279:
	slli t0, s1, 5
	add t0, t0, s0
	addi t0, t0, 2047
	addi t0, t0, 545
	ld t3, 0(t0)
	sd t3, 608(s0)
	ld t3, 8(t0)
	sd t3, 616(s0)
	ld t3, 16(t0)
	sd t3, 624(s0)
	ld t3, 24(t0)
	sd t3, 632(s0)
	addi a0, s0, 0
	addi a1, zero, 768
	addi a2, zero, 544
	addi a3, zero, 608
	call {vg_p224_sub_mod_p}
	addi t3, zero, 0
	ld t4, 768(s0)
	or t3, t3, t4
	ld t4, 776(s0)
	or t3, t3, t4
	ld t4, 784(s0)
	or t3, t3, t4
	ld t4, 792(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	addi t0, zero, 16
	sub t0, t0, s1
	andi t0, t0, 15
	and a7, a7, t0
	add s6, s6, a7
	addi s1, s1, 1
	addi t0, zero, 16
	bne s1, t0, 279b
	andi s6, s6, 15
	slli s6, s6, 48
	or s4, s4, s6
	addi t0, s0, 2047
	ld t0, 97(t0)
	sd t0, 544(s0)
	addi t0, s0, 2047
	ld t0, 105(t0)
	sd t0, 552(s0)
	addi t0, s0, 2047
	ld t0, 113(t0)
	sd t0, 560(s0)
	addi t0, s0, 2047
	ld t0, 121(t0)
	sd t0, 568(s0)
	addi s6, zero, 0
280:
	lla t0, {VG_P224_SQRT}
	addi t1, s6, 10
	slli t1, t1, 9
	add t0, t0, t1
	slli t2, s6, 2
	addi t3, zero, 16
	bltu s6, t3, 281f
	srl t2, s5, t2
	j 282f
281:
	srl t2, s4, t2
282:
	andi t2, t2, 15
	slli t2, t2, 5
	add t0, t0, t2
	ld t3, 0(t0)
	sd t3, 608(s0)
	ld t3, 8(t0)
	sd t3, 616(s0)
	ld t3, 16(t0)
	sd t3, 624(s0)
	ld t3, 24(t0)
	sd t3, 632(s0)
	addi a0, s0, 0
	addi a1, zero, 544
	addi a2, zero, 544
	addi a3, zero, 608
	call {vg_p224_mul_mod_p}
	addi s6, s6, 1
	addi t0, zero, 13
	bne s6, t0, 280b
	addi s6, zero, 0
	addi s1, zero, 0
283:
	slli t0, s1, 5
	add t0, t0, s0
	addi t0, t0, 2047
	addi t0, t0, 545
	ld t3, 0(t0)
	sd t3, 608(s0)
	ld t3, 8(t0)
	sd t3, 616(s0)
	ld t3, 16(t0)
	sd t3, 624(s0)
	ld t3, 24(t0)
	sd t3, 632(s0)
	addi a0, s0, 0
	addi a1, zero, 768
	addi a2, zero, 544
	addi a3, zero, 608
	call {vg_p224_sub_mod_p}
	addi t3, zero, 0
	ld t4, 768(s0)
	or t3, t3, t4
	ld t4, 776(s0)
	or t3, t3, t4
	ld t4, 784(s0)
	or t3, t3, t4
	ld t4, 792(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	addi t0, zero, 16
	sub t0, t0, s1
	andi t0, t0, 15
	and a7, a7, t0
	add s6, s6, a7
	addi s1, s1, 1
	addi t0, zero, 16
	bne s1, t0, 283b
	andi s6, s6, 15
	slli s6, s6, 52
	or s4, s4, s6
	addi t0, s0, 2047
	ld t0, 65(t0)
	sd t0, 544(s0)
	addi t0, s0, 2047
	ld t0, 73(t0)
	sd t0, 552(s0)
	addi t0, s0, 2047
	ld t0, 81(t0)
	sd t0, 560(s0)
	addi t0, s0, 2047
	ld t0, 89(t0)
	sd t0, 568(s0)
	addi s6, zero, 0
284:
	lla t0, {VG_P224_SQRT}
	addi t1, s6, 9
	slli t1, t1, 9
	add t0, t0, t1
	slli t2, s6, 2
	addi t3, zero, 16
	bltu s6, t3, 285f
	srl t2, s5, t2
	j 286f
285:
	srl t2, s4, t2
286:
	andi t2, t2, 15
	slli t2, t2, 5
	add t0, t0, t2
	ld t3, 0(t0)
	sd t3, 608(s0)
	ld t3, 8(t0)
	sd t3, 616(s0)
	ld t3, 16(t0)
	sd t3, 624(s0)
	ld t3, 24(t0)
	sd t3, 632(s0)
	addi a0, s0, 0
	addi a1, zero, 544
	addi a2, zero, 544
	addi a3, zero, 608
	call {vg_p224_mul_mod_p}
	addi s6, s6, 1
	addi t0, zero, 14
	bne s6, t0, 284b
	addi s6, zero, 0
	addi s1, zero, 0
287:
	slli t0, s1, 5
	add t0, t0, s0
	addi t0, t0, 2047
	addi t0, t0, 545
	ld t3, 0(t0)
	sd t3, 608(s0)
	ld t3, 8(t0)
	sd t3, 616(s0)
	ld t3, 16(t0)
	sd t3, 624(s0)
	ld t3, 24(t0)
	sd t3, 632(s0)
	addi a0, s0, 0
	addi a1, zero, 768
	addi a2, zero, 544
	addi a3, zero, 608
	call {vg_p224_sub_mod_p}
	addi t3, zero, 0
	ld t4, 768(s0)
	or t3, t3, t4
	ld t4, 776(s0)
	or t3, t3, t4
	ld t4, 784(s0)
	or t3, t3, t4
	ld t4, 792(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	addi t0, zero, 16
	sub t0, t0, s1
	andi t0, t0, 15
	and a7, a7, t0
	add s6, s6, a7
	addi s1, s1, 1
	addi t0, zero, 16
	bne s1, t0, 287b
	andi s6, s6, 15
	slli s6, s6, 56
	or s4, s4, s6
	addi t0, s0, 2047
	ld t0, 33(t0)
	sd t0, 544(s0)
	addi t0, s0, 2047
	ld t0, 41(t0)
	sd t0, 552(s0)
	addi t0, s0, 2047
	ld t0, 49(t0)
	sd t0, 560(s0)
	addi t0, s0, 2047
	ld t0, 57(t0)
	sd t0, 568(s0)
	addi s6, zero, 0
288:
	lla t0, {VG_P224_SQRT}
	addi t1, s6, 8
	slli t1, t1, 9
	add t0, t0, t1
	slli t2, s6, 2
	addi t3, zero, 16
	bltu s6, t3, 289f
	srl t2, s5, t2
	j 290f
289:
	srl t2, s4, t2
290:
	andi t2, t2, 15
	slli t2, t2, 5
	add t0, t0, t2
	ld t3, 0(t0)
	sd t3, 608(s0)
	ld t3, 8(t0)
	sd t3, 616(s0)
	ld t3, 16(t0)
	sd t3, 624(s0)
	ld t3, 24(t0)
	sd t3, 632(s0)
	addi a0, s0, 0
	addi a1, zero, 544
	addi a2, zero, 544
	addi a3, zero, 608
	call {vg_p224_mul_mod_p}
	addi s6, s6, 1
	addi t0, zero, 15
	bne s6, t0, 288b
	addi s6, zero, 0
	addi s1, zero, 0
291:
	slli t0, s1, 5
	add t0, t0, s0
	addi t0, t0, 2047
	addi t0, t0, 545
	ld t3, 0(t0)
	sd t3, 608(s0)
	ld t3, 8(t0)
	sd t3, 616(s0)
	ld t3, 16(t0)
	sd t3, 624(s0)
	ld t3, 24(t0)
	sd t3, 632(s0)
	addi a0, s0, 0
	addi a1, zero, 768
	addi a2, zero, 544
	addi a3, zero, 608
	call {vg_p224_sub_mod_p}
	addi t3, zero, 0
	ld t4, 768(s0)
	or t3, t3, t4
	ld t4, 776(s0)
	or t3, t3, t4
	ld t4, 784(s0)
	or t3, t3, t4
	ld t4, 792(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	addi t0, zero, 16
	sub t0, t0, s1
	andi t0, t0, 15
	and a7, a7, t0
	add s6, s6, a7
	addi s1, s1, 1
	addi t0, zero, 16
	bne s1, t0, 291b
	andi s6, s6, 15
	slli s6, s6, 60
	or s4, s4, s6
	addi t0, s0, 2047
	ld t0, 1(t0)
	sd t0, 544(s0)
	addi t0, s0, 2047
	ld t0, 9(t0)
	sd t0, 552(s0)
	addi t0, s0, 2047
	ld t0, 17(t0)
	sd t0, 560(s0)
	addi t0, s0, 2047
	ld t0, 25(t0)
	sd t0, 568(s0)
	addi s6, zero, 0
292:
	lla t0, {VG_P224_SQRT}
	addi t1, s6, 7
	slli t1, t1, 9
	add t0, t0, t1
	slli t2, s6, 2
	addi t3, zero, 16
	bltu s6, t3, 293f
	srl t2, s5, t2
	j 294f
293:
	srl t2, s4, t2
294:
	andi t2, t2, 15
	slli t2, t2, 5
	add t0, t0, t2
	ld t3, 0(t0)
	sd t3, 608(s0)
	ld t3, 8(t0)
	sd t3, 616(s0)
	ld t3, 16(t0)
	sd t3, 624(s0)
	ld t3, 24(t0)
	sd t3, 632(s0)
	addi a0, s0, 0
	addi a1, zero, 544
	addi a2, zero, 544
	addi a3, zero, 608
	call {vg_p224_mul_mod_p}
	addi s6, s6, 1
	addi t0, zero, 16
	bne s6, t0, 292b
	addi s6, zero, 0
	addi s1, zero, 0
295:
	slli t0, s1, 5
	add t0, t0, s0
	addi t0, t0, 2047
	addi t0, t0, 545
	ld t3, 0(t0)
	sd t3, 608(s0)
	ld t3, 8(t0)
	sd t3, 616(s0)
	ld t3, 16(t0)
	sd t3, 624(s0)
	ld t3, 24(t0)
	sd t3, 632(s0)
	addi a0, s0, 0
	addi a1, zero, 768
	addi a2, zero, 544
	addi a3, zero, 608
	call {vg_p224_sub_mod_p}
	addi t3, zero, 0
	ld t4, 768(s0)
	or t3, t3, t4
	ld t4, 776(s0)
	or t3, t3, t4
	ld t4, 784(s0)
	or t3, t3, t4
	ld t4, 792(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	addi t0, zero, 16
	sub t0, t0, s1
	andi t0, t0, 15
	and a7, a7, t0
	add s6, s6, a7
	addi s1, s1, 1
	addi t0, zero, 16
	bne s1, t0, 295b
	andi s6, s6, 15
	slli s6, s6, 0
	or s5, s5, s6
	ld t0, 2016(s0)
	sd t0, 544(s0)
	ld t0, 2024(s0)
	sd t0, 552(s0)
	ld t0, 2032(s0)
	sd t0, 560(s0)
	ld t0, 2040(s0)
	sd t0, 568(s0)
	addi s6, zero, 0
296:
	lla t0, {VG_P224_SQRT}
	addi t1, s6, 6
	slli t1, t1, 9
	add t0, t0, t1
	slli t2, s6, 2
	addi t3, zero, 16
	bltu s6, t3, 297f
	srl t2, s5, t2
	j 298f
297:
	srl t2, s4, t2
298:
	andi t2, t2, 15
	slli t2, t2, 5
	add t0, t0, t2
	ld t3, 0(t0)
	sd t3, 608(s0)
	ld t3, 8(t0)
	sd t3, 616(s0)
	ld t3, 16(t0)
	sd t3, 624(s0)
	ld t3, 24(t0)
	sd t3, 632(s0)
	addi a0, s0, 0
	addi a1, zero, 544
	addi a2, zero, 544
	addi a3, zero, 608
	call {vg_p224_mul_mod_p}
	addi s6, s6, 1
	addi t0, zero, 17
	bne s6, t0, 296b
	addi s6, zero, 0
	addi s1, zero, 0
299:
	slli t0, s1, 5
	add t0, t0, s0
	addi t0, t0, 2047
	addi t0, t0, 545
	ld t3, 0(t0)
	sd t3, 608(s0)
	ld t3, 8(t0)
	sd t3, 616(s0)
	ld t3, 16(t0)
	sd t3, 624(s0)
	ld t3, 24(t0)
	sd t3, 632(s0)
	addi a0, s0, 0
	addi a1, zero, 768
	addi a2, zero, 544
	addi a3, zero, 608
	call {vg_p224_sub_mod_p}
	addi t3, zero, 0
	ld t4, 768(s0)
	or t3, t3, t4
	ld t4, 776(s0)
	or t3, t3, t4
	ld t4, 784(s0)
	or t3, t3, t4
	ld t4, 792(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	addi t0, zero, 16
	sub t0, t0, s1
	andi t0, t0, 15
	and a7, a7, t0
	add s6, s6, a7
	addi s1, s1, 1
	addi t0, zero, 16
	bne s1, t0, 299b
	andi s6, s6, 15
	slli s6, s6, 4
	or s5, s5, s6
	ld t0, 1984(s0)
	sd t0, 544(s0)
	ld t0, 1992(s0)
	sd t0, 552(s0)
	ld t0, 2000(s0)
	sd t0, 560(s0)
	ld t0, 2008(s0)
	sd t0, 568(s0)
	addi s6, zero, 0
2100:
	lla t0, {VG_P224_SQRT}
	addi t1, s6, 5
	slli t1, t1, 9
	add t0, t0, t1
	slli t2, s6, 2
	addi t3, zero, 16
	bltu s6, t3, 2101f
	srl t2, s5, t2
	j 2102f
2101:
	srl t2, s4, t2
2102:
	andi t2, t2, 15
	slli t2, t2, 5
	add t0, t0, t2
	ld t3, 0(t0)
	sd t3, 608(s0)
	ld t3, 8(t0)
	sd t3, 616(s0)
	ld t3, 16(t0)
	sd t3, 624(s0)
	ld t3, 24(t0)
	sd t3, 632(s0)
	addi a0, s0, 0
	addi a1, zero, 544
	addi a2, zero, 544
	addi a3, zero, 608
	call {vg_p224_mul_mod_p}
	addi s6, s6, 1
	addi t0, zero, 18
	bne s6, t0, 2100b
	addi s6, zero, 0
	addi s1, zero, 0
2103:
	slli t0, s1, 5
	add t0, t0, s0
	addi t0, t0, 2047
	addi t0, t0, 545
	ld t3, 0(t0)
	sd t3, 608(s0)
	ld t3, 8(t0)
	sd t3, 616(s0)
	ld t3, 16(t0)
	sd t3, 624(s0)
	ld t3, 24(t0)
	sd t3, 632(s0)
	addi a0, s0, 0
	addi a1, zero, 768
	addi a2, zero, 544
	addi a3, zero, 608
	call {vg_p224_sub_mod_p}
	addi t3, zero, 0
	ld t4, 768(s0)
	or t3, t3, t4
	ld t4, 776(s0)
	or t3, t3, t4
	ld t4, 784(s0)
	or t3, t3, t4
	ld t4, 792(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	addi t0, zero, 16
	sub t0, t0, s1
	andi t0, t0, 15
	and a7, a7, t0
	add s6, s6, a7
	addi s1, s1, 1
	addi t0, zero, 16
	bne s1, t0, 2103b
	andi s6, s6, 15
	slli s6, s6, 8
	or s5, s5, s6
	ld t0, 1952(s0)
	sd t0, 544(s0)
	ld t0, 1960(s0)
	sd t0, 552(s0)
	ld t0, 1968(s0)
	sd t0, 560(s0)
	ld t0, 1976(s0)
	sd t0, 568(s0)
	addi s6, zero, 0
2104:
	lla t0, {VG_P224_SQRT}
	addi t1, s6, 4
	slli t1, t1, 9
	add t0, t0, t1
	slli t2, s6, 2
	addi t3, zero, 16
	bltu s6, t3, 2105f
	srl t2, s5, t2
	j 2106f
2105:
	srl t2, s4, t2
2106:
	andi t2, t2, 15
	slli t2, t2, 5
	add t0, t0, t2
	ld t3, 0(t0)
	sd t3, 608(s0)
	ld t3, 8(t0)
	sd t3, 616(s0)
	ld t3, 16(t0)
	sd t3, 624(s0)
	ld t3, 24(t0)
	sd t3, 632(s0)
	addi a0, s0, 0
	addi a1, zero, 544
	addi a2, zero, 544
	addi a3, zero, 608
	call {vg_p224_mul_mod_p}
	addi s6, s6, 1
	addi t0, zero, 19
	bne s6, t0, 2104b
	addi s6, zero, 0
	addi s1, zero, 0
2107:
	slli t0, s1, 5
	add t0, t0, s0
	addi t0, t0, 2047
	addi t0, t0, 545
	ld t3, 0(t0)
	sd t3, 608(s0)
	ld t3, 8(t0)
	sd t3, 616(s0)
	ld t3, 16(t0)
	sd t3, 624(s0)
	ld t3, 24(t0)
	sd t3, 632(s0)
	addi a0, s0, 0
	addi a1, zero, 768
	addi a2, zero, 544
	addi a3, zero, 608
	call {vg_p224_sub_mod_p}
	addi t3, zero, 0
	ld t4, 768(s0)
	or t3, t3, t4
	ld t4, 776(s0)
	or t3, t3, t4
	ld t4, 784(s0)
	or t3, t3, t4
	ld t4, 792(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	addi t0, zero, 16
	sub t0, t0, s1
	andi t0, t0, 15
	and a7, a7, t0
	add s6, s6, a7
	addi s1, s1, 1
	addi t0, zero, 16
	bne s1, t0, 2107b
	andi s6, s6, 15
	slli s6, s6, 12
	or s5, s5, s6
	ld t0, 1920(s0)
	sd t0, 544(s0)
	ld t0, 1928(s0)
	sd t0, 552(s0)
	ld t0, 1936(s0)
	sd t0, 560(s0)
	ld t0, 1944(s0)
	sd t0, 568(s0)
	addi s6, zero, 0
2108:
	lla t0, {VG_P224_SQRT}
	addi t1, s6, 3
	slli t1, t1, 9
	add t0, t0, t1
	slli t2, s6, 2
	addi t3, zero, 16
	bltu s6, t3, 2109f
	srl t2, s5, t2
	j 2110f
2109:
	srl t2, s4, t2
2110:
	andi t2, t2, 15
	slli t2, t2, 5
	add t0, t0, t2
	ld t3, 0(t0)
	sd t3, 608(s0)
	ld t3, 8(t0)
	sd t3, 616(s0)
	ld t3, 16(t0)
	sd t3, 624(s0)
	ld t3, 24(t0)
	sd t3, 632(s0)
	addi a0, s0, 0
	addi a1, zero, 544
	addi a2, zero, 544
	addi a3, zero, 608
	call {vg_p224_mul_mod_p}
	addi s6, s6, 1
	addi t0, zero, 20
	bne s6, t0, 2108b
	addi s6, zero, 0
	addi s1, zero, 0
2111:
	slli t0, s1, 5
	add t0, t0, s0
	addi t0, t0, 2047
	addi t0, t0, 545
	ld t3, 0(t0)
	sd t3, 608(s0)
	ld t3, 8(t0)
	sd t3, 616(s0)
	ld t3, 16(t0)
	sd t3, 624(s0)
	ld t3, 24(t0)
	sd t3, 632(s0)
	addi a0, s0, 0
	addi a1, zero, 768
	addi a2, zero, 544
	addi a3, zero, 608
	call {vg_p224_sub_mod_p}
	addi t3, zero, 0
	ld t4, 768(s0)
	or t3, t3, t4
	ld t4, 776(s0)
	or t3, t3, t4
	ld t4, 784(s0)
	or t3, t3, t4
	ld t4, 792(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	addi t0, zero, 16
	sub t0, t0, s1
	andi t0, t0, 15
	and a7, a7, t0
	add s6, s6, a7
	addi s1, s1, 1
	addi t0, zero, 16
	bne s1, t0, 2111b
	andi s6, s6, 15
	slli s6, s6, 16
	or s5, s5, s6
	ld t0, 1888(s0)
	sd t0, 544(s0)
	ld t0, 1896(s0)
	sd t0, 552(s0)
	ld t0, 1904(s0)
	sd t0, 560(s0)
	ld t0, 1912(s0)
	sd t0, 568(s0)
	addi s6, zero, 0
2112:
	lla t0, {VG_P224_SQRT}
	addi t1, s6, 2
	slli t1, t1, 9
	add t0, t0, t1
	slli t2, s6, 2
	addi t3, zero, 16
	bltu s6, t3, 2113f
	srl t2, s5, t2
	j 2114f
2113:
	srl t2, s4, t2
2114:
	andi t2, t2, 15
	slli t2, t2, 5
	add t0, t0, t2
	ld t3, 0(t0)
	sd t3, 608(s0)
	ld t3, 8(t0)
	sd t3, 616(s0)
	ld t3, 16(t0)
	sd t3, 624(s0)
	ld t3, 24(t0)
	sd t3, 632(s0)
	addi a0, s0, 0
	addi a1, zero, 544
	addi a2, zero, 544
	addi a3, zero, 608
	call {vg_p224_mul_mod_p}
	addi s6, s6, 1
	addi t0, zero, 21
	bne s6, t0, 2112b
	addi s6, zero, 0
	addi s1, zero, 0
2115:
	slli t0, s1, 5
	add t0, t0, s0
	addi t0, t0, 2047
	addi t0, t0, 545
	ld t3, 0(t0)
	sd t3, 608(s0)
	ld t3, 8(t0)
	sd t3, 616(s0)
	ld t3, 16(t0)
	sd t3, 624(s0)
	ld t3, 24(t0)
	sd t3, 632(s0)
	addi a0, s0, 0
	addi a1, zero, 768
	addi a2, zero, 544
	addi a3, zero, 608
	call {vg_p224_sub_mod_p}
	addi t3, zero, 0
	ld t4, 768(s0)
	or t3, t3, t4
	ld t4, 776(s0)
	or t3, t3, t4
	ld t4, 784(s0)
	or t3, t3, t4
	ld t4, 792(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	addi t0, zero, 16
	sub t0, t0, s1
	andi t0, t0, 15
	and a7, a7, t0
	add s6, s6, a7
	addi s1, s1, 1
	addi t0, zero, 16
	bne s1, t0, 2115b
	andi s6, s6, 15
	slli s6, s6, 20
	or s5, s5, s6
	ld t0, 1856(s0)
	sd t0, 544(s0)
	ld t0, 1864(s0)
	sd t0, 552(s0)
	ld t0, 1872(s0)
	sd t0, 560(s0)
	ld t0, 1880(s0)
	sd t0, 568(s0)
	addi s6, zero, 0
2116:
	lla t0, {VG_P224_SQRT}
	addi t1, s6, 1
	slli t1, t1, 9
	add t0, t0, t1
	slli t2, s6, 2
	addi t3, zero, 16
	bltu s6, t3, 2117f
	srl t2, s5, t2
	j 2118f
2117:
	srl t2, s4, t2
2118:
	andi t2, t2, 15
	slli t2, t2, 5
	add t0, t0, t2
	ld t3, 0(t0)
	sd t3, 608(s0)
	ld t3, 8(t0)
	sd t3, 616(s0)
	ld t3, 16(t0)
	sd t3, 624(s0)
	ld t3, 24(t0)
	sd t3, 632(s0)
	addi a0, s0, 0
	addi a1, zero, 544
	addi a2, zero, 544
	addi a3, zero, 608
	call {vg_p224_mul_mod_p}
	addi s6, s6, 1
	addi t0, zero, 22
	bne s6, t0, 2116b
	addi s6, zero, 0
	addi s1, zero, 0
2119:
	slli t0, s1, 5
	add t0, t0, s0
	addi t0, t0, 2047
	addi t0, t0, 545
	ld t3, 0(t0)
	sd t3, 608(s0)
	ld t3, 8(t0)
	sd t3, 616(s0)
	ld t3, 16(t0)
	sd t3, 624(s0)
	ld t3, 24(t0)
	sd t3, 632(s0)
	addi a0, s0, 0
	addi a1, zero, 768
	addi a2, zero, 544
	addi a3, zero, 608
	call {vg_p224_sub_mod_p}
	addi t3, zero, 0
	ld t4, 768(s0)
	or t3, t3, t4
	ld t4, 776(s0)
	or t3, t3, t4
	ld t4, 784(s0)
	or t3, t3, t4
	ld t4, 792(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	addi t0, zero, 16
	sub t0, t0, s1
	andi t0, t0, 15
	and a7, a7, t0
	add s6, s6, a7
	addi s1, s1, 1
	addi t0, zero, 16
	bne s1, t0, 2119b
	andi s6, s6, 15
	slli s6, s6, 24
	or s5, s5, s6
	ld t0, 1824(s0)
	sd t0, 544(s0)
	ld t0, 1832(s0)
	sd t0, 552(s0)
	ld t0, 1840(s0)
	sd t0, 560(s0)
	ld t0, 1848(s0)
	sd t0, 568(s0)
	addi s6, zero, 0
2120:
	lla t0, {VG_P224_SQRT}
	addi t1, s6, 0
	slli t1, t1, 9
	add t0, t0, t1
	slli t2, s6, 2
	addi t3, zero, 16
	bltu s6, t3, 2121f
	srl t2, s5, t2
	j 2122f
2121:
	srl t2, s4, t2
2122:
	andi t2, t2, 15
	slli t2, t2, 5
	add t0, t0, t2
	ld t3, 0(t0)
	sd t3, 608(s0)
	ld t3, 8(t0)
	sd t3, 616(s0)
	ld t3, 16(t0)
	sd t3, 624(s0)
	ld t3, 24(t0)
	sd t3, 632(s0)
	addi a0, s0, 0
	addi a1, zero, 544
	addi a2, zero, 544
	addi a3, zero, 608
	call {vg_p224_mul_mod_p}
	addi s6, s6, 1
	addi t0, zero, 23
	bne s6, t0, 2120b
	addi s6, zero, 0
	addi s1, zero, 0
2123:
	slli t0, s1, 5
	add t0, t0, s0
	addi t0, t0, 2047
	addi t0, t0, 545
	ld t3, 0(t0)
	sd t3, 608(s0)
	ld t3, 8(t0)
	sd t3, 616(s0)
	ld t3, 16(t0)
	sd t3, 624(s0)
	ld t3, 24(t0)
	sd t3, 632(s0)
	addi a0, s0, 0
	addi a1, zero, 768
	addi a2, zero, 544
	addi a3, zero, 608
	call {vg_p224_sub_mod_p}
	addi t3, zero, 0
	ld t4, 768(s0)
	or t3, t3, t4
	ld t4, 776(s0)
	or t3, t3, t4
	ld t4, 784(s0)
	or t3, t3, t4
	ld t4, 792(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	addi t0, zero, 16
	sub t0, t0, s1
	andi t0, t0, 15
	and a7, a7, t0
	add s6, s6, a7
	addi s1, s1, 1
	addi t0, zero, 16
	bne s1, t0, 2123b
	andi s6, s6, 15
	slli s6, s6, 28
	or s5, s5, s6
	ld t0, 480(s0)
	sd t0, 992(s0)
	ld t0, 488(s0)
	sd t0, 1000(s0)
	ld t0, 496(s0)
	sd t0, 1008(s0)
	ld t0, 504(s0)
	sd t0, 1016(s0)
	srli t0, s4, 1
	slli t1, s5, 63
	or s4, t0, t1
	srli s5, s5, 1
	addi s6, zero, 0
2124:
	lla t0, {VG_P224_SQRT}
	addi t1, s6, 0
	slli t1, t1, 9
	add t0, t0, t1
	slli t2, s6, 2
	addi t3, zero, 16
	bltu s6, t3, 2125f
	srl t2, s5, t2
	j 2126f
2125:
	srl t2, s4, t2
2126:
	andi t2, t2, 15
	slli t2, t2, 5
	add t0, t0, t2
	ld t3, 0(t0)
	sd t3, 608(s0)
	ld t3, 8(t0)
	sd t3, 616(s0)
	ld t3, 16(t0)
	sd t3, 624(s0)
	ld t3, 24(t0)
	sd t3, 632(s0)
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 608
	call {vg_p224_mul_mod_p}
	addi s6, s6, 1
	addi t0, zero, 24
	bne s6, t0, 2124b
	ld s4, 40(s0)
	ld s5, 48(s0)
	ld s6, 56(s0)
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 896
	addi a2, zero, 864
	addi a3, zero, 800
	call {vg_p224_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 672
	addi a2, zero, 992
	addi a3, zero, 192
	call {vg_p224_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 704
	addi a2, zero, 160
	addi a3, zero, 672
	call {vg_p224_sub_mod_p}
	addi t3, zero, 0
	ld t4, 896(s0)
	or t3, t3, t4
	ld t4, 904(s0)
	or t3, t3, t4
	ld t4, 912(s0)
	or t3, t3, t4
	ld t4, 920(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	ld t0, 1472(s0)
	and t0, t0, a7
	sd t0, 1472(s0)
	ld t0, 672(s0)
	ld t1, 384(s0)
	xor t0, t0, t1
	andi t0, t0, 1
	addi t1, zero, 0
	sub a7, t1, t0
	ld t0, 672(s0)
	ld t1, 704(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 736(s0)
	ld t0, 680(s0)
	ld t1, 712(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 744(s0)
	ld t0, 688(s0)
	ld t1, 720(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 752(s0)
	ld t0, 696(s0)
	ld t1, 728(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 760(s0)
	ld t0, 736(s0)
	ld t1, 384(s0)
	xor t0, t0, t1
	andi t0, t0, 1
	addi a7, t0, -1
	ld t0, 1472(s0)
	and t0, t0, a7
	sd t0, 1472(s0)
	ld a7, 1472(s0)
	addi t0, zero, 4
	and t0, t0, a7
	sb t0, 0(s2)
	ld t0, 1144(s0)
	and t0, t0, a7
	srli t1, t0, 24
	sb t1, 1(s2)
	srli t1, t0, 16
	sb t1, 2(s2)
	srli t1, t0, 8
	sb t1, 3(s2)
	srli t1, t0, 0
	sb t1, 4(s2)
	ld t0, 1136(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 5(s2)
	srli t1, t0, 48
	sb t1, 6(s2)
	srli t1, t0, 40
	sb t1, 7(s2)
	srli t1, t0, 32
	sb t1, 8(s2)
	srli t1, t0, 24
	sb t1, 9(s2)
	srli t1, t0, 16
	sb t1, 10(s2)
	srli t1, t0, 8
	sb t1, 11(s2)
	srli t1, t0, 0
	sb t1, 12(s2)
	ld t0, 1128(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 13(s2)
	srli t1, t0, 48
	sb t1, 14(s2)
	srli t1, t0, 40
	sb t1, 15(s2)
	srli t1, t0, 32
	sb t1, 16(s2)
	srli t1, t0, 24
	sb t1, 17(s2)
	srli t1, t0, 16
	sb t1, 18(s2)
	srli t1, t0, 8
	sb t1, 19(s2)
	srli t1, t0, 0
	sb t1, 20(s2)
	ld t0, 1120(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 21(s2)
	srli t1, t0, 48
	sb t1, 22(s2)
	srli t1, t0, 40
	sb t1, 23(s2)
	srli t1, t0, 32
	sb t1, 24(s2)
	srli t1, t0, 24
	sb t1, 25(s2)
	srli t1, t0, 16
	sb t1, 26(s2)
	srli t1, t0, 8
	sb t1, 27(s2)
	srli t1, t0, 0
	sb t1, 28(s2)
	ld t0, 760(s0)
	and t0, t0, a7
	srli t1, t0, 24
	sb t1, 29(s2)
	srli t1, t0, 16
	sb t1, 30(s2)
	srli t1, t0, 8
	sb t1, 31(s2)
	srli t1, t0, 0
	sb t1, 32(s2)
	ld t0, 752(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 33(s2)
	srli t1, t0, 48
	sb t1, 34(s2)
	srli t1, t0, 40
	sb t1, 35(s2)
	srli t1, t0, 32
	sb t1, 36(s2)
	srli t1, t0, 24
	sb t1, 37(s2)
	srli t1, t0, 16
	sb t1, 38(s2)
	srli t1, t0, 8
	sb t1, 39(s2)
	srli t1, t0, 0
	sb t1, 40(s2)
	ld t0, 744(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 41(s2)
	srli t1, t0, 48
	sb t1, 42(s2)
	srli t1, t0, 40
	sb t1, 43(s2)
	srli t1, t0, 32
	sb t1, 44(s2)
	srli t1, t0, 24
	sb t1, 45(s2)
	srli t1, t0, 16
	sb t1, 46(s2)
	srli t1, t0, 8
	sb t1, 47(s2)
	srli t1, t0, 0
	sb t1, 48(s2)
	ld t0, 736(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 49(s2)
	srli t1, t0, 48
	sb t1, 50(s2)
	srli t1, t0, 40
	sb t1, 51(s2)
	srli t1, t0, 32
	sb t1, 52(s2)
	srli t1, t0, 24
	sb t1, 53(s2)
	srli t1, t0, 16
	sb t1, 54(s2)
	srli t1, t0, 8
	sb t1, 55(s2)
	srli t1, t0, 0
	sb t1, 56(s2)
	ld a0, 1472(s0)
	andi a0, a0, 1
	ld ra, 24(s0)
	ld s2, 16(s0)
	ld s1, 8(s0)
	ld s3, 32(s0)
	ld s0, 0(s0)
	addi t0, zero, 0
	slli a0, a0, 32
	srli a0, a0, 32
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
	ret
	.option pop
