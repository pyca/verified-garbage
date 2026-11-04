// The functions of `src/ecdsa_secp256k1.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_secp256k1_verify:
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
	slli t0, t0, 8
	lbu t1, 2(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 3(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 4(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 5(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 6(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 7(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 8(a0)
	or t0, t0, t1
	sd t0, 1144(s0)
	lbu t0, 9(a0)
	slli t0, t0, 8
	lbu t1, 10(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 11(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 12(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 13(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 14(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 15(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 16(a0)
	or t0, t0, t1
	sd t0, 1136(s0)
	lbu t0, 17(a0)
	slli t0, t0, 8
	lbu t1, 18(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 19(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 20(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 21(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 22(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 23(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 24(a0)
	or t0, t0, t1
	sd t0, 1128(s0)
	lbu t0, 25(a0)
	slli t0, t0, 8
	lbu t1, 26(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 27(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 28(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 29(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 30(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 31(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 32(a0)
	or t0, t0, t1
	sd t0, 1120(s0)
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
	sd t0, 1240(s0)
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
	sd t0, 1232(s0)
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
	sd t0, 1224(s0)
	lbu t0, 57(a0)
	slli t0, t0, 8
	lbu t1, 58(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 59(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 60(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 61(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 62(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 63(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 64(a0)
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
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -977
	add t0, t0, t1
	sd t0, 64(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
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
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 88(s0)
	lui t0, 785702
	addiw t0, t0, -371
	slli t0, t0, 32
	lui t1, 852836
	addiw t1, t1, 321
	add t0, t0, t1
	sd t0, 96(s0)
	lui t0, 764654
	addiw t0, t0, -793
	slli t0, t0, 32
	lui t1, 717962
	addiw t1, t1, 59
	add t0, t0, t1
	sd t0, 104(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -2
	add t0, t0, t1
	sd t0, 112(s0)
	lui t0, 0
	addiw t0, t0, 0
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
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 977
	add t0, t0, t1
	sd t0, 224(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
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
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 256(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 264(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 272(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 280(s0)
	lui t0, 0
	addiw t0, t0, 21
	slli t0, t0, 32
	lui t1, 5
	addiw t1, t1, 37
	add t0, t0, t1
	sd t0, 288(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 296(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 304(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 312(s0)
	lui t0, 881507
	addiw t0, t0, -422
	slli t0, t0, 32
	lui t1, 296930
	addiw t1, t1, 151
	add t0, t0, t1
	sd t0, 320(s0)
	lui t0, 143843
	addiw t0, t0, -1709
	slli t0, t0, 32
	lui t1, 170950
	addiw t1, t1, 1755
	add t0, t0, t1
	sd t0, 328(s0)
	lui t0, 621045
	addiw t0, t0, -1856
	slli t0, t0, 32
	lui t1, 212945
	addiw t1, t1, 668
	add t0, t0, t1
	sd t0, 336(s0)
	lui t0, 628766
	addiw t0, t0, 1604
	slli t0, t0, 32
	lui t1, 954506
	addiw t1, t1, -184
	add t0, t0, t1
	sd t0, 344(s0)
	lui t0, 726506
	addiw t0, t0, 1747
	slli t0, t0, 32
	lui t1, 867771
	addiw t1, t1, -1054
	add t0, t0, t1
	sd t0, 352(s0)
	lui t0, 581574
	addiw t0, t0, -675
	slli t0, t0, 32
	lui t1, 127452
	addiw t1, t1, 1613
	add t0, t0, t1
	sd t0, 360(s0)
	lui t0, 461675
	addiw t0, t0, 1435
	slli t0, t0, 32
	lui t1, 704924
	addiw t1, t1, 310
	add t0, t0, t1
	sd t0, 368(s0)
	lui t0, 848888
	addiw t0, t0, 1312
	slli t0, t0, 32
	lui t1, 871000
	addiw t1, t1, 726
	add t0, t0, t1
	sd t0, 376(s0)
	lui t0, 0
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -979
	add t0, t0, t1
	sd t0, 448(s0)
	lui t0, 0
	addiw t0, t0, 0
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
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 472(s0)
	lui t0, 0
	addiw t0, t0, 1954
	slli t0, t0, 32
	lui t1, 233
	addiw t1, t1, 161
	add t0, t0, t1
	sd t0, 1312(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 1
	add t0, t0, t1
	sd t0, 1320(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1328(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1336(s0)
	lui t0, 0
	addiw t0, t0, 7
	slli t0, t0, 32
	lui t1, 2
	addiw t1, t1, -1353
	add t0, t0, t1
	sd t0, 1344(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1352(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1360(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1368(s0)
	lbu t0, 0(a2)
	slli t0, t0, 8
	lbu t1, 1(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 2(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 3(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 4(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 5(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 6(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 7(a2)
	or t0, t0, t1
	sd t0, 408(s0)
	lbu t0, 8(a2)
	slli t0, t0, 8
	lbu t1, 9(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 10(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 11(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 12(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 13(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 14(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 15(a2)
	or t0, t0, t1
	sd t0, 400(s0)
	lbu t0, 16(a2)
	slli t0, t0, 8
	lbu t1, 17(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 18(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 19(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 20(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 21(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 22(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 23(a2)
	or t0, t0, t1
	sd t0, 392(s0)
	lbu t0, 24(a2)
	slli t0, t0, 8
	lbu t1, 25(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 26(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 27(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 28(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 29(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 30(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 31(a2)
	or t0, t0, t1
	sd t0, 384(s0)
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
	sd t0, 440(s0)
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
	sd t0, 432(s0)
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
	sd t0, 424(s0)
	lbu t0, 56(a2)
	slli t0, t0, 8
	lbu t1, 57(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 58(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 59(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 60(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 61(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 62(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 63(a2)
	or t0, t0, t1
	sd t0, 416(s0)
	lbu t0, 0(a1)
	slli t0, t0, 8
	lbu t1, 1(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 2(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 3(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 4(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 5(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 6(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 7(a1)
	or t0, t0, t1
	sd t0, 1112(s0)
	lbu t0, 8(a1)
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
	slli t0, t0, 8
	lbu t1, 13(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 14(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 15(a1)
	or t0, t0, t1
	sd t0, 1104(s0)
	lbu t0, 16(a1)
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
	slli t0, t0, 8
	lbu t1, 21(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 22(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 23(a1)
	or t0, t0, t1
	sd t0, 1096(s0)
	lbu t0, 24(a1)
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
	slli t0, t0, 8
	lbu t1, 29(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 30(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 31(a1)
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
	call {vg_secp256k1_check_point}
	addi s0, s3, 0
	lui t0, 562895
	addiw t0, t0, 532
	slli t0, t0, 32
	lui t1, 425341
	addiw t1, t1, 320
	add t0, t0, t1
	sd t0, 1184(s0)
	lui t0, 475465
	addiw t0, t0, 1730
	slli t0, t0, 32
	lui t1, 59344
	addiw t1, t1, -1928
	add t0, t0, t1
	sd t0, 1192(s0)
	lui t0, 944511
	addiw t0, t0, 1508
	slli t0, t0, 32
	lui t1, 376016
	addiw t1, t1, 1990
	add t0, t0, t1
	sd t0, 1200(s0)
	lui t0, 644722
	addiw t0, t0, -810
	slli t0, t0, 32
	lui t1, 531562
	addiw t1, t1, -1083
	add t0, t0, t1
	sd t0, 1208(s0)
	lui t0, 262874
	addiw t0, t0, 371
	slli t0, t0, 32
	lui t1, 195740
	addiw t1, t1, -321
	add t0, t0, t1
	sd t0, 1216(s0)
	lui t0, 283922
	addiw t0, t0, 793
	slli t0, t0, 32
	lui t1, 330614
	addiw t1, t1, -60
	add t0, t0, t1
	sd t0, 1224(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 1
	add t0, t0, t1
	sd t0, 1232(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1240(s0)
	lui t0, 785702
	addiw t0, t0, -371
	slli t0, t0, 32
	lui t1, 852836
	addiw t1, t1, 319
	add t0, t0, t1
	sd t0, 1248(s0)
	lui t0, 764654
	addiw t0, t0, -793
	slli t0, t0, 32
	lui t1, 717962
	addiw t1, t1, 59
	add t0, t0, t1
	sd t0, 1256(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -2
	add t0, t0, t1
	sd t0, 1264(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 1272(s0)
	addi a0, s0, 0
	addi a1, zero, 704
	addi a2, zero, 416
	addi a3, zero, 1184
	call {vg_secp256k1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 704
	addi a3, zero, 1216
	call {vg_secp256k1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1536
	addi a3, zero, 1536
	call {vg_secp256k1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1568
	addi a2, zero, 1536
	addi a3, zero, 1792
	call {vg_secp256k1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1568
	addi a3, zero, 1792
	call {vg_secp256k1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1632
	addi a2, zero, 1600
	addi a3, zero, 1792
	call {vg_secp256k1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1632
	addi a3, zero, 1792
	call {vg_secp256k1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1696
	addi a2, zero, 1664
	addi a3, zero, 1792
	call {vg_secp256k1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1696
	addi a3, zero, 1792
	call {vg_secp256k1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1760
	addi a2, zero, 1728
	addi a3, zero, 1792
	call {vg_secp256k1_mul_mod_n}
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
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 20b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
21:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 21b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
22:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 22b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
23:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 23b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
24:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 24b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
25:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 25b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
26:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 26b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
27:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 27b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
28:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 28b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
29:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 29b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
210:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 210b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
211:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 211b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
212:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 212b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
213:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 213b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
214:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 214b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
215:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 215b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
216:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 216b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
217:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 217b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
218:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 218b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
219:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 219b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
220:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 220b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
221:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 221b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
222:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 222b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
223:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 223b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
224:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 224b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
225:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 225b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
226:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 226b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
227:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 227b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
228:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 228b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
229:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 229b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 3
230:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 230b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1632
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 5
231:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 231b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1696
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 3
232:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 232b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1600
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
233:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 233b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1600
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
234:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 234b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1632
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 5
235:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 235b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1728
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 2
236:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 236b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1568
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 5
237:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 237b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1632
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 6
238:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 238b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1728
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 5
239:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 239b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1696
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
240:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 240b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1728
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 3
241:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 241b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1536
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 6
242:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 242b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1600
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 10
243:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 243b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1632
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
244:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 244b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1632
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 5
245:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 245b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
246:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 246b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 5
247:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 247b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1664
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 6
248:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 248b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1696
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
249:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 249b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1728
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 5
250:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 250b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1568
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 6
251:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 251b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1728
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 10
252:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 252b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1728
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
253:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 253b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1664
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 9
254:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 254b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1664
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
255:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 255b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 1
256:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 256b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1536
	call {vg_secp256k1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 736
	addi a2, zero, 1088
	addi a3, zero, 1184
	call {vg_secp256k1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 768
	addi a2, zero, 736
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 768
	addi a3, zero, 192
	call {vg_secp256k1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 768
	addi a2, zero, 384
	addi a3, zero, 1184
	call {vg_secp256k1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 832
	addi a2, zero, 768
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 832
	addi a3, zero, 192
	call {vg_secp256k1_mul_mod_n}
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
	call {vg_secp256k1_mul}
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
	lui t0, 0
	addiw t0, t0, 7
	slli t0, t0, 32
	lui t1, 2
	addiw t1, t1, -1353
	add t0, t0, t1
	sd t0, 1344(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1352(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1360(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
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
	call {vg_secp256k1_mul_g}
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
	lui t0, 0
	addiw t0, t0, 7
	slli t0, t0, 32
	lui t1, 2
	addiw t1, t1, -1353
	add t0, t0, t1
	sd t0, 1344(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1352(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1360(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1368(s0)
	addi a0, s0, 0
	addi a1, zero, 800
	addi a2, zero, 512
	addi a3, zero, 320
	call {vg_secp256k1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 832
	addi a2, zero, 544
	addi a3, zero, 1280
	call {vg_secp256k1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 576
	addi a3, zero, 1440
	call {vg_secp256k1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 896
	addi a2, zero, 512
	addi a3, zero, 544
	call {vg_secp256k1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 928
	addi a2, zero, 320
	addi a3, zero, 1280
	call {vg_secp256k1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 896
	addi a2, zero, 896
	addi a3, zero, 928
	call {vg_secp256k1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 928
	addi a2, zero, 800
	addi a3, zero, 832
	call {vg_secp256k1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 896
	addi a2, zero, 896
	addi a3, zero, 928
	call {vg_secp256k1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 928
	addi a2, zero, 512
	addi a3, zero, 576
	call {vg_secp256k1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 960
	addi a2, zero, 320
	addi a3, zero, 1440
	call {vg_secp256k1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 928
	addi a2, zero, 928
	addi a3, zero, 960
	call {vg_secp256k1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 960
	addi a2, zero, 800
	addi a3, zero, 864
	call {vg_secp256k1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 928
	addi a2, zero, 928
	addi a3, zero, 960
	call {vg_secp256k1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 960
	addi a2, zero, 544
	addi a3, zero, 576
	call {vg_secp256k1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 704
	addi a2, zero, 1280
	addi a3, zero, 1440
	call {vg_secp256k1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 960
	addi a2, zero, 960
	addi a3, zero, 704
	call {vg_secp256k1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 704
	addi a2, zero, 832
	addi a3, zero, 864
	call {vg_secp256k1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 960
	addi a2, zero, 960
	addi a3, zero, 704
	call {vg_secp256k1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 768
	addi a2, zero, 256
	addi a3, zero, 928
	call {vg_secp256k1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 704
	addi a2, zero, 288
	addi a3, zero, 864
	call {vg_secp256k1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 768
	addi a2, zero, 704
	addi a3, zero, 768
	call {vg_secp256k1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 704
	addi a2, zero, 832
	addi a3, zero, 768
	call {vg_secp256k1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 768
	addi a2, zero, 832
	addi a3, zero, 768
	call {vg_secp256k1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 736
	addi a2, zero, 704
	addi a3, zero, 768
	call {vg_secp256k1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 832
	addi a2, zero, 800
	addi a3, zero, 800
	call {vg_secp256k1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 832
	addi a2, zero, 832
	addi a3, zero, 800
	call {vg_secp256k1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 256
	addi a3, zero, 864
	call {vg_secp256k1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 928
	addi a2, zero, 288
	addi a3, zero, 928
	call {vg_secp256k1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 832
	addi a2, zero, 832
	addi a3, zero, 864
	call {vg_secp256k1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 800
	addi a3, zero, 864
	call {vg_secp256k1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 256
	addi a3, zero, 864
	call {vg_secp256k1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 928
	addi a2, zero, 928
	addi a3, zero, 864
	call {vg_secp256k1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 800
	addi a2, zero, 832
	addi a3, zero, 928
	call {vg_secp256k1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 736
	addi a2, zero, 736
	addi a3, zero, 800
	call {vg_secp256k1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 800
	addi a2, zero, 960
	addi a3, zero, 928
	call {vg_secp256k1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 704
	addi a2, zero, 896
	addi a3, zero, 704
	call {vg_secp256k1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 704
	addi a2, zero, 704
	addi a3, zero, 800
	call {vg_secp256k1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 800
	addi a2, zero, 896
	addi a3, zero, 832
	call {vg_secp256k1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 768
	addi a2, zero, 960
	addi a3, zero, 768
	call {vg_secp256k1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 768
	addi a2, zero, 768
	addi a3, zero, 800
	call {vg_secp256k1_add_mod_p}
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
	call {vg_secp256k1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1536
	addi a3, zero, 1536
	call {vg_secp256k1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1568
	addi a2, zero, 1536
	addi a3, zero, 1792
	call {vg_secp256k1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1568
	addi a3, zero, 1792
	call {vg_secp256k1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1632
	addi a2, zero, 1600
	addi a3, zero, 1792
	call {vg_secp256k1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1632
	addi a3, zero, 1792
	call {vg_secp256k1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1696
	addi a2, zero, 1664
	addi a3, zero, 1792
	call {vg_secp256k1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1696
	addi a3, zero, 1792
	call {vg_secp256k1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1760
	addi a2, zero, 1728
	addi a3, zero, 1792
	call {vg_secp256k1_mul_mod_p}
	ld t0, 1760(s0)
	sd t0, 992(s0)
	ld t0, 1768(s0)
	sd t0, 1000(s0)
	ld t0, 1776(s0)
	sd t0, 1008(s0)
	ld t0, 1784(s0)
	sd t0, 1016(s0)
	addi s1, zero, 4
257:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 257b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
258:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 258b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
259:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 259b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
260:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 260b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
261:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 261b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
262:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 262b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
263:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 263b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
264:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 264b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
265:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 265b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
266:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 266b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
267:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 267b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
268:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 268b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
269:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 269b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
270:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 270b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
271:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 271b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
272:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 272b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
273:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 273b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
274:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 274b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
275:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 275b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
276:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 276b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
277:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 277b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
278:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 278b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
279:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 279b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
280:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 280b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
281:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 281b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
282:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 282b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
283:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 283b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
284:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 284b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
285:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 285b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
286:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 286b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
287:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 287b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
288:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 288b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
289:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 289b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
290:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 290b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
291:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 291b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
292:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 292b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
293:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 293b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
294:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 294b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
295:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 295b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
296:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 296b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
297:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 297b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
298:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 298b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
299:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 299b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
2100:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 2100b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
2101:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 2101b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
2102:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 2102b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
2103:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 2103b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
2104:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 2104b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
2105:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 2105b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
2106:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 2106b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
2107:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 2107b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
2108:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 2108b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
2109:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 2109b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
2110:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 2110b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 3
2111:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 2111b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1632
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 5
2112:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 2112b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
2113:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 2113b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
2114:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 2114b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
2115:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 2115b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
2116:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 2116b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 2
2117:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 2117b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1568
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 8
2118:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 2118b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1696
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 2
2119:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 2119b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1536
	call {vg_secp256k1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 608
	addi a2, zero, 512
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 640
	addi a2, zero, 608
	addi a3, zero, 192
	call {vg_secp256k1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 672
	addi a2, zero, 640
	addi a3, zero, 160
	call {vg_secp256k1_add_mod_n}
	addi a0, s0, 0
	addi a1, zero, 704
	addi a2, zero, 384
	addi a3, zero, 160
	call {vg_secp256k1_add_mod_n}
	addi a0, s0, 0
	addi a1, zero, 736
	addi a2, zero, 672
	addi a3, zero, 704
	call {vg_secp256k1_sub_mod_n}
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

vg_ecdsa_secp256k1_sign:
	.option push
	.option arch, +m, +c
	ld t2, 24(a5)
	addi t3, t2, 0
	beqz t3, 20f
	addi t3, t2, -1
	beqz t3, 22f
	addi t3, t2, -2
	beqz t3, 24f
	addi t3, t2, -3
	beqz t3, 26f
	addi t3, t2, -4
	beqz t3, 28f
	addi t3, t2, -5
	beqz t3, 210f
	addi t3, t2, -6
	beqz t3, 212f
	addi sp, sp, -224
	addi t0, sp, 0
	sd ra, 0(t0)
	sd s0, 8(t0)
	sd s1, 16(t0)
	sd s2, 24(t0)
	sd s3, 32(t0)
	sd s4, 40(t0)
	sd s5, 48(t0)
	sd s6, 56(t0)
	addi s1, t0, 0
	addi s2, a0, 0
	addi s3, a1, 0
	addi s4, a2, 0
	addi s0, a4, 0
	addi s6, a5, 0
	lbu t0, 0(s4)
	slli t0, t0, 8
	lbu t1, 1(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 2(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 3(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 4(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 5(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 6(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 7(s4)
	or t0, t0, t1
	sd t0, 24(s0)
	lbu t0, 8(s4)
	slli t0, t0, 8
	lbu t1, 9(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 10(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 11(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 12(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 13(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 14(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 15(s4)
	or t0, t0, t1
	sd t0, 16(s0)
	lbu t0, 16(s4)
	slli t0, t0, 8
	lbu t1, 17(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 18(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 19(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 20(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 21(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 22(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 23(s4)
	or t0, t0, t1
	sd t0, 8(s0)
	lbu t0, 24(s4)
	slli t0, t0, 8
	lbu t1, 25(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 26(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 27(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 28(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 29(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 30(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 31(s4)
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
	call {vg_secp256k1_add_mod_n}
	addi a7, zero, -1
	ld t0, 88(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 192(s1)
	srli t1, t0, 48
	sb t1, 193(s1)
	srli t1, t0, 40
	sb t1, 194(s1)
	srli t1, t0, 32
	sb t1, 195(s1)
	srli t1, t0, 24
	sb t1, 196(s1)
	srli t1, t0, 16
	sb t1, 197(s1)
	srli t1, t0, 8
	sb t1, 198(s1)
	srli t1, t0, 0
	sb t1, 199(s1)
	ld t0, 80(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 200(s1)
	srli t1, t0, 48
	sb t1, 201(s1)
	srli t1, t0, 40
	sb t1, 202(s1)
	srli t1, t0, 32
	sb t1, 203(s1)
	srli t1, t0, 24
	sb t1, 204(s1)
	srli t1, t0, 16
	sb t1, 205(s1)
	srli t1, t0, 8
	sb t1, 206(s1)
	srli t1, t0, 0
	sb t1, 207(s1)
	ld t0, 72(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 208(s1)
	srli t1, t0, 48
	sb t1, 209(s1)
	srli t1, t0, 40
	sb t1, 210(s1)
	srli t1, t0, 32
	sb t1, 211(s1)
	srli t1, t0, 24
	sb t1, 212(s1)
	srli t1, t0, 16
	sb t1, 213(s1)
	srli t1, t0, 8
	sb t1, 214(s1)
	srli t1, t0, 0
	sb t1, 215(s1)
	ld t0, 64(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 216(s1)
	srli t1, t0, 48
	sb t1, 217(s1)
	srli t1, t0, 40
	sb t1, 218(s1)
	srli t1, t0, 32
	sb t1, 219(s1)
	srli t1, t0, 24
	sb t1, 220(s1)
	srli t1, t0, 16
	sb t1, 221(s1)
	srli t1, t0, 8
	sb t1, 222(s1)
	srli t1, t0, 0
	sb t1, 223(s1)
	addi t0, zero, 0
	sb t0, 64(s1)
	addi t0, zero, 0
	sb t0, 65(s1)
	addi t0, zero, 0
	sb t0, 66(s1)
	addi t0, zero, 0
	sb t0, 67(s1)
	addi t0, zero, 0
	sb t0, 68(s1)
	addi t0, zero, 0
	sb t0, 69(s1)
	addi t0, zero, 0
	sb t0, 70(s1)
	addi t0, zero, 0
	sb t0, 71(s1)
	addi t0, zero, 0
	sb t0, 72(s1)
	addi t0, zero, 0
	sb t0, 73(s1)
	addi t0, zero, 0
	sb t0, 74(s1)
	addi t0, zero, 0
	sb t0, 75(s1)
	addi t0, zero, 0
	sb t0, 76(s1)
	addi t0, zero, 0
	sb t0, 77(s1)
	addi t0, zero, 0
	sb t0, 78(s1)
	addi t0, zero, 0
	sb t0, 79(s1)
	addi t0, zero, 0
	sb t0, 80(s1)
	addi t0, zero, 0
	sb t0, 81(s1)
	addi t0, zero, 0
	sb t0, 82(s1)
	addi t0, zero, 0
	sb t0, 83(s1)
	addi t0, zero, 0
	sb t0, 84(s1)
	addi t0, zero, 0
	sb t0, 85(s1)
	addi t0, zero, 0
	sb t0, 86(s1)
	addi t0, zero, 0
	sb t0, 87(s1)
	addi t0, zero, 0
	sb t0, 88(s1)
	addi t0, zero, 0
	sb t0, 89(s1)
	addi t0, zero, 0
	sb t0, 90(s1)
	addi t0, zero, 0
	sb t0, 91(s1)
	addi t0, zero, 0
	sb t0, 92(s1)
	addi t0, zero, 0
	sb t0, 93(s1)
	addi t0, zero, 0
	sb t0, 94(s1)
	addi t0, zero, 0
	sb t0, 95(s1)
	addi t0, zero, 1
	sb t0, 128(s1)
	addi t0, zero, 1
	sb t0, 129(s1)
	addi t0, zero, 1
	sb t0, 130(s1)
	addi t0, zero, 1
	sb t0, 131(s1)
	addi t0, zero, 1
	sb t0, 132(s1)
	addi t0, zero, 1
	sb t0, 133(s1)
	addi t0, zero, 1
	sb t0, 134(s1)
	addi t0, zero, 1
	sb t0, 135(s1)
	addi t0, zero, 1
	sb t0, 136(s1)
	addi t0, zero, 1
	sb t0, 137(s1)
	addi t0, zero, 1
	sb t0, 138(s1)
	addi t0, zero, 1
	sb t0, 139(s1)
	addi t0, zero, 1
	sb t0, 140(s1)
	addi t0, zero, 1
	sb t0, 141(s1)
	addi t0, zero, 1
	sb t0, 142(s1)
	addi t0, zero, 1
	sb t0, 143(s1)
	addi t0, zero, 1
	sb t0, 144(s1)
	addi t0, zero, 1
	sb t0, 145(s1)
	addi t0, zero, 1
	sb t0, 146(s1)
	addi t0, zero, 1
	sb t0, 147(s1)
	addi t0, zero, 1
	sb t0, 148(s1)
	addi t0, zero, 1
	sb t0, 149(s1)
	addi t0, zero, 1
	sb t0, 150(s1)
	addi t0, zero, 1
	sb t0, 151(s1)
	addi t0, zero, 1
	sb t0, 152(s1)
	addi t0, zero, 1
	sb t0, 153(s1)
	addi t0, zero, 1
	sb t0, 154(s1)
	addi t0, zero, 1
	sb t0, 155(s1)
	addi t0, zero, 1
	sb t0, 156(s1)
	addi t0, zero, 1
	sb t0, 157(s1)
	addi t0, zero, 1
	sb t0, 158(s1)
	addi t0, zero, 1
	sb t0, 159(s1)
	addi t0, zero, 0
	sb t0, 160(s1)
	addi a0, s0, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi t5, zero, 54
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	lwu t1, 92(s1)
	xor t1, t1, t5
	sw t1, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	sw t5, 448(s0)
	sw t5, 452(s0)
	sw t5, 456(s0)
	sw t5, 460(s0)
	sw t5, 464(s0)
	sw t5, 468(s0)
	sw t5, 472(s0)
	sw t5, 476(s0)
	sw t5, 480(s0)
	sw t5, 484(s0)
	sw t5, 488(s0)
	sw t5, 492(s0)
	sw t5, 496(s0)
	sw t5, 500(s0)
	sw t5, 504(s0)
	sw t5, 508(s0)
	addi a0, s0, 0
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 128
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi t5, zero, 92
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	lwu t1, 92(s1)
	xor t1, t1, t5
	sw t1, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	sw t5, 448(s0)
	sw t5, 452(s0)
	sw t5, 456(s0)
	sw t5, 460(s0)
	sw t5, 464(s0)
	sw t5, 468(s0)
	sw t5, 472(s0)
	sw t5, 476(s0)
	sw t5, 480(s0)
	sw t5, 484(s0)
	sw t5, 488(s0)
	sw t5, 492(s0)
	sw t5, 496(s0)
	sw t5, 500(s0)
	sw t5, 504(s0)
	sw t5, 508(s0)
	addi a0, s0, 192
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 128
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 128
	addi a2, s1, 128
	addi a3, zero, 33
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 161
	addi a2, s3, 0
	addi a3, zero, 32
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 193
	addi a2, s1, 192
	addi a3, zero, 32
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 225
	addi a2, s0, 512
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 128
	addi a2, s0, 512
	addi a3, zero, 32
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 160
	addi a2, s1, 64
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi t5, zero, 54
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	lwu t1, 92(s1)
	xor t1, t1, t5
	sw t1, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	sw t5, 448(s0)
	sw t5, 452(s0)
	sw t5, 456(s0)
	sw t5, 460(s0)
	sw t5, 464(s0)
	sw t5, 468(s0)
	sw t5, 472(s0)
	sw t5, 476(s0)
	sw t5, 480(s0)
	sw t5, 484(s0)
	sw t5, 488(s0)
	sw t5, 492(s0)
	sw t5, 496(s0)
	sw t5, 500(s0)
	sw t5, 504(s0)
	sw t5, 508(s0)
	addi a0, s0, 0
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 128
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi t5, zero, 92
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	lwu t1, 92(s1)
	xor t1, t1, t5
	sw t1, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	sw t5, 448(s0)
	sw t5, 452(s0)
	sw t5, 456(s0)
	sw t5, 460(s0)
	sw t5, 464(s0)
	sw t5, 468(s0)
	sw t5, 472(s0)
	sw t5, 476(s0)
	sw t5, 480(s0)
	sw t5, 484(s0)
	sw t5, 488(s0)
	sw t5, 492(s0)
	sw t5, 496(s0)
	sw t5, 500(s0)
	sw t5, 504(s0)
	sw t5, 508(s0)
	addi a0, s0, 192
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 128
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 128
	addi a2, s1, 128
	addi a3, zero, 32
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 160
	addi a2, s0, 512
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 128
	addi a2, s0, 512
	addi a3, zero, 32
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 160
	addi a2, s1, 128
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi t0, zero, 1
	sb t0, 160(s1)
	addi a0, s0, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi t5, zero, 54
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	lwu t1, 92(s1)
	xor t1, t1, t5
	sw t1, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	sw t5, 448(s0)
	sw t5, 452(s0)
	sw t5, 456(s0)
	sw t5, 460(s0)
	sw t5, 464(s0)
	sw t5, 468(s0)
	sw t5, 472(s0)
	sw t5, 476(s0)
	sw t5, 480(s0)
	sw t5, 484(s0)
	sw t5, 488(s0)
	sw t5, 492(s0)
	sw t5, 496(s0)
	sw t5, 500(s0)
	sw t5, 504(s0)
	sw t5, 508(s0)
	addi a0, s0, 0
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 128
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi t5, zero, 92
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	lwu t1, 92(s1)
	xor t1, t1, t5
	sw t1, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	sw t5, 448(s0)
	sw t5, 452(s0)
	sw t5, 456(s0)
	sw t5, 460(s0)
	sw t5, 464(s0)
	sw t5, 468(s0)
	sw t5, 472(s0)
	sw t5, 476(s0)
	sw t5, 480(s0)
	sw t5, 484(s0)
	sw t5, 488(s0)
	sw t5, 492(s0)
	sw t5, 496(s0)
	sw t5, 500(s0)
	sw t5, 504(s0)
	sw t5, 508(s0)
	addi a0, s0, 192
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 128
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 128
	addi a2, s1, 128
	addi a3, zero, 33
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 161
	addi a2, s3, 0
	addi a3, zero, 32
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 193
	addi a2, s1, 192
	addi a3, zero, 32
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 225
	addi a2, s0, 512
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 128
	addi a2, s0, 512
	addi a3, zero, 32
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 160
	addi a2, s1, 64
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi t5, zero, 54
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	lwu t1, 92(s1)
	xor t1, t1, t5
	sw t1, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	sw t5, 448(s0)
	sw t5, 452(s0)
	sw t5, 456(s0)
	sw t5, 460(s0)
	sw t5, 464(s0)
	sw t5, 468(s0)
	sw t5, 472(s0)
	sw t5, 476(s0)
	sw t5, 480(s0)
	sw t5, 484(s0)
	sw t5, 488(s0)
	sw t5, 492(s0)
	sw t5, 496(s0)
	sw t5, 500(s0)
	sw t5, 504(s0)
	sw t5, 508(s0)
	addi a0, s0, 0
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 128
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi t5, zero, 92
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	lwu t1, 92(s1)
	xor t1, t1, t5
	sw t1, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	sw t5, 448(s0)
	sw t5, 452(s0)
	sw t5, 456(s0)
	sw t5, 460(s0)
	sw t5, 464(s0)
	sw t5, 468(s0)
	sw t5, 472(s0)
	sw t5, 476(s0)
	sw t5, 480(s0)
	sw t5, 484(s0)
	sw t5, 488(s0)
	sw t5, 492(s0)
	sw t5, 496(s0)
	sw t5, 500(s0)
	sw t5, 504(s0)
	sw t5, 508(s0)
	addi a0, s0, 192
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 128
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 128
	addi a2, s1, 128
	addi a3, zero, 32
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 160
	addi a2, s0, 512
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 128
	addi a2, s0, 512
	addi a3, zero, 32
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 160
	addi a2, s1, 128
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi s5, zero, 8
214:
	addi a0, s0, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi t5, zero, 54
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	lwu t1, 92(s1)
	xor t1, t1, t5
	sw t1, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	sw t5, 448(s0)
	sw t5, 452(s0)
	sw t5, 456(s0)
	sw t5, 460(s0)
	sw t5, 464(s0)
	sw t5, 468(s0)
	sw t5, 472(s0)
	sw t5, 476(s0)
	sw t5, 480(s0)
	sw t5, 484(s0)
	sw t5, 488(s0)
	sw t5, 492(s0)
	sw t5, 496(s0)
	sw t5, 500(s0)
	sw t5, 504(s0)
	sw t5, 508(s0)
	addi a0, s0, 0
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 128
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi t5, zero, 92
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	lwu t1, 92(s1)
	xor t1, t1, t5
	sw t1, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	sw t5, 448(s0)
	sw t5, 452(s0)
	sw t5, 456(s0)
	sw t5, 460(s0)
	sw t5, 464(s0)
	sw t5, 468(s0)
	sw t5, 472(s0)
	sw t5, 476(s0)
	sw t5, 480(s0)
	sw t5, 484(s0)
	sw t5, 488(s0)
	sw t5, 492(s0)
	sw t5, 496(s0)
	sw t5, 500(s0)
	sw t5, 504(s0)
	sw t5, 508(s0)
	addi a0, s0, 192
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 128
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 128
	addi a2, s1, 128
	addi a3, zero, 32
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 160
	addi a2, s0, 512
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 128
	addi a2, s0, 512
	addi a3, zero, 32
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 160
	addi a2, s1, 128
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s2, 0
	addi a1, s3, 0
	addi a2, s4, 0
	addi a3, s1, 128
	addi a4, s0, 0
	call {vg_ecdsa_secp256k1_sign_k}
	addi s5, s5, -1
	andi t0, a0, 1
	addi t0, t0, -1
	and t6, t0, s5
	bnez t6, 215f
	addi t6, zero, 0
	j 216f
215:
	addi t0, zero, 0
	sb t0, 160(s1)
	addi a0, s0, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi t5, zero, 54
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	lwu t1, 92(s1)
	xor t1, t1, t5
	sw t1, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	sw t5, 448(s0)
	sw t5, 452(s0)
	sw t5, 456(s0)
	sw t5, 460(s0)
	sw t5, 464(s0)
	sw t5, 468(s0)
	sw t5, 472(s0)
	sw t5, 476(s0)
	sw t5, 480(s0)
	sw t5, 484(s0)
	sw t5, 488(s0)
	sw t5, 492(s0)
	sw t5, 496(s0)
	sw t5, 500(s0)
	sw t5, 504(s0)
	sw t5, 508(s0)
	addi a0, s0, 0
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 128
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi t5, zero, 92
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	lwu t1, 92(s1)
	xor t1, t1, t5
	sw t1, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	sw t5, 448(s0)
	sw t5, 452(s0)
	sw t5, 456(s0)
	sw t5, 460(s0)
	sw t5, 464(s0)
	sw t5, 468(s0)
	sw t5, 472(s0)
	sw t5, 476(s0)
	sw t5, 480(s0)
	sw t5, 484(s0)
	sw t5, 488(s0)
	sw t5, 492(s0)
	sw t5, 496(s0)
	sw t5, 500(s0)
	sw t5, 504(s0)
	sw t5, 508(s0)
	addi a0, s0, 192
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 128
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 128
	addi a2, s1, 128
	addi a3, zero, 33
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 161
	addi a2, s0, 512
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 128
	addi a2, s0, 512
	addi a3, zero, 32
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 160
	addi a2, s1, 64
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi t5, zero, 54
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	lwu t1, 92(s1)
	xor t1, t1, t5
	sw t1, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	sw t5, 448(s0)
	sw t5, 452(s0)
	sw t5, 456(s0)
	sw t5, 460(s0)
	sw t5, 464(s0)
	sw t5, 468(s0)
	sw t5, 472(s0)
	sw t5, 476(s0)
	sw t5, 480(s0)
	sw t5, 484(s0)
	sw t5, 488(s0)
	sw t5, 492(s0)
	sw t5, 496(s0)
	sw t5, 500(s0)
	sw t5, 504(s0)
	sw t5, 508(s0)
	addi a0, s0, 0
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 128
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi t5, zero, 92
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	lwu t1, 92(s1)
	xor t1, t1, t5
	sw t1, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	sw t5, 448(s0)
	sw t5, 452(s0)
	sw t5, 456(s0)
	sw t5, 460(s0)
	sw t5, 464(s0)
	sw t5, 468(s0)
	sw t5, 472(s0)
	sw t5, 476(s0)
	sw t5, 480(s0)
	sw t5, 484(s0)
	sw t5, 488(s0)
	sw t5, 492(s0)
	sw t5, 496(s0)
	sw t5, 500(s0)
	sw t5, 504(s0)
	sw t5, 508(s0)
	addi a0, s0, 192
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 128
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 128
	addi a2, s1, 128
	addi a3, zero, 32
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 160
	addi a2, s0, 512
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 128
	addi a2, s0, 512
	addi a3, zero, 32
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 160
	addi a2, s1, 128
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi t6, zero, 1
216:
	bnez t6, 214b
	addi t0, zero, 0
	sd t0, 64(s1)
	sd t0, 72(s1)
	sd t0, 80(s1)
	sd t0, 88(s1)
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
	ld ra, 0(s1)
	ld s0, 8(s1)
	ld s2, 24(s1)
	ld s3, 32(s1)
	ld s4, 40(s1)
	ld s5, 48(s1)
	ld s6, 56(s1)
	ld s1, 16(s1)
	addi sp, sp, 224
	j 213f
212:
	addi sp, sp, -256
	addi t0, sp, 0
	sd ra, 0(t0)
	sd s0, 8(t0)
	sd s1, 16(t0)
	sd s2, 24(t0)
	sd s3, 32(t0)
	sd s4, 40(t0)
	sd s5, 48(t0)
	sd s6, 56(t0)
	addi s1, t0, 0
	addi s2, a0, 0
	addi s3, a1, 0
	addi s4, a2, 0
	addi s0, a4, 0
	addi s6, a5, 0
	addi t0, zero, 0
	sb t0, 192(s1)
	addi t0, zero, 0
	sb t0, 193(s1)
	addi t0, zero, 0
	sb t0, 194(s1)
	addi t0, zero, 0
	sb t0, 195(s1)
	lbu t0, 0(s4)
	sb t0, 196(s1)
	lbu t0, 1(s4)
	sb t0, 197(s1)
	lbu t0, 2(s4)
	sb t0, 198(s1)
	lbu t0, 3(s4)
	sb t0, 199(s1)
	lbu t0, 4(s4)
	sb t0, 200(s1)
	lbu t0, 5(s4)
	sb t0, 201(s1)
	lbu t0, 6(s4)
	sb t0, 202(s1)
	lbu t0, 7(s4)
	sb t0, 203(s1)
	lbu t0, 8(s4)
	sb t0, 204(s1)
	lbu t0, 9(s4)
	sb t0, 205(s1)
	lbu t0, 10(s4)
	sb t0, 206(s1)
	lbu t0, 11(s4)
	sb t0, 207(s1)
	lbu t0, 12(s4)
	sb t0, 208(s1)
	lbu t0, 13(s4)
	sb t0, 209(s1)
	lbu t0, 14(s4)
	sb t0, 210(s1)
	lbu t0, 15(s4)
	sb t0, 211(s1)
	lbu t0, 16(s4)
	sb t0, 212(s1)
	lbu t0, 17(s4)
	sb t0, 213(s1)
	lbu t0, 18(s4)
	sb t0, 214(s1)
	lbu t0, 19(s4)
	sb t0, 215(s1)
	lbu t0, 20(s4)
	sb t0, 216(s1)
	lbu t0, 21(s4)
	sb t0, 217(s1)
	lbu t0, 22(s4)
	sb t0, 218(s1)
	lbu t0, 23(s4)
	sb t0, 219(s1)
	lbu t0, 24(s4)
	sb t0, 220(s1)
	lbu t0, 25(s4)
	sb t0, 221(s1)
	lbu t0, 26(s4)
	sb t0, 222(s1)
	lbu t0, 27(s4)
	sb t0, 223(s1)
	addi t0, zero, 0
	sb t0, 64(s1)
	addi t0, zero, 0
	sb t0, 65(s1)
	addi t0, zero, 0
	sb t0, 66(s1)
	addi t0, zero, 0
	sb t0, 67(s1)
	addi t0, zero, 0
	sb t0, 68(s1)
	addi t0, zero, 0
	sb t0, 69(s1)
	addi t0, zero, 0
	sb t0, 70(s1)
	addi t0, zero, 0
	sb t0, 71(s1)
	addi t0, zero, 0
	sb t0, 72(s1)
	addi t0, zero, 0
	sb t0, 73(s1)
	addi t0, zero, 0
	sb t0, 74(s1)
	addi t0, zero, 0
	sb t0, 75(s1)
	addi t0, zero, 0
	sb t0, 76(s1)
	addi t0, zero, 0
	sb t0, 77(s1)
	addi t0, zero, 0
	sb t0, 78(s1)
	addi t0, zero, 0
	sb t0, 79(s1)
	addi t0, zero, 0
	sb t0, 80(s1)
	addi t0, zero, 0
	sb t0, 81(s1)
	addi t0, zero, 0
	sb t0, 82(s1)
	addi t0, zero, 0
	sb t0, 83(s1)
	addi t0, zero, 0
	sb t0, 84(s1)
	addi t0, zero, 0
	sb t0, 85(s1)
	addi t0, zero, 0
	sb t0, 86(s1)
	addi t0, zero, 0
	sb t0, 87(s1)
	addi t0, zero, 0
	sb t0, 88(s1)
	addi t0, zero, 0
	sb t0, 89(s1)
	addi t0, zero, 0
	sb t0, 90(s1)
	addi t0, zero, 0
	sb t0, 91(s1)
	addi t0, zero, 1
	sb t0, 128(s1)
	addi t0, zero, 1
	sb t0, 129(s1)
	addi t0, zero, 1
	sb t0, 130(s1)
	addi t0, zero, 1
	sb t0, 131(s1)
	addi t0, zero, 1
	sb t0, 132(s1)
	addi t0, zero, 1
	sb t0, 133(s1)
	addi t0, zero, 1
	sb t0, 134(s1)
	addi t0, zero, 1
	sb t0, 135(s1)
	addi t0, zero, 1
	sb t0, 136(s1)
	addi t0, zero, 1
	sb t0, 137(s1)
	addi t0, zero, 1
	sb t0, 138(s1)
	addi t0, zero, 1
	sb t0, 139(s1)
	addi t0, zero, 1
	sb t0, 140(s1)
	addi t0, zero, 1
	sb t0, 141(s1)
	addi t0, zero, 1
	sb t0, 142(s1)
	addi t0, zero, 1
	sb t0, 143(s1)
	addi t0, zero, 1
	sb t0, 144(s1)
	addi t0, zero, 1
	sb t0, 145(s1)
	addi t0, zero, 1
	sb t0, 146(s1)
	addi t0, zero, 1
	sb t0, 147(s1)
	addi t0, zero, 1
	sb t0, 148(s1)
	addi t0, zero, 1
	sb t0, 149(s1)
	addi t0, zero, 1
	sb t0, 150(s1)
	addi t0, zero, 1
	sb t0, 151(s1)
	addi t0, zero, 1
	sb t0, 152(s1)
	addi t0, zero, 1
	sb t0, 153(s1)
	addi t0, zero, 1
	sb t0, 154(s1)
	addi t0, zero, 1
	sb t0, 155(s1)
	addi t0, zero, 0
	sb t0, 156(s1)
	addi a0, s0, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi t5, zero, 54
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	sw t5, 448(s0)
	sw t5, 452(s0)
	sw t5, 456(s0)
	sw t5, 460(s0)
	sw t5, 464(s0)
	sw t5, 468(s0)
	sw t5, 472(s0)
	sw t5, 476(s0)
	sw t5, 480(s0)
	sw t5, 484(s0)
	sw t5, 488(s0)
	sw t5, 492(s0)
	sw t5, 496(s0)
	sw t5, 500(s0)
	sw t5, 504(s0)
	sw t5, 508(s0)
	addi a0, s0, 0
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 128
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi t5, zero, 92
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	sw t5, 448(s0)
	sw t5, 452(s0)
	sw t5, 456(s0)
	sw t5, 460(s0)
	sw t5, 464(s0)
	sw t5, 468(s0)
	sw t5, 472(s0)
	sw t5, 476(s0)
	sw t5, 480(s0)
	sw t5, 484(s0)
	sw t5, 488(s0)
	sw t5, 492(s0)
	sw t5, 496(s0)
	sw t5, 500(s0)
	sw t5, 504(s0)
	sw t5, 508(s0)
	addi a0, s0, 192
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 128
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 128
	addi a2, s1, 128
	addi a3, zero, 29
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 157
	addi a2, s3, 0
	addi a3, zero, 32
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 189
	addi a2, s1, 192
	addi a3, zero, 32
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 221
	addi a2, s0, 512
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 128
	addi a2, s0, 512
	addi a3, zero, 28
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 156
	addi a2, s1, 64
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi t5, zero, 54
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	sw t5, 448(s0)
	sw t5, 452(s0)
	sw t5, 456(s0)
	sw t5, 460(s0)
	sw t5, 464(s0)
	sw t5, 468(s0)
	sw t5, 472(s0)
	sw t5, 476(s0)
	sw t5, 480(s0)
	sw t5, 484(s0)
	sw t5, 488(s0)
	sw t5, 492(s0)
	sw t5, 496(s0)
	sw t5, 500(s0)
	sw t5, 504(s0)
	sw t5, 508(s0)
	addi a0, s0, 0
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 128
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi t5, zero, 92
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	sw t5, 448(s0)
	sw t5, 452(s0)
	sw t5, 456(s0)
	sw t5, 460(s0)
	sw t5, 464(s0)
	sw t5, 468(s0)
	sw t5, 472(s0)
	sw t5, 476(s0)
	sw t5, 480(s0)
	sw t5, 484(s0)
	sw t5, 488(s0)
	sw t5, 492(s0)
	sw t5, 496(s0)
	sw t5, 500(s0)
	sw t5, 504(s0)
	sw t5, 508(s0)
	addi a0, s0, 192
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 128
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 128
	addi a2, s1, 128
	addi a3, zero, 28
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 156
	addi a2, s0, 512
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 128
	addi a2, s0, 512
	addi a3, zero, 28
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 156
	addi a2, s1, 128
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi t0, zero, 1
	sb t0, 156(s1)
	addi a0, s0, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi t5, zero, 54
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	sw t5, 448(s0)
	sw t5, 452(s0)
	sw t5, 456(s0)
	sw t5, 460(s0)
	sw t5, 464(s0)
	sw t5, 468(s0)
	sw t5, 472(s0)
	sw t5, 476(s0)
	sw t5, 480(s0)
	sw t5, 484(s0)
	sw t5, 488(s0)
	sw t5, 492(s0)
	sw t5, 496(s0)
	sw t5, 500(s0)
	sw t5, 504(s0)
	sw t5, 508(s0)
	addi a0, s0, 0
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 128
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi t5, zero, 92
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	sw t5, 448(s0)
	sw t5, 452(s0)
	sw t5, 456(s0)
	sw t5, 460(s0)
	sw t5, 464(s0)
	sw t5, 468(s0)
	sw t5, 472(s0)
	sw t5, 476(s0)
	sw t5, 480(s0)
	sw t5, 484(s0)
	sw t5, 488(s0)
	sw t5, 492(s0)
	sw t5, 496(s0)
	sw t5, 500(s0)
	sw t5, 504(s0)
	sw t5, 508(s0)
	addi a0, s0, 192
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 128
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 128
	addi a2, s1, 128
	addi a3, zero, 29
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 157
	addi a2, s3, 0
	addi a3, zero, 32
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 189
	addi a2, s1, 192
	addi a3, zero, 32
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 221
	addi a2, s0, 512
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 128
	addi a2, s0, 512
	addi a3, zero, 28
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 156
	addi a2, s1, 64
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi t5, zero, 54
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	sw t5, 448(s0)
	sw t5, 452(s0)
	sw t5, 456(s0)
	sw t5, 460(s0)
	sw t5, 464(s0)
	sw t5, 468(s0)
	sw t5, 472(s0)
	sw t5, 476(s0)
	sw t5, 480(s0)
	sw t5, 484(s0)
	sw t5, 488(s0)
	sw t5, 492(s0)
	sw t5, 496(s0)
	sw t5, 500(s0)
	sw t5, 504(s0)
	sw t5, 508(s0)
	addi a0, s0, 0
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 128
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi t5, zero, 92
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	sw t5, 448(s0)
	sw t5, 452(s0)
	sw t5, 456(s0)
	sw t5, 460(s0)
	sw t5, 464(s0)
	sw t5, 468(s0)
	sw t5, 472(s0)
	sw t5, 476(s0)
	sw t5, 480(s0)
	sw t5, 484(s0)
	sw t5, 488(s0)
	sw t5, 492(s0)
	sw t5, 496(s0)
	sw t5, 500(s0)
	sw t5, 504(s0)
	sw t5, 508(s0)
	addi a0, s0, 192
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 128
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 128
	addi a2, s1, 128
	addi a3, zero, 28
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 156
	addi a2, s0, 512
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 128
	addi a2, s0, 512
	addi a3, zero, 28
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 156
	addi a2, s1, 128
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi s5, zero, 8
217:
	addi a0, s0, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi t5, zero, 54
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	sw t5, 448(s0)
	sw t5, 452(s0)
	sw t5, 456(s0)
	sw t5, 460(s0)
	sw t5, 464(s0)
	sw t5, 468(s0)
	sw t5, 472(s0)
	sw t5, 476(s0)
	sw t5, 480(s0)
	sw t5, 484(s0)
	sw t5, 488(s0)
	sw t5, 492(s0)
	sw t5, 496(s0)
	sw t5, 500(s0)
	sw t5, 504(s0)
	sw t5, 508(s0)
	addi a0, s0, 0
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 128
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi t5, zero, 92
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	sw t5, 448(s0)
	sw t5, 452(s0)
	sw t5, 456(s0)
	sw t5, 460(s0)
	sw t5, 464(s0)
	sw t5, 468(s0)
	sw t5, 472(s0)
	sw t5, 476(s0)
	sw t5, 480(s0)
	sw t5, 484(s0)
	sw t5, 488(s0)
	sw t5, 492(s0)
	sw t5, 496(s0)
	sw t5, 500(s0)
	sw t5, 504(s0)
	sw t5, 508(s0)
	addi a0, s0, 192
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 128
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 128
	addi a2, s1, 128
	addi a3, zero, 28
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 156
	addi a2, s0, 512
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 128
	addi a2, s0, 512
	addi a3, zero, 28
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 156
	addi a2, s1, 128
	ld t1, 16(s6)
	jalr ra, 0(t1)
	lbu t0, 128(s1)
	sb t0, 224(s1)
	lbu t0, 129(s1)
	sb t0, 225(s1)
	lbu t0, 130(s1)
	sb t0, 226(s1)
	lbu t0, 131(s1)
	sb t0, 227(s1)
	lbu t0, 132(s1)
	sb t0, 228(s1)
	lbu t0, 133(s1)
	sb t0, 229(s1)
	lbu t0, 134(s1)
	sb t0, 230(s1)
	lbu t0, 135(s1)
	sb t0, 231(s1)
	lbu t0, 136(s1)
	sb t0, 232(s1)
	lbu t0, 137(s1)
	sb t0, 233(s1)
	lbu t0, 138(s1)
	sb t0, 234(s1)
	lbu t0, 139(s1)
	sb t0, 235(s1)
	lbu t0, 140(s1)
	sb t0, 236(s1)
	lbu t0, 141(s1)
	sb t0, 237(s1)
	lbu t0, 142(s1)
	sb t0, 238(s1)
	lbu t0, 143(s1)
	sb t0, 239(s1)
	lbu t0, 144(s1)
	sb t0, 240(s1)
	lbu t0, 145(s1)
	sb t0, 241(s1)
	lbu t0, 146(s1)
	sb t0, 242(s1)
	lbu t0, 147(s1)
	sb t0, 243(s1)
	lbu t0, 148(s1)
	sb t0, 244(s1)
	lbu t0, 149(s1)
	sb t0, 245(s1)
	lbu t0, 150(s1)
	sb t0, 246(s1)
	lbu t0, 151(s1)
	sb t0, 247(s1)
	lbu t0, 152(s1)
	sb t0, 248(s1)
	lbu t0, 153(s1)
	sb t0, 249(s1)
	lbu t0, 154(s1)
	sb t0, 250(s1)
	lbu t0, 155(s1)
	sb t0, 251(s1)
	addi a0, s0, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi t5, zero, 54
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	sw t5, 448(s0)
	sw t5, 452(s0)
	sw t5, 456(s0)
	sw t5, 460(s0)
	sw t5, 464(s0)
	sw t5, 468(s0)
	sw t5, 472(s0)
	sw t5, 476(s0)
	sw t5, 480(s0)
	sw t5, 484(s0)
	sw t5, 488(s0)
	sw t5, 492(s0)
	sw t5, 496(s0)
	sw t5, 500(s0)
	sw t5, 504(s0)
	sw t5, 508(s0)
	addi a0, s0, 0
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 128
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi t5, zero, 92
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	sw t5, 448(s0)
	sw t5, 452(s0)
	sw t5, 456(s0)
	sw t5, 460(s0)
	sw t5, 464(s0)
	sw t5, 468(s0)
	sw t5, 472(s0)
	sw t5, 476(s0)
	sw t5, 480(s0)
	sw t5, 484(s0)
	sw t5, 488(s0)
	sw t5, 492(s0)
	sw t5, 496(s0)
	sw t5, 500(s0)
	sw t5, 504(s0)
	sw t5, 508(s0)
	addi a0, s0, 192
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 128
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 128
	addi a2, s1, 128
	addi a3, zero, 28
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 156
	addi a2, s0, 512
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 128
	addi a2, s0, 512
	addi a3, zero, 28
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 156
	addi a2, s1, 128
	ld t1, 16(s6)
	jalr ra, 0(t1)
	lbu t0, 128(s1)
	sb t0, 252(s1)
	lbu t0, 129(s1)
	sb t0, 253(s1)
	lbu t0, 130(s1)
	sb t0, 254(s1)
	lbu t0, 131(s1)
	sb t0, 255(s1)
	addi a0, s2, 0
	addi a1, s3, 0
	addi a2, s1, 192
	addi a3, s1, 224
	addi a4, s0, 0
	call {vg_ecdsa_secp256k1_sign_k}
	addi s5, s5, -1
	andi t0, a0, 1
	addi t0, t0, -1
	and t6, t0, s5
	bnez t6, 218f
	addi t6, zero, 0
	j 219f
218:
	addi t0, zero, 0
	sb t0, 156(s1)
	addi a0, s0, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi t5, zero, 54
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	sw t5, 448(s0)
	sw t5, 452(s0)
	sw t5, 456(s0)
	sw t5, 460(s0)
	sw t5, 464(s0)
	sw t5, 468(s0)
	sw t5, 472(s0)
	sw t5, 476(s0)
	sw t5, 480(s0)
	sw t5, 484(s0)
	sw t5, 488(s0)
	sw t5, 492(s0)
	sw t5, 496(s0)
	sw t5, 500(s0)
	sw t5, 504(s0)
	sw t5, 508(s0)
	addi a0, s0, 0
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 128
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi t5, zero, 92
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	sw t5, 448(s0)
	sw t5, 452(s0)
	sw t5, 456(s0)
	sw t5, 460(s0)
	sw t5, 464(s0)
	sw t5, 468(s0)
	sw t5, 472(s0)
	sw t5, 476(s0)
	sw t5, 480(s0)
	sw t5, 484(s0)
	sw t5, 488(s0)
	sw t5, 492(s0)
	sw t5, 496(s0)
	sw t5, 500(s0)
	sw t5, 504(s0)
	sw t5, 508(s0)
	addi a0, s0, 192
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 128
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 128
	addi a2, s1, 128
	addi a3, zero, 29
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 157
	addi a2, s0, 512
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 128
	addi a2, s0, 512
	addi a3, zero, 28
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 156
	addi a2, s1, 64
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi t5, zero, 54
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	sw t5, 448(s0)
	sw t5, 452(s0)
	sw t5, 456(s0)
	sw t5, 460(s0)
	sw t5, 464(s0)
	sw t5, 468(s0)
	sw t5, 472(s0)
	sw t5, 476(s0)
	sw t5, 480(s0)
	sw t5, 484(s0)
	sw t5, 488(s0)
	sw t5, 492(s0)
	sw t5, 496(s0)
	sw t5, 500(s0)
	sw t5, 504(s0)
	sw t5, 508(s0)
	addi a0, s0, 0
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 128
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi t5, zero, 92
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	sw t5, 448(s0)
	sw t5, 452(s0)
	sw t5, 456(s0)
	sw t5, 460(s0)
	sw t5, 464(s0)
	sw t5, 468(s0)
	sw t5, 472(s0)
	sw t5, 476(s0)
	sw t5, 480(s0)
	sw t5, 484(s0)
	sw t5, 488(s0)
	sw t5, 492(s0)
	sw t5, 496(s0)
	sw t5, 500(s0)
	sw t5, 504(s0)
	sw t5, 508(s0)
	addi a0, s0, 192
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 128
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 128
	addi a2, s1, 128
	addi a3, zero, 28
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 156
	addi a2, s0, 512
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 128
	addi a2, s0, 512
	addi a3, zero, 28
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 156
	addi a2, s1, 128
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi t6, zero, 1
219:
	bnez t6, 217b
	addi t0, zero, 0
	sd t0, 64(s1)
	sd t0, 72(s1)
	sd t0, 80(s1)
	sd t0, 88(s1)
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
	ld ra, 0(s1)
	ld s0, 8(s1)
	ld s2, 24(s1)
	ld s3, 32(s1)
	ld s4, 40(s1)
	ld s5, 48(s1)
	ld s6, 56(s1)
	ld s1, 16(s1)
	addi sp, sp, 256
213:
	j 211f
210:
	addi sp, sp, -240
	addi t0, sp, 0
	sd ra, 0(t0)
	sd s0, 8(t0)
	sd s1, 16(t0)
	sd s2, 24(t0)
	sd s3, 32(t0)
	sd s4, 40(t0)
	sd s5, 48(t0)
	sd s6, 56(t0)
	addi s1, t0, 0
	addi s2, a0, 0
	addi s3, a1, 0
	addi s4, a2, 0
	addi s0, a4, 0
	addi s6, a5, 0
	lbu t0, 0(s4)
	slli t0, t0, 8
	lbu t1, 1(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 2(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 3(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 4(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 5(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 6(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 7(s4)
	or t0, t0, t1
	sd t0, 24(s0)
	lbu t0, 8(s4)
	slli t0, t0, 8
	lbu t1, 9(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 10(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 11(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 12(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 13(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 14(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 15(s4)
	or t0, t0, t1
	sd t0, 16(s0)
	lbu t0, 16(s4)
	slli t0, t0, 8
	lbu t1, 17(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 18(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 19(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 20(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 21(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 22(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 23(s4)
	or t0, t0, t1
	sd t0, 8(s0)
	lbu t0, 24(s4)
	slli t0, t0, 8
	lbu t1, 25(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 26(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 27(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 28(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 29(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 30(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 31(s4)
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
	call {vg_secp256k1_add_mod_n}
	addi a7, zero, -1
	ld t0, 88(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 208(s1)
	srli t1, t0, 48
	sb t1, 209(s1)
	srli t1, t0, 40
	sb t1, 210(s1)
	srli t1, t0, 32
	sb t1, 211(s1)
	srli t1, t0, 24
	sb t1, 212(s1)
	srli t1, t0, 16
	sb t1, 213(s1)
	srli t1, t0, 8
	sb t1, 214(s1)
	srli t1, t0, 0
	sb t1, 215(s1)
	ld t0, 80(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 216(s1)
	srli t1, t0, 48
	sb t1, 217(s1)
	srli t1, t0, 40
	sb t1, 218(s1)
	srli t1, t0, 32
	sb t1, 219(s1)
	srli t1, t0, 24
	sb t1, 220(s1)
	srli t1, t0, 16
	sb t1, 221(s1)
	srli t1, t0, 8
	sb t1, 222(s1)
	srli t1, t0, 0
	sb t1, 223(s1)
	ld t0, 72(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 224(s1)
	srli t1, t0, 48
	sb t1, 225(s1)
	srli t1, t0, 40
	sb t1, 226(s1)
	srli t1, t0, 32
	sb t1, 227(s1)
	srli t1, t0, 24
	sb t1, 228(s1)
	srli t1, t0, 16
	sb t1, 229(s1)
	srli t1, t0, 8
	sb t1, 230(s1)
	srli t1, t0, 0
	sb t1, 231(s1)
	ld t0, 64(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 232(s1)
	srli t1, t0, 48
	sb t1, 233(s1)
	srli t1, t0, 40
	sb t1, 234(s1)
	srli t1, t0, 32
	sb t1, 235(s1)
	srli t1, t0, 24
	sb t1, 236(s1)
	srli t1, t0, 16
	sb t1, 237(s1)
	srli t1, t0, 8
	sb t1, 238(s1)
	srli t1, t0, 0
	sb t1, 239(s1)
	addi t0, zero, 0
	sb t0, 64(s1)
	addi t0, zero, 0
	sb t0, 65(s1)
	addi t0, zero, 0
	sb t0, 66(s1)
	addi t0, zero, 0
	sb t0, 67(s1)
	addi t0, zero, 0
	sb t0, 68(s1)
	addi t0, zero, 0
	sb t0, 69(s1)
	addi t0, zero, 0
	sb t0, 70(s1)
	addi t0, zero, 0
	sb t0, 71(s1)
	addi t0, zero, 0
	sb t0, 72(s1)
	addi t0, zero, 0
	sb t0, 73(s1)
	addi t0, zero, 0
	sb t0, 74(s1)
	addi t0, zero, 0
	sb t0, 75(s1)
	addi t0, zero, 0
	sb t0, 76(s1)
	addi t0, zero, 0
	sb t0, 77(s1)
	addi t0, zero, 0
	sb t0, 78(s1)
	addi t0, zero, 0
	sb t0, 79(s1)
	addi t0, zero, 0
	sb t0, 80(s1)
	addi t0, zero, 0
	sb t0, 81(s1)
	addi t0, zero, 0
	sb t0, 82(s1)
	addi t0, zero, 0
	sb t0, 83(s1)
	addi t0, zero, 0
	sb t0, 84(s1)
	addi t0, zero, 0
	sb t0, 85(s1)
	addi t0, zero, 0
	sb t0, 86(s1)
	addi t0, zero, 0
	sb t0, 87(s1)
	addi t0, zero, 0
	sb t0, 88(s1)
	addi t0, zero, 0
	sb t0, 89(s1)
	addi t0, zero, 0
	sb t0, 90(s1)
	addi t0, zero, 0
	sb t0, 91(s1)
	addi t0, zero, 0
	sb t0, 92(s1)
	addi t0, zero, 0
	sb t0, 93(s1)
	addi t0, zero, 0
	sb t0, 94(s1)
	addi t0, zero, 0
	sb t0, 95(s1)
	addi t0, zero, 0
	sb t0, 96(s1)
	addi t0, zero, 0
	sb t0, 97(s1)
	addi t0, zero, 0
	sb t0, 98(s1)
	addi t0, zero, 0
	sb t0, 99(s1)
	addi t0, zero, 0
	sb t0, 100(s1)
	addi t0, zero, 0
	sb t0, 101(s1)
	addi t0, zero, 0
	sb t0, 102(s1)
	addi t0, zero, 0
	sb t0, 103(s1)
	addi t0, zero, 0
	sb t0, 104(s1)
	addi t0, zero, 0
	sb t0, 105(s1)
	addi t0, zero, 0
	sb t0, 106(s1)
	addi t0, zero, 0
	sb t0, 107(s1)
	addi t0, zero, 0
	sb t0, 108(s1)
	addi t0, zero, 0
	sb t0, 109(s1)
	addi t0, zero, 0
	sb t0, 110(s1)
	addi t0, zero, 0
	sb t0, 111(s1)
	addi t0, zero, 0
	sb t0, 112(s1)
	addi t0, zero, 0
	sb t0, 113(s1)
	addi t0, zero, 0
	sb t0, 114(s1)
	addi t0, zero, 0
	sb t0, 115(s1)
	addi t0, zero, 0
	sb t0, 116(s1)
	addi t0, zero, 0
	sb t0, 117(s1)
	addi t0, zero, 0
	sb t0, 118(s1)
	addi t0, zero, 0
	sb t0, 119(s1)
	addi t0, zero, 0
	sb t0, 120(s1)
	addi t0, zero, 0
	sb t0, 121(s1)
	addi t0, zero, 0
	sb t0, 122(s1)
	addi t0, zero, 0
	sb t0, 123(s1)
	addi t0, zero, 0
	sb t0, 124(s1)
	addi t0, zero, 0
	sb t0, 125(s1)
	addi t0, zero, 0
	sb t0, 126(s1)
	addi t0, zero, 0
	sb t0, 127(s1)
	addi t0, zero, 1
	sb t0, 128(s1)
	addi t0, zero, 1
	sb t0, 129(s1)
	addi t0, zero, 1
	sb t0, 130(s1)
	addi t0, zero, 1
	sb t0, 131(s1)
	addi t0, zero, 1
	sb t0, 132(s1)
	addi t0, zero, 1
	sb t0, 133(s1)
	addi t0, zero, 1
	sb t0, 134(s1)
	addi t0, zero, 1
	sb t0, 135(s1)
	addi t0, zero, 1
	sb t0, 136(s1)
	addi t0, zero, 1
	sb t0, 137(s1)
	addi t0, zero, 1
	sb t0, 138(s1)
	addi t0, zero, 1
	sb t0, 139(s1)
	addi t0, zero, 1
	sb t0, 140(s1)
	addi t0, zero, 1
	sb t0, 141(s1)
	addi t0, zero, 1
	sb t0, 142(s1)
	addi t0, zero, 1
	sb t0, 143(s1)
	addi t0, zero, 1
	sb t0, 144(s1)
	addi t0, zero, 1
	sb t0, 145(s1)
	addi t0, zero, 1
	sb t0, 146(s1)
	addi t0, zero, 1
	sb t0, 147(s1)
	addi t0, zero, 1
	sb t0, 148(s1)
	addi t0, zero, 1
	sb t0, 149(s1)
	addi t0, zero, 1
	sb t0, 150(s1)
	addi t0, zero, 1
	sb t0, 151(s1)
	addi t0, zero, 1
	sb t0, 152(s1)
	addi t0, zero, 1
	sb t0, 153(s1)
	addi t0, zero, 1
	sb t0, 154(s1)
	addi t0, zero, 1
	sb t0, 155(s1)
	addi t0, zero, 1
	sb t0, 156(s1)
	addi t0, zero, 1
	sb t0, 157(s1)
	addi t0, zero, 1
	sb t0, 158(s1)
	addi t0, zero, 1
	sb t0, 159(s1)
	addi t0, zero, 1
	sb t0, 160(s1)
	addi t0, zero, 1
	sb t0, 161(s1)
	addi t0, zero, 1
	sb t0, 162(s1)
	addi t0, zero, 1
	sb t0, 163(s1)
	addi t0, zero, 1
	sb t0, 164(s1)
	addi t0, zero, 1
	sb t0, 165(s1)
	addi t0, zero, 1
	sb t0, 166(s1)
	addi t0, zero, 1
	sb t0, 167(s1)
	addi t0, zero, 1
	sb t0, 168(s1)
	addi t0, zero, 1
	sb t0, 169(s1)
	addi t0, zero, 1
	sb t0, 170(s1)
	addi t0, zero, 1
	sb t0, 171(s1)
	addi t0, zero, 1
	sb t0, 172(s1)
	addi t0, zero, 1
	sb t0, 173(s1)
	addi t0, zero, 1
	sb t0, 174(s1)
	addi t0, zero, 1
	sb t0, 175(s1)
	addi t0, zero, 1
	sb t0, 176(s1)
	addi t0, zero, 1
	sb t0, 177(s1)
	addi t0, zero, 1
	sb t0, 178(s1)
	addi t0, zero, 1
	sb t0, 179(s1)
	addi t0, zero, 1
	sb t0, 180(s1)
	addi t0, zero, 1
	sb t0, 181(s1)
	addi t0, zero, 1
	sb t0, 182(s1)
	addi t0, zero, 1
	sb t0, 183(s1)
	addi t0, zero, 1
	sb t0, 184(s1)
	addi t0, zero, 1
	sb t0, 185(s1)
	addi t0, zero, 1
	sb t0, 186(s1)
	addi t0, zero, 1
	sb t0, 187(s1)
	addi t0, zero, 1
	sb t0, 188(s1)
	addi t0, zero, 1
	sb t0, 189(s1)
	addi t0, zero, 1
	sb t0, 190(s1)
	addi t0, zero, 1
	sb t0, 191(s1)
	addi t0, zero, 0
	sb t0, 192(s1)
	addi a0, s0, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi t5, zero, 54
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	lwu t1, 92(s1)
	xor t1, t1, t5
	sw t1, 412(s0)
	lwu t1, 96(s1)
	xor t1, t1, t5
	sw t1, 416(s0)
	lwu t1, 100(s1)
	xor t1, t1, t5
	sw t1, 420(s0)
	lwu t1, 104(s1)
	xor t1, t1, t5
	sw t1, 424(s0)
	lwu t1, 108(s1)
	xor t1, t1, t5
	sw t1, 428(s0)
	lwu t1, 112(s1)
	xor t1, t1, t5
	sw t1, 432(s0)
	lwu t1, 116(s1)
	xor t1, t1, t5
	sw t1, 436(s0)
	lwu t1, 120(s1)
	xor t1, t1, t5
	sw t1, 440(s0)
	lwu t1, 124(s1)
	xor t1, t1, t5
	sw t1, 444(s0)
	sw t5, 448(s0)
	sw t5, 452(s0)
	sw t5, 456(s0)
	sw t5, 460(s0)
	sw t5, 464(s0)
	sw t5, 468(s0)
	sw t5, 472(s0)
	sw t5, 476(s0)
	sw t5, 480(s0)
	sw t5, 484(s0)
	sw t5, 488(s0)
	sw t5, 492(s0)
	sw t5, 496(s0)
	sw t5, 500(s0)
	sw t5, 504(s0)
	sw t5, 508(s0)
	addi a0, s0, 0
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 128
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi t5, zero, 92
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	lwu t1, 92(s1)
	xor t1, t1, t5
	sw t1, 412(s0)
	lwu t1, 96(s1)
	xor t1, t1, t5
	sw t1, 416(s0)
	lwu t1, 100(s1)
	xor t1, t1, t5
	sw t1, 420(s0)
	lwu t1, 104(s1)
	xor t1, t1, t5
	sw t1, 424(s0)
	lwu t1, 108(s1)
	xor t1, t1, t5
	sw t1, 428(s0)
	lwu t1, 112(s1)
	xor t1, t1, t5
	sw t1, 432(s0)
	lwu t1, 116(s1)
	xor t1, t1, t5
	sw t1, 436(s0)
	lwu t1, 120(s1)
	xor t1, t1, t5
	sw t1, 440(s0)
	lwu t1, 124(s1)
	xor t1, t1, t5
	sw t1, 444(s0)
	sw t5, 448(s0)
	sw t5, 452(s0)
	sw t5, 456(s0)
	sw t5, 460(s0)
	sw t5, 464(s0)
	sw t5, 468(s0)
	sw t5, 472(s0)
	sw t5, 476(s0)
	sw t5, 480(s0)
	sw t5, 484(s0)
	sw t5, 488(s0)
	sw t5, 492(s0)
	sw t5, 496(s0)
	sw t5, 500(s0)
	sw t5, 504(s0)
	sw t5, 508(s0)
	addi a0, s0, 192
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 128
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 128
	addi a2, s1, 128
	addi a3, zero, 65
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 193
	addi a2, s3, 0
	addi a3, zero, 32
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 225
	addi a2, s1, 208
	addi a3, zero, 32
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 257
	addi a2, s0, 512
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 128
	addi a2, s0, 512
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 192
	addi a2, s1, 64
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi t5, zero, 54
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	lwu t1, 92(s1)
	xor t1, t1, t5
	sw t1, 412(s0)
	lwu t1, 96(s1)
	xor t1, t1, t5
	sw t1, 416(s0)
	lwu t1, 100(s1)
	xor t1, t1, t5
	sw t1, 420(s0)
	lwu t1, 104(s1)
	xor t1, t1, t5
	sw t1, 424(s0)
	lwu t1, 108(s1)
	xor t1, t1, t5
	sw t1, 428(s0)
	lwu t1, 112(s1)
	xor t1, t1, t5
	sw t1, 432(s0)
	lwu t1, 116(s1)
	xor t1, t1, t5
	sw t1, 436(s0)
	lwu t1, 120(s1)
	xor t1, t1, t5
	sw t1, 440(s0)
	lwu t1, 124(s1)
	xor t1, t1, t5
	sw t1, 444(s0)
	sw t5, 448(s0)
	sw t5, 452(s0)
	sw t5, 456(s0)
	sw t5, 460(s0)
	sw t5, 464(s0)
	sw t5, 468(s0)
	sw t5, 472(s0)
	sw t5, 476(s0)
	sw t5, 480(s0)
	sw t5, 484(s0)
	sw t5, 488(s0)
	sw t5, 492(s0)
	sw t5, 496(s0)
	sw t5, 500(s0)
	sw t5, 504(s0)
	sw t5, 508(s0)
	addi a0, s0, 0
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 128
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi t5, zero, 92
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	lwu t1, 92(s1)
	xor t1, t1, t5
	sw t1, 412(s0)
	lwu t1, 96(s1)
	xor t1, t1, t5
	sw t1, 416(s0)
	lwu t1, 100(s1)
	xor t1, t1, t5
	sw t1, 420(s0)
	lwu t1, 104(s1)
	xor t1, t1, t5
	sw t1, 424(s0)
	lwu t1, 108(s1)
	xor t1, t1, t5
	sw t1, 428(s0)
	lwu t1, 112(s1)
	xor t1, t1, t5
	sw t1, 432(s0)
	lwu t1, 116(s1)
	xor t1, t1, t5
	sw t1, 436(s0)
	lwu t1, 120(s1)
	xor t1, t1, t5
	sw t1, 440(s0)
	lwu t1, 124(s1)
	xor t1, t1, t5
	sw t1, 444(s0)
	sw t5, 448(s0)
	sw t5, 452(s0)
	sw t5, 456(s0)
	sw t5, 460(s0)
	sw t5, 464(s0)
	sw t5, 468(s0)
	sw t5, 472(s0)
	sw t5, 476(s0)
	sw t5, 480(s0)
	sw t5, 484(s0)
	sw t5, 488(s0)
	sw t5, 492(s0)
	sw t5, 496(s0)
	sw t5, 500(s0)
	sw t5, 504(s0)
	sw t5, 508(s0)
	addi a0, s0, 192
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 128
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 128
	addi a2, s1, 128
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 192
	addi a2, s0, 512
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 128
	addi a2, s0, 512
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 192
	addi a2, s1, 128
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi t0, zero, 1
	sb t0, 192(s1)
	addi a0, s0, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi t5, zero, 54
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	lwu t1, 92(s1)
	xor t1, t1, t5
	sw t1, 412(s0)
	lwu t1, 96(s1)
	xor t1, t1, t5
	sw t1, 416(s0)
	lwu t1, 100(s1)
	xor t1, t1, t5
	sw t1, 420(s0)
	lwu t1, 104(s1)
	xor t1, t1, t5
	sw t1, 424(s0)
	lwu t1, 108(s1)
	xor t1, t1, t5
	sw t1, 428(s0)
	lwu t1, 112(s1)
	xor t1, t1, t5
	sw t1, 432(s0)
	lwu t1, 116(s1)
	xor t1, t1, t5
	sw t1, 436(s0)
	lwu t1, 120(s1)
	xor t1, t1, t5
	sw t1, 440(s0)
	lwu t1, 124(s1)
	xor t1, t1, t5
	sw t1, 444(s0)
	sw t5, 448(s0)
	sw t5, 452(s0)
	sw t5, 456(s0)
	sw t5, 460(s0)
	sw t5, 464(s0)
	sw t5, 468(s0)
	sw t5, 472(s0)
	sw t5, 476(s0)
	sw t5, 480(s0)
	sw t5, 484(s0)
	sw t5, 488(s0)
	sw t5, 492(s0)
	sw t5, 496(s0)
	sw t5, 500(s0)
	sw t5, 504(s0)
	sw t5, 508(s0)
	addi a0, s0, 0
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 128
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi t5, zero, 92
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	lwu t1, 92(s1)
	xor t1, t1, t5
	sw t1, 412(s0)
	lwu t1, 96(s1)
	xor t1, t1, t5
	sw t1, 416(s0)
	lwu t1, 100(s1)
	xor t1, t1, t5
	sw t1, 420(s0)
	lwu t1, 104(s1)
	xor t1, t1, t5
	sw t1, 424(s0)
	lwu t1, 108(s1)
	xor t1, t1, t5
	sw t1, 428(s0)
	lwu t1, 112(s1)
	xor t1, t1, t5
	sw t1, 432(s0)
	lwu t1, 116(s1)
	xor t1, t1, t5
	sw t1, 436(s0)
	lwu t1, 120(s1)
	xor t1, t1, t5
	sw t1, 440(s0)
	lwu t1, 124(s1)
	xor t1, t1, t5
	sw t1, 444(s0)
	sw t5, 448(s0)
	sw t5, 452(s0)
	sw t5, 456(s0)
	sw t5, 460(s0)
	sw t5, 464(s0)
	sw t5, 468(s0)
	sw t5, 472(s0)
	sw t5, 476(s0)
	sw t5, 480(s0)
	sw t5, 484(s0)
	sw t5, 488(s0)
	sw t5, 492(s0)
	sw t5, 496(s0)
	sw t5, 500(s0)
	sw t5, 504(s0)
	sw t5, 508(s0)
	addi a0, s0, 192
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 128
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 128
	addi a2, s1, 128
	addi a3, zero, 65
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 193
	addi a2, s3, 0
	addi a3, zero, 32
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 225
	addi a2, s1, 208
	addi a3, zero, 32
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 257
	addi a2, s0, 512
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 128
	addi a2, s0, 512
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 192
	addi a2, s1, 64
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi t5, zero, 54
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	lwu t1, 92(s1)
	xor t1, t1, t5
	sw t1, 412(s0)
	lwu t1, 96(s1)
	xor t1, t1, t5
	sw t1, 416(s0)
	lwu t1, 100(s1)
	xor t1, t1, t5
	sw t1, 420(s0)
	lwu t1, 104(s1)
	xor t1, t1, t5
	sw t1, 424(s0)
	lwu t1, 108(s1)
	xor t1, t1, t5
	sw t1, 428(s0)
	lwu t1, 112(s1)
	xor t1, t1, t5
	sw t1, 432(s0)
	lwu t1, 116(s1)
	xor t1, t1, t5
	sw t1, 436(s0)
	lwu t1, 120(s1)
	xor t1, t1, t5
	sw t1, 440(s0)
	lwu t1, 124(s1)
	xor t1, t1, t5
	sw t1, 444(s0)
	sw t5, 448(s0)
	sw t5, 452(s0)
	sw t5, 456(s0)
	sw t5, 460(s0)
	sw t5, 464(s0)
	sw t5, 468(s0)
	sw t5, 472(s0)
	sw t5, 476(s0)
	sw t5, 480(s0)
	sw t5, 484(s0)
	sw t5, 488(s0)
	sw t5, 492(s0)
	sw t5, 496(s0)
	sw t5, 500(s0)
	sw t5, 504(s0)
	sw t5, 508(s0)
	addi a0, s0, 0
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 128
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi t5, zero, 92
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	lwu t1, 92(s1)
	xor t1, t1, t5
	sw t1, 412(s0)
	lwu t1, 96(s1)
	xor t1, t1, t5
	sw t1, 416(s0)
	lwu t1, 100(s1)
	xor t1, t1, t5
	sw t1, 420(s0)
	lwu t1, 104(s1)
	xor t1, t1, t5
	sw t1, 424(s0)
	lwu t1, 108(s1)
	xor t1, t1, t5
	sw t1, 428(s0)
	lwu t1, 112(s1)
	xor t1, t1, t5
	sw t1, 432(s0)
	lwu t1, 116(s1)
	xor t1, t1, t5
	sw t1, 436(s0)
	lwu t1, 120(s1)
	xor t1, t1, t5
	sw t1, 440(s0)
	lwu t1, 124(s1)
	xor t1, t1, t5
	sw t1, 444(s0)
	sw t5, 448(s0)
	sw t5, 452(s0)
	sw t5, 456(s0)
	sw t5, 460(s0)
	sw t5, 464(s0)
	sw t5, 468(s0)
	sw t5, 472(s0)
	sw t5, 476(s0)
	sw t5, 480(s0)
	sw t5, 484(s0)
	sw t5, 488(s0)
	sw t5, 492(s0)
	sw t5, 496(s0)
	sw t5, 500(s0)
	sw t5, 504(s0)
	sw t5, 508(s0)
	addi a0, s0, 192
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 128
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 128
	addi a2, s1, 128
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 192
	addi a2, s0, 512
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 128
	addi a2, s0, 512
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 192
	addi a2, s1, 128
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi s5, zero, 8
220:
	addi a0, s0, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi t5, zero, 54
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	lwu t1, 92(s1)
	xor t1, t1, t5
	sw t1, 412(s0)
	lwu t1, 96(s1)
	xor t1, t1, t5
	sw t1, 416(s0)
	lwu t1, 100(s1)
	xor t1, t1, t5
	sw t1, 420(s0)
	lwu t1, 104(s1)
	xor t1, t1, t5
	sw t1, 424(s0)
	lwu t1, 108(s1)
	xor t1, t1, t5
	sw t1, 428(s0)
	lwu t1, 112(s1)
	xor t1, t1, t5
	sw t1, 432(s0)
	lwu t1, 116(s1)
	xor t1, t1, t5
	sw t1, 436(s0)
	lwu t1, 120(s1)
	xor t1, t1, t5
	sw t1, 440(s0)
	lwu t1, 124(s1)
	xor t1, t1, t5
	sw t1, 444(s0)
	sw t5, 448(s0)
	sw t5, 452(s0)
	sw t5, 456(s0)
	sw t5, 460(s0)
	sw t5, 464(s0)
	sw t5, 468(s0)
	sw t5, 472(s0)
	sw t5, 476(s0)
	sw t5, 480(s0)
	sw t5, 484(s0)
	sw t5, 488(s0)
	sw t5, 492(s0)
	sw t5, 496(s0)
	sw t5, 500(s0)
	sw t5, 504(s0)
	sw t5, 508(s0)
	addi a0, s0, 0
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 128
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi t5, zero, 92
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	lwu t1, 92(s1)
	xor t1, t1, t5
	sw t1, 412(s0)
	lwu t1, 96(s1)
	xor t1, t1, t5
	sw t1, 416(s0)
	lwu t1, 100(s1)
	xor t1, t1, t5
	sw t1, 420(s0)
	lwu t1, 104(s1)
	xor t1, t1, t5
	sw t1, 424(s0)
	lwu t1, 108(s1)
	xor t1, t1, t5
	sw t1, 428(s0)
	lwu t1, 112(s1)
	xor t1, t1, t5
	sw t1, 432(s0)
	lwu t1, 116(s1)
	xor t1, t1, t5
	sw t1, 436(s0)
	lwu t1, 120(s1)
	xor t1, t1, t5
	sw t1, 440(s0)
	lwu t1, 124(s1)
	xor t1, t1, t5
	sw t1, 444(s0)
	sw t5, 448(s0)
	sw t5, 452(s0)
	sw t5, 456(s0)
	sw t5, 460(s0)
	sw t5, 464(s0)
	sw t5, 468(s0)
	sw t5, 472(s0)
	sw t5, 476(s0)
	sw t5, 480(s0)
	sw t5, 484(s0)
	sw t5, 488(s0)
	sw t5, 492(s0)
	sw t5, 496(s0)
	sw t5, 500(s0)
	sw t5, 504(s0)
	sw t5, 508(s0)
	addi a0, s0, 192
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 128
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 128
	addi a2, s1, 128
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 192
	addi a2, s0, 512
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 128
	addi a2, s0, 512
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 192
	addi a2, s1, 128
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s2, 0
	addi a1, s3, 0
	addi a2, s4, 0
	addi a3, s1, 128
	addi a4, s0, 0
	call {vg_ecdsa_secp256k1_sign_k}
	addi s5, s5, -1
	andi t0, a0, 1
	addi t0, t0, -1
	and t6, t0, s5
	bnez t6, 221f
	addi t6, zero, 0
	j 222f
221:
	addi t0, zero, 0
	sb t0, 192(s1)
	addi a0, s0, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi t5, zero, 54
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	lwu t1, 92(s1)
	xor t1, t1, t5
	sw t1, 412(s0)
	lwu t1, 96(s1)
	xor t1, t1, t5
	sw t1, 416(s0)
	lwu t1, 100(s1)
	xor t1, t1, t5
	sw t1, 420(s0)
	lwu t1, 104(s1)
	xor t1, t1, t5
	sw t1, 424(s0)
	lwu t1, 108(s1)
	xor t1, t1, t5
	sw t1, 428(s0)
	lwu t1, 112(s1)
	xor t1, t1, t5
	sw t1, 432(s0)
	lwu t1, 116(s1)
	xor t1, t1, t5
	sw t1, 436(s0)
	lwu t1, 120(s1)
	xor t1, t1, t5
	sw t1, 440(s0)
	lwu t1, 124(s1)
	xor t1, t1, t5
	sw t1, 444(s0)
	sw t5, 448(s0)
	sw t5, 452(s0)
	sw t5, 456(s0)
	sw t5, 460(s0)
	sw t5, 464(s0)
	sw t5, 468(s0)
	sw t5, 472(s0)
	sw t5, 476(s0)
	sw t5, 480(s0)
	sw t5, 484(s0)
	sw t5, 488(s0)
	sw t5, 492(s0)
	sw t5, 496(s0)
	sw t5, 500(s0)
	sw t5, 504(s0)
	sw t5, 508(s0)
	addi a0, s0, 0
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 128
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi t5, zero, 92
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	lwu t1, 92(s1)
	xor t1, t1, t5
	sw t1, 412(s0)
	lwu t1, 96(s1)
	xor t1, t1, t5
	sw t1, 416(s0)
	lwu t1, 100(s1)
	xor t1, t1, t5
	sw t1, 420(s0)
	lwu t1, 104(s1)
	xor t1, t1, t5
	sw t1, 424(s0)
	lwu t1, 108(s1)
	xor t1, t1, t5
	sw t1, 428(s0)
	lwu t1, 112(s1)
	xor t1, t1, t5
	sw t1, 432(s0)
	lwu t1, 116(s1)
	xor t1, t1, t5
	sw t1, 436(s0)
	lwu t1, 120(s1)
	xor t1, t1, t5
	sw t1, 440(s0)
	lwu t1, 124(s1)
	xor t1, t1, t5
	sw t1, 444(s0)
	sw t5, 448(s0)
	sw t5, 452(s0)
	sw t5, 456(s0)
	sw t5, 460(s0)
	sw t5, 464(s0)
	sw t5, 468(s0)
	sw t5, 472(s0)
	sw t5, 476(s0)
	sw t5, 480(s0)
	sw t5, 484(s0)
	sw t5, 488(s0)
	sw t5, 492(s0)
	sw t5, 496(s0)
	sw t5, 500(s0)
	sw t5, 504(s0)
	sw t5, 508(s0)
	addi a0, s0, 192
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 128
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 128
	addi a2, s1, 128
	addi a3, zero, 65
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 193
	addi a2, s0, 512
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 128
	addi a2, s0, 512
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 192
	addi a2, s1, 64
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi t5, zero, 54
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	lwu t1, 92(s1)
	xor t1, t1, t5
	sw t1, 412(s0)
	lwu t1, 96(s1)
	xor t1, t1, t5
	sw t1, 416(s0)
	lwu t1, 100(s1)
	xor t1, t1, t5
	sw t1, 420(s0)
	lwu t1, 104(s1)
	xor t1, t1, t5
	sw t1, 424(s0)
	lwu t1, 108(s1)
	xor t1, t1, t5
	sw t1, 428(s0)
	lwu t1, 112(s1)
	xor t1, t1, t5
	sw t1, 432(s0)
	lwu t1, 116(s1)
	xor t1, t1, t5
	sw t1, 436(s0)
	lwu t1, 120(s1)
	xor t1, t1, t5
	sw t1, 440(s0)
	lwu t1, 124(s1)
	xor t1, t1, t5
	sw t1, 444(s0)
	sw t5, 448(s0)
	sw t5, 452(s0)
	sw t5, 456(s0)
	sw t5, 460(s0)
	sw t5, 464(s0)
	sw t5, 468(s0)
	sw t5, 472(s0)
	sw t5, 476(s0)
	sw t5, 480(s0)
	sw t5, 484(s0)
	sw t5, 488(s0)
	sw t5, 492(s0)
	sw t5, 496(s0)
	sw t5, 500(s0)
	sw t5, 504(s0)
	sw t5, 508(s0)
	addi a0, s0, 0
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 128
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi t5, zero, 92
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	lwu t1, 92(s1)
	xor t1, t1, t5
	sw t1, 412(s0)
	lwu t1, 96(s1)
	xor t1, t1, t5
	sw t1, 416(s0)
	lwu t1, 100(s1)
	xor t1, t1, t5
	sw t1, 420(s0)
	lwu t1, 104(s1)
	xor t1, t1, t5
	sw t1, 424(s0)
	lwu t1, 108(s1)
	xor t1, t1, t5
	sw t1, 428(s0)
	lwu t1, 112(s1)
	xor t1, t1, t5
	sw t1, 432(s0)
	lwu t1, 116(s1)
	xor t1, t1, t5
	sw t1, 436(s0)
	lwu t1, 120(s1)
	xor t1, t1, t5
	sw t1, 440(s0)
	lwu t1, 124(s1)
	xor t1, t1, t5
	sw t1, 444(s0)
	sw t5, 448(s0)
	sw t5, 452(s0)
	sw t5, 456(s0)
	sw t5, 460(s0)
	sw t5, 464(s0)
	sw t5, 468(s0)
	sw t5, 472(s0)
	sw t5, 476(s0)
	sw t5, 480(s0)
	sw t5, 484(s0)
	sw t5, 488(s0)
	sw t5, 492(s0)
	sw t5, 496(s0)
	sw t5, 500(s0)
	sw t5, 504(s0)
	sw t5, 508(s0)
	addi a0, s0, 192
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 128
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 128
	addi a2, s1, 128
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 192
	addi a2, s0, 512
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 128
	addi a2, s0, 512
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 192
	addi a2, s1, 128
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi t6, zero, 1
222:
	bnez t6, 220b
	addi t0, zero, 0
	sd t0, 64(s1)
	sd t0, 72(s1)
	sd t0, 80(s1)
	sd t0, 88(s1)
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
	ld ra, 0(s1)
	ld s0, 8(s1)
	ld s2, 24(s1)
	ld s3, 32(s1)
	ld s4, 40(s1)
	ld s5, 48(s1)
	ld s6, 56(s1)
	ld s1, 16(s1)
	addi sp, sp, 240
211:
	j 29f
28:
	addi sp, sp, -224
	addi t0, sp, 0
	sd ra, 0(t0)
	sd s0, 8(t0)
	sd s1, 16(t0)
	sd s2, 24(t0)
	sd s3, 32(t0)
	sd s4, 40(t0)
	sd s5, 48(t0)
	sd s6, 56(t0)
	addi s1, t0, 0
	addi s2, a0, 0
	addi s3, a1, 0
	addi s4, a2, 0
	addi s0, a4, 0
	addi s6, a5, 0
	lbu t0, 0(s4)
	slli t0, t0, 8
	lbu t1, 1(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 2(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 3(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 4(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 5(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 6(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 7(s4)
	or t0, t0, t1
	sd t0, 24(s0)
	lbu t0, 8(s4)
	slli t0, t0, 8
	lbu t1, 9(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 10(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 11(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 12(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 13(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 14(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 15(s4)
	or t0, t0, t1
	sd t0, 16(s0)
	lbu t0, 16(s4)
	slli t0, t0, 8
	lbu t1, 17(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 18(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 19(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 20(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 21(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 22(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 23(s4)
	or t0, t0, t1
	sd t0, 8(s0)
	lbu t0, 24(s4)
	slli t0, t0, 8
	lbu t1, 25(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 26(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 27(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 28(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 29(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 30(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 31(s4)
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
	call {vg_secp256k1_add_mod_n}
	addi a7, zero, -1
	ld t0, 88(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 192(s1)
	srli t1, t0, 48
	sb t1, 193(s1)
	srli t1, t0, 40
	sb t1, 194(s1)
	srli t1, t0, 32
	sb t1, 195(s1)
	srli t1, t0, 24
	sb t1, 196(s1)
	srli t1, t0, 16
	sb t1, 197(s1)
	srli t1, t0, 8
	sb t1, 198(s1)
	srli t1, t0, 0
	sb t1, 199(s1)
	ld t0, 80(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 200(s1)
	srli t1, t0, 48
	sb t1, 201(s1)
	srli t1, t0, 40
	sb t1, 202(s1)
	srli t1, t0, 32
	sb t1, 203(s1)
	srli t1, t0, 24
	sb t1, 204(s1)
	srli t1, t0, 16
	sb t1, 205(s1)
	srli t1, t0, 8
	sb t1, 206(s1)
	srli t1, t0, 0
	sb t1, 207(s1)
	ld t0, 72(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 208(s1)
	srli t1, t0, 48
	sb t1, 209(s1)
	srli t1, t0, 40
	sb t1, 210(s1)
	srli t1, t0, 32
	sb t1, 211(s1)
	srli t1, t0, 24
	sb t1, 212(s1)
	srli t1, t0, 16
	sb t1, 213(s1)
	srli t1, t0, 8
	sb t1, 214(s1)
	srli t1, t0, 0
	sb t1, 215(s1)
	ld t0, 64(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 216(s1)
	srli t1, t0, 48
	sb t1, 217(s1)
	srli t1, t0, 40
	sb t1, 218(s1)
	srli t1, t0, 32
	sb t1, 219(s1)
	srli t1, t0, 24
	sb t1, 220(s1)
	srli t1, t0, 16
	sb t1, 221(s1)
	srli t1, t0, 8
	sb t1, 222(s1)
	srli t1, t0, 0
	sb t1, 223(s1)
	addi t0, zero, 0
	sb t0, 64(s1)
	addi t0, zero, 0
	sb t0, 65(s1)
	addi t0, zero, 0
	sb t0, 66(s1)
	addi t0, zero, 0
	sb t0, 67(s1)
	addi t0, zero, 0
	sb t0, 68(s1)
	addi t0, zero, 0
	sb t0, 69(s1)
	addi t0, zero, 0
	sb t0, 70(s1)
	addi t0, zero, 0
	sb t0, 71(s1)
	addi t0, zero, 0
	sb t0, 72(s1)
	addi t0, zero, 0
	sb t0, 73(s1)
	addi t0, zero, 0
	sb t0, 74(s1)
	addi t0, zero, 0
	sb t0, 75(s1)
	addi t0, zero, 0
	sb t0, 76(s1)
	addi t0, zero, 0
	sb t0, 77(s1)
	addi t0, zero, 0
	sb t0, 78(s1)
	addi t0, zero, 0
	sb t0, 79(s1)
	addi t0, zero, 0
	sb t0, 80(s1)
	addi t0, zero, 0
	sb t0, 81(s1)
	addi t0, zero, 0
	sb t0, 82(s1)
	addi t0, zero, 0
	sb t0, 83(s1)
	addi t0, zero, 0
	sb t0, 84(s1)
	addi t0, zero, 0
	sb t0, 85(s1)
	addi t0, zero, 0
	sb t0, 86(s1)
	addi t0, zero, 0
	sb t0, 87(s1)
	addi t0, zero, 0
	sb t0, 88(s1)
	addi t0, zero, 0
	sb t0, 89(s1)
	addi t0, zero, 0
	sb t0, 90(s1)
	addi t0, zero, 0
	sb t0, 91(s1)
	addi t0, zero, 0
	sb t0, 92(s1)
	addi t0, zero, 0
	sb t0, 93(s1)
	addi t0, zero, 0
	sb t0, 94(s1)
	addi t0, zero, 0
	sb t0, 95(s1)
	addi t0, zero, 0
	sb t0, 96(s1)
	addi t0, zero, 0
	sb t0, 97(s1)
	addi t0, zero, 0
	sb t0, 98(s1)
	addi t0, zero, 0
	sb t0, 99(s1)
	addi t0, zero, 0
	sb t0, 100(s1)
	addi t0, zero, 0
	sb t0, 101(s1)
	addi t0, zero, 0
	sb t0, 102(s1)
	addi t0, zero, 0
	sb t0, 103(s1)
	addi t0, zero, 0
	sb t0, 104(s1)
	addi t0, zero, 0
	sb t0, 105(s1)
	addi t0, zero, 0
	sb t0, 106(s1)
	addi t0, zero, 0
	sb t0, 107(s1)
	addi t0, zero, 0
	sb t0, 108(s1)
	addi t0, zero, 0
	sb t0, 109(s1)
	addi t0, zero, 0
	sb t0, 110(s1)
	addi t0, zero, 0
	sb t0, 111(s1)
	addi t0, zero, 1
	sb t0, 128(s1)
	addi t0, zero, 1
	sb t0, 129(s1)
	addi t0, zero, 1
	sb t0, 130(s1)
	addi t0, zero, 1
	sb t0, 131(s1)
	addi t0, zero, 1
	sb t0, 132(s1)
	addi t0, zero, 1
	sb t0, 133(s1)
	addi t0, zero, 1
	sb t0, 134(s1)
	addi t0, zero, 1
	sb t0, 135(s1)
	addi t0, zero, 1
	sb t0, 136(s1)
	addi t0, zero, 1
	sb t0, 137(s1)
	addi t0, zero, 1
	sb t0, 138(s1)
	addi t0, zero, 1
	sb t0, 139(s1)
	addi t0, zero, 1
	sb t0, 140(s1)
	addi t0, zero, 1
	sb t0, 141(s1)
	addi t0, zero, 1
	sb t0, 142(s1)
	addi t0, zero, 1
	sb t0, 143(s1)
	addi t0, zero, 1
	sb t0, 144(s1)
	addi t0, zero, 1
	sb t0, 145(s1)
	addi t0, zero, 1
	sb t0, 146(s1)
	addi t0, zero, 1
	sb t0, 147(s1)
	addi t0, zero, 1
	sb t0, 148(s1)
	addi t0, zero, 1
	sb t0, 149(s1)
	addi t0, zero, 1
	sb t0, 150(s1)
	addi t0, zero, 1
	sb t0, 151(s1)
	addi t0, zero, 1
	sb t0, 152(s1)
	addi t0, zero, 1
	sb t0, 153(s1)
	addi t0, zero, 1
	sb t0, 154(s1)
	addi t0, zero, 1
	sb t0, 155(s1)
	addi t0, zero, 1
	sb t0, 156(s1)
	addi t0, zero, 1
	sb t0, 157(s1)
	addi t0, zero, 1
	sb t0, 158(s1)
	addi t0, zero, 1
	sb t0, 159(s1)
	addi t0, zero, 1
	sb t0, 160(s1)
	addi t0, zero, 1
	sb t0, 161(s1)
	addi t0, zero, 1
	sb t0, 162(s1)
	addi t0, zero, 1
	sb t0, 163(s1)
	addi t0, zero, 1
	sb t0, 164(s1)
	addi t0, zero, 1
	sb t0, 165(s1)
	addi t0, zero, 1
	sb t0, 166(s1)
	addi t0, zero, 1
	sb t0, 167(s1)
	addi t0, zero, 1
	sb t0, 168(s1)
	addi t0, zero, 1
	sb t0, 169(s1)
	addi t0, zero, 1
	sb t0, 170(s1)
	addi t0, zero, 1
	sb t0, 171(s1)
	addi t0, zero, 1
	sb t0, 172(s1)
	addi t0, zero, 1
	sb t0, 173(s1)
	addi t0, zero, 1
	sb t0, 174(s1)
	addi t0, zero, 1
	sb t0, 175(s1)
	addi t0, zero, 0
	sb t0, 176(s1)
	addi a0, s0, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi t5, zero, 54
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	lwu t1, 92(s1)
	xor t1, t1, t5
	sw t1, 412(s0)
	lwu t1, 96(s1)
	xor t1, t1, t5
	sw t1, 416(s0)
	lwu t1, 100(s1)
	xor t1, t1, t5
	sw t1, 420(s0)
	lwu t1, 104(s1)
	xor t1, t1, t5
	sw t1, 424(s0)
	lwu t1, 108(s1)
	xor t1, t1, t5
	sw t1, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	sw t5, 448(s0)
	sw t5, 452(s0)
	sw t5, 456(s0)
	sw t5, 460(s0)
	sw t5, 464(s0)
	sw t5, 468(s0)
	sw t5, 472(s0)
	sw t5, 476(s0)
	sw t5, 480(s0)
	sw t5, 484(s0)
	sw t5, 488(s0)
	sw t5, 492(s0)
	sw t5, 496(s0)
	sw t5, 500(s0)
	sw t5, 504(s0)
	sw t5, 508(s0)
	addi a0, s0, 0
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 128
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi t5, zero, 92
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	lwu t1, 92(s1)
	xor t1, t1, t5
	sw t1, 412(s0)
	lwu t1, 96(s1)
	xor t1, t1, t5
	sw t1, 416(s0)
	lwu t1, 100(s1)
	xor t1, t1, t5
	sw t1, 420(s0)
	lwu t1, 104(s1)
	xor t1, t1, t5
	sw t1, 424(s0)
	lwu t1, 108(s1)
	xor t1, t1, t5
	sw t1, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	sw t5, 448(s0)
	sw t5, 452(s0)
	sw t5, 456(s0)
	sw t5, 460(s0)
	sw t5, 464(s0)
	sw t5, 468(s0)
	sw t5, 472(s0)
	sw t5, 476(s0)
	sw t5, 480(s0)
	sw t5, 484(s0)
	sw t5, 488(s0)
	sw t5, 492(s0)
	sw t5, 496(s0)
	sw t5, 500(s0)
	sw t5, 504(s0)
	sw t5, 508(s0)
	addi a0, s0, 192
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 128
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 128
	addi a2, s1, 128
	addi a3, zero, 49
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 177
	addi a2, s3, 0
	addi a3, zero, 32
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 209
	addi a2, s1, 192
	addi a3, zero, 32
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 241
	addi a2, s0, 512
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 128
	addi a2, s0, 512
	addi a3, zero, 48
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 176
	addi a2, s1, 64
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi t5, zero, 54
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	lwu t1, 92(s1)
	xor t1, t1, t5
	sw t1, 412(s0)
	lwu t1, 96(s1)
	xor t1, t1, t5
	sw t1, 416(s0)
	lwu t1, 100(s1)
	xor t1, t1, t5
	sw t1, 420(s0)
	lwu t1, 104(s1)
	xor t1, t1, t5
	sw t1, 424(s0)
	lwu t1, 108(s1)
	xor t1, t1, t5
	sw t1, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	sw t5, 448(s0)
	sw t5, 452(s0)
	sw t5, 456(s0)
	sw t5, 460(s0)
	sw t5, 464(s0)
	sw t5, 468(s0)
	sw t5, 472(s0)
	sw t5, 476(s0)
	sw t5, 480(s0)
	sw t5, 484(s0)
	sw t5, 488(s0)
	sw t5, 492(s0)
	sw t5, 496(s0)
	sw t5, 500(s0)
	sw t5, 504(s0)
	sw t5, 508(s0)
	addi a0, s0, 0
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 128
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi t5, zero, 92
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	lwu t1, 92(s1)
	xor t1, t1, t5
	sw t1, 412(s0)
	lwu t1, 96(s1)
	xor t1, t1, t5
	sw t1, 416(s0)
	lwu t1, 100(s1)
	xor t1, t1, t5
	sw t1, 420(s0)
	lwu t1, 104(s1)
	xor t1, t1, t5
	sw t1, 424(s0)
	lwu t1, 108(s1)
	xor t1, t1, t5
	sw t1, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	sw t5, 448(s0)
	sw t5, 452(s0)
	sw t5, 456(s0)
	sw t5, 460(s0)
	sw t5, 464(s0)
	sw t5, 468(s0)
	sw t5, 472(s0)
	sw t5, 476(s0)
	sw t5, 480(s0)
	sw t5, 484(s0)
	sw t5, 488(s0)
	sw t5, 492(s0)
	sw t5, 496(s0)
	sw t5, 500(s0)
	sw t5, 504(s0)
	sw t5, 508(s0)
	addi a0, s0, 192
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 128
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 128
	addi a2, s1, 128
	addi a3, zero, 48
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 176
	addi a2, s0, 512
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 128
	addi a2, s0, 512
	addi a3, zero, 48
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 176
	addi a2, s1, 128
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi t0, zero, 1
	sb t0, 176(s1)
	addi a0, s0, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi t5, zero, 54
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	lwu t1, 92(s1)
	xor t1, t1, t5
	sw t1, 412(s0)
	lwu t1, 96(s1)
	xor t1, t1, t5
	sw t1, 416(s0)
	lwu t1, 100(s1)
	xor t1, t1, t5
	sw t1, 420(s0)
	lwu t1, 104(s1)
	xor t1, t1, t5
	sw t1, 424(s0)
	lwu t1, 108(s1)
	xor t1, t1, t5
	sw t1, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	sw t5, 448(s0)
	sw t5, 452(s0)
	sw t5, 456(s0)
	sw t5, 460(s0)
	sw t5, 464(s0)
	sw t5, 468(s0)
	sw t5, 472(s0)
	sw t5, 476(s0)
	sw t5, 480(s0)
	sw t5, 484(s0)
	sw t5, 488(s0)
	sw t5, 492(s0)
	sw t5, 496(s0)
	sw t5, 500(s0)
	sw t5, 504(s0)
	sw t5, 508(s0)
	addi a0, s0, 0
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 128
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi t5, zero, 92
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	lwu t1, 92(s1)
	xor t1, t1, t5
	sw t1, 412(s0)
	lwu t1, 96(s1)
	xor t1, t1, t5
	sw t1, 416(s0)
	lwu t1, 100(s1)
	xor t1, t1, t5
	sw t1, 420(s0)
	lwu t1, 104(s1)
	xor t1, t1, t5
	sw t1, 424(s0)
	lwu t1, 108(s1)
	xor t1, t1, t5
	sw t1, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	sw t5, 448(s0)
	sw t5, 452(s0)
	sw t5, 456(s0)
	sw t5, 460(s0)
	sw t5, 464(s0)
	sw t5, 468(s0)
	sw t5, 472(s0)
	sw t5, 476(s0)
	sw t5, 480(s0)
	sw t5, 484(s0)
	sw t5, 488(s0)
	sw t5, 492(s0)
	sw t5, 496(s0)
	sw t5, 500(s0)
	sw t5, 504(s0)
	sw t5, 508(s0)
	addi a0, s0, 192
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 128
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 128
	addi a2, s1, 128
	addi a3, zero, 49
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 177
	addi a2, s3, 0
	addi a3, zero, 32
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 209
	addi a2, s1, 192
	addi a3, zero, 32
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 241
	addi a2, s0, 512
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 128
	addi a2, s0, 512
	addi a3, zero, 48
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 176
	addi a2, s1, 64
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi t5, zero, 54
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	lwu t1, 92(s1)
	xor t1, t1, t5
	sw t1, 412(s0)
	lwu t1, 96(s1)
	xor t1, t1, t5
	sw t1, 416(s0)
	lwu t1, 100(s1)
	xor t1, t1, t5
	sw t1, 420(s0)
	lwu t1, 104(s1)
	xor t1, t1, t5
	sw t1, 424(s0)
	lwu t1, 108(s1)
	xor t1, t1, t5
	sw t1, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	sw t5, 448(s0)
	sw t5, 452(s0)
	sw t5, 456(s0)
	sw t5, 460(s0)
	sw t5, 464(s0)
	sw t5, 468(s0)
	sw t5, 472(s0)
	sw t5, 476(s0)
	sw t5, 480(s0)
	sw t5, 484(s0)
	sw t5, 488(s0)
	sw t5, 492(s0)
	sw t5, 496(s0)
	sw t5, 500(s0)
	sw t5, 504(s0)
	sw t5, 508(s0)
	addi a0, s0, 0
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 128
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi t5, zero, 92
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	lwu t1, 92(s1)
	xor t1, t1, t5
	sw t1, 412(s0)
	lwu t1, 96(s1)
	xor t1, t1, t5
	sw t1, 416(s0)
	lwu t1, 100(s1)
	xor t1, t1, t5
	sw t1, 420(s0)
	lwu t1, 104(s1)
	xor t1, t1, t5
	sw t1, 424(s0)
	lwu t1, 108(s1)
	xor t1, t1, t5
	sw t1, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	sw t5, 448(s0)
	sw t5, 452(s0)
	sw t5, 456(s0)
	sw t5, 460(s0)
	sw t5, 464(s0)
	sw t5, 468(s0)
	sw t5, 472(s0)
	sw t5, 476(s0)
	sw t5, 480(s0)
	sw t5, 484(s0)
	sw t5, 488(s0)
	sw t5, 492(s0)
	sw t5, 496(s0)
	sw t5, 500(s0)
	sw t5, 504(s0)
	sw t5, 508(s0)
	addi a0, s0, 192
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 128
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 128
	addi a2, s1, 128
	addi a3, zero, 48
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 176
	addi a2, s0, 512
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 128
	addi a2, s0, 512
	addi a3, zero, 48
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 176
	addi a2, s1, 128
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi s5, zero, 8
223:
	addi a0, s0, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi t5, zero, 54
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	lwu t1, 92(s1)
	xor t1, t1, t5
	sw t1, 412(s0)
	lwu t1, 96(s1)
	xor t1, t1, t5
	sw t1, 416(s0)
	lwu t1, 100(s1)
	xor t1, t1, t5
	sw t1, 420(s0)
	lwu t1, 104(s1)
	xor t1, t1, t5
	sw t1, 424(s0)
	lwu t1, 108(s1)
	xor t1, t1, t5
	sw t1, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	sw t5, 448(s0)
	sw t5, 452(s0)
	sw t5, 456(s0)
	sw t5, 460(s0)
	sw t5, 464(s0)
	sw t5, 468(s0)
	sw t5, 472(s0)
	sw t5, 476(s0)
	sw t5, 480(s0)
	sw t5, 484(s0)
	sw t5, 488(s0)
	sw t5, 492(s0)
	sw t5, 496(s0)
	sw t5, 500(s0)
	sw t5, 504(s0)
	sw t5, 508(s0)
	addi a0, s0, 0
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 128
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi t5, zero, 92
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	lwu t1, 92(s1)
	xor t1, t1, t5
	sw t1, 412(s0)
	lwu t1, 96(s1)
	xor t1, t1, t5
	sw t1, 416(s0)
	lwu t1, 100(s1)
	xor t1, t1, t5
	sw t1, 420(s0)
	lwu t1, 104(s1)
	xor t1, t1, t5
	sw t1, 424(s0)
	lwu t1, 108(s1)
	xor t1, t1, t5
	sw t1, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	sw t5, 448(s0)
	sw t5, 452(s0)
	sw t5, 456(s0)
	sw t5, 460(s0)
	sw t5, 464(s0)
	sw t5, 468(s0)
	sw t5, 472(s0)
	sw t5, 476(s0)
	sw t5, 480(s0)
	sw t5, 484(s0)
	sw t5, 488(s0)
	sw t5, 492(s0)
	sw t5, 496(s0)
	sw t5, 500(s0)
	sw t5, 504(s0)
	sw t5, 508(s0)
	addi a0, s0, 192
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 128
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 128
	addi a2, s1, 128
	addi a3, zero, 48
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 176
	addi a2, s0, 512
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 128
	addi a2, s0, 512
	addi a3, zero, 48
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 176
	addi a2, s1, 128
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s2, 0
	addi a1, s3, 0
	addi a2, s4, 0
	addi a3, s1, 128
	addi a4, s0, 0
	call {vg_ecdsa_secp256k1_sign_k}
	addi s5, s5, -1
	andi t0, a0, 1
	addi t0, t0, -1
	and t6, t0, s5
	bnez t6, 224f
	addi t6, zero, 0
	j 225f
224:
	addi t0, zero, 0
	sb t0, 176(s1)
	addi a0, s0, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi t5, zero, 54
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	lwu t1, 92(s1)
	xor t1, t1, t5
	sw t1, 412(s0)
	lwu t1, 96(s1)
	xor t1, t1, t5
	sw t1, 416(s0)
	lwu t1, 100(s1)
	xor t1, t1, t5
	sw t1, 420(s0)
	lwu t1, 104(s1)
	xor t1, t1, t5
	sw t1, 424(s0)
	lwu t1, 108(s1)
	xor t1, t1, t5
	sw t1, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	sw t5, 448(s0)
	sw t5, 452(s0)
	sw t5, 456(s0)
	sw t5, 460(s0)
	sw t5, 464(s0)
	sw t5, 468(s0)
	sw t5, 472(s0)
	sw t5, 476(s0)
	sw t5, 480(s0)
	sw t5, 484(s0)
	sw t5, 488(s0)
	sw t5, 492(s0)
	sw t5, 496(s0)
	sw t5, 500(s0)
	sw t5, 504(s0)
	sw t5, 508(s0)
	addi a0, s0, 0
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 128
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi t5, zero, 92
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	lwu t1, 92(s1)
	xor t1, t1, t5
	sw t1, 412(s0)
	lwu t1, 96(s1)
	xor t1, t1, t5
	sw t1, 416(s0)
	lwu t1, 100(s1)
	xor t1, t1, t5
	sw t1, 420(s0)
	lwu t1, 104(s1)
	xor t1, t1, t5
	sw t1, 424(s0)
	lwu t1, 108(s1)
	xor t1, t1, t5
	sw t1, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	sw t5, 448(s0)
	sw t5, 452(s0)
	sw t5, 456(s0)
	sw t5, 460(s0)
	sw t5, 464(s0)
	sw t5, 468(s0)
	sw t5, 472(s0)
	sw t5, 476(s0)
	sw t5, 480(s0)
	sw t5, 484(s0)
	sw t5, 488(s0)
	sw t5, 492(s0)
	sw t5, 496(s0)
	sw t5, 500(s0)
	sw t5, 504(s0)
	sw t5, 508(s0)
	addi a0, s0, 192
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 128
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 128
	addi a2, s1, 128
	addi a3, zero, 49
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 177
	addi a2, s0, 512
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 128
	addi a2, s0, 512
	addi a3, zero, 48
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 176
	addi a2, s1, 64
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi t5, zero, 54
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	lwu t1, 92(s1)
	xor t1, t1, t5
	sw t1, 412(s0)
	lwu t1, 96(s1)
	xor t1, t1, t5
	sw t1, 416(s0)
	lwu t1, 100(s1)
	xor t1, t1, t5
	sw t1, 420(s0)
	lwu t1, 104(s1)
	xor t1, t1, t5
	sw t1, 424(s0)
	lwu t1, 108(s1)
	xor t1, t1, t5
	sw t1, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	sw t5, 448(s0)
	sw t5, 452(s0)
	sw t5, 456(s0)
	sw t5, 460(s0)
	sw t5, 464(s0)
	sw t5, 468(s0)
	sw t5, 472(s0)
	sw t5, 476(s0)
	sw t5, 480(s0)
	sw t5, 484(s0)
	sw t5, 488(s0)
	sw t5, 492(s0)
	sw t5, 496(s0)
	sw t5, 500(s0)
	sw t5, 504(s0)
	sw t5, 508(s0)
	addi a0, s0, 0
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 128
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi t5, zero, 92
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	lwu t1, 92(s1)
	xor t1, t1, t5
	sw t1, 412(s0)
	lwu t1, 96(s1)
	xor t1, t1, t5
	sw t1, 416(s0)
	lwu t1, 100(s1)
	xor t1, t1, t5
	sw t1, 420(s0)
	lwu t1, 104(s1)
	xor t1, t1, t5
	sw t1, 424(s0)
	lwu t1, 108(s1)
	xor t1, t1, t5
	sw t1, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	sw t5, 448(s0)
	sw t5, 452(s0)
	sw t5, 456(s0)
	sw t5, 460(s0)
	sw t5, 464(s0)
	sw t5, 468(s0)
	sw t5, 472(s0)
	sw t5, 476(s0)
	sw t5, 480(s0)
	sw t5, 484(s0)
	sw t5, 488(s0)
	sw t5, 492(s0)
	sw t5, 496(s0)
	sw t5, 500(s0)
	sw t5, 504(s0)
	sw t5, 508(s0)
	addi a0, s0, 192
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 128
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 128
	addi a2, s1, 128
	addi a3, zero, 48
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 176
	addi a2, s0, 512
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 128
	addi a2, s0, 512
	addi a3, zero, 48
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 176
	addi a2, s1, 128
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi t6, zero, 1
225:
	bnez t6, 223b
	addi t0, zero, 0
	sd t0, 64(s1)
	sd t0, 72(s1)
	sd t0, 80(s1)
	sd t0, 88(s1)
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
	ld ra, 0(s1)
	ld s0, 8(s1)
	ld s2, 24(s1)
	ld s3, 32(s1)
	ld s4, 40(s1)
	ld s5, 48(s1)
	ld s6, 56(s1)
	ld s1, 16(s1)
	addi sp, sp, 224
29:
	j 27f
26:
	addi sp, sp, -224
	addi t0, sp, 0
	sd ra, 0(t0)
	sd s0, 8(t0)
	sd s1, 16(t0)
	sd s2, 24(t0)
	sd s3, 32(t0)
	sd s4, 40(t0)
	sd s5, 48(t0)
	sd s6, 56(t0)
	addi s1, t0, 0
	addi s2, a0, 0
	addi s3, a1, 0
	addi s4, a2, 0
	addi s0, a4, 0
	addi s6, a5, 0
	lbu t0, 0(s4)
	slli t0, t0, 8
	lbu t1, 1(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 2(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 3(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 4(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 5(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 6(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 7(s4)
	or t0, t0, t1
	sd t0, 24(s0)
	lbu t0, 8(s4)
	slli t0, t0, 8
	lbu t1, 9(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 10(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 11(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 12(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 13(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 14(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 15(s4)
	or t0, t0, t1
	sd t0, 16(s0)
	lbu t0, 16(s4)
	slli t0, t0, 8
	lbu t1, 17(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 18(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 19(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 20(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 21(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 22(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 23(s4)
	or t0, t0, t1
	sd t0, 8(s0)
	lbu t0, 24(s4)
	slli t0, t0, 8
	lbu t1, 25(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 26(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 27(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 28(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 29(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 30(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 31(s4)
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
	call {vg_secp256k1_add_mod_n}
	addi a7, zero, -1
	ld t0, 88(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 192(s1)
	srli t1, t0, 48
	sb t1, 193(s1)
	srli t1, t0, 40
	sb t1, 194(s1)
	srli t1, t0, 32
	sb t1, 195(s1)
	srli t1, t0, 24
	sb t1, 196(s1)
	srli t1, t0, 16
	sb t1, 197(s1)
	srli t1, t0, 8
	sb t1, 198(s1)
	srli t1, t0, 0
	sb t1, 199(s1)
	ld t0, 80(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 200(s1)
	srli t1, t0, 48
	sb t1, 201(s1)
	srli t1, t0, 40
	sb t1, 202(s1)
	srli t1, t0, 32
	sb t1, 203(s1)
	srli t1, t0, 24
	sb t1, 204(s1)
	srli t1, t0, 16
	sb t1, 205(s1)
	srli t1, t0, 8
	sb t1, 206(s1)
	srli t1, t0, 0
	sb t1, 207(s1)
	ld t0, 72(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 208(s1)
	srli t1, t0, 48
	sb t1, 209(s1)
	srli t1, t0, 40
	sb t1, 210(s1)
	srli t1, t0, 32
	sb t1, 211(s1)
	srli t1, t0, 24
	sb t1, 212(s1)
	srli t1, t0, 16
	sb t1, 213(s1)
	srli t1, t0, 8
	sb t1, 214(s1)
	srli t1, t0, 0
	sb t1, 215(s1)
	ld t0, 64(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 216(s1)
	srli t1, t0, 48
	sb t1, 217(s1)
	srli t1, t0, 40
	sb t1, 218(s1)
	srli t1, t0, 32
	sb t1, 219(s1)
	srli t1, t0, 24
	sb t1, 220(s1)
	srli t1, t0, 16
	sb t1, 221(s1)
	srli t1, t0, 8
	sb t1, 222(s1)
	srli t1, t0, 0
	sb t1, 223(s1)
	addi t0, zero, 0
	sb t0, 64(s1)
	addi t0, zero, 0
	sb t0, 65(s1)
	addi t0, zero, 0
	sb t0, 66(s1)
	addi t0, zero, 0
	sb t0, 67(s1)
	addi t0, zero, 0
	sb t0, 68(s1)
	addi t0, zero, 0
	sb t0, 69(s1)
	addi t0, zero, 0
	sb t0, 70(s1)
	addi t0, zero, 0
	sb t0, 71(s1)
	addi t0, zero, 0
	sb t0, 72(s1)
	addi t0, zero, 0
	sb t0, 73(s1)
	addi t0, zero, 0
	sb t0, 74(s1)
	addi t0, zero, 0
	sb t0, 75(s1)
	addi t0, zero, 0
	sb t0, 76(s1)
	addi t0, zero, 0
	sb t0, 77(s1)
	addi t0, zero, 0
	sb t0, 78(s1)
	addi t0, zero, 0
	sb t0, 79(s1)
	addi t0, zero, 0
	sb t0, 80(s1)
	addi t0, zero, 0
	sb t0, 81(s1)
	addi t0, zero, 0
	sb t0, 82(s1)
	addi t0, zero, 0
	sb t0, 83(s1)
	addi t0, zero, 0
	sb t0, 84(s1)
	addi t0, zero, 0
	sb t0, 85(s1)
	addi t0, zero, 0
	sb t0, 86(s1)
	addi t0, zero, 0
	sb t0, 87(s1)
	addi t0, zero, 0
	sb t0, 88(s1)
	addi t0, zero, 0
	sb t0, 89(s1)
	addi t0, zero, 0
	sb t0, 90(s1)
	addi t0, zero, 0
	sb t0, 91(s1)
	addi t0, zero, 0
	sb t0, 92(s1)
	addi t0, zero, 0
	sb t0, 93(s1)
	addi t0, zero, 0
	sb t0, 94(s1)
	addi t0, zero, 0
	sb t0, 95(s1)
	addi t0, zero, 1
	sb t0, 128(s1)
	addi t0, zero, 1
	sb t0, 129(s1)
	addi t0, zero, 1
	sb t0, 130(s1)
	addi t0, zero, 1
	sb t0, 131(s1)
	addi t0, zero, 1
	sb t0, 132(s1)
	addi t0, zero, 1
	sb t0, 133(s1)
	addi t0, zero, 1
	sb t0, 134(s1)
	addi t0, zero, 1
	sb t0, 135(s1)
	addi t0, zero, 1
	sb t0, 136(s1)
	addi t0, zero, 1
	sb t0, 137(s1)
	addi t0, zero, 1
	sb t0, 138(s1)
	addi t0, zero, 1
	sb t0, 139(s1)
	addi t0, zero, 1
	sb t0, 140(s1)
	addi t0, zero, 1
	sb t0, 141(s1)
	addi t0, zero, 1
	sb t0, 142(s1)
	addi t0, zero, 1
	sb t0, 143(s1)
	addi t0, zero, 1
	sb t0, 144(s1)
	addi t0, zero, 1
	sb t0, 145(s1)
	addi t0, zero, 1
	sb t0, 146(s1)
	addi t0, zero, 1
	sb t0, 147(s1)
	addi t0, zero, 1
	sb t0, 148(s1)
	addi t0, zero, 1
	sb t0, 149(s1)
	addi t0, zero, 1
	sb t0, 150(s1)
	addi t0, zero, 1
	sb t0, 151(s1)
	addi t0, zero, 1
	sb t0, 152(s1)
	addi t0, zero, 1
	sb t0, 153(s1)
	addi t0, zero, 1
	sb t0, 154(s1)
	addi t0, zero, 1
	sb t0, 155(s1)
	addi t0, zero, 1
	sb t0, 156(s1)
	addi t0, zero, 1
	sb t0, 157(s1)
	addi t0, zero, 1
	sb t0, 158(s1)
	addi t0, zero, 1
	sb t0, 159(s1)
	addi t0, zero, 0
	sb t0, 160(s1)
	addi a0, s0, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi t5, zero, 54
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	lwu t1, 92(s1)
	xor t1, t1, t5
	sw t1, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 0
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi t5, zero, 92
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	lwu t1, 92(s1)
	xor t1, t1, t5
	sw t1, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 192
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 64
	addi a2, s1, 128
	addi a3, zero, 33
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 97
	addi a2, s3, 0
	addi a3, zero, 32
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 129
	addi a2, s1, 192
	addi a3, zero, 32
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 161
	addi a2, s0, 512
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 64
	addi a2, s0, 512
	addi a3, zero, 32
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 96
	addi a2, s1, 64
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi t5, zero, 54
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	lwu t1, 92(s1)
	xor t1, t1, t5
	sw t1, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 0
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi t5, zero, 92
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	lwu t1, 92(s1)
	xor t1, t1, t5
	sw t1, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 192
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 64
	addi a2, s1, 128
	addi a3, zero, 32
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 96
	addi a2, s0, 512
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 64
	addi a2, s0, 512
	addi a3, zero, 32
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 96
	addi a2, s1, 128
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi t0, zero, 1
	sb t0, 160(s1)
	addi a0, s0, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi t5, zero, 54
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	lwu t1, 92(s1)
	xor t1, t1, t5
	sw t1, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 0
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi t5, zero, 92
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	lwu t1, 92(s1)
	xor t1, t1, t5
	sw t1, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 192
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 64
	addi a2, s1, 128
	addi a3, zero, 33
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 97
	addi a2, s3, 0
	addi a3, zero, 32
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 129
	addi a2, s1, 192
	addi a3, zero, 32
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 161
	addi a2, s0, 512
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 64
	addi a2, s0, 512
	addi a3, zero, 32
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 96
	addi a2, s1, 64
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi t5, zero, 54
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	lwu t1, 92(s1)
	xor t1, t1, t5
	sw t1, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 0
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi t5, zero, 92
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	lwu t1, 92(s1)
	xor t1, t1, t5
	sw t1, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 192
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 64
	addi a2, s1, 128
	addi a3, zero, 32
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 96
	addi a2, s0, 512
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 64
	addi a2, s0, 512
	addi a3, zero, 32
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 96
	addi a2, s1, 128
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi s5, zero, 8
226:
	addi a0, s0, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi t5, zero, 54
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	lwu t1, 92(s1)
	xor t1, t1, t5
	sw t1, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 0
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi t5, zero, 92
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	lwu t1, 92(s1)
	xor t1, t1, t5
	sw t1, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 192
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 64
	addi a2, s1, 128
	addi a3, zero, 32
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 96
	addi a2, s0, 512
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 64
	addi a2, s0, 512
	addi a3, zero, 32
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 96
	addi a2, s1, 128
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s2, 0
	addi a1, s3, 0
	addi a2, s4, 0
	addi a3, s1, 128
	addi a4, s0, 0
	call {vg_ecdsa_secp256k1_sign_k}
	addi s5, s5, -1
	andi t0, a0, 1
	addi t0, t0, -1
	and t6, t0, s5
	bnez t6, 227f
	addi t6, zero, 0
	j 228f
227:
	addi t0, zero, 0
	sb t0, 160(s1)
	addi a0, s0, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi t5, zero, 54
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	lwu t1, 92(s1)
	xor t1, t1, t5
	sw t1, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 0
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi t5, zero, 92
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	lwu t1, 92(s1)
	xor t1, t1, t5
	sw t1, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 192
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 64
	addi a2, s1, 128
	addi a3, zero, 33
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 97
	addi a2, s0, 512
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 64
	addi a2, s0, 512
	addi a3, zero, 32
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 96
	addi a2, s1, 64
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi t5, zero, 54
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	lwu t1, 92(s1)
	xor t1, t1, t5
	sw t1, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 0
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi t5, zero, 92
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	lwu t1, 92(s1)
	xor t1, t1, t5
	sw t1, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 192
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 64
	addi a2, s1, 128
	addi a3, zero, 32
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 96
	addi a2, s0, 512
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 64
	addi a2, s0, 512
	addi a3, zero, 32
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 96
	addi a2, s1, 128
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi t6, zero, 1
228:
	bnez t6, 226b
	addi t0, zero, 0
	sd t0, 64(s1)
	sd t0, 72(s1)
	sd t0, 80(s1)
	sd t0, 88(s1)
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
	ld ra, 0(s1)
	ld s0, 8(s1)
	ld s2, 24(s1)
	ld s3, 32(s1)
	ld s4, 40(s1)
	ld s5, 48(s1)
	ld s6, 56(s1)
	ld s1, 16(s1)
	addi sp, sp, 224
27:
	j 25f
24:
	addi sp, sp, -256
	addi t0, sp, 0
	sd ra, 0(t0)
	sd s0, 8(t0)
	sd s1, 16(t0)
	sd s2, 24(t0)
	sd s3, 32(t0)
	sd s4, 40(t0)
	sd s5, 48(t0)
	sd s6, 56(t0)
	addi s1, t0, 0
	addi s2, a0, 0
	addi s3, a1, 0
	addi s4, a2, 0
	addi s0, a4, 0
	addi s6, a5, 0
	addi t0, zero, 0
	sb t0, 192(s1)
	addi t0, zero, 0
	sb t0, 193(s1)
	addi t0, zero, 0
	sb t0, 194(s1)
	addi t0, zero, 0
	sb t0, 195(s1)
	lbu t0, 0(s4)
	sb t0, 196(s1)
	lbu t0, 1(s4)
	sb t0, 197(s1)
	lbu t0, 2(s4)
	sb t0, 198(s1)
	lbu t0, 3(s4)
	sb t0, 199(s1)
	lbu t0, 4(s4)
	sb t0, 200(s1)
	lbu t0, 5(s4)
	sb t0, 201(s1)
	lbu t0, 6(s4)
	sb t0, 202(s1)
	lbu t0, 7(s4)
	sb t0, 203(s1)
	lbu t0, 8(s4)
	sb t0, 204(s1)
	lbu t0, 9(s4)
	sb t0, 205(s1)
	lbu t0, 10(s4)
	sb t0, 206(s1)
	lbu t0, 11(s4)
	sb t0, 207(s1)
	lbu t0, 12(s4)
	sb t0, 208(s1)
	lbu t0, 13(s4)
	sb t0, 209(s1)
	lbu t0, 14(s4)
	sb t0, 210(s1)
	lbu t0, 15(s4)
	sb t0, 211(s1)
	lbu t0, 16(s4)
	sb t0, 212(s1)
	lbu t0, 17(s4)
	sb t0, 213(s1)
	lbu t0, 18(s4)
	sb t0, 214(s1)
	lbu t0, 19(s4)
	sb t0, 215(s1)
	lbu t0, 20(s4)
	sb t0, 216(s1)
	lbu t0, 21(s4)
	sb t0, 217(s1)
	lbu t0, 22(s4)
	sb t0, 218(s1)
	lbu t0, 23(s4)
	sb t0, 219(s1)
	lbu t0, 24(s4)
	sb t0, 220(s1)
	lbu t0, 25(s4)
	sb t0, 221(s1)
	lbu t0, 26(s4)
	sb t0, 222(s1)
	lbu t0, 27(s4)
	sb t0, 223(s1)
	addi t0, zero, 0
	sb t0, 64(s1)
	addi t0, zero, 0
	sb t0, 65(s1)
	addi t0, zero, 0
	sb t0, 66(s1)
	addi t0, zero, 0
	sb t0, 67(s1)
	addi t0, zero, 0
	sb t0, 68(s1)
	addi t0, zero, 0
	sb t0, 69(s1)
	addi t0, zero, 0
	sb t0, 70(s1)
	addi t0, zero, 0
	sb t0, 71(s1)
	addi t0, zero, 0
	sb t0, 72(s1)
	addi t0, zero, 0
	sb t0, 73(s1)
	addi t0, zero, 0
	sb t0, 74(s1)
	addi t0, zero, 0
	sb t0, 75(s1)
	addi t0, zero, 0
	sb t0, 76(s1)
	addi t0, zero, 0
	sb t0, 77(s1)
	addi t0, zero, 0
	sb t0, 78(s1)
	addi t0, zero, 0
	sb t0, 79(s1)
	addi t0, zero, 0
	sb t0, 80(s1)
	addi t0, zero, 0
	sb t0, 81(s1)
	addi t0, zero, 0
	sb t0, 82(s1)
	addi t0, zero, 0
	sb t0, 83(s1)
	addi t0, zero, 0
	sb t0, 84(s1)
	addi t0, zero, 0
	sb t0, 85(s1)
	addi t0, zero, 0
	sb t0, 86(s1)
	addi t0, zero, 0
	sb t0, 87(s1)
	addi t0, zero, 0
	sb t0, 88(s1)
	addi t0, zero, 0
	sb t0, 89(s1)
	addi t0, zero, 0
	sb t0, 90(s1)
	addi t0, zero, 0
	sb t0, 91(s1)
	addi t0, zero, 1
	sb t0, 128(s1)
	addi t0, zero, 1
	sb t0, 129(s1)
	addi t0, zero, 1
	sb t0, 130(s1)
	addi t0, zero, 1
	sb t0, 131(s1)
	addi t0, zero, 1
	sb t0, 132(s1)
	addi t0, zero, 1
	sb t0, 133(s1)
	addi t0, zero, 1
	sb t0, 134(s1)
	addi t0, zero, 1
	sb t0, 135(s1)
	addi t0, zero, 1
	sb t0, 136(s1)
	addi t0, zero, 1
	sb t0, 137(s1)
	addi t0, zero, 1
	sb t0, 138(s1)
	addi t0, zero, 1
	sb t0, 139(s1)
	addi t0, zero, 1
	sb t0, 140(s1)
	addi t0, zero, 1
	sb t0, 141(s1)
	addi t0, zero, 1
	sb t0, 142(s1)
	addi t0, zero, 1
	sb t0, 143(s1)
	addi t0, zero, 1
	sb t0, 144(s1)
	addi t0, zero, 1
	sb t0, 145(s1)
	addi t0, zero, 1
	sb t0, 146(s1)
	addi t0, zero, 1
	sb t0, 147(s1)
	addi t0, zero, 1
	sb t0, 148(s1)
	addi t0, zero, 1
	sb t0, 149(s1)
	addi t0, zero, 1
	sb t0, 150(s1)
	addi t0, zero, 1
	sb t0, 151(s1)
	addi t0, zero, 1
	sb t0, 152(s1)
	addi t0, zero, 1
	sb t0, 153(s1)
	addi t0, zero, 1
	sb t0, 154(s1)
	addi t0, zero, 1
	sb t0, 155(s1)
	addi t0, zero, 0
	sb t0, 156(s1)
	addi a0, s0, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi t5, zero, 54
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 0
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi t5, zero, 92
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 192
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 64
	addi a2, s1, 128
	addi a3, zero, 29
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 93
	addi a2, s3, 0
	addi a3, zero, 32
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 125
	addi a2, s1, 192
	addi a3, zero, 32
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 157
	addi a2, s0, 512
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 64
	addi a2, s0, 512
	addi a3, zero, 28
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 92
	addi a2, s1, 64
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi t5, zero, 54
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 0
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi t5, zero, 92
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 192
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 64
	addi a2, s1, 128
	addi a3, zero, 28
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 92
	addi a2, s0, 512
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 64
	addi a2, s0, 512
	addi a3, zero, 28
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 92
	addi a2, s1, 128
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi t0, zero, 1
	sb t0, 156(s1)
	addi a0, s0, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi t5, zero, 54
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 0
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi t5, zero, 92
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 192
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 64
	addi a2, s1, 128
	addi a3, zero, 29
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 93
	addi a2, s3, 0
	addi a3, zero, 32
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 125
	addi a2, s1, 192
	addi a3, zero, 32
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 157
	addi a2, s0, 512
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 64
	addi a2, s0, 512
	addi a3, zero, 28
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 92
	addi a2, s1, 64
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi t5, zero, 54
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 0
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi t5, zero, 92
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 192
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 64
	addi a2, s1, 128
	addi a3, zero, 28
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 92
	addi a2, s0, 512
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 64
	addi a2, s0, 512
	addi a3, zero, 28
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 92
	addi a2, s1, 128
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi s5, zero, 8
229:
	addi a0, s0, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi t5, zero, 54
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 0
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi t5, zero, 92
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 192
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 64
	addi a2, s1, 128
	addi a3, zero, 28
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 92
	addi a2, s0, 512
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 64
	addi a2, s0, 512
	addi a3, zero, 28
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 92
	addi a2, s1, 128
	ld t1, 16(s6)
	jalr ra, 0(t1)
	lbu t0, 128(s1)
	sb t0, 224(s1)
	lbu t0, 129(s1)
	sb t0, 225(s1)
	lbu t0, 130(s1)
	sb t0, 226(s1)
	lbu t0, 131(s1)
	sb t0, 227(s1)
	lbu t0, 132(s1)
	sb t0, 228(s1)
	lbu t0, 133(s1)
	sb t0, 229(s1)
	lbu t0, 134(s1)
	sb t0, 230(s1)
	lbu t0, 135(s1)
	sb t0, 231(s1)
	lbu t0, 136(s1)
	sb t0, 232(s1)
	lbu t0, 137(s1)
	sb t0, 233(s1)
	lbu t0, 138(s1)
	sb t0, 234(s1)
	lbu t0, 139(s1)
	sb t0, 235(s1)
	lbu t0, 140(s1)
	sb t0, 236(s1)
	lbu t0, 141(s1)
	sb t0, 237(s1)
	lbu t0, 142(s1)
	sb t0, 238(s1)
	lbu t0, 143(s1)
	sb t0, 239(s1)
	lbu t0, 144(s1)
	sb t0, 240(s1)
	lbu t0, 145(s1)
	sb t0, 241(s1)
	lbu t0, 146(s1)
	sb t0, 242(s1)
	lbu t0, 147(s1)
	sb t0, 243(s1)
	lbu t0, 148(s1)
	sb t0, 244(s1)
	lbu t0, 149(s1)
	sb t0, 245(s1)
	lbu t0, 150(s1)
	sb t0, 246(s1)
	lbu t0, 151(s1)
	sb t0, 247(s1)
	lbu t0, 152(s1)
	sb t0, 248(s1)
	lbu t0, 153(s1)
	sb t0, 249(s1)
	lbu t0, 154(s1)
	sb t0, 250(s1)
	lbu t0, 155(s1)
	sb t0, 251(s1)
	addi a0, s0, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi t5, zero, 54
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 0
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi t5, zero, 92
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 192
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 64
	addi a2, s1, 128
	addi a3, zero, 28
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 92
	addi a2, s0, 512
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 64
	addi a2, s0, 512
	addi a3, zero, 28
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 92
	addi a2, s1, 128
	ld t1, 16(s6)
	jalr ra, 0(t1)
	lbu t0, 128(s1)
	sb t0, 252(s1)
	lbu t0, 129(s1)
	sb t0, 253(s1)
	lbu t0, 130(s1)
	sb t0, 254(s1)
	lbu t0, 131(s1)
	sb t0, 255(s1)
	addi a0, s2, 0
	addi a1, s3, 0
	addi a2, s1, 192
	addi a3, s1, 224
	addi a4, s0, 0
	call {vg_ecdsa_secp256k1_sign_k}
	addi s5, s5, -1
	andi t0, a0, 1
	addi t0, t0, -1
	and t6, t0, s5
	bnez t6, 230f
	addi t6, zero, 0
	j 231f
230:
	addi t0, zero, 0
	sb t0, 156(s1)
	addi a0, s0, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi t5, zero, 54
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 0
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi t5, zero, 92
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 192
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 64
	addi a2, s1, 128
	addi a3, zero, 29
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 93
	addi a2, s0, 512
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 64
	addi a2, s0, 512
	addi a3, zero, 28
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 92
	addi a2, s1, 64
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi t5, zero, 54
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 0
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi t5, zero, 92
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	lwu t1, 84(s1)
	xor t1, t1, t5
	sw t1, 404(s0)
	lwu t1, 88(s1)
	xor t1, t1, t5
	sw t1, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 192
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 64
	addi a2, s1, 128
	addi a3, zero, 28
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 92
	addi a2, s0, 512
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 64
	addi a2, s0, 512
	addi a3, zero, 28
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 92
	addi a2, s1, 128
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi t6, zero, 1
231:
	bnez t6, 229b
	addi t0, zero, 0
	sd t0, 64(s1)
	sd t0, 72(s1)
	sd t0, 80(s1)
	sd t0, 88(s1)
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
	ld ra, 0(s1)
	ld s0, 8(s1)
	ld s2, 24(s1)
	ld s3, 32(s1)
	ld s4, 40(s1)
	ld s5, 48(s1)
	ld s6, 56(s1)
	ld s1, 16(s1)
	addi sp, sp, 256
25:
	j 23f
22:
	addi sp, sp, -256
	addi t0, sp, 0
	sd ra, 0(t0)
	sd s0, 8(t0)
	sd s1, 16(t0)
	sd s2, 24(t0)
	sd s3, 32(t0)
	sd s4, 40(t0)
	sd s5, 48(t0)
	sd s6, 56(t0)
	addi s1, t0, 0
	addi s2, a0, 0
	addi s3, a1, 0
	addi s4, a2, 0
	addi s0, a4, 0
	addi s6, a5, 0
	addi t0, zero, 0
	sb t0, 192(s1)
	addi t0, zero, 0
	sb t0, 193(s1)
	addi t0, zero, 0
	sb t0, 194(s1)
	addi t0, zero, 0
	sb t0, 195(s1)
	addi t0, zero, 0
	sb t0, 196(s1)
	addi t0, zero, 0
	sb t0, 197(s1)
	addi t0, zero, 0
	sb t0, 198(s1)
	addi t0, zero, 0
	sb t0, 199(s1)
	addi t0, zero, 0
	sb t0, 200(s1)
	addi t0, zero, 0
	sb t0, 201(s1)
	addi t0, zero, 0
	sb t0, 202(s1)
	addi t0, zero, 0
	sb t0, 203(s1)
	lbu t0, 0(s4)
	sb t0, 204(s1)
	lbu t0, 1(s4)
	sb t0, 205(s1)
	lbu t0, 2(s4)
	sb t0, 206(s1)
	lbu t0, 3(s4)
	sb t0, 207(s1)
	lbu t0, 4(s4)
	sb t0, 208(s1)
	lbu t0, 5(s4)
	sb t0, 209(s1)
	lbu t0, 6(s4)
	sb t0, 210(s1)
	lbu t0, 7(s4)
	sb t0, 211(s1)
	lbu t0, 8(s4)
	sb t0, 212(s1)
	lbu t0, 9(s4)
	sb t0, 213(s1)
	lbu t0, 10(s4)
	sb t0, 214(s1)
	lbu t0, 11(s4)
	sb t0, 215(s1)
	lbu t0, 12(s4)
	sb t0, 216(s1)
	lbu t0, 13(s4)
	sb t0, 217(s1)
	lbu t0, 14(s4)
	sb t0, 218(s1)
	lbu t0, 15(s4)
	sb t0, 219(s1)
	lbu t0, 16(s4)
	sb t0, 220(s1)
	lbu t0, 17(s4)
	sb t0, 221(s1)
	lbu t0, 18(s4)
	sb t0, 222(s1)
	lbu t0, 19(s4)
	sb t0, 223(s1)
	addi t0, zero, 0
	sb t0, 64(s1)
	addi t0, zero, 0
	sb t0, 65(s1)
	addi t0, zero, 0
	sb t0, 66(s1)
	addi t0, zero, 0
	sb t0, 67(s1)
	addi t0, zero, 0
	sb t0, 68(s1)
	addi t0, zero, 0
	sb t0, 69(s1)
	addi t0, zero, 0
	sb t0, 70(s1)
	addi t0, zero, 0
	sb t0, 71(s1)
	addi t0, zero, 0
	sb t0, 72(s1)
	addi t0, zero, 0
	sb t0, 73(s1)
	addi t0, zero, 0
	sb t0, 74(s1)
	addi t0, zero, 0
	sb t0, 75(s1)
	addi t0, zero, 0
	sb t0, 76(s1)
	addi t0, zero, 0
	sb t0, 77(s1)
	addi t0, zero, 0
	sb t0, 78(s1)
	addi t0, zero, 0
	sb t0, 79(s1)
	addi t0, zero, 0
	sb t0, 80(s1)
	addi t0, zero, 0
	sb t0, 81(s1)
	addi t0, zero, 0
	sb t0, 82(s1)
	addi t0, zero, 0
	sb t0, 83(s1)
	addi t0, zero, 1
	sb t0, 128(s1)
	addi t0, zero, 1
	sb t0, 129(s1)
	addi t0, zero, 1
	sb t0, 130(s1)
	addi t0, zero, 1
	sb t0, 131(s1)
	addi t0, zero, 1
	sb t0, 132(s1)
	addi t0, zero, 1
	sb t0, 133(s1)
	addi t0, zero, 1
	sb t0, 134(s1)
	addi t0, zero, 1
	sb t0, 135(s1)
	addi t0, zero, 1
	sb t0, 136(s1)
	addi t0, zero, 1
	sb t0, 137(s1)
	addi t0, zero, 1
	sb t0, 138(s1)
	addi t0, zero, 1
	sb t0, 139(s1)
	addi t0, zero, 1
	sb t0, 140(s1)
	addi t0, zero, 1
	sb t0, 141(s1)
	addi t0, zero, 1
	sb t0, 142(s1)
	addi t0, zero, 1
	sb t0, 143(s1)
	addi t0, zero, 1
	sb t0, 144(s1)
	addi t0, zero, 1
	sb t0, 145(s1)
	addi t0, zero, 1
	sb t0, 146(s1)
	addi t0, zero, 1
	sb t0, 147(s1)
	addi t0, zero, 0
	sb t0, 148(s1)
	addi a0, s0, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi t5, zero, 54
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	sw t5, 404(s0)
	sw t5, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 0
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi t5, zero, 92
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	sw t5, 404(s0)
	sw t5, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 192
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 64
	addi a2, s1, 128
	addi a3, zero, 21
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 85
	addi a2, s3, 0
	addi a3, zero, 32
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 117
	addi a2, s1, 192
	addi a3, zero, 32
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 149
	addi a2, s0, 512
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 64
	addi a2, s0, 512
	addi a3, zero, 20
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 84
	addi a2, s1, 64
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi t5, zero, 54
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	sw t5, 404(s0)
	sw t5, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 0
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi t5, zero, 92
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	sw t5, 404(s0)
	sw t5, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 192
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 64
	addi a2, s1, 128
	addi a3, zero, 20
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 84
	addi a2, s0, 512
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 64
	addi a2, s0, 512
	addi a3, zero, 20
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 84
	addi a2, s1, 128
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi t0, zero, 1
	sb t0, 148(s1)
	addi a0, s0, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi t5, zero, 54
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	sw t5, 404(s0)
	sw t5, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 0
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi t5, zero, 92
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	sw t5, 404(s0)
	sw t5, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 192
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 64
	addi a2, s1, 128
	addi a3, zero, 21
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 85
	addi a2, s3, 0
	addi a3, zero, 32
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 117
	addi a2, s1, 192
	addi a3, zero, 32
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 149
	addi a2, s0, 512
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 64
	addi a2, s0, 512
	addi a3, zero, 20
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 84
	addi a2, s1, 64
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi t5, zero, 54
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	sw t5, 404(s0)
	sw t5, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 0
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi t5, zero, 92
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	sw t5, 404(s0)
	sw t5, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 192
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 64
	addi a2, s1, 128
	addi a3, zero, 20
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 84
	addi a2, s0, 512
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 64
	addi a2, s0, 512
	addi a3, zero, 20
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 84
	addi a2, s1, 128
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi s5, zero, 8
232:
	addi a0, s0, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi t5, zero, 54
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	sw t5, 404(s0)
	sw t5, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 0
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi t5, zero, 92
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	sw t5, 404(s0)
	sw t5, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 192
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 64
	addi a2, s1, 128
	addi a3, zero, 20
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 84
	addi a2, s0, 512
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 64
	addi a2, s0, 512
	addi a3, zero, 20
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 84
	addi a2, s1, 128
	ld t1, 16(s6)
	jalr ra, 0(t1)
	lbu t0, 128(s1)
	sb t0, 224(s1)
	lbu t0, 129(s1)
	sb t0, 225(s1)
	lbu t0, 130(s1)
	sb t0, 226(s1)
	lbu t0, 131(s1)
	sb t0, 227(s1)
	lbu t0, 132(s1)
	sb t0, 228(s1)
	lbu t0, 133(s1)
	sb t0, 229(s1)
	lbu t0, 134(s1)
	sb t0, 230(s1)
	lbu t0, 135(s1)
	sb t0, 231(s1)
	lbu t0, 136(s1)
	sb t0, 232(s1)
	lbu t0, 137(s1)
	sb t0, 233(s1)
	lbu t0, 138(s1)
	sb t0, 234(s1)
	lbu t0, 139(s1)
	sb t0, 235(s1)
	lbu t0, 140(s1)
	sb t0, 236(s1)
	lbu t0, 141(s1)
	sb t0, 237(s1)
	lbu t0, 142(s1)
	sb t0, 238(s1)
	lbu t0, 143(s1)
	sb t0, 239(s1)
	lbu t0, 144(s1)
	sb t0, 240(s1)
	lbu t0, 145(s1)
	sb t0, 241(s1)
	lbu t0, 146(s1)
	sb t0, 242(s1)
	lbu t0, 147(s1)
	sb t0, 243(s1)
	addi a0, s0, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi t5, zero, 54
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	sw t5, 404(s0)
	sw t5, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 0
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi t5, zero, 92
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	sw t5, 404(s0)
	sw t5, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 192
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 64
	addi a2, s1, 128
	addi a3, zero, 20
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 84
	addi a2, s0, 512
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 64
	addi a2, s0, 512
	addi a3, zero, 20
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 84
	addi a2, s1, 128
	ld t1, 16(s6)
	jalr ra, 0(t1)
	lbu t0, 128(s1)
	sb t0, 244(s1)
	lbu t0, 129(s1)
	sb t0, 245(s1)
	lbu t0, 130(s1)
	sb t0, 246(s1)
	lbu t0, 131(s1)
	sb t0, 247(s1)
	lbu t0, 132(s1)
	sb t0, 248(s1)
	lbu t0, 133(s1)
	sb t0, 249(s1)
	lbu t0, 134(s1)
	sb t0, 250(s1)
	lbu t0, 135(s1)
	sb t0, 251(s1)
	lbu t0, 136(s1)
	sb t0, 252(s1)
	lbu t0, 137(s1)
	sb t0, 253(s1)
	lbu t0, 138(s1)
	sb t0, 254(s1)
	lbu t0, 139(s1)
	sb t0, 255(s1)
	addi a0, s2, 0
	addi a1, s3, 0
	addi a2, s1, 192
	addi a3, s1, 224
	addi a4, s0, 0
	call {vg_ecdsa_secp256k1_sign_k}
	addi s5, s5, -1
	andi t0, a0, 1
	addi t0, t0, -1
	and t6, t0, s5
	bnez t6, 233f
	addi t6, zero, 0
	j 234f
233:
	addi t0, zero, 0
	sb t0, 148(s1)
	addi a0, s0, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi t5, zero, 54
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	sw t5, 404(s0)
	sw t5, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 0
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi t5, zero, 92
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	sw t5, 404(s0)
	sw t5, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 192
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 64
	addi a2, s1, 128
	addi a3, zero, 21
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 85
	addi a2, s0, 512
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 64
	addi a2, s0, 512
	addi a3, zero, 20
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 84
	addi a2, s1, 64
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi t5, zero, 54
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	sw t5, 404(s0)
	sw t5, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 0
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi t5, zero, 92
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	lwu t1, 80(s1)
	xor t1, t1, t5
	sw t1, 400(s0)
	sw t5, 404(s0)
	sw t5, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 192
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 64
	addi a2, s1, 128
	addi a3, zero, 20
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 84
	addi a2, s0, 512
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 64
	addi a2, s0, 512
	addi a3, zero, 20
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 84
	addi a2, s1, 128
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi t6, zero, 1
234:
	bnez t6, 232b
	addi t0, zero, 0
	sd t0, 64(s1)
	sd t0, 72(s1)
	sd t0, 80(s1)
	sd t0, 88(s1)
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
	ld ra, 0(s1)
	ld s0, 8(s1)
	ld s2, 24(s1)
	ld s3, 32(s1)
	ld s4, 40(s1)
	ld s5, 48(s1)
	ld s6, 56(s1)
	ld s1, 16(s1)
	addi sp, sp, 256
23:
	j 21f
20:
	addi sp, sp, -256
	addi t0, sp, 0
	sd ra, 0(t0)
	sd s0, 8(t0)
	sd s1, 16(t0)
	sd s2, 24(t0)
	sd s3, 32(t0)
	sd s4, 40(t0)
	sd s5, 48(t0)
	sd s6, 56(t0)
	addi s1, t0, 0
	addi s2, a0, 0
	addi s3, a1, 0
	addi s4, a2, 0
	addi s0, a4, 0
	addi s6, a5, 0
	addi t0, zero, 0
	sb t0, 192(s1)
	addi t0, zero, 0
	sb t0, 193(s1)
	addi t0, zero, 0
	sb t0, 194(s1)
	addi t0, zero, 0
	sb t0, 195(s1)
	addi t0, zero, 0
	sb t0, 196(s1)
	addi t0, zero, 0
	sb t0, 197(s1)
	addi t0, zero, 0
	sb t0, 198(s1)
	addi t0, zero, 0
	sb t0, 199(s1)
	addi t0, zero, 0
	sb t0, 200(s1)
	addi t0, zero, 0
	sb t0, 201(s1)
	addi t0, zero, 0
	sb t0, 202(s1)
	addi t0, zero, 0
	sb t0, 203(s1)
	addi t0, zero, 0
	sb t0, 204(s1)
	addi t0, zero, 0
	sb t0, 205(s1)
	addi t0, zero, 0
	sb t0, 206(s1)
	addi t0, zero, 0
	sb t0, 207(s1)
	lbu t0, 0(s4)
	sb t0, 208(s1)
	lbu t0, 1(s4)
	sb t0, 209(s1)
	lbu t0, 2(s4)
	sb t0, 210(s1)
	lbu t0, 3(s4)
	sb t0, 211(s1)
	lbu t0, 4(s4)
	sb t0, 212(s1)
	lbu t0, 5(s4)
	sb t0, 213(s1)
	lbu t0, 6(s4)
	sb t0, 214(s1)
	lbu t0, 7(s4)
	sb t0, 215(s1)
	lbu t0, 8(s4)
	sb t0, 216(s1)
	lbu t0, 9(s4)
	sb t0, 217(s1)
	lbu t0, 10(s4)
	sb t0, 218(s1)
	lbu t0, 11(s4)
	sb t0, 219(s1)
	lbu t0, 12(s4)
	sb t0, 220(s1)
	lbu t0, 13(s4)
	sb t0, 221(s1)
	lbu t0, 14(s4)
	sb t0, 222(s1)
	lbu t0, 15(s4)
	sb t0, 223(s1)
	addi t0, zero, 0
	sb t0, 64(s1)
	addi t0, zero, 0
	sb t0, 65(s1)
	addi t0, zero, 0
	sb t0, 66(s1)
	addi t0, zero, 0
	sb t0, 67(s1)
	addi t0, zero, 0
	sb t0, 68(s1)
	addi t0, zero, 0
	sb t0, 69(s1)
	addi t0, zero, 0
	sb t0, 70(s1)
	addi t0, zero, 0
	sb t0, 71(s1)
	addi t0, zero, 0
	sb t0, 72(s1)
	addi t0, zero, 0
	sb t0, 73(s1)
	addi t0, zero, 0
	sb t0, 74(s1)
	addi t0, zero, 0
	sb t0, 75(s1)
	addi t0, zero, 0
	sb t0, 76(s1)
	addi t0, zero, 0
	sb t0, 77(s1)
	addi t0, zero, 0
	sb t0, 78(s1)
	addi t0, zero, 0
	sb t0, 79(s1)
	addi t0, zero, 1
	sb t0, 128(s1)
	addi t0, zero, 1
	sb t0, 129(s1)
	addi t0, zero, 1
	sb t0, 130(s1)
	addi t0, zero, 1
	sb t0, 131(s1)
	addi t0, zero, 1
	sb t0, 132(s1)
	addi t0, zero, 1
	sb t0, 133(s1)
	addi t0, zero, 1
	sb t0, 134(s1)
	addi t0, zero, 1
	sb t0, 135(s1)
	addi t0, zero, 1
	sb t0, 136(s1)
	addi t0, zero, 1
	sb t0, 137(s1)
	addi t0, zero, 1
	sb t0, 138(s1)
	addi t0, zero, 1
	sb t0, 139(s1)
	addi t0, zero, 1
	sb t0, 140(s1)
	addi t0, zero, 1
	sb t0, 141(s1)
	addi t0, zero, 1
	sb t0, 142(s1)
	addi t0, zero, 1
	sb t0, 143(s1)
	addi t0, zero, 0
	sb t0, 144(s1)
	addi a0, s0, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi t5, zero, 54
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	sw t5, 400(s0)
	sw t5, 404(s0)
	sw t5, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 0
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi t5, zero, 92
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	sw t5, 400(s0)
	sw t5, 404(s0)
	sw t5, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 192
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 64
	addi a2, s1, 128
	addi a3, zero, 17
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 81
	addi a2, s3, 0
	addi a3, zero, 32
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 113
	addi a2, s1, 192
	addi a3, zero, 32
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 145
	addi a2, s0, 512
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 64
	addi a2, s0, 512
	addi a3, zero, 16
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 80
	addi a2, s1, 64
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi t5, zero, 54
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	sw t5, 400(s0)
	sw t5, 404(s0)
	sw t5, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 0
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi t5, zero, 92
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	sw t5, 400(s0)
	sw t5, 404(s0)
	sw t5, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 192
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 64
	addi a2, s1, 128
	addi a3, zero, 16
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 80
	addi a2, s0, 512
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 64
	addi a2, s0, 512
	addi a3, zero, 16
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 80
	addi a2, s1, 128
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi t0, zero, 1
	sb t0, 144(s1)
	addi a0, s0, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi t5, zero, 54
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	sw t5, 400(s0)
	sw t5, 404(s0)
	sw t5, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 0
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi t5, zero, 92
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	sw t5, 400(s0)
	sw t5, 404(s0)
	sw t5, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 192
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 64
	addi a2, s1, 128
	addi a3, zero, 17
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 81
	addi a2, s3, 0
	addi a3, zero, 32
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 113
	addi a2, s1, 192
	addi a3, zero, 32
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 145
	addi a2, s0, 512
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 64
	addi a2, s0, 512
	addi a3, zero, 16
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 80
	addi a2, s1, 64
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi t5, zero, 54
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	sw t5, 400(s0)
	sw t5, 404(s0)
	sw t5, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 0
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi t5, zero, 92
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	sw t5, 400(s0)
	sw t5, 404(s0)
	sw t5, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 192
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 64
	addi a2, s1, 128
	addi a3, zero, 16
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 80
	addi a2, s0, 512
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 64
	addi a2, s0, 512
	addi a3, zero, 16
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 80
	addi a2, s1, 128
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi s5, zero, 8
235:
	addi a0, s0, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi t5, zero, 54
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	sw t5, 400(s0)
	sw t5, 404(s0)
	sw t5, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 0
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi t5, zero, 92
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	sw t5, 400(s0)
	sw t5, 404(s0)
	sw t5, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 192
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 64
	addi a2, s1, 128
	addi a3, zero, 16
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 80
	addi a2, s0, 512
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 64
	addi a2, s0, 512
	addi a3, zero, 16
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 80
	addi a2, s1, 128
	ld t1, 16(s6)
	jalr ra, 0(t1)
	lbu t0, 128(s1)
	sb t0, 224(s1)
	lbu t0, 129(s1)
	sb t0, 225(s1)
	lbu t0, 130(s1)
	sb t0, 226(s1)
	lbu t0, 131(s1)
	sb t0, 227(s1)
	lbu t0, 132(s1)
	sb t0, 228(s1)
	lbu t0, 133(s1)
	sb t0, 229(s1)
	lbu t0, 134(s1)
	sb t0, 230(s1)
	lbu t0, 135(s1)
	sb t0, 231(s1)
	lbu t0, 136(s1)
	sb t0, 232(s1)
	lbu t0, 137(s1)
	sb t0, 233(s1)
	lbu t0, 138(s1)
	sb t0, 234(s1)
	lbu t0, 139(s1)
	sb t0, 235(s1)
	lbu t0, 140(s1)
	sb t0, 236(s1)
	lbu t0, 141(s1)
	sb t0, 237(s1)
	lbu t0, 142(s1)
	sb t0, 238(s1)
	lbu t0, 143(s1)
	sb t0, 239(s1)
	addi a0, s0, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi t5, zero, 54
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	sw t5, 400(s0)
	sw t5, 404(s0)
	sw t5, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 0
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi t5, zero, 92
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	sw t5, 400(s0)
	sw t5, 404(s0)
	sw t5, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 192
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 64
	addi a2, s1, 128
	addi a3, zero, 16
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 80
	addi a2, s0, 512
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 64
	addi a2, s0, 512
	addi a3, zero, 16
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 80
	addi a2, s1, 128
	ld t1, 16(s6)
	jalr ra, 0(t1)
	lbu t0, 128(s1)
	sb t0, 240(s1)
	lbu t0, 129(s1)
	sb t0, 241(s1)
	lbu t0, 130(s1)
	sb t0, 242(s1)
	lbu t0, 131(s1)
	sb t0, 243(s1)
	lbu t0, 132(s1)
	sb t0, 244(s1)
	lbu t0, 133(s1)
	sb t0, 245(s1)
	lbu t0, 134(s1)
	sb t0, 246(s1)
	lbu t0, 135(s1)
	sb t0, 247(s1)
	lbu t0, 136(s1)
	sb t0, 248(s1)
	lbu t0, 137(s1)
	sb t0, 249(s1)
	lbu t0, 138(s1)
	sb t0, 250(s1)
	lbu t0, 139(s1)
	sb t0, 251(s1)
	lbu t0, 140(s1)
	sb t0, 252(s1)
	lbu t0, 141(s1)
	sb t0, 253(s1)
	lbu t0, 142(s1)
	sb t0, 254(s1)
	lbu t0, 143(s1)
	sb t0, 255(s1)
	addi a0, s2, 0
	addi a1, s3, 0
	addi a2, s1, 192
	addi a3, s1, 224
	addi a4, s0, 0
	call {vg_ecdsa_secp256k1_sign_k}
	addi s5, s5, -1
	andi t0, a0, 1
	addi t0, t0, -1
	and t6, t0, s5
	bnez t6, 236f
	addi t6, zero, 0
	j 237f
236:
	addi t0, zero, 0
	sb t0, 144(s1)
	addi a0, s0, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi t5, zero, 54
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	sw t5, 400(s0)
	sw t5, 404(s0)
	sw t5, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 0
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi t5, zero, 92
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	sw t5, 400(s0)
	sw t5, 404(s0)
	sw t5, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 192
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 64
	addi a2, s1, 128
	addi a3, zero, 17
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 81
	addi a2, s0, 512
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 64
	addi a2, s0, 512
	addi a3, zero, 16
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 80
	addi a2, s1, 64
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	ld t1, 0(s6)
	jalr ra, 0(t1)
	addi t5, zero, 54
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	sw t5, 400(s0)
	sw t5, 404(s0)
	sw t5, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 0
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi t5, zero, 92
	slli t4, t5, 8
	or t5, t5, t4
	slli t4, t5, 16
	or t5, t5, t4
	lwu t1, 64(s1)
	xor t1, t1, t5
	sw t1, 384(s0)
	lwu t1, 68(s1)
	xor t1, t1, t5
	sw t1, 388(s0)
	lwu t1, 72(s1)
	xor t1, t1, t5
	sw t1, 392(s0)
	lwu t1, 76(s1)
	xor t1, t1, t5
	sw t1, 396(s0)
	sw t5, 400(s0)
	sw t5, 404(s0)
	sw t5, 408(s0)
	sw t5, 412(s0)
	sw t5, 416(s0)
	sw t5, 420(s0)
	sw t5, 424(s0)
	sw t5, 428(s0)
	sw t5, 432(s0)
	sw t5, 436(s0)
	sw t5, 440(s0)
	sw t5, 444(s0)
	addi a0, s0, 192
	addi a1, zero, 0
	addi a2, s0, 384
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 64
	addi a2, s1, 128
	addi a3, zero, 16
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 80
	addi a2, s0, 512
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 64
	addi a2, s0, 512
	addi a3, zero, 16
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 192
	addi a1, zero, 80
	addi a2, s1, 128
	ld t1, 16(s6)
	jalr ra, 0(t1)
	addi t6, zero, 1
237:
	bnez t6, 235b
	addi t0, zero, 0
	sd t0, 64(s1)
	sd t0, 72(s1)
	sd t0, 80(s1)
	sd t0, 88(s1)
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
	ld ra, 0(s1)
	ld s0, 8(s1)
	ld s2, 24(s1)
	ld s3, 32(s1)
	ld s4, 40(s1)
	ld s5, 48(s1)
	ld s6, 56(s1)
	ld s1, 16(s1)
	addi sp, sp, 256
21:
	ret
	.option pop
