// The functions of `src/internal/vg_ecdsa_secp256k1_sign.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_secp256k1_sign:
	.option push
	.option arch, +m, +c
	sd s0, 0(a4)
	sd s1, 8(a4)
	sd s2, 16(a4)
	sd ra, 24(a4)
	sd s3, 32(a4)
	addi s0, a4, 0
	addi s3, a4, 0
	addi s2, a0, 0
	lbu t0, 0(a3)
	slli t0, t0, 8
	lbu t1, 1(a3)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 2(a3)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 3(a3)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 4(a3)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 5(a3)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 6(a3)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 7(a3)
	or t0, t0, t1
	sd t0, 1080(s0)
	lbu t0, 8(a3)
	slli t0, t0, 8
	lbu t1, 9(a3)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 10(a3)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 11(a3)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 12(a3)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 13(a3)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 14(a3)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 15(a3)
	or t0, t0, t1
	sd t0, 1072(s0)
	lbu t0, 16(a3)
	slli t0, t0, 8
	lbu t1, 17(a3)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 18(a3)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 19(a3)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 20(a3)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 21(a3)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 22(a3)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 23(a3)
	or t0, t0, t1
	sd t0, 1064(s0)
	lbu t0, 24(a3)
	slli t0, t0, 8
	lbu t1, 25(a3)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 26(a3)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 27(a3)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 28(a3)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 29(a3)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 30(a3)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 31(a3)
	or t0, t0, t1
	sd t0, 1056(s0)
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
	sd t0, 1144(s0)
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
	sd t0, 1136(s0)
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
	sd t0, 1128(s0)
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
	sd t0, 1120(s0)
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
	sd t0, 1176(s0)
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
	sd t0, 1168(s0)
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
	sd t0, 1160(s0)
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
	sd t0, 1152(s0)
	addi t0, zero, 0
	addi t0, t0, -1
	sd t0, 1472(s0)
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
	addi t5, zero, 0
	ld t3, 1120(s0)
	ld t4, 96(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1128(s0)
	ld t4, 104(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1136(s0)
	ld t4, 112(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1144(s0)
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
	xori a7, a7, -1
	ld t0, 1472(s0)
	and t0, t0, a7
	sd t0, 1472(s0)
	ld t0, 320(s0)
	sd t0, 512(s0)
	ld t0, 328(s0)
	sd t0, 520(s0)
	ld t0, 336(s0)
	sd t0, 528(s0)
	ld t0, 344(s0)
	sd t0, 536(s0)
	ld t0, 352(s0)
	sd t0, 544(s0)
	ld t0, 360(s0)
	sd t0, 552(s0)
	ld t0, 368(s0)
	sd t0, 560(s0)
	ld t0, 376(s0)
	sd t0, 568(s0)
	addi t5, zero, 0
	ld t3, 1056(s0)
	ld t4, 96(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1064(s0)
	ld t4, 104(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1072(s0)
	ld t4, 112(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1080(s0)
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
	ld t4, 1056(s0)
	or t3, t3, t4
	ld t4, 1064(s0)
	or t3, t3, t4
	ld t4, 1072(s0)
	or t3, t3, t4
	ld t4, 1080(s0)
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
	call {vg_secp256k1_mul_g}
	addi s0, s3, 0
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
20:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 20b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
21:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 21b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
22:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 22b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
23:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 23b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
24:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 24b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
25:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 25b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
26:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 26b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
27:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 27b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
28:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 28b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
29:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 29b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
210:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 210b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
211:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 211b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
212:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 212b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
213:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 213b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
214:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 214b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
215:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 215b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
216:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 216b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
217:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 217b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
218:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 218b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
219:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 219b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
220:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 220b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
221:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 221b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
222:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 222b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
223:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 223b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
224:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 224b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
225:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 225b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
226:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 226b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
227:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 227b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
228:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 228b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
229:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 229b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
230:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 230b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
231:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 231b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
232:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 232b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
233:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 233b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
234:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 234b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
235:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 235b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
236:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 236b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
237:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 237b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
238:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 238b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
239:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 239b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
240:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 240b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
241:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 241b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
242:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 242b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
243:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 243b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
244:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 244b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
245:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 245b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
246:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 246b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
247:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 247b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
248:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 248b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
249:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 249b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
250:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 250b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
251:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 251b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
252:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 252b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
253:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 253b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 3
254:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 254b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1632
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 5
255:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 255b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 4
256:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_p}
	bnez s1, 256b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_p}
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
	addi s1, zero, 2
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
	addi a3, zero, 1568
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 8
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
	addi a3, zero, 1696
	call {vg_secp256k1_mul_mod_p}
	addi s1, zero, 2
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
	addi a2, zero, 1056
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
263:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 263b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
264:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 264b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
265:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 265b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
266:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 266b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
267:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 267b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
268:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 268b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
269:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 269b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
270:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 270b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
271:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 271b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
272:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 272b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
273:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 273b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
274:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 274b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
275:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 275b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
276:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 276b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
277:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 277b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
278:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 278b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
279:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 279b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
280:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 280b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
281:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 281b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
282:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 282b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
283:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 283b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
284:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 284b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
285:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 285b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
286:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 286b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
287:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 287b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
288:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 288b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
289:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 289b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
290:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 290b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
291:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 291b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
292:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 292b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 3
293:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 293b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1632
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 5
294:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 294b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1696
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 3
295:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 295b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1600
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
296:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 296b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1600
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
297:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 297b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1632
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 5
298:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 298b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1728
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 2
299:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 299b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1568
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 5
2100:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 2100b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1632
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 6
2101:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 2101b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1728
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 5
2102:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 2102b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1696
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
2103:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 2103b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1728
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 3
2104:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 2104b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1536
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 6
2105:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 2105b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1600
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 10
2106:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 2106b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1632
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
2107:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 2107b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1632
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 5
2108:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 2108b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
2109:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 2109b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 5
2110:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 2110b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1664
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 6
2111:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 2111b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1696
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
2112:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 2112b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1728
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 5
2113:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 2113b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1568
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 6
2114:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 2114b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1728
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 10
2115:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 2115b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1728
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
2116:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 2116b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1664
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 9
2117:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 2117b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1664
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 4
2118:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 2118b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_secp256k1_mul_mod_n}
	addi s1, zero, 1
2119:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_secp256k1_mul_mod_n}
	bnez s1, 2119b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1536
	call {vg_secp256k1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 736
	addi a2, zero, 1152
	addi a3, zero, 1184
	call {vg_secp256k1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 768
	addi a2, zero, 672
	addi a3, zero, 1184
	call {vg_secp256k1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 800
	addi a2, zero, 1120
	addi a3, zero, 1184
	call {vg_secp256k1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 832
	addi a2, zero, 768
	addi a3, zero, 800
	call {vg_secp256k1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 736
	addi a3, zero, 832
	call {vg_secp256k1_add_mod_n}
	addi a0, s0, 0
	addi a1, zero, 896
	addi a2, zero, 992
	addi a3, zero, 864
	call {vg_secp256k1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 928
	addi a2, zero, 896
	addi a3, zero, 192
	call {vg_secp256k1_mul_mod_n}
	addi t3, zero, 0
	ld t4, 672(s0)
	or t3, t3, t4
	ld t4, 680(s0)
	or t3, t3, t4
	ld t4, 688(s0)
	or t3, t3, t4
	ld t4, 696(s0)
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
	ld t4, 928(s0)
	or t3, t3, t4
	ld t4, 936(s0)
	or t3, t3, t4
	ld t4, 944(s0)
	or t3, t3, t4
	ld t4, 952(s0)
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
	ld a7, 1472(s0)
	ld t0, 696(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 0(s2)
	srli t1, t0, 48
	sb t1, 1(s2)
	srli t1, t0, 40
	sb t1, 2(s2)
	srli t1, t0, 32
	sb t1, 3(s2)
	srli t1, t0, 24
	sb t1, 4(s2)
	srli t1, t0, 16
	sb t1, 5(s2)
	srli t1, t0, 8
	sb t1, 6(s2)
	srli t1, t0, 0
	sb t1, 7(s2)
	ld t0, 688(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 8(s2)
	srli t1, t0, 48
	sb t1, 9(s2)
	srli t1, t0, 40
	sb t1, 10(s2)
	srli t1, t0, 32
	sb t1, 11(s2)
	srli t1, t0, 24
	sb t1, 12(s2)
	srli t1, t0, 16
	sb t1, 13(s2)
	srli t1, t0, 8
	sb t1, 14(s2)
	srli t1, t0, 0
	sb t1, 15(s2)
	ld t0, 680(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 16(s2)
	srli t1, t0, 48
	sb t1, 17(s2)
	srli t1, t0, 40
	sb t1, 18(s2)
	srli t1, t0, 32
	sb t1, 19(s2)
	srli t1, t0, 24
	sb t1, 20(s2)
	srli t1, t0, 16
	sb t1, 21(s2)
	srli t1, t0, 8
	sb t1, 22(s2)
	srli t1, t0, 0
	sb t1, 23(s2)
	ld t0, 672(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 24(s2)
	srli t1, t0, 48
	sb t1, 25(s2)
	srli t1, t0, 40
	sb t1, 26(s2)
	srli t1, t0, 32
	sb t1, 27(s2)
	srli t1, t0, 24
	sb t1, 28(s2)
	srli t1, t0, 16
	sb t1, 29(s2)
	srli t1, t0, 8
	sb t1, 30(s2)
	srli t1, t0, 0
	sb t1, 31(s2)
	ld t0, 952(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 32(s2)
	srli t1, t0, 48
	sb t1, 33(s2)
	srli t1, t0, 40
	sb t1, 34(s2)
	srli t1, t0, 32
	sb t1, 35(s2)
	srli t1, t0, 24
	sb t1, 36(s2)
	srli t1, t0, 16
	sb t1, 37(s2)
	srli t1, t0, 8
	sb t1, 38(s2)
	srli t1, t0, 0
	sb t1, 39(s2)
	ld t0, 944(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 40(s2)
	srli t1, t0, 48
	sb t1, 41(s2)
	srli t1, t0, 40
	sb t1, 42(s2)
	srli t1, t0, 32
	sb t1, 43(s2)
	srli t1, t0, 24
	sb t1, 44(s2)
	srli t1, t0, 16
	sb t1, 45(s2)
	srli t1, t0, 8
	sb t1, 46(s2)
	srli t1, t0, 0
	sb t1, 47(s2)
	ld t0, 936(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 48(s2)
	srli t1, t0, 48
	sb t1, 49(s2)
	srli t1, t0, 40
	sb t1, 50(s2)
	srli t1, t0, 32
	sb t1, 51(s2)
	srli t1, t0, 24
	sb t1, 52(s2)
	srli t1, t0, 16
	sb t1, 53(s2)
	srli t1, t0, 8
	sb t1, 54(s2)
	srli t1, t0, 0
	sb t1, 55(s2)
	ld t0, 928(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 56(s2)
	srli t1, t0, 48
	sb t1, 57(s2)
	srli t1, t0, 40
	sb t1, 58(s2)
	srli t1, t0, 32
	sb t1, 59(s2)
	srli t1, t0, 24
	sb t1, 60(s2)
	srli t1, t0, 16
	sb t1, 61(s2)
	srli t1, t0, 8
	sb t1, 62(s2)
	srli t1, t0, 0
	sb t1, 63(s2)
	ld a0, 1472(s0)
	andi a0, a0, 1
	ld ra, 24(s0)
	ld s2, 16(s0)
	ld s1, 8(s0)
	ld s3, 32(s0)
	ld s0, 0(s0)
	ret
	.option pop
