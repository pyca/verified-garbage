// The functions of `src/ecdsa_brainpoolp512r1.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_brainpoolp512r1_verify:
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
	addi s0, s0, 2047
	sd t0, 185(s0)
	addi s0, s0, -2047
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
	addi s0, s0, 2047
	sd t0, 177(s0)
	addi s0, s0, -2047
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
	addi s0, s0, 2047
	sd t0, 169(s0)
	addi s0, s0, -2047
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
	addi s0, s0, 2047
	sd t0, 161(s0)
	addi s0, s0, -2047
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
	addi s0, s0, 2047
	sd t0, 153(s0)
	addi s0, s0, -2047
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
	addi s0, s0, 2047
	sd t0, 145(s0)
	addi s0, s0, -2047
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
	addi s0, s0, 2047
	sd t0, 137(s0)
	addi s0, s0, -2047
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
	addi s0, s0, 2047
	sd t0, 129(s0)
	addi s0, s0, -2047
	lbu t0, 65(a0)
	slli t0, t0, 8
	lbu t1, 66(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 67(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 68(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 69(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 70(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 71(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 72(a0)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 377(s0)
	addi s0, s0, -2047
	lbu t0, 73(a0)
	slli t0, t0, 8
	lbu t1, 74(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 75(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 76(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 77(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 78(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 79(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 80(a0)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 369(s0)
	addi s0, s0, -2047
	lbu t0, 81(a0)
	slli t0, t0, 8
	lbu t1, 82(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 83(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 84(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 85(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 86(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 87(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 88(a0)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 361(s0)
	addi s0, s0, -2047
	lbu t0, 89(a0)
	slli t0, t0, 8
	lbu t1, 90(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 91(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 92(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 93(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 94(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 95(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 96(a0)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 353(s0)
	addi s0, s0, -2047
	lbu t0, 97(a0)
	slli t0, t0, 8
	lbu t1, 98(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 99(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 100(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 101(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 102(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 103(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 104(a0)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 345(s0)
	addi s0, s0, -2047
	lbu t0, 105(a0)
	slli t0, t0, 8
	lbu t1, 106(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 107(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 108(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 109(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 110(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 111(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 112(a0)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 337(s0)
	addi s0, s0, -2047
	lbu t0, 113(a0)
	slli t0, t0, 8
	lbu t1, 114(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 115(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 116(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 117(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 118(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 119(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 120(a0)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 329(s0)
	addi s0, s0, -2047
	lbu t0, 121(a0)
	slli t0, t0, 8
	lbu t1, 122(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 123(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 124(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 125(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 126(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 127(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 128(a0)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 321(s0)
	addi s0, s0, -2047
	lbu t0, 0(a0)
	xori t0, t0, 4
	addi t0, t0, -1
	srli t0, t0, 63
	addi t1, zero, 0
	sub a7, t1, t0
	addi s0, s0, 2047
	sd a7, 833(s0)
	addi s0, s0, -2047
	lui t0, 166566
	addiw t0, t0, 86
	slli t0, t0, 32
	lui t1, 361381
	addiw t1, t1, -1805
	add t0, t0, t1
	sd t0, 64(s0)
	lui t0, 165920
	addiw t0, t0, -209
	slli t0, t0, 32
	lui t1, 186412
	addiw t1, t1, 1669
	add t0, t0, t1
	sd t0, 72(s0)
	lui t0, 715994
	addiw t0, t0, 299
	slli t0, t0, 32
	lui t1, 944696
	addiw t1, t1, 230
	add t0, t0, t1
	sd t0, 80(s0)
	lui t0, 513242
	addiw t0, t0, -1279
	slli t0, t0, 32
	lui t1, 638055
	addiw t1, t1, -1982
	add t0, t0, t1
	sd t0, 88(s0)
	lui t0, 878138
	addiw t0, t0, -822
	slli t0, t0, 32
	lui t1, 459569
	addiw t1, t1, -1935
	add t0, t0, t1
	sd t0, 96(s0)
	lui t0, 832265
	addiw t0, t0, -588
	slli t0, t0, 32
	lui t1, 736413
	addiw t1, t1, 526
	add t0, t0, t1
	sd t0, 104(s0)
	lui t0, 261454
	addiw t0, t0, 1710
	slli t0, t0, 32
	lui t1, 212128
	addiw t1, t1, -1017
	add t0, t0, t1
	sd t0, 112(s0)
	lui t0, 699866
	addiw t0, t0, -583
	slli t0, t0, 32
	lui t1, 900764
	addiw t1, t1, 1163
	add t0, t0, t1
	sd t0, 120(s0)
	lui t0, 743545
	addiw t0, t0, 1667
	slli t0, t0, 32
	lui t1, 641680
	addiw t1, t1, 105
	add t0, t0, t1
	sd t0, 128(s0)
	lui t0, 121629
	addiw t0, t0, 897
	slli t0, t0, 32
	lui t1, 34270
	addiw t1, t1, -1315
	add t0, t0, t1
	sd t0, 136(s0)
	lui t0, 268390
	addiw t0, t0, 281
	slli t0, t0, 32
	lui t1, 522945
	addiw t1, t1, 71
	add t0, t0, t1
	sd t0, 144(s0)
	lui t0, 349158
	addiw t0, t0, -959
	slli t0, t0, 32
	lui t1, 314002
	addiw t1, t1, 1561
	add t0, t0, t1
	sd t0, 152(s0)
	lui t0, 878138
	addiw t0, t0, -822
	slli t0, t0, 32
	lui t1, 459569
	addiw t1, t1, -1936
	add t0, t0, t1
	sd t0, 160(s0)
	lui t0, 832265
	addiw t0, t0, -588
	slli t0, t0, 32
	lui t1, 736413
	addiw t1, t1, 526
	add t0, t0, t1
	sd t0, 168(s0)
	lui t0, 261454
	addiw t0, t0, 1710
	slli t0, t0, 32
	lui t1, 212128
	addiw t1, t1, -1017
	add t0, t0, t1
	sd t0, 176(s0)
	lui t0, 699866
	addiw t0, t0, -583
	slli t0, t0, 32
	lui t1, 900764
	addiw t1, t1, 1163
	add t0, t0, t1
	sd t0, 184(s0)
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
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
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
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 1
	add t0, t0, t1
	sd t0, 320(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 328(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 336(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 344(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 352(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 360(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 368(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 376(s0)
	lui t0, 882010
	addiw t0, t0, -86
	slli t0, t0, 32
	lui t1, 687195
	addiw t1, t1, 1805
	add t0, t0, t1
	sd t0, 384(s0)
	lui t0, 882656
	addiw t0, t0, 209
	slli t0, t0, 32
	lui t1, 862164
	addiw t1, t1, -1670
	add t0, t0, t1
	sd t0, 392(s0)
	lui t0, 332582
	addiw t0, t0, -299
	slli t0, t0, 32
	lui t1, 103880
	addiw t1, t1, -231
	add t0, t0, t1
	sd t0, 400(s0)
	lui t0, 535334
	addiw t0, t0, 1279
	slli t0, t0, 32
	lui t1, 410521
	addiw t1, t1, 1981
	add t0, t0, t1
	sd t0, 408(s0)
	lui t0, 170438
	addiw t0, t0, 822
	slli t0, t0, 32
	lui t1, 589007
	addiw t1, t1, 1934
	add t0, t0, t1
	sd t0, 416(s0)
	lui t0, 216311
	addiw t0, t0, 588
	slli t0, t0, 32
	lui t1, 312163
	addiw t1, t1, -527
	add t0, t0, t1
	sd t0, 424(s0)
	lui t0, 787122
	addiw t0, t0, -1710
	slli t0, t0, 32
	lui t1, 836448
	addiw t1, t1, 1016
	add t0, t0, t1
	sd t0, 432(s0)
	lui t0, 348710
	addiw t0, t0, 583
	slli t0, t0, 32
	lui t1, 147812
	addiw t1, t1, -1164
	add t0, t0, t1
	sd t0, 440(s0)
	lui t0, 893433
	addiw t0, t0, -1483
	slli t0, t0, 32
	lui t1, 958732
	addiw t1, t1, 1094
	add t0, t0, t1
	sd t0, 448(s0)
	lui t0, 85577
	addiw t0, t0, 1406
	slli t0, t0, 32
	lui t1, 719485
	addiw t1, t1, 643
	add t0, t0, t1
	sd t0, 456(s0)
	lui t0, 264965
	addiw t0, t0, -1166
	slli t0, t0, 32
	lui t1, 288604
	addiw t1, t1, -1109
	add t0, t0, t1
	sd t0, 464(s0)
	lui t0, 850160
	addiw t0, t0, 274
	slli t0, t0, 32
	lui t1, 648936
	addiw t1, t1, 2047
	add t0, t0, t1
	sd t0, 472(s0)
	lui t0, 679619
	addiw t0, t0, 200
	slli t0, t0, 32
	lui t1, 260109
	addiw t1, t1, 455
	add t0, t0, t1
	sd t0, 480(s0)
	lui t0, 99025
	addiw t0, t0, -166
	slli t0, t0, 32
	lui t1, 999912
	addiw t1, t1, 1912
	add t0, t0, t1
	sd t0, 488(s0)
	lui t0, 754616
	addiw t0, t0, 1275
	slli t0, t0, 32
	lui t1, 929032
	addiw t1, t1, 1292
	add t0, t0, t1
	sd t0, 496(s0)
	lui t0, 388175
	addiw t0, t0, 391
	slli t0, t0, 32
	lui t1, 141267
	addiw t1, t1, -1405
	add t0, t0, t1
	sd t0, 504(s0)
	lui t0, 822547
	addiw t0, t0, -1428
	slli t0, t0, 32
	lui t1, 43027
	addiw t1, t1, 1449
	add t0, t0, t1
	sd t0, 512(s0)
	lui t0, 890115
	addiw t0, t0, -983
	slli t0, t0, 32
	lui t1, 537221
	addiw t1, t1, -2025
	add t0, t0, t1
	sd t0, 520(s0)
	lui t0, 1005397
	addiw t0, t0, -1064
	slli t0, t0, 32
	lui t1, 663327
	addiw t1, t1, -745
	add t0, t0, t1
	sd t0, 528(s0)
	lui t0, 886479
	addiw t0, t0, 1977
	slli t0, t0, 32
	lui t1, 186893
	addiw t1, t1, 453
	add t0, t0, t1
	sd t0, 536(s0)
	lui t0, 988105
	addiw t0, t0, -1950
	slli t0, t0, 32
	lui t1, 566070
	addiw t1, t1, 1065
	add t0, t0, t1
	sd t0, 544(s0)
	lui t0, 624104
	addiw t0, t0, -1710
	slli t0, t0, 32
	lui t1, 604123
	addiw t1, t1, 1609
	add t0, t0, t1
	sd t0, 552(s0)
	lui t0, 969029
	addiw t0, t0, 321
	slli t0, t0, 32
	lui t1, 980336
	addiw t1, t1, 992
	add t0, t0, t1
	sd t0, 560(s0)
	lui t0, 606246
	addiw t0, t0, 1380
	slli t0, t0, 32
	lui t1, 1021726
	addiw t1, t1, 1898
	add t0, t0, t1
	sd t0, 568(s0)
	lui t0, 806121
	addiw t0, t0, 1545
	slli t0, t0, 32
	lui t1, 333342
	addiw t1, t1, -1581
	add t0, t0, t1
	sd t0, 576(s0)
	lui t0, 426981
	addiw t0, t0, -668
	slli t0, t0, 32
	lui t1, 160448
	addiw t1, t1, 676
	add t0, t0, t1
	sd t0, 584(s0)
	lui t0, 215728
	addiw t0, t0, 1044
	slli t0, t0, 32
	lui t1, 450390
	addiw t1, t1, -369
	add t0, t0, t1
	sd t0, 592(s0)
	lui t0, 546053
	addiw t0, t0, 917
	slli t0, t0, 32
	lui t1, 84994
	addiw t1, t1, -56
	add t0, t0, t1
	sd t0, 600(s0)
	lui t0, 148285
	addiw t0, t0, 1904
	slli t0, t0, 32
	lui t1, 591304
	addiw t1, t1, 1847
	add t0, t0, t1
	sd t0, 608(s0)
	lui t0, 732015
	addiw t0, t0, -1480
	slli t0, t0, 32
	lui t1, 997076
	addiw t1, t1, -777
	add t0, t0, t1
	sd t0, 616(s0)
	lui t0, 553419
	addiw t0, t0, 1482
	slli t0, t0, 32
	lui t1, 1748
	addiw t1, t1, 1395
	add t0, t0, t1
	sd t0, 624(s0)
	lui t0, 369338
	addiw t0, t0, 332
	slli t0, t0, 32
	lui t1, 39247
	addiw t1, t1, -1663
	add t0, t0, t1
	sd t0, 632(s0)
	lui t0, 194822
	addiw t0, t0, 1577
	slli t0, t0, 32
	lui t1, 151619
	addiw t1, t1, -1427
	add t0, t0, t1
	sd t0, 640(s0)
	lui t0, 479630
	addiw t0, t0, -145
	slli t0, t0, 32
	lui t1, 291887
	addiw t1, t1, 805
	add t0, t0, t1
	sd t0, 648(s0)
	lui t0, 784453
	addiw t0, t0, 1363
	slli t0, t0, 32
	lui t1, 313433
	addiw t1, t1, 1168
	add t0, t0, t1
	sd t0, 656(s0)
	lui t0, 221420
	addiw t0, t0, 1909
	slli t0, t0, 32
	lui t1, 366829
	addiw t1, t1, -962
	add t0, t0, t1
	sd t0, 664(s0)
	lui t0, 508273
	addiw t0, t0, -1143
	slli t0, t0, 32
	lui t1, 589411
	addiw t1, t1, -36
	add t0, t0, t1
	sd t0, 672(s0)
	lui t0, 361939
	addiw t0, t0, -1160
	slli t0, t0, 32
	lui t1, 842196
	addiw t1, t1, -116
	add t0, t0, t1
	sd t0, 680(s0)
	lui t0, 632301
	addiw t0, t0, 2011
	slli t0, t0, 32
	lui t1, 553204
	addiw t1, t1, -101
	add t0, t0, t1
	sd t0, 688(s0)
	lui t0, 574733
	addiw t0, t0, -1583
	slli t0, t0, 32
	lui t1, 175287
	addiw t1, t1, 641
	add t0, t0, t1
	sd t0, 696(s0)
	lui t0, 166566
	addiw t0, t0, 86
	slli t0, t0, 32
	lui t1, 361381
	addiw t1, t1, -1807
	add t0, t0, t1
	sd t0, 832(s0)
	lui t0, 165920
	addiw t0, t0, -209
	slli t0, t0, 32
	lui t1, 186412
	addiw t1, t1, 1669
	add t0, t0, t1
	sd t0, 840(s0)
	lui t0, 715994
	addiw t0, t0, 299
	slli t0, t0, 32
	lui t1, 944696
	addiw t1, t1, 230
	add t0, t0, t1
	sd t0, 848(s0)
	lui t0, 513242
	addiw t0, t0, -1279
	slli t0, t0, 32
	lui t1, 638055
	addiw t1, t1, -1982
	add t0, t0, t1
	sd t0, 856(s0)
	lui t0, 878138
	addiw t0, t0, -822
	slli t0, t0, 32
	lui t1, 459569
	addiw t1, t1, -1935
	add t0, t0, t1
	sd t0, 864(s0)
	lui t0, 832265
	addiw t0, t0, -588
	slli t0, t0, 32
	lui t1, 736413
	addiw t1, t1, 526
	add t0, t0, t1
	sd t0, 872(s0)
	lui t0, 261454
	addiw t0, t0, 1710
	slli t0, t0, 32
	lui t1, 212128
	addiw t1, t1, -1017
	add t0, t0, t1
	sd t0, 880(s0)
	lui t0, 699866
	addiw t0, t0, -583
	slli t0, t0, 32
	lui t1, 900764
	addiw t1, t1, 1163
	add t0, t0, t1
	sd t0, 888(s0)
	lui t0, 301777
	addiw t0, t0, 1098
	slli t0, t0, 32
	lui t1, 398735
	addiw t1, t1, 517
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 513(s0)
	addi s0, s0, -2047
	lui t0, 496635
	addiw t0, t0, 304
	slli t0, t0, 32
	lui t1, 160088
	addiw t1, t1, -1787
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 521(s0)
	addi s0, s0, -2047
	lui t0, 342912
	addiw t0, t0, -1603
	slli t0, t0, 32
	lui t1, 591280
	addiw t1, t1, -45
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 529(s0)
	addi s0, s0, -2047
	lui t0, 920602
	addiw t0, t0, -1416
	slli t0, t0, 32
	lui t1, 537877
	addiw t1, t1, -1499
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 537(s0)
	addi s0, s0, -2047
	lui t0, 103559
	addiw t0, t0, -39
	slli t0, t0, 32
	lui t1, 874648
	addiw t1, t1, 87
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 545(s0)
	addi s0, s0, -2047
	lui t0, 661211
	addiw t0, t0, -1440
	slli t0, t0, 32
	lui t1, 869056
	addiw t1, t1, -125
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 553(s0)
	addi s0, s0, -2047
	lui t0, 131810
	addiw t0, t0, -1728
	slli t0, t0, 32
	lui t1, 132463
	addiw t1, t1, -308
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 561(s0)
	addi s0, s0, -2047
	lui t0, 246986
	addiw t0, t0, -762
	slli t0, t0, 32
	lui t1, 696310
	addiw t1, t1, 1104
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 569(s0)
	addi s0, s0, -2047
	lui t0, 329704
	addiw t0, t0, 918
	slli t0, t0, 32
	lui t1, 134803
	addiw t1, t1, -1484
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 577(s0)
	addi s0, s0, -2047
	lui t0, 2486
	addiw t0, t0, 968
	slli t0, t0, 32
	lui t1, 940262
	addiw t1, t1, -1484
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 585(s0)
	addi s0, s0, -2047
	lui t0, 923322
	addiw t0, t0, 1110
	slli t0, t0, 32
	lui t1, 186482
	addiw t1, t1, 1194
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 593(s0)
	addi s0, s0, -2047
	lui t0, 816099
	addiw t0, t0, 233
	slli t0, t0, 32
	lui t1, 624508
	addiw t1, t1, -510
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 601(s0)
	addi s0, s0, -2047
	lui t0, 622081
	addiw t0, t0, -924
	slli t0, t0, 32
	lui t1, 1040930
	addiw t1, t1, 1075
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 609(s0)
	addi s0, s0, -2047
	lui t0, 834981
	addiw t0, t0, 1964
	slli t0, t0, 32
	lui t1, 446846
	addiw t1, t1, -2019
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 617(s0)
	addi s0, s0, -2047
	lui t0, 410161
	addiw t0, t0, 677
	slli t0, t0, 32
	lui t1, 47963
	addiw t1, t1, -1374
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 625(s0)
	addi s0, s0, -2047
	lui t0, 435371
	addiw t0, t0, -1100
	slli t0, t0, 32
	lui t1, 291305
	addiw t1, t1, -345
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 633(s0)
	addi s0, s0, -2047
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
	sd t0, 760(s0)
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
	sd t0, 752(s0)
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
	sd t0, 744(s0)
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
	sd t0, 736(s0)
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
	sd t0, 728(s0)
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
	sd t0, 720(s0)
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
	sd t0, 712(s0)
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
	sd t0, 704(s0)
	lbu t0, 64(a2)
	slli t0, t0, 8
	lbu t1, 65(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 66(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 67(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 68(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 69(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 70(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 71(a2)
	or t0, t0, t1
	sd t0, 824(s0)
	lbu t0, 72(a2)
	slli t0, t0, 8
	lbu t1, 73(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 74(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 75(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 76(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 77(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 78(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 79(a2)
	or t0, t0, t1
	sd t0, 816(s0)
	lbu t0, 80(a2)
	slli t0, t0, 8
	lbu t1, 81(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 82(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 83(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 84(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 85(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 86(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 87(a2)
	or t0, t0, t1
	sd t0, 808(s0)
	lbu t0, 88(a2)
	slli t0, t0, 8
	lbu t1, 89(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 90(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 91(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 92(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 93(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 94(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 95(a2)
	or t0, t0, t1
	sd t0, 800(s0)
	lbu t0, 96(a2)
	slli t0, t0, 8
	lbu t1, 97(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 98(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 99(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 100(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 101(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 102(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 103(a2)
	or t0, t0, t1
	sd t0, 792(s0)
	lbu t0, 104(a2)
	slli t0, t0, 8
	lbu t1, 105(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 106(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 107(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 108(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 109(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 110(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 111(a2)
	or t0, t0, t1
	sd t0, 784(s0)
	lbu t0, 112(a2)
	slli t0, t0, 8
	lbu t1, 113(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 114(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 115(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 116(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 117(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 118(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 119(a2)
	or t0, t0, t1
	sd t0, 776(s0)
	lbu t0, 120(a2)
	slli t0, t0, 8
	lbu t1, 121(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 122(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 123(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 124(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 125(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 126(a2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 127(a2)
	or t0, t0, t1
	sd t0, 768(s0)
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
	addi s0, s0, 2047
	sd t0, 121(s0)
	addi s0, s0, -2047
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
	addi s0, s0, 2047
	sd t0, 113(s0)
	addi s0, s0, -2047
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
	addi s0, s0, 2047
	sd t0, 105(s0)
	addi s0, s0, -2047
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
	addi s0, s0, 2047
	sd t0, 97(s0)
	addi s0, s0, -2047
	lbu t0, 32(a1)
	slli t0, t0, 8
	lbu t1, 33(a1)
	or t0, t0, t1
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
	addi s0, s0, 2047
	sd t0, 89(s0)
	addi s0, s0, -2047
	lbu t0, 40(a1)
	slli t0, t0, 8
	lbu t1, 41(a1)
	or t0, t0, t1
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
	addi s0, s0, 2047
	sd t0, 81(s0)
	addi s0, s0, -2047
	lbu t0, 48(a1)
	slli t0, t0, 8
	lbu t1, 49(a1)
	or t0, t0, t1
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
	addi s0, s0, 2047
	sd t0, 73(s0)
	addi s0, s0, -2047
	lbu t0, 56(a1)
	slli t0, t0, 8
	lbu t1, 57(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 58(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 59(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 60(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 61(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 62(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 63(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 65(s0)
	addi s0, s0, -2047
	addi t5, zero, 0
	ld t3, 704(s0)
	ld t4, 128(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 712(s0)
	ld t4, 136(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 720(s0)
	ld t4, 144(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 728(s0)
	ld t4, 152(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 736(s0)
	ld t4, 160(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 744(s0)
	ld t4, 168(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 752(s0)
	ld t4, 176(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 760(s0)
	ld t4, 184(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t6, zero, 0
	sub a7, t6, t5
	addi t0, s0, 2047
	ld t0, 833(t0)
	and t0, t0, a7
	addi s0, s0, 2047
	sd t0, 833(s0)
	addi s0, s0, -2047
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
	xori a7, a7, -1
	addi t0, s0, 2047
	ld t0, 833(t0)
	and t0, t0, a7
	addi s0, s0, 2047
	sd t0, 833(s0)
	addi s0, s0, -2047
	addi t5, zero, 0
	ld t3, 768(s0)
	ld t4, 128(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 776(s0)
	ld t4, 136(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 784(s0)
	ld t4, 144(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 792(s0)
	ld t4, 152(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 800(s0)
	ld t4, 160(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 808(s0)
	ld t4, 168(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 816(s0)
	ld t4, 176(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 824(s0)
	ld t4, 184(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t6, zero, 0
	sub a7, t6, t5
	addi t0, s0, 2047
	ld t0, 833(t0)
	and t0, t0, a7
	addi s0, s0, 2047
	sd t0, 833(s0)
	addi s0, s0, -2047
	addi t3, zero, 0
	ld t4, 768(s0)
	or t3, t3, t4
	ld t4, 776(s0)
	or t3, t3, t4
	ld t4, 784(s0)
	or t3, t3, t4
	ld t4, 792(s0)
	or t3, t3, t4
	ld t4, 800(s0)
	or t3, t3, t4
	ld t4, 808(s0)
	or t3, t3, t4
	ld t4, 816(s0)
	or t3, t3, t4
	ld t4, 824(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	xori a7, a7, -1
	addi t0, s0, 2047
	ld t0, 833(t0)
	and t0, t0, a7
	addi s0, s0, 2047
	sd t0, 833(s0)
	addi s0, s0, -2047
	addi a0, s0, 0
	call {vg_brainpoolp512r1_check_point}
	addi s0, s3, 0
	lui t0, 862775
	addiw t0, t0, -2017
	slli t0, t0, 32
	lui t1, 842369
	addiw t1, t1, 1649
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 257(s0)
	addi s0, s0, -2047
	lui t0, 34923
	addiw t0, t0, 1881
	slli t0, t0, 32
	lui t1, 610948
	addiw t1, t1, -547
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 265(s0)
	addi s0, s0, -2047
	lui t0, 257125
	addiw t0, t0, -1072
	slli t0, t0, 32
	lui t1, 211830
	addiw t1, t1, 639
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 273(s0)
	addi s0, s0, -2047
	lui t0, 683811
	addiw t0, t0, 199
	slli t0, t0, 32
	lui t1, 192544
	addiw t1, t1, 2024
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 281(s0)
	addi s0, s0, -2047
	lui t0, 884637
	addiw t0, t0, -986
	slli t0, t0, 32
	lui t1, 243601
	addiw t1, t1, -541
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 289(s0)
	addi s0, s0, -2047
	lui t0, 467907
	addiw t0, t0, 1954
	slli t0, t0, 32
	lui t1, 192876
	addiw t1, t1, -1057
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 297(s0)
	addi s0, s0, -2047
	lui t0, 613874
	addiw t0, t0, -1204
	slli t0, t0, 32
	lui t1, 103603
	addiw t1, t1, -426
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 305(s0)
	addi s0, s0, -2047
	lui t0, 686406
	addiw t0, t0, -1942
	slli t0, t0, 32
	lui t1, 464960
	addiw t1, t1, 1968
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 313(s0)
	addi s0, s0, -2047
	lui t0, 305031
	addiw t0, t0, -1667
	slli t0, t0, 32
	lui t1, 406896
	addiw t1, t1, -105
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 321(s0)
	addi s0, s0, -2047
	lui t0, 926947
	addiw t0, t0, -897
	slli t0, t0, 32
	lui t1, 1014306
	addiw t1, t1, 1314
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 329(s0)
	addi s0, s0, -2047
	lui t0, 780186
	addiw t0, t0, -281
	slli t0, t0, 32
	lui t1, 525631
	addiw t1, t1, -72
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 337(s0)
	addi s0, s0, -2047
	lui t0, 699418
	addiw t0, t0, 959
	slli t0, t0, 32
	lui t1, 734574
	addiw t1, t1, -1562
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 345(s0)
	addi s0, s0, -2047
	lui t0, 170438
	addiw t0, t0, 822
	slli t0, t0, 32
	lui t1, 589007
	addiw t1, t1, 1935
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 353(s0)
	addi s0, s0, -2047
	lui t0, 216311
	addiw t0, t0, 588
	slli t0, t0, 32
	lui t1, 312163
	addiw t1, t1, -527
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 361(s0)
	addi s0, s0, -2047
	lui t0, 787122
	addiw t0, t0, -1710
	slli t0, t0, 32
	lui t1, 836448
	addiw t1, t1, 1016
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 369(s0)
	addi s0, s0, -2047
	lui t0, 348710
	addiw t0, t0, 583
	slli t0, t0, 32
	lui t1, 147812
	addiw t1, t1, -1164
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 377(s0)
	addi s0, s0, -2047
	lui t0, 743545
	addiw t0, t0, 1667
	slli t0, t0, 32
	lui t1, 641680
	addiw t1, t1, 103
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 385(s0)
	addi s0, s0, -2047
	lui t0, 121629
	addiw t0, t0, 897
	slli t0, t0, 32
	lui t1, 34270
	addiw t1, t1, -1315
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 393(s0)
	addi s0, s0, -2047
	lui t0, 268390
	addiw t0, t0, 281
	slli t0, t0, 32
	lui t1, 522945
	addiw t1, t1, 71
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 401(s0)
	addi s0, s0, -2047
	lui t0, 349158
	addiw t0, t0, -959
	slli t0, t0, 32
	lui t1, 314002
	addiw t1, t1, 1561
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 409(s0)
	addi s0, s0, -2047
	lui t0, 878138
	addiw t0, t0, -822
	slli t0, t0, 32
	lui t1, 459569
	addiw t1, t1, -1936
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 417(s0)
	addi s0, s0, -2047
	lui t0, 832265
	addiw t0, t0, -588
	slli t0, t0, 32
	lui t1, 736413
	addiw t1, t1, 526
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 425(s0)
	addi s0, s0, -2047
	lui t0, 261454
	addiw t0, t0, 1710
	slli t0, t0, 32
	lui t1, 212128
	addiw t1, t1, -1017
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 433(s0)
	addi s0, s0, -2047
	lui t0, 699866
	addiw t0, t0, -583
	slli t0, t0, 32
	lui t1, 900764
	addiw t1, t1, 1163
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 441(s0)
	addi s0, s0, -2047
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 768
	addi a3, zero, 2047
	addi a3, a3, 257
	call {vg_brainpoolp512r1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 961
	addi a2, zero, 1344
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_brainpoolp512r1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1473
	addi a2, zero, 2047
	addi a2, a2, 961
	addi a3, zero, 2047
	addi a3, a3, 961
	call {vg_brainpoolp512r1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1025
	addi a2, zero, 2047
	addi a2, a2, 961
	addi a3, zero, 2047
	addi a3, a3, 1473
	call {vg_brainpoolp512r1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1089
	addi a2, zero, 2047
	addi a2, a2, 1025
	addi a3, zero, 2047
	addi a3, a3, 1473
	call {vg_brainpoolp512r1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1153
	addi a2, zero, 2047
	addi a2, a2, 1089
	addi a3, zero, 2047
	addi a3, a3, 1473
	call {vg_brainpoolp512r1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1217
	addi a2, zero, 2047
	addi a2, a2, 1153
	addi a3, zero, 2047
	addi a3, a3, 1473
	call {vg_brainpoolp512r1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1281
	addi a2, zero, 2047
	addi a2, a2, 1217
	addi a3, zero, 2047
	addi a3, a3, 1473
	call {vg_brainpoolp512r1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1345
	addi a2, zero, 2047
	addi a2, a2, 1281
	addi a3, zero, 2047
	addi a3, a3, 1473
	call {vg_brainpoolp512r1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1409
	addi a2, zero, 2047
	addi a2, a2, 1345
	addi a3, zero, 2047
	addi a3, a3, 1473
	call {vg_brainpoolp512r1_mul_mod_n}
	addi t0, s0, 2047
	ld t0, 1089(t0)
	sd t0, 1920(s0)
	addi t0, s0, 2047
	ld t0, 1097(t0)
	sd t0, 1928(s0)
	addi t0, s0, 2047
	ld t0, 1105(t0)
	sd t0, 1936(s0)
	addi t0, s0, 2047
	ld t0, 1113(t0)
	sd t0, 1944(s0)
	addi t0, s0, 2047
	ld t0, 1121(t0)
	sd t0, 1952(s0)
	addi t0, s0, 2047
	ld t0, 1129(t0)
	sd t0, 1960(s0)
	addi t0, s0, 2047
	ld t0, 1137(t0)
	sd t0, 1968(s0)
	addi t0, s0, 2047
	ld t0, 1145(t0)
	sd t0, 1976(s0)
	addi s1, zero, 4
20:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 20b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1089
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 5
21:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 21b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1345
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 4
22:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 22b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1345
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 4
23:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 23b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1217
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 4
24:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 24b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1345
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 4
25:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 25b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1281
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 1
26:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 26b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 961
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 7
27:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 27b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1345
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 4
28:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 28b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1281
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 3
29:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 29b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1153
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 5
210:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 210b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1217
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 2
211:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 211b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1025
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 7
212:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 212b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1217
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 7
213:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 213b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1281
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 6
214:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 214b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1409
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 4
215:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 215b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1409
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 4
216:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 216b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1089
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 5
217:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 217b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1153
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 6
218:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 218b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1345
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 5
219:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 219b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1281
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 1
220:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 220b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 961
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 5
221:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 221b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1025
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 6
222:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 222b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1409
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 6
223:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 223b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1217
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 4
224:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 224b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1409
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 2
225:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 225b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1025
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 11
226:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 226b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1409
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 4
227:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 227b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1217
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 3
228:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 228b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1025
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 4
229:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 229b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1025
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 5
230:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 230b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 961
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 7
231:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 231b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1345
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 4
232:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 232b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1281
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 5
233:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 233b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1153
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 3
234:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 234b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1025
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 6
235:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 235b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1409
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 6
236:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 236b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1217
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 4
237:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 237b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1345
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 3
238:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 238b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 961
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 8
239:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 239b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1153
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 5
240:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 240b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1345
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 3
241:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 241b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1025
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 4
242:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 242b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1025
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 6
243:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 243b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1153
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 5
244:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 244b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1153
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 4
245:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 245b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1025
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 5
246:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 246b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1089
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 5
247:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 247b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1153
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 8
248:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 248b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1025
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 4
249:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 249b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1025
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 5
250:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 250b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 961
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 7
251:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 251b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1153
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 8
252:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 252b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1089
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 4
253:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 253b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1089
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 6
254:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 254b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1409
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 4
255:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 255b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1217
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 4
256:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 256b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1153
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 4
257:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 257b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 961
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 8
258:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 258b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1089
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 4
259:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 259b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1025
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 5
260:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 260b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1089
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 5
261:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 261b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1217
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 6
262:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 262b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1217
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 1
263:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 263b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 961
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 6
264:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 264b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1025
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 5
265:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 265b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1089
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 7
266:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 266b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1025
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 6
267:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 267b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1025
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 4
268:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 268b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1025
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 5
269:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 269b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 961
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 5
270:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 270b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1025
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 6
271:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 271b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1281
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 4
272:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 272b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1409
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 4
273:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 273b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1345
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 3
274:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 274b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1025
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 6
275:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 275b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 961
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 6
276:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 276b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 961
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 6
277:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 277b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1153
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 6
278:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 278b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1153
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 5
279:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 279b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1345
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 1
280:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 280b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 961
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 6
281:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 281b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1153
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 5
282:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 282b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1217
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 2
283:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 283b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1025
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 7
284:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 284b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 961
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 5
285:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 285b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 961
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 8
286:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 286b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1281
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 4
287:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 287b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1281
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 4
288:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 288b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1281
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 5
289:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 289b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1281
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 4
290:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 290b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1153
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 5
291:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 291b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1345
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 3
292:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 292b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1089
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 3
293:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 293b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1025
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 8
294:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 294b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1409
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 6
295:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 295b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1281
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 2
296:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 296b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 961
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 8
297:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 297b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1089
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 5
298:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 298b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1153
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 5
299:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 299b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1089
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 5
2100:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 2100b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1217
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 11
2101:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 2101b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1025
	call {vg_brainpoolp512r1_mul_mod_n}
	addi s1, zero, 5
2102:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	bnez s1, 2102b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1153
	call {vg_brainpoolp512r1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 2047
	addi a2, a2, 65
	addi a3, zero, 2047
	addi a3, a3, 257
	call {vg_brainpoolp512r1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1408
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 129
	addi a2, zero, 1472
	addi a3, zero, 320
	call {vg_brainpoolp512r1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 704
	addi a3, zero, 2047
	addi a3, a3, 257
	call {vg_brainpoolp512r1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1472
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 321
	addi a2, zero, 1600
	addi a3, zero, 320
	call {vg_brainpoolp512r1_mul_mod_n}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 256(s0)
	sd t0, 0(a6)
	ld t0, 264(s0)
	sd t0, 8(a6)
	ld t0, 272(s0)
	sd t0, 16(a6)
	ld t0, 280(s0)
	sd t0, 24(a6)
	ld t0, 288(s0)
	sd t0, 32(a6)
	ld t0, 296(s0)
	sd t0, 40(a6)
	ld t0, 304(s0)
	sd t0, 48(a6)
	ld t0, 312(s0)
	sd t0, 56(a6)
	ld t0, 384(s0)
	sd t0, 64(a6)
	ld t0, 392(s0)
	sd t0, 72(a6)
	ld t0, 400(s0)
	sd t0, 80(a6)
	ld t0, 408(s0)
	sd t0, 88(a6)
	ld t0, 416(s0)
	sd t0, 96(a6)
	ld t0, 424(s0)
	sd t0, 104(a6)
	ld t0, 432(s0)
	sd t0, 112(a6)
	ld t0, 440(s0)
	sd t0, 120(a6)
	ld t0, 256(s0)
	sd t0, 128(a6)
	ld t0, 264(s0)
	sd t0, 136(a6)
	ld t0, 272(s0)
	sd t0, 144(a6)
	ld t0, 280(s0)
	sd t0, 152(a6)
	ld t0, 288(s0)
	sd t0, 160(a6)
	ld t0, 296(s0)
	sd t0, 168(a6)
	ld t0, 304(s0)
	sd t0, 176(a6)
	ld t0, 312(s0)
	sd t0, 184(a6)
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 576(s0)
	sd t0, 768(a6)
	ld t0, 584(s0)
	sd t0, 776(a6)
	ld t0, 592(s0)
	sd t0, 784(a6)
	ld t0, 600(s0)
	sd t0, 792(a6)
	ld t0, 608(s0)
	sd t0, 800(a6)
	ld t0, 616(s0)
	sd t0, 808(a6)
	ld t0, 624(s0)
	sd t0, 816(a6)
	ld t0, 632(s0)
	sd t0, 824(a6)
	ld t0, 640(s0)
	sd t0, 832(a6)
	ld t0, 648(s0)
	sd t0, 840(a6)
	ld t0, 656(s0)
	sd t0, 848(a6)
	ld t0, 664(s0)
	sd t0, 856(a6)
	ld t0, 672(s0)
	sd t0, 864(a6)
	ld t0, 680(s0)
	sd t0, 872(a6)
	ld t0, 688(s0)
	sd t0, 880(a6)
	ld t0, 696(s0)
	sd t0, 888(a6)
	ld t0, 384(s0)
	sd t0, 896(a6)
	ld t0, 392(s0)
	sd t0, 904(a6)
	ld t0, 400(s0)
	sd t0, 912(a6)
	ld t0, 408(s0)
	sd t0, 920(a6)
	ld t0, 416(s0)
	sd t0, 928(a6)
	ld t0, 424(s0)
	sd t0, 936(a6)
	ld t0, 432(s0)
	sd t0, 944(a6)
	ld t0, 440(s0)
	sd t0, 952(a6)
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	addi t0, s0, 2047
	ld t0, 449(t0)
	sd t0, 192(a6)
	addi t0, s0, 2047
	ld t0, 457(t0)
	sd t0, 200(a6)
	addi t0, s0, 2047
	ld t0, 465(t0)
	sd t0, 208(a6)
	addi t0, s0, 2047
	ld t0, 473(t0)
	sd t0, 216(a6)
	addi t0, s0, 2047
	ld t0, 481(t0)
	sd t0, 224(a6)
	addi t0, s0, 2047
	ld t0, 489(t0)
	sd t0, 232(a6)
	addi t0, s0, 2047
	ld t0, 497(t0)
	sd t0, 240(a6)
	addi t0, s0, 2047
	ld t0, 505(t0)
	sd t0, 248(a6)
	addi t0, s0, 2047
	ld t0, 769(t0)
	sd t0, 256(a6)
	addi t0, s0, 2047
	ld t0, 777(t0)
	sd t0, 264(a6)
	addi t0, s0, 2047
	ld t0, 785(t0)
	sd t0, 272(a6)
	addi t0, s0, 2047
	ld t0, 793(t0)
	sd t0, 280(a6)
	addi t0, s0, 2047
	ld t0, 801(t0)
	sd t0, 288(a6)
	addi t0, s0, 2047
	ld t0, 809(t0)
	sd t0, 296(a6)
	addi t0, s0, 2047
	ld t0, 817(t0)
	sd t0, 304(a6)
	addi t0, s0, 2047
	ld t0, 825(t0)
	sd t0, 312(a6)
	ld t0, 384(s0)
	sd t0, 320(a6)
	ld t0, 392(s0)
	sd t0, 328(a6)
	ld t0, 400(s0)
	sd t0, 336(a6)
	ld t0, 408(s0)
	sd t0, 344(a6)
	ld t0, 416(s0)
	sd t0, 352(a6)
	ld t0, 424(s0)
	sd t0, 360(a6)
	ld t0, 432(s0)
	sd t0, 368(a6)
	ld t0, 440(s0)
	sd t0, 376(a6)
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 576
	addi a3, zero, 576
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 640
	addi a3, zero, 640
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 384
	addi a3, zero, 384
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 576
	addi a3, zero, 640
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 576
	addi a3, zero, 640
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
	addi a2, zero, 576
	addi a3, zero, 384
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 576
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
	addi a2, zero, 640
	addi a3, zero, 384
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 961
	addi a2, zero, 640
	addi a3, zero, 384
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1856
	addi a3, zero, 2047
	addi a3, a3, 961
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 961
	addi a2, zero, 1600
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1856
	addi a3, zero, 2047
	addi a3, a3, 961
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1089
	addi a2, zero, 448
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 961
	addi a2, zero, 512
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1089
	addi a2, zero, 2047
	addi a2, a2, 961
	addi a3, zero, 2047
	addi a3, a3, 1089
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 961
	addi a2, zero, 1600
	addi a3, zero, 2047
	addi a3, a3, 1089
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1089
	addi a2, zero, 1600
	addi a3, zero, 2047
	addi a3, a3, 1089
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1025
	addi a2, zero, 2047
	addi a2, a2, 961
	addi a3, zero, 2047
	addi a3, a3, 1089
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
	addi a1, zero, 2047
	addi a1, a1, 1025
	addi a2, zero, 2047
	addi a2, a2, 1025
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1856
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 961
	addi a2, zero, 1728
	addi a3, zero, 2047
	addi a3, a3, 961
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 961
	addi a2, zero, 2047
	addi a2, a2, 961
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1728
	addi a3, zero, 1600
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1089
	addi a2, zero, 1856
	addi a3, zero, 2047
	addi a3, a3, 1089
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1089
	addi a2, zero, 2047
	addi a2, a2, 1089
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	addi t0, s0, 2047
	ld t0, 961(t0)
	sd t0, 1536(a6)
	addi t0, s0, 2047
	ld t0, 969(t0)
	sd t0, 1544(a6)
	addi t0, s0, 2047
	ld t0, 977(t0)
	sd t0, 1552(a6)
	addi t0, s0, 2047
	ld t0, 985(t0)
	sd t0, 1560(a6)
	addi t0, s0, 2047
	ld t0, 993(t0)
	sd t0, 1568(a6)
	addi t0, s0, 2047
	ld t0, 1001(t0)
	sd t0, 1576(a6)
	addi t0, s0, 2047
	ld t0, 1009(t0)
	sd t0, 1584(a6)
	addi t0, s0, 2047
	ld t0, 1017(t0)
	sd t0, 1592(a6)
	addi t0, s0, 2047
	ld t0, 1025(t0)
	sd t0, 1600(a6)
	addi t0, s0, 2047
	ld t0, 1033(t0)
	sd t0, 1608(a6)
	addi t0, s0, 2047
	ld t0, 1041(t0)
	sd t0, 1616(a6)
	addi t0, s0, 2047
	ld t0, 1049(t0)
	sd t0, 1624(a6)
	addi t0, s0, 2047
	ld t0, 1057(t0)
	sd t0, 1632(a6)
	addi t0, s0, 2047
	ld t0, 1065(t0)
	sd t0, 1640(a6)
	addi t0, s0, 2047
	ld t0, 1073(t0)
	sd t0, 1648(a6)
	addi t0, s0, 2047
	ld t0, 1081(t0)
	sd t0, 1656(a6)
	addi t0, s0, 2047
	ld t0, 1089(t0)
	sd t0, 1664(a6)
	addi t0, s0, 2047
	ld t0, 1097(t0)
	sd t0, 1672(a6)
	addi t0, s0, 2047
	ld t0, 1105(t0)
	sd t0, 1680(a6)
	addi t0, s0, 2047
	ld t0, 1113(t0)
	sd t0, 1688(a6)
	addi t0, s0, 2047
	ld t0, 1121(t0)
	sd t0, 1696(a6)
	addi t0, s0, 2047
	ld t0, 1129(t0)
	sd t0, 1704(a6)
	addi t0, s0, 2047
	ld t0, 1137(t0)
	sd t0, 1712(a6)
	addi t0, s0, 2047
	ld t0, 1145(t0)
	sd t0, 1720(a6)
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 2047
	addi a2, a2, 961
	addi a3, zero, 576
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 2047
	addi a2, a2, 1025
	addi a3, zero, 640
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 2047
	addi a2, a2, 1089
	addi a3, zero, 384
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 2047
	addi a2, a2, 961
	addi a3, zero, 2047
	addi a3, a3, 1025
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 576
	addi a3, zero, 640
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
	addi a2, zero, 2047
	addi a2, a2, 961
	addi a3, zero, 2047
	addi a3, a3, 1089
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 576
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
	addi a2, zero, 2047
	addi a2, a2, 1025
	addi a3, zero, 2047
	addi a3, a3, 1089
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1153
	addi a2, zero, 640
	addi a3, zero, 384
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1856
	addi a3, zero, 2047
	addi a3, a3, 1153
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1153
	addi a2, zero, 1600
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1856
	addi a3, zero, 2047
	addi a3, a3, 1153
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1281
	addi a2, zero, 448
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1153
	addi a2, zero, 512
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1281
	addi a2, zero, 2047
	addi a2, a2, 1153
	addi a3, zero, 2047
	addi a3, a3, 1281
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1153
	addi a2, zero, 1600
	addi a3, zero, 2047
	addi a3, a3, 1281
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1281
	addi a2, zero, 1600
	addi a3, zero, 2047
	addi a3, a3, 1281
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1217
	addi a2, zero, 2047
	addi a2, a2, 1153
	addi a3, zero, 2047
	addi a3, a3, 1281
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
	addi a1, zero, 2047
	addi a1, a1, 1217
	addi a2, zero, 2047
	addi a2, a2, 1217
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1856
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1153
	addi a2, zero, 1728
	addi a3, zero, 2047
	addi a3, a3, 1153
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1153
	addi a2, zero, 2047
	addi a2, a2, 1153
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1728
	addi a3, zero, 1600
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1281
	addi a2, zero, 1856
	addi a3, zero, 2047
	addi a3, a3, 1281
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1281
	addi a2, zero, 2047
	addi a2, a2, 1281
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	addi t0, s0, 2047
	ld t0, 1153(t0)
	addi a6, a6, 2047
	sd t0, 257(a6)
	addi a6, a6, -2047
	addi t0, s0, 2047
	ld t0, 1161(t0)
	addi a6, a6, 2047
	sd t0, 265(a6)
	addi a6, a6, -2047
	addi t0, s0, 2047
	ld t0, 1169(t0)
	addi a6, a6, 2047
	sd t0, 273(a6)
	addi a6, a6, -2047
	addi t0, s0, 2047
	ld t0, 1177(t0)
	addi a6, a6, 2047
	sd t0, 281(a6)
	addi a6, a6, -2047
	addi t0, s0, 2047
	ld t0, 1185(t0)
	addi a6, a6, 2047
	sd t0, 289(a6)
	addi a6, a6, -2047
	addi t0, s0, 2047
	ld t0, 1193(t0)
	addi a6, a6, 2047
	sd t0, 297(a6)
	addi a6, a6, -2047
	addi t0, s0, 2047
	ld t0, 1201(t0)
	addi a6, a6, 2047
	sd t0, 305(a6)
	addi a6, a6, -2047
	addi t0, s0, 2047
	ld t0, 1209(t0)
	addi a6, a6, 2047
	sd t0, 313(a6)
	addi a6, a6, -2047
	addi t0, s0, 2047
	ld t0, 1217(t0)
	addi a6, a6, 2047
	sd t0, 321(a6)
	addi a6, a6, -2047
	addi t0, s0, 2047
	ld t0, 1225(t0)
	addi a6, a6, 2047
	sd t0, 329(a6)
	addi a6, a6, -2047
	addi t0, s0, 2047
	ld t0, 1233(t0)
	addi a6, a6, 2047
	sd t0, 337(a6)
	addi a6, a6, -2047
	addi t0, s0, 2047
	ld t0, 1241(t0)
	addi a6, a6, 2047
	sd t0, 345(a6)
	addi a6, a6, -2047
	addi t0, s0, 2047
	ld t0, 1249(t0)
	addi a6, a6, 2047
	sd t0, 353(a6)
	addi a6, a6, -2047
	addi t0, s0, 2047
	ld t0, 1257(t0)
	addi a6, a6, 2047
	sd t0, 361(a6)
	addi a6, a6, -2047
	addi t0, s0, 2047
	ld t0, 1265(t0)
	addi a6, a6, 2047
	sd t0, 369(a6)
	addi a6, a6, -2047
	addi t0, s0, 2047
	ld t0, 1273(t0)
	addi a6, a6, 2047
	sd t0, 377(a6)
	addi a6, a6, -2047
	addi t0, s0, 2047
	ld t0, 1281(t0)
	addi a6, a6, 2047
	sd t0, 385(a6)
	addi a6, a6, -2047
	addi t0, s0, 2047
	ld t0, 1289(t0)
	addi a6, a6, 2047
	sd t0, 393(a6)
	addi a6, a6, -2047
	addi t0, s0, 2047
	ld t0, 1297(t0)
	addi a6, a6, 2047
	sd t0, 401(a6)
	addi a6, a6, -2047
	addi t0, s0, 2047
	ld t0, 1305(t0)
	addi a6, a6, 2047
	sd t0, 409(a6)
	addi a6, a6, -2047
	addi t0, s0, 2047
	ld t0, 1313(t0)
	addi a6, a6, 2047
	sd t0, 417(a6)
	addi a6, a6, -2047
	addi t0, s0, 2047
	ld t0, 1321(t0)
	addi a6, a6, 2047
	sd t0, 425(a6)
	addi a6, a6, -2047
	addi t0, s0, 2047
	ld t0, 1329(t0)
	addi a6, a6, 2047
	sd t0, 433(a6)
	addi a6, a6, -2047
	addi t0, s0, 2047
	ld t0, 1337(t0)
	addi a6, a6, 2047
	sd t0, 441(a6)
	addi a6, a6, -2047
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 2047
	addi a2, a2, 449
	addi a3, zero, 2047
	addi a3, a3, 449
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 2047
	addi a2, a2, 769
	addi a3, zero, 2047
	addi a3, a3, 769
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 384
	addi a3, zero, 384
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 2047
	addi a2, a2, 449
	addi a3, zero, 2047
	addi a3, a3, 769
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 2047
	addi a2, a2, 449
	addi a3, zero, 2047
	addi a3, a3, 769
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
	addi a2, zero, 2047
	addi a2, a2, 449
	addi a3, zero, 384
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 2047
	addi a2, a2, 449
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
	addi a2, zero, 2047
	addi a2, a2, 769
	addi a3, zero, 384
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1345
	addi a2, zero, 2047
	addi a2, a2, 769
	addi a3, zero, 384
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1856
	addi a3, zero, 2047
	addi a3, a3, 1345
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1345
	addi a2, zero, 1600
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1856
	addi a3, zero, 2047
	addi a3, a3, 1345
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1473
	addi a2, zero, 448
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1345
	addi a2, zero, 512
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1473
	addi a2, zero, 2047
	addi a2, a2, 1345
	addi a3, zero, 2047
	addi a3, a3, 1473
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1345
	addi a2, zero, 1600
	addi a3, zero, 2047
	addi a3, a3, 1473
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1473
	addi a2, zero, 1600
	addi a3, zero, 2047
	addi a3, a3, 1473
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1409
	addi a2, zero, 2047
	addi a2, a2, 1345
	addi a3, zero, 2047
	addi a3, a3, 1473
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
	addi a1, zero, 2047
	addi a1, a1, 1409
	addi a2, zero, 2047
	addi a2, a2, 1409
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1856
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1345
	addi a2, zero, 1728
	addi a3, zero, 2047
	addi a3, a3, 1345
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1345
	addi a2, zero, 2047
	addi a2, a2, 1345
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1728
	addi a3, zero, 1600
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1473
	addi a2, zero, 1856
	addi a3, zero, 2047
	addi a3, a3, 1473
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1473
	addi a2, zero, 2047
	addi a2, a2, 1473
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	addi t0, s0, 2047
	ld t0, 1345(t0)
	sd t0, 384(a6)
	addi t0, s0, 2047
	ld t0, 1353(t0)
	sd t0, 392(a6)
	addi t0, s0, 2047
	ld t0, 1361(t0)
	sd t0, 400(a6)
	addi t0, s0, 2047
	ld t0, 1369(t0)
	sd t0, 408(a6)
	addi t0, s0, 2047
	ld t0, 1377(t0)
	sd t0, 416(a6)
	addi t0, s0, 2047
	ld t0, 1385(t0)
	sd t0, 424(a6)
	addi t0, s0, 2047
	ld t0, 1393(t0)
	sd t0, 432(a6)
	addi t0, s0, 2047
	ld t0, 1401(t0)
	sd t0, 440(a6)
	addi t0, s0, 2047
	ld t0, 1409(t0)
	sd t0, 448(a6)
	addi t0, s0, 2047
	ld t0, 1417(t0)
	sd t0, 456(a6)
	addi t0, s0, 2047
	ld t0, 1425(t0)
	sd t0, 464(a6)
	addi t0, s0, 2047
	ld t0, 1433(t0)
	sd t0, 472(a6)
	addi t0, s0, 2047
	ld t0, 1441(t0)
	sd t0, 480(a6)
	addi t0, s0, 2047
	ld t0, 1449(t0)
	sd t0, 488(a6)
	addi t0, s0, 2047
	ld t0, 1457(t0)
	sd t0, 496(a6)
	addi t0, s0, 2047
	ld t0, 1465(t0)
	sd t0, 504(a6)
	addi t0, s0, 2047
	ld t0, 1473(t0)
	sd t0, 512(a6)
	addi t0, s0, 2047
	ld t0, 1481(t0)
	sd t0, 520(a6)
	addi t0, s0, 2047
	ld t0, 1489(t0)
	sd t0, 528(a6)
	addi t0, s0, 2047
	ld t0, 1497(t0)
	sd t0, 536(a6)
	addi t0, s0, 2047
	ld t0, 1505(t0)
	sd t0, 544(a6)
	addi t0, s0, 2047
	ld t0, 1513(t0)
	sd t0, 552(a6)
	addi t0, s0, 2047
	ld t0, 1521(t0)
	sd t0, 560(a6)
	addi t0, s0, 2047
	ld t0, 1529(t0)
	sd t0, 568(a6)
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 2047
	addi a2, a2, 1345
	addi a3, zero, 2047
	addi a3, a3, 449
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 2047
	addi a2, a2, 1409
	addi a3, zero, 2047
	addi a3, a3, 769
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 2047
	addi a2, a2, 1473
	addi a3, zero, 384
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 2047
	addi a2, a2, 1345
	addi a3, zero, 2047
	addi a3, a3, 1409
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 2047
	addi a2, a2, 449
	addi a3, zero, 2047
	addi a3, a3, 769
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
	addi a2, zero, 2047
	addi a2, a2, 1345
	addi a3, zero, 2047
	addi a3, a3, 1473
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 2047
	addi a2, a2, 449
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
	addi a2, zero, 2047
	addi a2, a2, 1409
	addi a3, zero, 2047
	addi a3, a3, 1473
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1537
	addi a2, zero, 2047
	addi a2, a2, 769
	addi a3, zero, 384
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1856
	addi a3, zero, 2047
	addi a3, a3, 1537
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1537
	addi a2, zero, 1600
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1856
	addi a3, zero, 2047
	addi a3, a3, 1537
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1665
	addi a2, zero, 448
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1537
	addi a2, zero, 512
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1665
	addi a2, zero, 2047
	addi a2, a2, 1537
	addi a3, zero, 2047
	addi a3, a3, 1665
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1537
	addi a2, zero, 1600
	addi a3, zero, 2047
	addi a3, a3, 1665
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1665
	addi a2, zero, 1600
	addi a3, zero, 2047
	addi a3, a3, 1665
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1601
	addi a2, zero, 2047
	addi a2, a2, 1537
	addi a3, zero, 2047
	addi a3, a3, 1665
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
	addi a1, zero, 2047
	addi a1, a1, 1601
	addi a2, zero, 2047
	addi a2, a2, 1601
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1856
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1537
	addi a2, zero, 1728
	addi a3, zero, 2047
	addi a3, a3, 1537
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1537
	addi a2, zero, 2047
	addi a2, a2, 1537
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1728
	addi a3, zero, 1600
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1665
	addi a2, zero, 1856
	addi a3, zero, 2047
	addi a3, a3, 1665
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1665
	addi a2, zero, 2047
	addi a2, a2, 1665
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	addi t0, s0, 2047
	ld t0, 1537(t0)
	sd t0, 576(a6)
	addi t0, s0, 2047
	ld t0, 1545(t0)
	sd t0, 584(a6)
	addi t0, s0, 2047
	ld t0, 1553(t0)
	sd t0, 592(a6)
	addi t0, s0, 2047
	ld t0, 1561(t0)
	sd t0, 600(a6)
	addi t0, s0, 2047
	ld t0, 1569(t0)
	sd t0, 608(a6)
	addi t0, s0, 2047
	ld t0, 1577(t0)
	sd t0, 616(a6)
	addi t0, s0, 2047
	ld t0, 1585(t0)
	sd t0, 624(a6)
	addi t0, s0, 2047
	ld t0, 1593(t0)
	sd t0, 632(a6)
	addi t0, s0, 2047
	ld t0, 1601(t0)
	sd t0, 640(a6)
	addi t0, s0, 2047
	ld t0, 1609(t0)
	sd t0, 648(a6)
	addi t0, s0, 2047
	ld t0, 1617(t0)
	sd t0, 656(a6)
	addi t0, s0, 2047
	ld t0, 1625(t0)
	sd t0, 664(a6)
	addi t0, s0, 2047
	ld t0, 1633(t0)
	sd t0, 672(a6)
	addi t0, s0, 2047
	ld t0, 1641(t0)
	sd t0, 680(a6)
	addi t0, s0, 2047
	ld t0, 1649(t0)
	sd t0, 688(a6)
	addi t0, s0, 2047
	ld t0, 1657(t0)
	sd t0, 696(a6)
	addi t0, s0, 2047
	ld t0, 1665(t0)
	sd t0, 704(a6)
	addi t0, s0, 2047
	ld t0, 1673(t0)
	sd t0, 712(a6)
	addi t0, s0, 2047
	ld t0, 1681(t0)
	sd t0, 720(a6)
	addi t0, s0, 2047
	ld t0, 1689(t0)
	sd t0, 728(a6)
	addi t0, s0, 2047
	ld t0, 1697(t0)
	sd t0, 736(a6)
	addi t0, s0, 2047
	ld t0, 1705(t0)
	sd t0, 744(a6)
	addi t0, s0, 2047
	ld t0, 1713(t0)
	sd t0, 752(a6)
	addi t0, s0, 2047
	ld t0, 1721(t0)
	sd t0, 760(a6)
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 576
	addi a3, zero, 2047
	addi a3, a3, 449
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 640
	addi a3, zero, 2047
	addi a3, a3, 769
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 384
	addi a3, zero, 384
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 576
	addi a3, zero, 640
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 2047
	addi a2, a2, 449
	addi a3, zero, 2047
	addi a3, a3, 769
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
	addi a2, zero, 576
	addi a3, zero, 384
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 2047
	addi a2, a2, 449
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
	addi a2, zero, 640
	addi a3, zero, 384
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 2047
	addi a2, a2, 769
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
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 1344(s0)
	sd t0, 960(a6)
	ld t0, 1352(s0)
	sd t0, 968(a6)
	ld t0, 1360(s0)
	sd t0, 976(a6)
	ld t0, 1368(s0)
	sd t0, 984(a6)
	ld t0, 1376(s0)
	sd t0, 992(a6)
	ld t0, 1384(s0)
	sd t0, 1000(a6)
	ld t0, 1392(s0)
	sd t0, 1008(a6)
	ld t0, 1400(s0)
	sd t0, 1016(a6)
	ld t0, 1408(s0)
	sd t0, 1024(a6)
	ld t0, 1416(s0)
	sd t0, 1032(a6)
	ld t0, 1424(s0)
	sd t0, 1040(a6)
	ld t0, 1432(s0)
	sd t0, 1048(a6)
	ld t0, 1440(s0)
	sd t0, 1056(a6)
	ld t0, 1448(s0)
	sd t0, 1064(a6)
	ld t0, 1456(s0)
	sd t0, 1072(a6)
	ld t0, 1464(s0)
	sd t0, 1080(a6)
	ld t0, 1472(s0)
	sd t0, 1088(a6)
	ld t0, 1480(s0)
	sd t0, 1096(a6)
	ld t0, 1488(s0)
	sd t0, 1104(a6)
	ld t0, 1496(s0)
	sd t0, 1112(a6)
	ld t0, 1504(s0)
	sd t0, 1120(a6)
	ld t0, 1512(s0)
	sd t0, 1128(a6)
	ld t0, 1520(s0)
	sd t0, 1136(a6)
	ld t0, 1528(s0)
	sd t0, 1144(a6)
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 576
	addi a3, zero, 2047
	addi a3, a3, 1345
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 640
	addi a3, zero, 2047
	addi a3, a3, 1409
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 384
	addi a3, zero, 2047
	addi a3, a3, 1473
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 576
	addi a3, zero, 640
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 2047
	addi a2, a2, 1345
	addi a3, zero, 2047
	addi a3, a3, 1409
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
	addi a2, zero, 576
	addi a3, zero, 384
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 2047
	addi a2, a2, 1345
	addi a3, zero, 2047
	addi a3, a3, 1473
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
	addi a2, zero, 640
	addi a3, zero, 384
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 2047
	addi a2, a2, 1409
	addi a3, zero, 2047
	addi a3, a3, 1473
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
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 1344(s0)
	sd t0, 1152(a6)
	ld t0, 1352(s0)
	sd t0, 1160(a6)
	ld t0, 1360(s0)
	sd t0, 1168(a6)
	ld t0, 1368(s0)
	sd t0, 1176(a6)
	ld t0, 1376(s0)
	sd t0, 1184(a6)
	ld t0, 1384(s0)
	sd t0, 1192(a6)
	ld t0, 1392(s0)
	sd t0, 1200(a6)
	ld t0, 1400(s0)
	sd t0, 1208(a6)
	ld t0, 1408(s0)
	sd t0, 1216(a6)
	ld t0, 1416(s0)
	sd t0, 1224(a6)
	ld t0, 1424(s0)
	sd t0, 1232(a6)
	ld t0, 1432(s0)
	sd t0, 1240(a6)
	ld t0, 1440(s0)
	sd t0, 1248(a6)
	ld t0, 1448(s0)
	sd t0, 1256(a6)
	ld t0, 1456(s0)
	sd t0, 1264(a6)
	ld t0, 1464(s0)
	sd t0, 1272(a6)
	ld t0, 1472(s0)
	sd t0, 1280(a6)
	ld t0, 1480(s0)
	sd t0, 1288(a6)
	ld t0, 1488(s0)
	sd t0, 1296(a6)
	ld t0, 1496(s0)
	sd t0, 1304(a6)
	ld t0, 1504(s0)
	sd t0, 1312(a6)
	ld t0, 1512(s0)
	sd t0, 1320(a6)
	ld t0, 1520(s0)
	sd t0, 1328(a6)
	ld t0, 1528(s0)
	sd t0, 1336(a6)
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 576
	addi a3, zero, 2047
	addi a3, a3, 1537
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 640
	addi a3, zero, 2047
	addi a3, a3, 1601
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 384
	addi a3, zero, 2047
	addi a3, a3, 1665
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 576
	addi a3, zero, 640
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 2047
	addi a2, a2, 1537
	addi a3, zero, 2047
	addi a3, a3, 1601
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
	addi a2, zero, 576
	addi a3, zero, 384
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 2047
	addi a2, a2, 1537
	addi a3, zero, 2047
	addi a3, a3, 1665
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
	addi a2, zero, 640
	addi a3, zero, 384
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 2047
	addi a2, a2, 1601
	addi a3, zero, 2047
	addi a3, a3, 1665
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
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 1344(s0)
	sd t0, 1344(a6)
	ld t0, 1352(s0)
	sd t0, 1352(a6)
	ld t0, 1360(s0)
	sd t0, 1360(a6)
	ld t0, 1368(s0)
	sd t0, 1368(a6)
	ld t0, 1376(s0)
	sd t0, 1376(a6)
	ld t0, 1384(s0)
	sd t0, 1384(a6)
	ld t0, 1392(s0)
	sd t0, 1392(a6)
	ld t0, 1400(s0)
	sd t0, 1400(a6)
	ld t0, 1408(s0)
	sd t0, 1408(a6)
	ld t0, 1416(s0)
	sd t0, 1416(a6)
	ld t0, 1424(s0)
	sd t0, 1424(a6)
	ld t0, 1432(s0)
	sd t0, 1432(a6)
	ld t0, 1440(s0)
	sd t0, 1440(a6)
	ld t0, 1448(s0)
	sd t0, 1448(a6)
	ld t0, 1456(s0)
	sd t0, 1456(a6)
	ld t0, 1464(s0)
	sd t0, 1464(a6)
	ld t0, 1472(s0)
	sd t0, 1472(a6)
	ld t0, 1480(s0)
	sd t0, 1480(a6)
	ld t0, 1488(s0)
	sd t0, 1488(a6)
	ld t0, 1496(s0)
	sd t0, 1496(a6)
	ld t0, 1504(s0)
	sd t0, 1504(a6)
	ld t0, 1512(s0)
	sd t0, 1512(a6)
	ld t0, 1520(s0)
	sd t0, 1520(a6)
	ld t0, 1528(s0)
	sd t0, 1528(a6)
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 2047
	addi a2, a2, 961
	addi a3, zero, 2047
	addi a3, a3, 449
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 2047
	addi a2, a2, 1025
	addi a3, zero, 2047
	addi a3, a3, 769
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 2047
	addi a2, a2, 1089
	addi a3, zero, 384
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 2047
	addi a2, a2, 961
	addi a3, zero, 2047
	addi a3, a3, 1025
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 2047
	addi a2, a2, 449
	addi a3, zero, 2047
	addi a3, a3, 769
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
	addi a2, zero, 2047
	addi a2, a2, 961
	addi a3, zero, 2047
	addi a3, a3, 1089
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 2047
	addi a2, a2, 449
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
	addi a2, zero, 2047
	addi a2, a2, 1025
	addi a3, zero, 2047
	addi a3, a3, 1089
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 2047
	addi a2, a2, 769
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
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 1344(s0)
	sd t0, 1728(a6)
	ld t0, 1352(s0)
	sd t0, 1736(a6)
	ld t0, 1360(s0)
	sd t0, 1744(a6)
	ld t0, 1368(s0)
	sd t0, 1752(a6)
	ld t0, 1376(s0)
	sd t0, 1760(a6)
	ld t0, 1384(s0)
	sd t0, 1768(a6)
	ld t0, 1392(s0)
	sd t0, 1776(a6)
	ld t0, 1400(s0)
	sd t0, 1784(a6)
	ld t0, 1408(s0)
	sd t0, 1792(a6)
	ld t0, 1416(s0)
	sd t0, 1800(a6)
	ld t0, 1424(s0)
	sd t0, 1808(a6)
	ld t0, 1432(s0)
	sd t0, 1816(a6)
	ld t0, 1440(s0)
	sd t0, 1824(a6)
	ld t0, 1448(s0)
	sd t0, 1832(a6)
	ld t0, 1456(s0)
	sd t0, 1840(a6)
	ld t0, 1464(s0)
	sd t0, 1848(a6)
	ld t0, 1472(s0)
	sd t0, 1856(a6)
	ld t0, 1480(s0)
	sd t0, 1864(a6)
	ld t0, 1488(s0)
	sd t0, 1872(a6)
	ld t0, 1496(s0)
	sd t0, 1880(a6)
	ld t0, 1504(s0)
	sd t0, 1888(a6)
	ld t0, 1512(s0)
	sd t0, 1896(a6)
	ld t0, 1520(s0)
	sd t0, 1904(a6)
	ld t0, 1528(s0)
	sd t0, 1912(a6)
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 2047
	addi a2, a2, 961
	addi a3, zero, 2047
	addi a3, a3, 1345
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 2047
	addi a2, a2, 1025
	addi a3, zero, 2047
	addi a3, a3, 1409
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 2047
	addi a2, a2, 1089
	addi a3, zero, 2047
	addi a3, a3, 1473
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 2047
	addi a2, a2, 961
	addi a3, zero, 2047
	addi a3, a3, 1025
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 2047
	addi a2, a2, 1345
	addi a3, zero, 2047
	addi a3, a3, 1409
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
	addi a2, zero, 2047
	addi a2, a2, 961
	addi a3, zero, 2047
	addi a3, a3, 1089
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 2047
	addi a2, a2, 1345
	addi a3, zero, 2047
	addi a3, a3, 1473
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
	addi a2, zero, 2047
	addi a2, a2, 1025
	addi a3, zero, 2047
	addi a3, a3, 1089
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 2047
	addi a2, a2, 1409
	addi a3, zero, 2047
	addi a3, a3, 1473
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
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 1344(s0)
	sd t0, 1920(a6)
	ld t0, 1352(s0)
	sd t0, 1928(a6)
	ld t0, 1360(s0)
	sd t0, 1936(a6)
	ld t0, 1368(s0)
	sd t0, 1944(a6)
	ld t0, 1376(s0)
	sd t0, 1952(a6)
	ld t0, 1384(s0)
	sd t0, 1960(a6)
	ld t0, 1392(s0)
	sd t0, 1968(a6)
	ld t0, 1400(s0)
	sd t0, 1976(a6)
	ld t0, 1408(s0)
	sd t0, 1984(a6)
	ld t0, 1416(s0)
	sd t0, 1992(a6)
	ld t0, 1424(s0)
	sd t0, 2000(a6)
	ld t0, 1432(s0)
	sd t0, 2008(a6)
	ld t0, 1440(s0)
	sd t0, 2016(a6)
	ld t0, 1448(s0)
	sd t0, 2024(a6)
	ld t0, 1456(s0)
	sd t0, 2032(a6)
	ld t0, 1464(s0)
	sd t0, 2040(a6)
	ld t0, 1472(s0)
	addi a6, a6, 2047
	sd t0, 1(a6)
	addi a6, a6, -2047
	ld t0, 1480(s0)
	addi a6, a6, 2047
	sd t0, 9(a6)
	addi a6, a6, -2047
	ld t0, 1488(s0)
	addi a6, a6, 2047
	sd t0, 17(a6)
	addi a6, a6, -2047
	ld t0, 1496(s0)
	addi a6, a6, 2047
	sd t0, 25(a6)
	addi a6, a6, -2047
	ld t0, 1504(s0)
	addi a6, a6, 2047
	sd t0, 33(a6)
	addi a6, a6, -2047
	ld t0, 1512(s0)
	addi a6, a6, 2047
	sd t0, 41(a6)
	addi a6, a6, -2047
	ld t0, 1520(s0)
	addi a6, a6, 2047
	sd t0, 49(a6)
	addi a6, a6, -2047
	ld t0, 1528(s0)
	addi a6, a6, 2047
	sd t0, 57(a6)
	addi a6, a6, -2047
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 2047
	addi a2, a2, 961
	addi a3, zero, 2047
	addi a3, a3, 1537
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 2047
	addi a2, a2, 1025
	addi a3, zero, 2047
	addi a3, a3, 1601
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 2047
	addi a2, a2, 1089
	addi a3, zero, 2047
	addi a3, a3, 1665
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 2047
	addi a2, a2, 961
	addi a3, zero, 2047
	addi a3, a3, 1025
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 2047
	addi a2, a2, 1537
	addi a3, zero, 2047
	addi a3, a3, 1601
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
	addi a2, zero, 2047
	addi a2, a2, 961
	addi a3, zero, 2047
	addi a3, a3, 1089
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 2047
	addi a2, a2, 1537
	addi a3, zero, 2047
	addi a3, a3, 1665
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
	addi a2, zero, 2047
	addi a2, a2, 1025
	addi a3, zero, 2047
	addi a3, a3, 1089
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 2047
	addi a2, a2, 1601
	addi a3, zero, 2047
	addi a3, a3, 1665
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
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 1344(s0)
	addi a6, a6, 2047
	sd t0, 65(a6)
	addi a6, a6, -2047
	ld t0, 1352(s0)
	addi a6, a6, 2047
	sd t0, 73(a6)
	addi a6, a6, -2047
	ld t0, 1360(s0)
	addi a6, a6, 2047
	sd t0, 81(a6)
	addi a6, a6, -2047
	ld t0, 1368(s0)
	addi a6, a6, 2047
	sd t0, 89(a6)
	addi a6, a6, -2047
	ld t0, 1376(s0)
	addi a6, a6, 2047
	sd t0, 97(a6)
	addi a6, a6, -2047
	ld t0, 1384(s0)
	addi a6, a6, 2047
	sd t0, 105(a6)
	addi a6, a6, -2047
	ld t0, 1392(s0)
	addi a6, a6, 2047
	sd t0, 113(a6)
	addi a6, a6, -2047
	ld t0, 1400(s0)
	addi a6, a6, 2047
	sd t0, 121(a6)
	addi a6, a6, -2047
	ld t0, 1408(s0)
	addi a6, a6, 2047
	sd t0, 129(a6)
	addi a6, a6, -2047
	ld t0, 1416(s0)
	addi a6, a6, 2047
	sd t0, 137(a6)
	addi a6, a6, -2047
	ld t0, 1424(s0)
	addi a6, a6, 2047
	sd t0, 145(a6)
	addi a6, a6, -2047
	ld t0, 1432(s0)
	addi a6, a6, 2047
	sd t0, 153(a6)
	addi a6, a6, -2047
	ld t0, 1440(s0)
	addi a6, a6, 2047
	sd t0, 161(a6)
	addi a6, a6, -2047
	ld t0, 1448(s0)
	addi a6, a6, 2047
	sd t0, 169(a6)
	addi a6, a6, -2047
	ld t0, 1456(s0)
	addi a6, a6, 2047
	sd t0, 177(a6)
	addi a6, a6, -2047
	ld t0, 1464(s0)
	addi a6, a6, 2047
	sd t0, 185(a6)
	addi a6, a6, -2047
	ld t0, 1472(s0)
	addi a6, a6, 2047
	sd t0, 193(a6)
	addi a6, a6, -2047
	ld t0, 1480(s0)
	addi a6, a6, 2047
	sd t0, 201(a6)
	addi a6, a6, -2047
	ld t0, 1488(s0)
	addi a6, a6, 2047
	sd t0, 209(a6)
	addi a6, a6, -2047
	ld t0, 1496(s0)
	addi a6, a6, 2047
	sd t0, 217(a6)
	addi a6, a6, -2047
	ld t0, 1504(s0)
	addi a6, a6, 2047
	sd t0, 225(a6)
	addi a6, a6, -2047
	ld t0, 1512(s0)
	addi a6, a6, 2047
	sd t0, 233(a6)
	addi a6, a6, -2047
	ld t0, 1520(s0)
	addi a6, a6, 2047
	sd t0, 241(a6)
	addi a6, a6, -2047
	ld t0, 1528(s0)
	addi a6, a6, 2047
	sd t0, 249(a6)
	addi a6, a6, -2047
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 2047
	addi a2, a2, 1153
	addi a3, zero, 2047
	addi a3, a3, 449
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 2047
	addi a2, a2, 1217
	addi a3, zero, 2047
	addi a3, a3, 769
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 2047
	addi a2, a2, 1281
	addi a3, zero, 384
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 2047
	addi a2, a2, 1153
	addi a3, zero, 2047
	addi a3, a3, 1217
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 2047
	addi a2, a2, 449
	addi a3, zero, 2047
	addi a3, a3, 769
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
	addi a2, zero, 2047
	addi a2, a2, 1153
	addi a3, zero, 2047
	addi a3, a3, 1281
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 2047
	addi a2, a2, 449
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
	addi a2, zero, 2047
	addi a2, a2, 1217
	addi a3, zero, 2047
	addi a3, a3, 1281
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 2047
	addi a2, a2, 769
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
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 1344(s0)
	addi a6, a6, 2047
	sd t0, 449(a6)
	addi a6, a6, -2047
	ld t0, 1352(s0)
	addi a6, a6, 2047
	sd t0, 457(a6)
	addi a6, a6, -2047
	ld t0, 1360(s0)
	addi a6, a6, 2047
	sd t0, 465(a6)
	addi a6, a6, -2047
	ld t0, 1368(s0)
	addi a6, a6, 2047
	sd t0, 473(a6)
	addi a6, a6, -2047
	ld t0, 1376(s0)
	addi a6, a6, 2047
	sd t0, 481(a6)
	addi a6, a6, -2047
	ld t0, 1384(s0)
	addi a6, a6, 2047
	sd t0, 489(a6)
	addi a6, a6, -2047
	ld t0, 1392(s0)
	addi a6, a6, 2047
	sd t0, 497(a6)
	addi a6, a6, -2047
	ld t0, 1400(s0)
	addi a6, a6, 2047
	sd t0, 505(a6)
	addi a6, a6, -2047
	ld t0, 1408(s0)
	addi a6, a6, 2047
	sd t0, 513(a6)
	addi a6, a6, -2047
	ld t0, 1416(s0)
	addi a6, a6, 2047
	sd t0, 521(a6)
	addi a6, a6, -2047
	ld t0, 1424(s0)
	addi a6, a6, 2047
	sd t0, 529(a6)
	addi a6, a6, -2047
	ld t0, 1432(s0)
	addi a6, a6, 2047
	sd t0, 537(a6)
	addi a6, a6, -2047
	ld t0, 1440(s0)
	addi a6, a6, 2047
	sd t0, 545(a6)
	addi a6, a6, -2047
	ld t0, 1448(s0)
	addi a6, a6, 2047
	sd t0, 553(a6)
	addi a6, a6, -2047
	ld t0, 1456(s0)
	addi a6, a6, 2047
	sd t0, 561(a6)
	addi a6, a6, -2047
	ld t0, 1464(s0)
	addi a6, a6, 2047
	sd t0, 569(a6)
	addi a6, a6, -2047
	ld t0, 1472(s0)
	addi a6, a6, 2047
	sd t0, 577(a6)
	addi a6, a6, -2047
	ld t0, 1480(s0)
	addi a6, a6, 2047
	sd t0, 585(a6)
	addi a6, a6, -2047
	ld t0, 1488(s0)
	addi a6, a6, 2047
	sd t0, 593(a6)
	addi a6, a6, -2047
	ld t0, 1496(s0)
	addi a6, a6, 2047
	sd t0, 601(a6)
	addi a6, a6, -2047
	ld t0, 1504(s0)
	addi a6, a6, 2047
	sd t0, 609(a6)
	addi a6, a6, -2047
	ld t0, 1512(s0)
	addi a6, a6, 2047
	sd t0, 617(a6)
	addi a6, a6, -2047
	ld t0, 1520(s0)
	addi a6, a6, 2047
	sd t0, 625(a6)
	addi a6, a6, -2047
	ld t0, 1528(s0)
	addi a6, a6, 2047
	sd t0, 633(a6)
	addi a6, a6, -2047
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 2047
	addi a2, a2, 1153
	addi a3, zero, 2047
	addi a3, a3, 1345
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 2047
	addi a2, a2, 1217
	addi a3, zero, 2047
	addi a3, a3, 1409
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 2047
	addi a2, a2, 1281
	addi a3, zero, 2047
	addi a3, a3, 1473
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 2047
	addi a2, a2, 1153
	addi a3, zero, 2047
	addi a3, a3, 1217
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 2047
	addi a2, a2, 1345
	addi a3, zero, 2047
	addi a3, a3, 1409
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
	addi a2, zero, 2047
	addi a2, a2, 1153
	addi a3, zero, 2047
	addi a3, a3, 1281
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 2047
	addi a2, a2, 1345
	addi a3, zero, 2047
	addi a3, a3, 1473
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
	addi a2, zero, 2047
	addi a2, a2, 1217
	addi a3, zero, 2047
	addi a3, a3, 1281
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 2047
	addi a2, a2, 1409
	addi a3, zero, 2047
	addi a3, a3, 1473
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
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 1344(s0)
	addi a6, a6, 2047
	sd t0, 641(a6)
	addi a6, a6, -2047
	ld t0, 1352(s0)
	addi a6, a6, 2047
	sd t0, 649(a6)
	addi a6, a6, -2047
	ld t0, 1360(s0)
	addi a6, a6, 2047
	sd t0, 657(a6)
	addi a6, a6, -2047
	ld t0, 1368(s0)
	addi a6, a6, 2047
	sd t0, 665(a6)
	addi a6, a6, -2047
	ld t0, 1376(s0)
	addi a6, a6, 2047
	sd t0, 673(a6)
	addi a6, a6, -2047
	ld t0, 1384(s0)
	addi a6, a6, 2047
	sd t0, 681(a6)
	addi a6, a6, -2047
	ld t0, 1392(s0)
	addi a6, a6, 2047
	sd t0, 689(a6)
	addi a6, a6, -2047
	ld t0, 1400(s0)
	addi a6, a6, 2047
	sd t0, 697(a6)
	addi a6, a6, -2047
	ld t0, 1408(s0)
	addi a6, a6, 2047
	sd t0, 705(a6)
	addi a6, a6, -2047
	ld t0, 1416(s0)
	addi a6, a6, 2047
	sd t0, 713(a6)
	addi a6, a6, -2047
	ld t0, 1424(s0)
	addi a6, a6, 2047
	sd t0, 721(a6)
	addi a6, a6, -2047
	ld t0, 1432(s0)
	addi a6, a6, 2047
	sd t0, 729(a6)
	addi a6, a6, -2047
	ld t0, 1440(s0)
	addi a6, a6, 2047
	sd t0, 737(a6)
	addi a6, a6, -2047
	ld t0, 1448(s0)
	addi a6, a6, 2047
	sd t0, 745(a6)
	addi a6, a6, -2047
	ld t0, 1456(s0)
	addi a6, a6, 2047
	sd t0, 753(a6)
	addi a6, a6, -2047
	ld t0, 1464(s0)
	addi a6, a6, 2047
	sd t0, 761(a6)
	addi a6, a6, -2047
	ld t0, 1472(s0)
	addi a6, a6, 2047
	sd t0, 769(a6)
	addi a6, a6, -2047
	ld t0, 1480(s0)
	addi a6, a6, 2047
	sd t0, 777(a6)
	addi a6, a6, -2047
	ld t0, 1488(s0)
	addi a6, a6, 2047
	sd t0, 785(a6)
	addi a6, a6, -2047
	ld t0, 1496(s0)
	addi a6, a6, 2047
	sd t0, 793(a6)
	addi a6, a6, -2047
	ld t0, 1504(s0)
	addi a6, a6, 2047
	sd t0, 801(a6)
	addi a6, a6, -2047
	ld t0, 1512(s0)
	addi a6, a6, 2047
	sd t0, 809(a6)
	addi a6, a6, -2047
	ld t0, 1520(s0)
	addi a6, a6, 2047
	sd t0, 817(a6)
	addi a6, a6, -2047
	ld t0, 1528(s0)
	addi a6, a6, 2047
	sd t0, 825(a6)
	addi a6, a6, -2047
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 2047
	addi a2, a2, 1153
	addi a3, zero, 2047
	addi a3, a3, 1537
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 2047
	addi a2, a2, 1217
	addi a3, zero, 2047
	addi a3, a3, 1601
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 2047
	addi a2, a2, 1281
	addi a3, zero, 2047
	addi a3, a3, 1665
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 2047
	addi a2, a2, 1153
	addi a3, zero, 2047
	addi a3, a3, 1217
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 2047
	addi a2, a2, 1537
	addi a3, zero, 2047
	addi a3, a3, 1601
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
	addi a2, zero, 2047
	addi a2, a2, 1153
	addi a3, zero, 2047
	addi a3, a3, 1281
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 2047
	addi a2, a2, 1537
	addi a3, zero, 2047
	addi a3, a3, 1665
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
	addi a2, zero, 2047
	addi a2, a2, 1217
	addi a3, zero, 2047
	addi a3, a3, 1281
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 2047
	addi a2, a2, 1601
	addi a3, zero, 2047
	addi a3, a3, 1665
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
	addi a6, s0, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	ld t0, 1344(s0)
	addi a6, a6, 2047
	sd t0, 833(a6)
	addi a6, a6, -2047
	ld t0, 1352(s0)
	addi a6, a6, 2047
	sd t0, 841(a6)
	addi a6, a6, -2047
	ld t0, 1360(s0)
	addi a6, a6, 2047
	sd t0, 849(a6)
	addi a6, a6, -2047
	ld t0, 1368(s0)
	addi a6, a6, 2047
	sd t0, 857(a6)
	addi a6, a6, -2047
	ld t0, 1376(s0)
	addi a6, a6, 2047
	sd t0, 865(a6)
	addi a6, a6, -2047
	ld t0, 1384(s0)
	addi a6, a6, 2047
	sd t0, 873(a6)
	addi a6, a6, -2047
	ld t0, 1392(s0)
	addi a6, a6, 2047
	sd t0, 881(a6)
	addi a6, a6, -2047
	ld t0, 1400(s0)
	addi a6, a6, 2047
	sd t0, 889(a6)
	addi a6, a6, -2047
	ld t0, 1408(s0)
	addi a6, a6, 2047
	sd t0, 897(a6)
	addi a6, a6, -2047
	ld t0, 1416(s0)
	addi a6, a6, 2047
	sd t0, 905(a6)
	addi a6, a6, -2047
	ld t0, 1424(s0)
	addi a6, a6, 2047
	sd t0, 913(a6)
	addi a6, a6, -2047
	ld t0, 1432(s0)
	addi a6, a6, 2047
	sd t0, 921(a6)
	addi a6, a6, -2047
	ld t0, 1440(s0)
	addi a6, a6, 2047
	sd t0, 929(a6)
	addi a6, a6, -2047
	ld t0, 1448(s0)
	addi a6, a6, 2047
	sd t0, 937(a6)
	addi a6, a6, -2047
	ld t0, 1456(s0)
	addi a6, a6, 2047
	sd t0, 945(a6)
	addi a6, a6, -2047
	ld t0, 1464(s0)
	addi a6, a6, 2047
	sd t0, 953(a6)
	addi a6, a6, -2047
	ld t0, 1472(s0)
	addi a6, a6, 2047
	sd t0, 961(a6)
	addi a6, a6, -2047
	ld t0, 1480(s0)
	addi a6, a6, 2047
	sd t0, 969(a6)
	addi a6, a6, -2047
	ld t0, 1488(s0)
	addi a6, a6, 2047
	sd t0, 977(a6)
	addi a6, a6, -2047
	ld t0, 1496(s0)
	addi a6, a6, 2047
	sd t0, 985(a6)
	addi a6, a6, -2047
	ld t0, 1504(s0)
	addi a6, a6, 2047
	sd t0, 993(a6)
	addi a6, a6, -2047
	ld t0, 1512(s0)
	addi a6, a6, 2047
	sd t0, 1001(a6)
	addi a6, a6, -2047
	ld t0, 1520(s0)
	addi a6, a6, 2047
	sd t0, 1009(a6)
	addi a6, a6, -2047
	ld t0, 1528(s0)
	addi a6, a6, 2047
	sd t0, 1017(a6)
	addi a6, a6, -2047
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
	addi s1, zero, 256
2103:
	addi s1, s1, -1
	srli t1, s1, 5
	slli t1, t1, 3
	add t1, t1, s0
	addi t2, t1, 2047
	ld t2, 129(t2)
	addi t3, t1, 2047
	ld t3, 321(t3)
	slli t0, s1, 1
	srl t2, t2, t0
	srl t3, t3, t0
	andi t2, t2, 3
	andi t3, t3, 3
	slli t2, t2, 2
	or t2, t2, t3
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
	ld t1, 192(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 384(a0)
	ld t2, 576(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 768(a0)
	ld t2, 960(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1152(a0)
	ld t3, 1344(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1536(a0)
	ld t2, 1728(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1920(a0)
	addi t3, a0, 2047
	ld t3, 65(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 257(t2)
	addi t3, a0, 2047
	ld t3, 449(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 641(t3)
	addi t4, a0, 2047
	ld t4, 833(t4)
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
	sd t0, 1729(s0)
	addi s0, s0, -2047
	ld t0, 8(a0)
	ld t1, 200(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 392(a0)
	ld t2, 584(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 776(a0)
	ld t2, 968(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1160(a0)
	ld t3, 1352(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1544(a0)
	ld t2, 1736(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1928(a0)
	addi t3, a0, 2047
	ld t3, 73(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 265(t2)
	addi t3, a0, 2047
	ld t3, 457(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 649(t3)
	addi t4, a0, 2047
	ld t4, 841(t4)
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
	sd t0, 1737(s0)
	addi s0, s0, -2047
	ld t0, 16(a0)
	ld t1, 208(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 400(a0)
	ld t2, 592(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 784(a0)
	ld t2, 976(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1168(a0)
	ld t3, 1360(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1552(a0)
	ld t2, 1744(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1936(a0)
	addi t3, a0, 2047
	ld t3, 81(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 273(t2)
	addi t3, a0, 2047
	ld t3, 465(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 657(t3)
	addi t4, a0, 2047
	ld t4, 849(t4)
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
	sd t0, 1745(s0)
	addi s0, s0, -2047
	ld t0, 24(a0)
	ld t1, 216(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 408(a0)
	ld t2, 600(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 792(a0)
	ld t2, 984(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1176(a0)
	ld t3, 1368(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1560(a0)
	ld t2, 1752(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1944(a0)
	addi t3, a0, 2047
	ld t3, 89(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 281(t2)
	addi t3, a0, 2047
	ld t3, 473(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 665(t3)
	addi t4, a0, 2047
	ld t4, 857(t4)
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
	sd t0, 1753(s0)
	addi s0, s0, -2047
	ld t0, 32(a0)
	ld t1, 224(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 416(a0)
	ld t2, 608(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 800(a0)
	ld t2, 992(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1184(a0)
	ld t3, 1376(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1568(a0)
	ld t2, 1760(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1952(a0)
	addi t3, a0, 2047
	ld t3, 97(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 289(t2)
	addi t3, a0, 2047
	ld t3, 481(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 673(t3)
	addi t4, a0, 2047
	ld t4, 865(t4)
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
	sd t0, 1761(s0)
	addi s0, s0, -2047
	ld t0, 40(a0)
	ld t1, 232(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 424(a0)
	ld t2, 616(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 808(a0)
	ld t2, 1000(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1192(a0)
	ld t3, 1384(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1576(a0)
	ld t2, 1768(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1960(a0)
	addi t3, a0, 2047
	ld t3, 105(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 297(t2)
	addi t3, a0, 2047
	ld t3, 489(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 681(t3)
	addi t4, a0, 2047
	ld t4, 873(t4)
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
	sd t0, 1769(s0)
	addi s0, s0, -2047
	ld t0, 48(a0)
	ld t1, 240(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 432(a0)
	ld t2, 624(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 816(a0)
	ld t2, 1008(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1200(a0)
	ld t3, 1392(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1584(a0)
	ld t2, 1776(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1968(a0)
	addi t3, a0, 2047
	ld t3, 113(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 305(t2)
	addi t3, a0, 2047
	ld t3, 497(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 689(t3)
	addi t4, a0, 2047
	ld t4, 881(t4)
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
	sd t0, 1777(s0)
	addi s0, s0, -2047
	ld t0, 56(a0)
	ld t1, 248(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 440(a0)
	ld t2, 632(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 824(a0)
	ld t2, 1016(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1208(a0)
	ld t3, 1400(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1592(a0)
	ld t2, 1784(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1976(a0)
	addi t3, a0, 2047
	ld t3, 121(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 313(t2)
	addi t3, a0, 2047
	ld t3, 505(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 697(t3)
	addi t4, a0, 2047
	ld t4, 889(t4)
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
	sd t0, 1785(s0)
	addi s0, s0, -2047
	ld t0, 64(a0)
	ld t1, 256(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 448(a0)
	ld t2, 640(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 832(a0)
	ld t2, 1024(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1216(a0)
	ld t3, 1408(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1600(a0)
	ld t2, 1792(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1984(a0)
	addi t3, a0, 2047
	ld t3, 129(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 321(t2)
	addi t3, a0, 2047
	ld t3, 513(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 705(t3)
	addi t4, a0, 2047
	ld t4, 897(t4)
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
	sd t0, 1793(s0)
	addi s0, s0, -2047
	ld t0, 72(a0)
	ld t1, 264(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 456(a0)
	ld t2, 648(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 840(a0)
	ld t2, 1032(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1224(a0)
	ld t3, 1416(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1608(a0)
	ld t2, 1800(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1992(a0)
	addi t3, a0, 2047
	ld t3, 137(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 329(t2)
	addi t3, a0, 2047
	ld t3, 521(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 713(t3)
	addi t4, a0, 2047
	ld t4, 905(t4)
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
	sd t0, 1801(s0)
	addi s0, s0, -2047
	ld t0, 80(a0)
	ld t1, 272(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 464(a0)
	ld t2, 656(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 848(a0)
	ld t2, 1040(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1232(a0)
	ld t3, 1424(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1616(a0)
	ld t2, 1808(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 2000(a0)
	addi t3, a0, 2047
	ld t3, 145(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 337(t2)
	addi t3, a0, 2047
	ld t3, 529(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 721(t3)
	addi t4, a0, 2047
	ld t4, 913(t4)
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
	sd t0, 1809(s0)
	addi s0, s0, -2047
	ld t0, 88(a0)
	ld t1, 280(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 472(a0)
	ld t2, 664(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 856(a0)
	ld t2, 1048(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1240(a0)
	ld t3, 1432(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1624(a0)
	ld t2, 1816(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 2008(a0)
	addi t3, a0, 2047
	ld t3, 153(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 345(t2)
	addi t3, a0, 2047
	ld t3, 537(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 729(t3)
	addi t4, a0, 2047
	ld t4, 921(t4)
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
	sd t0, 1817(s0)
	addi s0, s0, -2047
	ld t0, 96(a0)
	ld t1, 288(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 480(a0)
	ld t2, 672(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 864(a0)
	ld t2, 1056(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1248(a0)
	ld t3, 1440(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1632(a0)
	ld t2, 1824(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 2016(a0)
	addi t3, a0, 2047
	ld t3, 161(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 353(t2)
	addi t3, a0, 2047
	ld t3, 545(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 737(t3)
	addi t4, a0, 2047
	ld t4, 929(t4)
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
	sd t0, 1825(s0)
	addi s0, s0, -2047
	ld t0, 104(a0)
	ld t1, 296(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 488(a0)
	ld t2, 680(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 872(a0)
	ld t2, 1064(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1256(a0)
	ld t3, 1448(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1640(a0)
	ld t2, 1832(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 2024(a0)
	addi t3, a0, 2047
	ld t3, 169(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 361(t2)
	addi t3, a0, 2047
	ld t3, 553(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 745(t3)
	addi t4, a0, 2047
	ld t4, 937(t4)
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
	sd t0, 1833(s0)
	addi s0, s0, -2047
	ld t0, 112(a0)
	ld t1, 304(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 496(a0)
	ld t2, 688(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 880(a0)
	ld t2, 1072(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1264(a0)
	ld t3, 1456(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1648(a0)
	ld t2, 1840(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 2032(a0)
	addi t3, a0, 2047
	ld t3, 177(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 369(t2)
	addi t3, a0, 2047
	ld t3, 561(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 753(t3)
	addi t4, a0, 2047
	ld t4, 945(t4)
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
	sd t0, 1841(s0)
	addi s0, s0, -2047
	ld t0, 120(a0)
	ld t1, 312(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 504(a0)
	ld t2, 696(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 888(a0)
	ld t2, 1080(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1272(a0)
	ld t3, 1464(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1656(a0)
	ld t2, 1848(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 2040(a0)
	addi t3, a0, 2047
	ld t3, 185(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 377(t2)
	addi t3, a0, 2047
	ld t3, 569(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 761(t3)
	addi t4, a0, 2047
	ld t4, 953(t4)
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
	sd t0, 1849(s0)
	addi s0, s0, -2047
	ld t0, 128(a0)
	ld t1, 320(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 512(a0)
	ld t2, 704(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 896(a0)
	ld t2, 1088(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1280(a0)
	ld t3, 1472(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1664(a0)
	ld t2, 1856(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 1(t2)
	addi t3, a0, 2047
	ld t3, 193(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 385(t2)
	addi t3, a0, 2047
	ld t3, 577(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 769(t3)
	addi t4, a0, 2047
	ld t4, 961(t4)
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
	sd t0, 1857(s0)
	addi s0, s0, -2047
	ld t0, 136(a0)
	ld t1, 328(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 520(a0)
	ld t2, 712(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 904(a0)
	ld t2, 1096(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1288(a0)
	ld t3, 1480(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1672(a0)
	ld t2, 1864(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 9(t2)
	addi t3, a0, 2047
	ld t3, 201(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 393(t2)
	addi t3, a0, 2047
	ld t3, 585(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 777(t3)
	addi t4, a0, 2047
	ld t4, 969(t4)
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
	sd t0, 1865(s0)
	addi s0, s0, -2047
	ld t0, 144(a0)
	ld t1, 336(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 528(a0)
	ld t2, 720(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 912(a0)
	ld t2, 1104(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1296(a0)
	ld t3, 1488(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1680(a0)
	ld t2, 1872(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 17(t2)
	addi t3, a0, 2047
	ld t3, 209(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 401(t2)
	addi t3, a0, 2047
	ld t3, 593(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 785(t3)
	addi t4, a0, 2047
	ld t4, 977(t4)
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
	sd t0, 1873(s0)
	addi s0, s0, -2047
	ld t0, 152(a0)
	ld t1, 344(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 536(a0)
	ld t2, 728(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 920(a0)
	ld t2, 1112(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1304(a0)
	ld t3, 1496(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1688(a0)
	ld t2, 1880(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 25(t2)
	addi t3, a0, 2047
	ld t3, 217(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 409(t2)
	addi t3, a0, 2047
	ld t3, 601(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 793(t3)
	addi t4, a0, 2047
	ld t4, 985(t4)
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
	sd t0, 1881(s0)
	addi s0, s0, -2047
	ld t0, 160(a0)
	ld t1, 352(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 544(a0)
	ld t2, 736(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 928(a0)
	ld t2, 1120(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1312(a0)
	ld t3, 1504(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1696(a0)
	ld t2, 1888(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 33(t2)
	addi t3, a0, 2047
	ld t3, 225(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 417(t2)
	addi t3, a0, 2047
	ld t3, 609(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 801(t3)
	addi t4, a0, 2047
	ld t4, 993(t4)
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
	sd t0, 1889(s0)
	addi s0, s0, -2047
	ld t0, 168(a0)
	ld t1, 360(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 552(a0)
	ld t2, 744(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 936(a0)
	ld t2, 1128(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1320(a0)
	ld t3, 1512(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1704(a0)
	ld t2, 1896(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 41(t2)
	addi t3, a0, 2047
	ld t3, 233(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 425(t2)
	addi t3, a0, 2047
	ld t3, 617(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 809(t3)
	addi t4, a0, 2047
	ld t4, 1001(t4)
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
	sd t0, 1897(s0)
	addi s0, s0, -2047
	ld t0, 176(a0)
	ld t1, 368(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 560(a0)
	ld t2, 752(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 944(a0)
	ld t2, 1136(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1328(a0)
	ld t3, 1520(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1712(a0)
	ld t2, 1904(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 49(t2)
	addi t3, a0, 2047
	ld t3, 241(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 433(t2)
	addi t3, a0, 2047
	ld t3, 625(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 817(t3)
	addi t4, a0, 2047
	ld t4, 1009(t4)
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
	sd t0, 1905(s0)
	addi s0, s0, -2047
	ld t0, 184(a0)
	ld t1, 376(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 568(a0)
	ld t2, 760(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 952(a0)
	ld t2, 1144(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1336(a0)
	ld t3, 1528(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 1720(a0)
	ld t2, 1912(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 57(t2)
	addi t3, a0, 2047
	ld t3, 249(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	addi t2, a0, 2047
	ld t2, 441(t2)
	addi t3, a0, 2047
	ld t3, 633(t3)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	addi t3, a0, 2047
	ld t3, 825(t3)
	addi t4, a0, 2047
	ld t4, 1017(t4)
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
	sd t0, 1913(s0)
	addi s0, s0, -2047
	addi a0, s0, 0
	addi a1, zero, 1152
	addi a2, zero, 960
	addi a3, zero, 1088
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1088
	addi a3, zero, 1088
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1024
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1280
	addi a2, zero, 1088
	addi a3, zero, 256
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1152
	addi a3, zero, 1152
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1216
	addi a3, zero, 1216
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1600
	addi a3, zero, 1600
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1152
	addi a3, zero, 1600
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1728
	addi a3, zero, 1728
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1728
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1728
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1728
	addi a3, zero, 1728
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1280
	addi a3, zero, 1280
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 448
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1536
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1856
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1856
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1216
	addi a3, zero, 1280
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1472
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1792
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1344
	addi a3, zero, 1728
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1344
	addi a3, zero, 1728
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1728
	addi a3, zero, 1344
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1792
	addi a3, zero, 1408
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1664
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1664
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1664
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1408
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1344
	addi a3, zero, 1344
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1408
	addi a3, zero, 1408
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1600
	addi a3, zero, 1600
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1344
	addi a3, zero, 1600
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1728
	addi a3, zero, 1728
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1728
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1728
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1728
	addi a3, zero, 1728
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1472
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 448
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1536
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1856
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1856
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1280
	addi a2, zero, 1408
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1280
	addi a2, zero, 1280
	addi a3, zero, 1280
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1152
	addi a2, zero, 1792
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1152
	addi a2, zero, 1152
	addi a3, zero, 1728
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1152
	addi a2, zero, 1152
	addi a3, zero, 1728
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1728
	addi a3, zero, 1152
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1792
	addi a3, zero, 1216
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1664
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1664
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1664
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 1152
	addi a3, zero, 1280
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1280
	addi a3, zero, 1280
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1472
	addi a2, zero, 1536
	addi a3, zero, 1280
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1216
	addi a3, zero, 256
	call {vg_brainpoolp512r1_add_mod_p}
	addi t3, zero, 0
	ld t4, 1472(s0)
	or t3, t3, t4
	ld t4, 1480(s0)
	or t3, t3, t4
	ld t4, 1488(s0)
	or t3, t3, t4
	ld t4, 1496(s0)
	or t3, t3, t4
	ld t4, 1504(s0)
	or t3, t3, t4
	ld t4, 1512(s0)
	or t3, t3, t4
	ld t4, 1520(s0)
	or t3, t3, t4
	ld t4, 1528(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	ld t0, 1408(s0)
	ld t1, 384(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1408(s0)
	ld t0, 1416(s0)
	ld t1, 392(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1416(s0)
	ld t0, 1424(s0)
	ld t1, 400(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1424(s0)
	ld t0, 1432(s0)
	ld t1, 408(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1432(s0)
	ld t0, 1440(s0)
	ld t1, 416(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1440(s0)
	ld t0, 1448(s0)
	ld t1, 424(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1448(s0)
	ld t0, 1456(s0)
	ld t1, 432(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1456(s0)
	ld t0, 1464(s0)
	ld t1, 440(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1464(s0)
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1344
	addi a3, zero, 2047
	addi a3, a3, 1729
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1408
	addi a3, zero, 2047
	addi a3, a3, 1793
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1472
	addi a3, zero, 2047
	addi a3, a3, 1857
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1344
	addi a3, zero, 1408
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 2047
	addi a2, a2, 1729
	addi a3, zero, 2047
	addi a3, a3, 1793
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
	addi a2, zero, 1344
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 2047
	addi a2, a2, 1729
	addi a3, zero, 2047
	addi a3, a3, 1857
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
	addi a2, zero, 1408
	addi a3, zero, 1472
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 960
	addi a2, zero, 2047
	addi a2, a2, 1793
	addi a3, zero, 2047
	addi a3, a3, 1857
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1856
	addi a3, zero, 960
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 960
	addi a2, zero, 1600
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1856
	addi a2, zero, 1856
	addi a3, zero, 960
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1088
	addi a2, zero, 448
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 960
	addi a2, zero, 512
	addi a3, zero, 1664
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1088
	addi a2, zero, 960
	addi a3, zero, 1088
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 960
	addi a2, zero, 1600
	addi a3, zero, 1088
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1088
	addi a2, zero, 1600
	addi a3, zero, 1088
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 960
	addi a3, zero, 1088
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
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1856
	addi a3, zero, 1792
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 960
	addi a2, zero, 1728
	addi a3, zero, 960
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 960
	addi a2, zero, 960
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1728
	addi a3, zero, 1600
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1088
	addi a2, zero, 1856
	addi a3, zero, 1088
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1088
	addi a2, zero, 1088
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_add_mod_p}
	bnez s1, 2103b
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 961
	addi a2, zero, 1088
	addi a3, zero, 384
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1473
	addi a2, zero, 2047
	addi a2, a2, 961
	addi a3, zero, 2047
	addi a3, a3, 961
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1025
	addi a2, zero, 2047
	addi a2, a2, 961
	addi a3, zero, 2047
	addi a3, a3, 1473
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1089
	addi a2, zero, 2047
	addi a2, a2, 1025
	addi a3, zero, 2047
	addi a3, a3, 1473
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1153
	addi a2, zero, 2047
	addi a2, a2, 1089
	addi a3, zero, 2047
	addi a3, a3, 1473
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1217
	addi a2, zero, 2047
	addi a2, a2, 1153
	addi a3, zero, 2047
	addi a3, a3, 1473
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1281
	addi a2, zero, 2047
	addi a2, a2, 1217
	addi a3, zero, 2047
	addi a3, a3, 1473
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1345
	addi a2, zero, 2047
	addi a2, a2, 1281
	addi a3, zero, 2047
	addi a3, a3, 1473
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1409
	addi a2, zero, 2047
	addi a2, a2, 1345
	addi a3, zero, 2047
	addi a3, a3, 1473
	call {vg_brainpoolp512r1_mul_mod_p}
	addi t0, s0, 2047
	ld t0, 1089(t0)
	sd t0, 1920(s0)
	addi t0, s0, 2047
	ld t0, 1097(t0)
	sd t0, 1928(s0)
	addi t0, s0, 2047
	ld t0, 1105(t0)
	sd t0, 1936(s0)
	addi t0, s0, 2047
	ld t0, 1113(t0)
	sd t0, 1944(s0)
	addi t0, s0, 2047
	ld t0, 1121(t0)
	sd t0, 1952(s0)
	addi t0, s0, 2047
	ld t0, 1129(t0)
	sd t0, 1960(s0)
	addi t0, s0, 2047
	ld t0, 1137(t0)
	sd t0, 1968(s0)
	addi t0, s0, 2047
	ld t0, 1145(t0)
	sd t0, 1976(s0)
	addi s1, zero, 4
2104:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2104b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1089
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 5
2105:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2105b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1345
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 4
2106:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2106b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1345
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 4
2107:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2107b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1217
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 4
2108:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2108b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1345
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 4
2109:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2109b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1281
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 1
2110:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2110b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 961
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 7
2111:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2111b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1345
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 4
2112:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2112b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1281
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 3
2113:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2113b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1153
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 5
2114:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2114b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1217
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 2
2115:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2115b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1025
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 7
2116:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2116b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1217
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 7
2117:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2117b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1281
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 6
2118:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2118b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1409
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 4
2119:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2119b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1409
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 4
2120:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2120b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1089
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 5
2121:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2121b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1153
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 6
2122:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2122b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1345
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 5
2123:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2123b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1281
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 1
2124:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2124b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 961
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 5
2125:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2125b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1025
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 6
2126:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2126b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1409
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 6
2127:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2127b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1217
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 4
2128:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2128b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1409
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 2
2129:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2129b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1025
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 11
2130:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2130b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1409
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 4
2131:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2131b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1217
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 3
2132:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2132b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1025
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 4
2133:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2133b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1025
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 5
2134:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2134b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 961
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 7
2135:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2135b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1345
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 4
2136:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2136b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1281
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 5
2137:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2137b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1153
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 3
2138:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2138b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1025
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 6
2139:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2139b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1409
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 6
2140:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2140b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1217
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 4
2141:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2141b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1345
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 3
2142:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2142b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 961
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 8
2143:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2143b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1153
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 5
2144:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2144b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1345
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 3
2145:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2145b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1025
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 4
2146:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2146b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1025
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 6
2147:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2147b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1153
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 5
2148:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2148b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1153
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 4
2149:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2149b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1025
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 5
2150:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2150b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1089
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 5
2151:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2151b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1153
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 8
2152:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2152b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1025
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 4
2153:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2153b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1025
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 5
2154:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2154b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 961
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 7
2155:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2155b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1153
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 7
2156:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2156b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1281
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 3
2157:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2157b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1153
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 4
2158:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2158b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1089
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 6
2159:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2159b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1345
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 4
2160:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2160b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1217
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 4
2161:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2161b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1281
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 12
2162:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2162b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1217
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 4
2163:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2163b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1281
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 2
2164:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2164b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1025
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 5
2165:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2165b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1025
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 6
2166:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2166b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1345
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 5
2167:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2167b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 961
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 7
2168:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2168b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1089
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 5
2169:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2169b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1281
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 4
2170:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2170b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1281
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 6
2171:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2171b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1345
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 3
2172:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2172b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1089
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 8
2173:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2173b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1217
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 4
2174:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2174b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1089
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 4
2175:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2175b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1153
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 6
2176:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2176b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1345
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 2
2177:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2177b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 961
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 6
2178:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2178b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1153
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 10
2179:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2179b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1153
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 4
2180:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2180b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1025
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 6
2181:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2181b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1089
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 4
2182:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2182b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 961
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 10
2183:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2183b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1409
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 4
2184:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2184b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1409
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 4
2185:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2185b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1217
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 5
2186:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2186b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1409
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 6
2187:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2187b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1281
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 3
2188:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2188b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1025
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 9
2189:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2189b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1281
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 7
2190:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2190b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1345
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 7
2191:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2191b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1089
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 5
2192:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2192b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1089
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 6
2193:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2193b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1089
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 4
2194:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2194b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1089
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 4
2195:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2195b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1025
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 9
2196:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2196b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1089
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 3
2197:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2197b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1025
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 6
2198:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2198b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1281
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 8
2199:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2199b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1153
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 5
2200:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2200b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1217
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 3
2201:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2201b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 961
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 7
2202:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2202b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1409
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 4
2203:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 2203b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 961
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1152
	addi a2, zero, 960
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1152
	addi a3, zero, 320
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1280
	addi a2, zero, 1216
	addi a3, zero, 256
	call {vg_brainpoolp512r1_add_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 704
	addi a3, zero, 256
	call {vg_brainpoolp512r1_add_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1280
	addi a3, zero, 1344
	call {vg_brainpoolp512r1_sub_mod_n}
	addi t3, zero, 0
	ld t4, 1088(s0)
	or t3, t3, t4
	ld t4, 1096(s0)
	or t3, t3, t4
	ld t4, 1104(s0)
	or t3, t3, t4
	ld t4, 1112(s0)
	or t3, t3, t4
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
	addi t0, s0, 2047
	ld t0, 833(t0)
	and t0, t0, a7
	addi s0, s0, 2047
	sd t0, 833(s0)
	addi s0, s0, -2047
	addi t3, zero, 0
	ld t4, 1408(s0)
	or t3, t3, t4
	ld t4, 1416(s0)
	or t3, t3, t4
	ld t4, 1424(s0)
	or t3, t3, t4
	ld t4, 1432(s0)
	or t3, t3, t4
	ld t4, 1440(s0)
	or t3, t3, t4
	ld t4, 1448(s0)
	or t3, t3, t4
	ld t4, 1456(s0)
	or t3, t3, t4
	ld t4, 1464(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	addi t0, s0, 2047
	ld t0, 833(t0)
	and t0, t0, a7
	addi s0, s0, 2047
	sd t0, 833(s0)
	addi s0, s0, -2047
	addi a0, s0, 2047
	ld a0, 833(a0)
	andi a0, a0, 1
	ld ra, 24(s0)
	ld s2, 16(s0)
	ld s1, 8(s0)
	ld s3, 32(s0)
	ld s0, 0(s0)
	ret
	.option pop

vg_ecdsa_brainpoolp512r1_sign:
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
	addi sp, sp, -320
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
	addi t0, zero, 0
	sb t0, 208(s1)
	addi t0, zero, 0
	sb t0, 209(s1)
	addi t0, zero, 0
	sb t0, 210(s1)
	addi t0, zero, 0
	sb t0, 211(s1)
	addi t0, zero, 0
	sb t0, 212(s1)
	addi t0, zero, 0
	sb t0, 213(s1)
	addi t0, zero, 0
	sb t0, 214(s1)
	addi t0, zero, 0
	sb t0, 215(s1)
	addi t0, zero, 0
	sb t0, 216(s1)
	addi t0, zero, 0
	sb t0, 217(s1)
	addi t0, zero, 0
	sb t0, 218(s1)
	addi t0, zero, 0
	sb t0, 219(s1)
	addi t0, zero, 0
	sb t0, 220(s1)
	addi t0, zero, 0
	sb t0, 221(s1)
	addi t0, zero, 0
	sb t0, 222(s1)
	addi t0, zero, 0
	sb t0, 223(s1)
	lbu t0, 0(s4)
	sb t0, 224(s1)
	lbu t0, 1(s4)
	sb t0, 225(s1)
	lbu t0, 2(s4)
	sb t0, 226(s1)
	lbu t0, 3(s4)
	sb t0, 227(s1)
	lbu t0, 4(s4)
	sb t0, 228(s1)
	lbu t0, 5(s4)
	sb t0, 229(s1)
	lbu t0, 6(s4)
	sb t0, 230(s1)
	lbu t0, 7(s4)
	sb t0, 231(s1)
	lbu t0, 8(s4)
	sb t0, 232(s1)
	lbu t0, 9(s4)
	sb t0, 233(s1)
	lbu t0, 10(s4)
	sb t0, 234(s1)
	lbu t0, 11(s4)
	sb t0, 235(s1)
	lbu t0, 12(s4)
	sb t0, 236(s1)
	lbu t0, 13(s4)
	sb t0, 237(s1)
	lbu t0, 14(s4)
	sb t0, 238(s1)
	lbu t0, 15(s4)
	sb t0, 239(s1)
	lbu t0, 16(s4)
	sb t0, 240(s1)
	lbu t0, 17(s4)
	sb t0, 241(s1)
	lbu t0, 18(s4)
	sb t0, 242(s1)
	lbu t0, 19(s4)
	sb t0, 243(s1)
	lbu t0, 20(s4)
	sb t0, 244(s1)
	lbu t0, 21(s4)
	sb t0, 245(s1)
	lbu t0, 22(s4)
	sb t0, 246(s1)
	lbu t0, 23(s4)
	sb t0, 247(s1)
	lbu t0, 24(s4)
	sb t0, 248(s1)
	lbu t0, 25(s4)
	sb t0, 249(s1)
	lbu t0, 26(s4)
	sb t0, 250(s1)
	lbu t0, 27(s4)
	sb t0, 251(s1)
	lbu t0, 28(s4)
	sb t0, 252(s1)
	lbu t0, 29(s4)
	sb t0, 253(s1)
	lbu t0, 30(s4)
	sb t0, 254(s1)
	lbu t0, 31(s4)
	sb t0, 255(s1)
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
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 225
	addi a2, s1, 192
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 289
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
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 225
	addi a2, s1, 192
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 289
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
	addi s5, zero, 128
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
	lbu t0, 128(s1)
	sb t0, 256(s1)
	lbu t0, 129(s1)
	sb t0, 257(s1)
	lbu t0, 130(s1)
	sb t0, 258(s1)
	lbu t0, 131(s1)
	sb t0, 259(s1)
	lbu t0, 132(s1)
	sb t0, 260(s1)
	lbu t0, 133(s1)
	sb t0, 261(s1)
	lbu t0, 134(s1)
	sb t0, 262(s1)
	lbu t0, 135(s1)
	sb t0, 263(s1)
	lbu t0, 136(s1)
	sb t0, 264(s1)
	lbu t0, 137(s1)
	sb t0, 265(s1)
	lbu t0, 138(s1)
	sb t0, 266(s1)
	lbu t0, 139(s1)
	sb t0, 267(s1)
	lbu t0, 140(s1)
	sb t0, 268(s1)
	lbu t0, 141(s1)
	sb t0, 269(s1)
	lbu t0, 142(s1)
	sb t0, 270(s1)
	lbu t0, 143(s1)
	sb t0, 271(s1)
	lbu t0, 144(s1)
	sb t0, 272(s1)
	lbu t0, 145(s1)
	sb t0, 273(s1)
	lbu t0, 146(s1)
	sb t0, 274(s1)
	lbu t0, 147(s1)
	sb t0, 275(s1)
	lbu t0, 148(s1)
	sb t0, 276(s1)
	lbu t0, 149(s1)
	sb t0, 277(s1)
	lbu t0, 150(s1)
	sb t0, 278(s1)
	lbu t0, 151(s1)
	sb t0, 279(s1)
	lbu t0, 152(s1)
	sb t0, 280(s1)
	lbu t0, 153(s1)
	sb t0, 281(s1)
	lbu t0, 154(s1)
	sb t0, 282(s1)
	lbu t0, 155(s1)
	sb t0, 283(s1)
	lbu t0, 156(s1)
	sb t0, 284(s1)
	lbu t0, 157(s1)
	sb t0, 285(s1)
	lbu t0, 158(s1)
	sb t0, 286(s1)
	lbu t0, 159(s1)
	sb t0, 287(s1)
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
	lbu t0, 128(s1)
	sb t0, 288(s1)
	lbu t0, 129(s1)
	sb t0, 289(s1)
	lbu t0, 130(s1)
	sb t0, 290(s1)
	lbu t0, 131(s1)
	sb t0, 291(s1)
	lbu t0, 132(s1)
	sb t0, 292(s1)
	lbu t0, 133(s1)
	sb t0, 293(s1)
	lbu t0, 134(s1)
	sb t0, 294(s1)
	lbu t0, 135(s1)
	sb t0, 295(s1)
	lbu t0, 136(s1)
	sb t0, 296(s1)
	lbu t0, 137(s1)
	sb t0, 297(s1)
	lbu t0, 138(s1)
	sb t0, 298(s1)
	lbu t0, 139(s1)
	sb t0, 299(s1)
	lbu t0, 140(s1)
	sb t0, 300(s1)
	lbu t0, 141(s1)
	sb t0, 301(s1)
	lbu t0, 142(s1)
	sb t0, 302(s1)
	lbu t0, 143(s1)
	sb t0, 303(s1)
	lbu t0, 144(s1)
	sb t0, 304(s1)
	lbu t0, 145(s1)
	sb t0, 305(s1)
	lbu t0, 146(s1)
	sb t0, 306(s1)
	lbu t0, 147(s1)
	sb t0, 307(s1)
	lbu t0, 148(s1)
	sb t0, 308(s1)
	lbu t0, 149(s1)
	sb t0, 309(s1)
	lbu t0, 150(s1)
	sb t0, 310(s1)
	lbu t0, 151(s1)
	sb t0, 311(s1)
	lbu t0, 152(s1)
	sb t0, 312(s1)
	lbu t0, 153(s1)
	sb t0, 313(s1)
	lbu t0, 154(s1)
	sb t0, 314(s1)
	lbu t0, 155(s1)
	sb t0, 315(s1)
	lbu t0, 156(s1)
	sb t0, 316(s1)
	lbu t0, 157(s1)
	sb t0, 317(s1)
	lbu t0, 158(s1)
	sb t0, 318(s1)
	lbu t0, 159(s1)
	sb t0, 319(s1)
	addi a0, s2, 0
	addi a1, s3, 0
	addi a2, s1, 192
	addi a3, s1, 256
	addi a4, s0, 0
	call {vg_ecdsa_brainpoolp512r1_sign_k}
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
	ld ra, 0(s1)
	ld s0, 8(s1)
	ld s2, 24(s1)
	ld s3, 32(s1)
	ld s4, 40(s1)
	ld s5, 48(s1)
	ld s6, 56(s1)
	ld s1, 16(s1)
	addi sp, sp, 320
	j 213f
212:
	addi sp, sp, -320
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
	addi t0, zero, 0
	sb t0, 208(s1)
	addi t0, zero, 0
	sb t0, 209(s1)
	addi t0, zero, 0
	sb t0, 210(s1)
	addi t0, zero, 0
	sb t0, 211(s1)
	addi t0, zero, 0
	sb t0, 212(s1)
	addi t0, zero, 0
	sb t0, 213(s1)
	addi t0, zero, 0
	sb t0, 214(s1)
	addi t0, zero, 0
	sb t0, 215(s1)
	addi t0, zero, 0
	sb t0, 216(s1)
	addi t0, zero, 0
	sb t0, 217(s1)
	addi t0, zero, 0
	sb t0, 218(s1)
	addi t0, zero, 0
	sb t0, 219(s1)
	addi t0, zero, 0
	sb t0, 220(s1)
	addi t0, zero, 0
	sb t0, 221(s1)
	addi t0, zero, 0
	sb t0, 222(s1)
	addi t0, zero, 0
	sb t0, 223(s1)
	addi t0, zero, 0
	sb t0, 224(s1)
	addi t0, zero, 0
	sb t0, 225(s1)
	addi t0, zero, 0
	sb t0, 226(s1)
	addi t0, zero, 0
	sb t0, 227(s1)
	lbu t0, 0(s4)
	sb t0, 228(s1)
	lbu t0, 1(s4)
	sb t0, 229(s1)
	lbu t0, 2(s4)
	sb t0, 230(s1)
	lbu t0, 3(s4)
	sb t0, 231(s1)
	lbu t0, 4(s4)
	sb t0, 232(s1)
	lbu t0, 5(s4)
	sb t0, 233(s1)
	lbu t0, 6(s4)
	sb t0, 234(s1)
	lbu t0, 7(s4)
	sb t0, 235(s1)
	lbu t0, 8(s4)
	sb t0, 236(s1)
	lbu t0, 9(s4)
	sb t0, 237(s1)
	lbu t0, 10(s4)
	sb t0, 238(s1)
	lbu t0, 11(s4)
	sb t0, 239(s1)
	lbu t0, 12(s4)
	sb t0, 240(s1)
	lbu t0, 13(s4)
	sb t0, 241(s1)
	lbu t0, 14(s4)
	sb t0, 242(s1)
	lbu t0, 15(s4)
	sb t0, 243(s1)
	lbu t0, 16(s4)
	sb t0, 244(s1)
	lbu t0, 17(s4)
	sb t0, 245(s1)
	lbu t0, 18(s4)
	sb t0, 246(s1)
	lbu t0, 19(s4)
	sb t0, 247(s1)
	lbu t0, 20(s4)
	sb t0, 248(s1)
	lbu t0, 21(s4)
	sb t0, 249(s1)
	lbu t0, 22(s4)
	sb t0, 250(s1)
	lbu t0, 23(s4)
	sb t0, 251(s1)
	lbu t0, 24(s4)
	sb t0, 252(s1)
	lbu t0, 25(s4)
	sb t0, 253(s1)
	lbu t0, 26(s4)
	sb t0, 254(s1)
	lbu t0, 27(s4)
	sb t0, 255(s1)
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
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 221
	addi a2, s1, 192
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 285
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
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 221
	addi a2, s1, 192
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 285
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
	addi s5, zero, 128
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
	sb t0, 256(s1)
	lbu t0, 129(s1)
	sb t0, 257(s1)
	lbu t0, 130(s1)
	sb t0, 258(s1)
	lbu t0, 131(s1)
	sb t0, 259(s1)
	lbu t0, 132(s1)
	sb t0, 260(s1)
	lbu t0, 133(s1)
	sb t0, 261(s1)
	lbu t0, 134(s1)
	sb t0, 262(s1)
	lbu t0, 135(s1)
	sb t0, 263(s1)
	lbu t0, 136(s1)
	sb t0, 264(s1)
	lbu t0, 137(s1)
	sb t0, 265(s1)
	lbu t0, 138(s1)
	sb t0, 266(s1)
	lbu t0, 139(s1)
	sb t0, 267(s1)
	lbu t0, 140(s1)
	sb t0, 268(s1)
	lbu t0, 141(s1)
	sb t0, 269(s1)
	lbu t0, 142(s1)
	sb t0, 270(s1)
	lbu t0, 143(s1)
	sb t0, 271(s1)
	lbu t0, 144(s1)
	sb t0, 272(s1)
	lbu t0, 145(s1)
	sb t0, 273(s1)
	lbu t0, 146(s1)
	sb t0, 274(s1)
	lbu t0, 147(s1)
	sb t0, 275(s1)
	lbu t0, 148(s1)
	sb t0, 276(s1)
	lbu t0, 149(s1)
	sb t0, 277(s1)
	lbu t0, 150(s1)
	sb t0, 278(s1)
	lbu t0, 151(s1)
	sb t0, 279(s1)
	lbu t0, 152(s1)
	sb t0, 280(s1)
	lbu t0, 153(s1)
	sb t0, 281(s1)
	lbu t0, 154(s1)
	sb t0, 282(s1)
	lbu t0, 155(s1)
	sb t0, 283(s1)
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
	sb t0, 284(s1)
	lbu t0, 129(s1)
	sb t0, 285(s1)
	lbu t0, 130(s1)
	sb t0, 286(s1)
	lbu t0, 131(s1)
	sb t0, 287(s1)
	lbu t0, 132(s1)
	sb t0, 288(s1)
	lbu t0, 133(s1)
	sb t0, 289(s1)
	lbu t0, 134(s1)
	sb t0, 290(s1)
	lbu t0, 135(s1)
	sb t0, 291(s1)
	lbu t0, 136(s1)
	sb t0, 292(s1)
	lbu t0, 137(s1)
	sb t0, 293(s1)
	lbu t0, 138(s1)
	sb t0, 294(s1)
	lbu t0, 139(s1)
	sb t0, 295(s1)
	lbu t0, 140(s1)
	sb t0, 296(s1)
	lbu t0, 141(s1)
	sb t0, 297(s1)
	lbu t0, 142(s1)
	sb t0, 298(s1)
	lbu t0, 143(s1)
	sb t0, 299(s1)
	lbu t0, 144(s1)
	sb t0, 300(s1)
	lbu t0, 145(s1)
	sb t0, 301(s1)
	lbu t0, 146(s1)
	sb t0, 302(s1)
	lbu t0, 147(s1)
	sb t0, 303(s1)
	lbu t0, 148(s1)
	sb t0, 304(s1)
	lbu t0, 149(s1)
	sb t0, 305(s1)
	lbu t0, 150(s1)
	sb t0, 306(s1)
	lbu t0, 151(s1)
	sb t0, 307(s1)
	lbu t0, 152(s1)
	sb t0, 308(s1)
	lbu t0, 153(s1)
	sb t0, 309(s1)
	lbu t0, 154(s1)
	sb t0, 310(s1)
	lbu t0, 155(s1)
	sb t0, 311(s1)
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
	sb t0, 312(s1)
	lbu t0, 129(s1)
	sb t0, 313(s1)
	lbu t0, 130(s1)
	sb t0, 314(s1)
	lbu t0, 131(s1)
	sb t0, 315(s1)
	lbu t0, 132(s1)
	sb t0, 316(s1)
	lbu t0, 133(s1)
	sb t0, 317(s1)
	lbu t0, 134(s1)
	sb t0, 318(s1)
	lbu t0, 135(s1)
	sb t0, 319(s1)
	addi a0, s2, 0
	addi a1, s3, 0
	addi a2, s1, 192
	addi a3, s1, 256
	addi a4, s0, 0
	call {vg_ecdsa_brainpoolp512r1_sign_k}
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
	sd t0, 256(s1)
	sd t0, 264(s1)
	sd t0, 272(s1)
	sd t0, 280(s1)
	sd t0, 288(s1)
	sd t0, 296(s1)
	sd t0, 304(s1)
	sd t0, 312(s1)
	ld ra, 0(s1)
	ld s0, 8(s1)
	ld s2, 24(s1)
	ld s3, 32(s1)
	ld s4, 40(s1)
	ld s5, 48(s1)
	ld s6, 56(s1)
	ld s1, 16(s1)
	addi sp, sp, 320
213:
	j 211f
210:
	addi sp, sp, -272
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
	sd t0, 56(s0)
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
	sd t0, 48(s0)
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
	sd t0, 40(s0)
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
	sd t0, 32(s0)
	lbu t0, 32(s4)
	slli t0, t0, 8
	lbu t1, 33(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 34(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 35(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 36(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 37(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 38(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 39(s4)
	or t0, t0, t1
	sd t0, 24(s0)
	lbu t0, 40(s4)
	slli t0, t0, 8
	lbu t1, 41(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 42(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 43(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 44(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 45(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 46(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 47(s4)
	or t0, t0, t1
	sd t0, 16(s0)
	lbu t0, 48(s4)
	slli t0, t0, 8
	lbu t1, 49(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 50(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 51(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 52(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 53(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 54(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 55(s4)
	or t0, t0, t1
	sd t0, 8(s0)
	lbu t0, 56(s4)
	slli t0, t0, 8
	lbu t1, 57(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 58(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 59(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 60(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 61(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 62(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 63(s4)
	or t0, t0, t1
	sd t0, 0(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 64(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 72(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 80(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 88(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 96(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 104(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 112(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 120(s0)
	addi a0, s0, 0
	addi a1, zero, 128
	addi a2, zero, 0
	addi a3, zero, 64
	call {vg_brainpoolp512r1_add_mod_n}
	addi a7, zero, -1
	ld t0, 184(s0)
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
	ld t0, 176(s0)
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
	ld t0, 168(s0)
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
	ld t0, 160(s0)
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
	ld t0, 152(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 240(s1)
	srli t1, t0, 48
	sb t1, 241(s1)
	srli t1, t0, 40
	sb t1, 242(s1)
	srli t1, t0, 32
	sb t1, 243(s1)
	srli t1, t0, 24
	sb t1, 244(s1)
	srli t1, t0, 16
	sb t1, 245(s1)
	srli t1, t0, 8
	sb t1, 246(s1)
	srli t1, t0, 0
	sb t1, 247(s1)
	ld t0, 144(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 248(s1)
	srli t1, t0, 48
	sb t1, 249(s1)
	srli t1, t0, 40
	sb t1, 250(s1)
	srli t1, t0, 32
	sb t1, 251(s1)
	srli t1, t0, 24
	sb t1, 252(s1)
	srli t1, t0, 16
	sb t1, 253(s1)
	srli t1, t0, 8
	sb t1, 254(s1)
	srli t1, t0, 0
	sb t1, 255(s1)
	ld t0, 136(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 256(s1)
	srli t1, t0, 48
	sb t1, 257(s1)
	srli t1, t0, 40
	sb t1, 258(s1)
	srli t1, t0, 32
	sb t1, 259(s1)
	srli t1, t0, 24
	sb t1, 260(s1)
	srli t1, t0, 16
	sb t1, 261(s1)
	srli t1, t0, 8
	sb t1, 262(s1)
	srli t1, t0, 0
	sb t1, 263(s1)
	ld t0, 128(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 264(s1)
	srli t1, t0, 48
	sb t1, 265(s1)
	srli t1, t0, 40
	sb t1, 266(s1)
	srli t1, t0, 32
	sb t1, 267(s1)
	srli t1, t0, 24
	sb t1, 268(s1)
	srli t1, t0, 16
	sb t1, 269(s1)
	srli t1, t0, 8
	sb t1, 270(s1)
	srli t1, t0, 0
	sb t1, 271(s1)
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
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 257
	addi a2, s1, 208
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 321
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
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 257
	addi a2, s1, 208
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 321
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
	addi s5, zero, 128
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
	call {vg_ecdsa_brainpoolp512r1_sign_k}
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
	sd t0, 240(s1)
	sd t0, 248(s1)
	sd t0, 256(s1)
	sd t0, 264(s1)
	ld ra, 0(s1)
	ld s0, 8(s1)
	ld s2, 24(s1)
	ld s3, 32(s1)
	ld s4, 40(s1)
	ld s5, 48(s1)
	ld s6, 56(s1)
	ld s1, 16(s1)
	addi sp, sp, 272
211:
	j 29f
28:
	addi sp, sp, -320
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
	lbu t0, 16(s4)
	sb t0, 224(s1)
	lbu t0, 17(s4)
	sb t0, 225(s1)
	lbu t0, 18(s4)
	sb t0, 226(s1)
	lbu t0, 19(s4)
	sb t0, 227(s1)
	lbu t0, 20(s4)
	sb t0, 228(s1)
	lbu t0, 21(s4)
	sb t0, 229(s1)
	lbu t0, 22(s4)
	sb t0, 230(s1)
	lbu t0, 23(s4)
	sb t0, 231(s1)
	lbu t0, 24(s4)
	sb t0, 232(s1)
	lbu t0, 25(s4)
	sb t0, 233(s1)
	lbu t0, 26(s4)
	sb t0, 234(s1)
	lbu t0, 27(s4)
	sb t0, 235(s1)
	lbu t0, 28(s4)
	sb t0, 236(s1)
	lbu t0, 29(s4)
	sb t0, 237(s1)
	lbu t0, 30(s4)
	sb t0, 238(s1)
	lbu t0, 31(s4)
	sb t0, 239(s1)
	lbu t0, 32(s4)
	sb t0, 240(s1)
	lbu t0, 33(s4)
	sb t0, 241(s1)
	lbu t0, 34(s4)
	sb t0, 242(s1)
	lbu t0, 35(s4)
	sb t0, 243(s1)
	lbu t0, 36(s4)
	sb t0, 244(s1)
	lbu t0, 37(s4)
	sb t0, 245(s1)
	lbu t0, 38(s4)
	sb t0, 246(s1)
	lbu t0, 39(s4)
	sb t0, 247(s1)
	lbu t0, 40(s4)
	sb t0, 248(s1)
	lbu t0, 41(s4)
	sb t0, 249(s1)
	lbu t0, 42(s4)
	sb t0, 250(s1)
	lbu t0, 43(s4)
	sb t0, 251(s1)
	lbu t0, 44(s4)
	sb t0, 252(s1)
	lbu t0, 45(s4)
	sb t0, 253(s1)
	lbu t0, 46(s4)
	sb t0, 254(s1)
	lbu t0, 47(s4)
	sb t0, 255(s1)
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
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 241
	addi a2, s1, 192
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 305
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
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 241
	addi a2, s1, 192
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 305
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
	addi s5, zero, 128
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
	lbu t0, 128(s1)
	sb t0, 256(s1)
	lbu t0, 129(s1)
	sb t0, 257(s1)
	lbu t0, 130(s1)
	sb t0, 258(s1)
	lbu t0, 131(s1)
	sb t0, 259(s1)
	lbu t0, 132(s1)
	sb t0, 260(s1)
	lbu t0, 133(s1)
	sb t0, 261(s1)
	lbu t0, 134(s1)
	sb t0, 262(s1)
	lbu t0, 135(s1)
	sb t0, 263(s1)
	lbu t0, 136(s1)
	sb t0, 264(s1)
	lbu t0, 137(s1)
	sb t0, 265(s1)
	lbu t0, 138(s1)
	sb t0, 266(s1)
	lbu t0, 139(s1)
	sb t0, 267(s1)
	lbu t0, 140(s1)
	sb t0, 268(s1)
	lbu t0, 141(s1)
	sb t0, 269(s1)
	lbu t0, 142(s1)
	sb t0, 270(s1)
	lbu t0, 143(s1)
	sb t0, 271(s1)
	lbu t0, 144(s1)
	sb t0, 272(s1)
	lbu t0, 145(s1)
	sb t0, 273(s1)
	lbu t0, 146(s1)
	sb t0, 274(s1)
	lbu t0, 147(s1)
	sb t0, 275(s1)
	lbu t0, 148(s1)
	sb t0, 276(s1)
	lbu t0, 149(s1)
	sb t0, 277(s1)
	lbu t0, 150(s1)
	sb t0, 278(s1)
	lbu t0, 151(s1)
	sb t0, 279(s1)
	lbu t0, 152(s1)
	sb t0, 280(s1)
	lbu t0, 153(s1)
	sb t0, 281(s1)
	lbu t0, 154(s1)
	sb t0, 282(s1)
	lbu t0, 155(s1)
	sb t0, 283(s1)
	lbu t0, 156(s1)
	sb t0, 284(s1)
	lbu t0, 157(s1)
	sb t0, 285(s1)
	lbu t0, 158(s1)
	sb t0, 286(s1)
	lbu t0, 159(s1)
	sb t0, 287(s1)
	lbu t0, 160(s1)
	sb t0, 288(s1)
	lbu t0, 161(s1)
	sb t0, 289(s1)
	lbu t0, 162(s1)
	sb t0, 290(s1)
	lbu t0, 163(s1)
	sb t0, 291(s1)
	lbu t0, 164(s1)
	sb t0, 292(s1)
	lbu t0, 165(s1)
	sb t0, 293(s1)
	lbu t0, 166(s1)
	sb t0, 294(s1)
	lbu t0, 167(s1)
	sb t0, 295(s1)
	lbu t0, 168(s1)
	sb t0, 296(s1)
	lbu t0, 169(s1)
	sb t0, 297(s1)
	lbu t0, 170(s1)
	sb t0, 298(s1)
	lbu t0, 171(s1)
	sb t0, 299(s1)
	lbu t0, 172(s1)
	sb t0, 300(s1)
	lbu t0, 173(s1)
	sb t0, 301(s1)
	lbu t0, 174(s1)
	sb t0, 302(s1)
	lbu t0, 175(s1)
	sb t0, 303(s1)
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
	lbu t0, 128(s1)
	sb t0, 304(s1)
	lbu t0, 129(s1)
	sb t0, 305(s1)
	lbu t0, 130(s1)
	sb t0, 306(s1)
	lbu t0, 131(s1)
	sb t0, 307(s1)
	lbu t0, 132(s1)
	sb t0, 308(s1)
	lbu t0, 133(s1)
	sb t0, 309(s1)
	lbu t0, 134(s1)
	sb t0, 310(s1)
	lbu t0, 135(s1)
	sb t0, 311(s1)
	lbu t0, 136(s1)
	sb t0, 312(s1)
	lbu t0, 137(s1)
	sb t0, 313(s1)
	lbu t0, 138(s1)
	sb t0, 314(s1)
	lbu t0, 139(s1)
	sb t0, 315(s1)
	lbu t0, 140(s1)
	sb t0, 316(s1)
	lbu t0, 141(s1)
	sb t0, 317(s1)
	lbu t0, 142(s1)
	sb t0, 318(s1)
	lbu t0, 143(s1)
	sb t0, 319(s1)
	addi a0, s2, 0
	addi a1, s3, 0
	addi a2, s1, 192
	addi a3, s1, 256
	addi a4, s0, 0
	call {vg_ecdsa_brainpoolp512r1_sign_k}
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
	ld ra, 0(s1)
	ld s0, 8(s1)
	ld s2, 24(s1)
	ld s3, 32(s1)
	ld s4, 40(s1)
	ld s5, 48(s1)
	ld s6, 56(s1)
	ld s1, 16(s1)
	addi sp, sp, 320
29:
	j 27f
26:
	addi sp, sp, -320
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
	addi t0, zero, 0
	sb t0, 208(s1)
	addi t0, zero, 0
	sb t0, 209(s1)
	addi t0, zero, 0
	sb t0, 210(s1)
	addi t0, zero, 0
	sb t0, 211(s1)
	addi t0, zero, 0
	sb t0, 212(s1)
	addi t0, zero, 0
	sb t0, 213(s1)
	addi t0, zero, 0
	sb t0, 214(s1)
	addi t0, zero, 0
	sb t0, 215(s1)
	addi t0, zero, 0
	sb t0, 216(s1)
	addi t0, zero, 0
	sb t0, 217(s1)
	addi t0, zero, 0
	sb t0, 218(s1)
	addi t0, zero, 0
	sb t0, 219(s1)
	addi t0, zero, 0
	sb t0, 220(s1)
	addi t0, zero, 0
	sb t0, 221(s1)
	addi t0, zero, 0
	sb t0, 222(s1)
	addi t0, zero, 0
	sb t0, 223(s1)
	lbu t0, 0(s4)
	sb t0, 224(s1)
	lbu t0, 1(s4)
	sb t0, 225(s1)
	lbu t0, 2(s4)
	sb t0, 226(s1)
	lbu t0, 3(s4)
	sb t0, 227(s1)
	lbu t0, 4(s4)
	sb t0, 228(s1)
	lbu t0, 5(s4)
	sb t0, 229(s1)
	lbu t0, 6(s4)
	sb t0, 230(s1)
	lbu t0, 7(s4)
	sb t0, 231(s1)
	lbu t0, 8(s4)
	sb t0, 232(s1)
	lbu t0, 9(s4)
	sb t0, 233(s1)
	lbu t0, 10(s4)
	sb t0, 234(s1)
	lbu t0, 11(s4)
	sb t0, 235(s1)
	lbu t0, 12(s4)
	sb t0, 236(s1)
	lbu t0, 13(s4)
	sb t0, 237(s1)
	lbu t0, 14(s4)
	sb t0, 238(s1)
	lbu t0, 15(s4)
	sb t0, 239(s1)
	lbu t0, 16(s4)
	sb t0, 240(s1)
	lbu t0, 17(s4)
	sb t0, 241(s1)
	lbu t0, 18(s4)
	sb t0, 242(s1)
	lbu t0, 19(s4)
	sb t0, 243(s1)
	lbu t0, 20(s4)
	sb t0, 244(s1)
	lbu t0, 21(s4)
	sb t0, 245(s1)
	lbu t0, 22(s4)
	sb t0, 246(s1)
	lbu t0, 23(s4)
	sb t0, 247(s1)
	lbu t0, 24(s4)
	sb t0, 248(s1)
	lbu t0, 25(s4)
	sb t0, 249(s1)
	lbu t0, 26(s4)
	sb t0, 250(s1)
	lbu t0, 27(s4)
	sb t0, 251(s1)
	lbu t0, 28(s4)
	sb t0, 252(s1)
	lbu t0, 29(s4)
	sb t0, 253(s1)
	lbu t0, 30(s4)
	sb t0, 254(s1)
	lbu t0, 31(s4)
	sb t0, 255(s1)
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
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 161
	addi a2, s1, 192
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 225
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
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 161
	addi a2, s1, 192
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 225
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
	addi s5, zero, 128
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
	lbu t0, 128(s1)
	sb t0, 256(s1)
	lbu t0, 129(s1)
	sb t0, 257(s1)
	lbu t0, 130(s1)
	sb t0, 258(s1)
	lbu t0, 131(s1)
	sb t0, 259(s1)
	lbu t0, 132(s1)
	sb t0, 260(s1)
	lbu t0, 133(s1)
	sb t0, 261(s1)
	lbu t0, 134(s1)
	sb t0, 262(s1)
	lbu t0, 135(s1)
	sb t0, 263(s1)
	lbu t0, 136(s1)
	sb t0, 264(s1)
	lbu t0, 137(s1)
	sb t0, 265(s1)
	lbu t0, 138(s1)
	sb t0, 266(s1)
	lbu t0, 139(s1)
	sb t0, 267(s1)
	lbu t0, 140(s1)
	sb t0, 268(s1)
	lbu t0, 141(s1)
	sb t0, 269(s1)
	lbu t0, 142(s1)
	sb t0, 270(s1)
	lbu t0, 143(s1)
	sb t0, 271(s1)
	lbu t0, 144(s1)
	sb t0, 272(s1)
	lbu t0, 145(s1)
	sb t0, 273(s1)
	lbu t0, 146(s1)
	sb t0, 274(s1)
	lbu t0, 147(s1)
	sb t0, 275(s1)
	lbu t0, 148(s1)
	sb t0, 276(s1)
	lbu t0, 149(s1)
	sb t0, 277(s1)
	lbu t0, 150(s1)
	sb t0, 278(s1)
	lbu t0, 151(s1)
	sb t0, 279(s1)
	lbu t0, 152(s1)
	sb t0, 280(s1)
	lbu t0, 153(s1)
	sb t0, 281(s1)
	lbu t0, 154(s1)
	sb t0, 282(s1)
	lbu t0, 155(s1)
	sb t0, 283(s1)
	lbu t0, 156(s1)
	sb t0, 284(s1)
	lbu t0, 157(s1)
	sb t0, 285(s1)
	lbu t0, 158(s1)
	sb t0, 286(s1)
	lbu t0, 159(s1)
	sb t0, 287(s1)
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
	lbu t0, 128(s1)
	sb t0, 288(s1)
	lbu t0, 129(s1)
	sb t0, 289(s1)
	lbu t0, 130(s1)
	sb t0, 290(s1)
	lbu t0, 131(s1)
	sb t0, 291(s1)
	lbu t0, 132(s1)
	sb t0, 292(s1)
	lbu t0, 133(s1)
	sb t0, 293(s1)
	lbu t0, 134(s1)
	sb t0, 294(s1)
	lbu t0, 135(s1)
	sb t0, 295(s1)
	lbu t0, 136(s1)
	sb t0, 296(s1)
	lbu t0, 137(s1)
	sb t0, 297(s1)
	lbu t0, 138(s1)
	sb t0, 298(s1)
	lbu t0, 139(s1)
	sb t0, 299(s1)
	lbu t0, 140(s1)
	sb t0, 300(s1)
	lbu t0, 141(s1)
	sb t0, 301(s1)
	lbu t0, 142(s1)
	sb t0, 302(s1)
	lbu t0, 143(s1)
	sb t0, 303(s1)
	lbu t0, 144(s1)
	sb t0, 304(s1)
	lbu t0, 145(s1)
	sb t0, 305(s1)
	lbu t0, 146(s1)
	sb t0, 306(s1)
	lbu t0, 147(s1)
	sb t0, 307(s1)
	lbu t0, 148(s1)
	sb t0, 308(s1)
	lbu t0, 149(s1)
	sb t0, 309(s1)
	lbu t0, 150(s1)
	sb t0, 310(s1)
	lbu t0, 151(s1)
	sb t0, 311(s1)
	lbu t0, 152(s1)
	sb t0, 312(s1)
	lbu t0, 153(s1)
	sb t0, 313(s1)
	lbu t0, 154(s1)
	sb t0, 314(s1)
	lbu t0, 155(s1)
	sb t0, 315(s1)
	lbu t0, 156(s1)
	sb t0, 316(s1)
	lbu t0, 157(s1)
	sb t0, 317(s1)
	lbu t0, 158(s1)
	sb t0, 318(s1)
	lbu t0, 159(s1)
	sb t0, 319(s1)
	addi a0, s2, 0
	addi a1, s3, 0
	addi a2, s1, 192
	addi a3, s1, 256
	addi a4, s0, 0
	call {vg_ecdsa_brainpoolp512r1_sign_k}
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
	ld ra, 0(s1)
	ld s0, 8(s1)
	ld s2, 24(s1)
	ld s3, 32(s1)
	ld s4, 40(s1)
	ld s5, 48(s1)
	ld s6, 56(s1)
	ld s1, 16(s1)
	addi sp, sp, 320
27:
	j 25f
24:
	addi sp, sp, -320
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
	addi t0, zero, 0
	sb t0, 208(s1)
	addi t0, zero, 0
	sb t0, 209(s1)
	addi t0, zero, 0
	sb t0, 210(s1)
	addi t0, zero, 0
	sb t0, 211(s1)
	addi t0, zero, 0
	sb t0, 212(s1)
	addi t0, zero, 0
	sb t0, 213(s1)
	addi t0, zero, 0
	sb t0, 214(s1)
	addi t0, zero, 0
	sb t0, 215(s1)
	addi t0, zero, 0
	sb t0, 216(s1)
	addi t0, zero, 0
	sb t0, 217(s1)
	addi t0, zero, 0
	sb t0, 218(s1)
	addi t0, zero, 0
	sb t0, 219(s1)
	addi t0, zero, 0
	sb t0, 220(s1)
	addi t0, zero, 0
	sb t0, 221(s1)
	addi t0, zero, 0
	sb t0, 222(s1)
	addi t0, zero, 0
	sb t0, 223(s1)
	addi t0, zero, 0
	sb t0, 224(s1)
	addi t0, zero, 0
	sb t0, 225(s1)
	addi t0, zero, 0
	sb t0, 226(s1)
	addi t0, zero, 0
	sb t0, 227(s1)
	lbu t0, 0(s4)
	sb t0, 228(s1)
	lbu t0, 1(s4)
	sb t0, 229(s1)
	lbu t0, 2(s4)
	sb t0, 230(s1)
	lbu t0, 3(s4)
	sb t0, 231(s1)
	lbu t0, 4(s4)
	sb t0, 232(s1)
	lbu t0, 5(s4)
	sb t0, 233(s1)
	lbu t0, 6(s4)
	sb t0, 234(s1)
	lbu t0, 7(s4)
	sb t0, 235(s1)
	lbu t0, 8(s4)
	sb t0, 236(s1)
	lbu t0, 9(s4)
	sb t0, 237(s1)
	lbu t0, 10(s4)
	sb t0, 238(s1)
	lbu t0, 11(s4)
	sb t0, 239(s1)
	lbu t0, 12(s4)
	sb t0, 240(s1)
	lbu t0, 13(s4)
	sb t0, 241(s1)
	lbu t0, 14(s4)
	sb t0, 242(s1)
	lbu t0, 15(s4)
	sb t0, 243(s1)
	lbu t0, 16(s4)
	sb t0, 244(s1)
	lbu t0, 17(s4)
	sb t0, 245(s1)
	lbu t0, 18(s4)
	sb t0, 246(s1)
	lbu t0, 19(s4)
	sb t0, 247(s1)
	lbu t0, 20(s4)
	sb t0, 248(s1)
	lbu t0, 21(s4)
	sb t0, 249(s1)
	lbu t0, 22(s4)
	sb t0, 250(s1)
	lbu t0, 23(s4)
	sb t0, 251(s1)
	lbu t0, 24(s4)
	sb t0, 252(s1)
	lbu t0, 25(s4)
	sb t0, 253(s1)
	lbu t0, 26(s4)
	sb t0, 254(s1)
	lbu t0, 27(s4)
	sb t0, 255(s1)
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
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 157
	addi a2, s1, 192
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 221
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
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 157
	addi a2, s1, 192
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 221
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
	addi s5, zero, 128
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
	sb t0, 256(s1)
	lbu t0, 129(s1)
	sb t0, 257(s1)
	lbu t0, 130(s1)
	sb t0, 258(s1)
	lbu t0, 131(s1)
	sb t0, 259(s1)
	lbu t0, 132(s1)
	sb t0, 260(s1)
	lbu t0, 133(s1)
	sb t0, 261(s1)
	lbu t0, 134(s1)
	sb t0, 262(s1)
	lbu t0, 135(s1)
	sb t0, 263(s1)
	lbu t0, 136(s1)
	sb t0, 264(s1)
	lbu t0, 137(s1)
	sb t0, 265(s1)
	lbu t0, 138(s1)
	sb t0, 266(s1)
	lbu t0, 139(s1)
	sb t0, 267(s1)
	lbu t0, 140(s1)
	sb t0, 268(s1)
	lbu t0, 141(s1)
	sb t0, 269(s1)
	lbu t0, 142(s1)
	sb t0, 270(s1)
	lbu t0, 143(s1)
	sb t0, 271(s1)
	lbu t0, 144(s1)
	sb t0, 272(s1)
	lbu t0, 145(s1)
	sb t0, 273(s1)
	lbu t0, 146(s1)
	sb t0, 274(s1)
	lbu t0, 147(s1)
	sb t0, 275(s1)
	lbu t0, 148(s1)
	sb t0, 276(s1)
	lbu t0, 149(s1)
	sb t0, 277(s1)
	lbu t0, 150(s1)
	sb t0, 278(s1)
	lbu t0, 151(s1)
	sb t0, 279(s1)
	lbu t0, 152(s1)
	sb t0, 280(s1)
	lbu t0, 153(s1)
	sb t0, 281(s1)
	lbu t0, 154(s1)
	sb t0, 282(s1)
	lbu t0, 155(s1)
	sb t0, 283(s1)
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
	sb t0, 284(s1)
	lbu t0, 129(s1)
	sb t0, 285(s1)
	lbu t0, 130(s1)
	sb t0, 286(s1)
	lbu t0, 131(s1)
	sb t0, 287(s1)
	lbu t0, 132(s1)
	sb t0, 288(s1)
	lbu t0, 133(s1)
	sb t0, 289(s1)
	lbu t0, 134(s1)
	sb t0, 290(s1)
	lbu t0, 135(s1)
	sb t0, 291(s1)
	lbu t0, 136(s1)
	sb t0, 292(s1)
	lbu t0, 137(s1)
	sb t0, 293(s1)
	lbu t0, 138(s1)
	sb t0, 294(s1)
	lbu t0, 139(s1)
	sb t0, 295(s1)
	lbu t0, 140(s1)
	sb t0, 296(s1)
	lbu t0, 141(s1)
	sb t0, 297(s1)
	lbu t0, 142(s1)
	sb t0, 298(s1)
	lbu t0, 143(s1)
	sb t0, 299(s1)
	lbu t0, 144(s1)
	sb t0, 300(s1)
	lbu t0, 145(s1)
	sb t0, 301(s1)
	lbu t0, 146(s1)
	sb t0, 302(s1)
	lbu t0, 147(s1)
	sb t0, 303(s1)
	lbu t0, 148(s1)
	sb t0, 304(s1)
	lbu t0, 149(s1)
	sb t0, 305(s1)
	lbu t0, 150(s1)
	sb t0, 306(s1)
	lbu t0, 151(s1)
	sb t0, 307(s1)
	lbu t0, 152(s1)
	sb t0, 308(s1)
	lbu t0, 153(s1)
	sb t0, 309(s1)
	lbu t0, 154(s1)
	sb t0, 310(s1)
	lbu t0, 155(s1)
	sb t0, 311(s1)
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
	sb t0, 312(s1)
	lbu t0, 129(s1)
	sb t0, 313(s1)
	lbu t0, 130(s1)
	sb t0, 314(s1)
	lbu t0, 131(s1)
	sb t0, 315(s1)
	lbu t0, 132(s1)
	sb t0, 316(s1)
	lbu t0, 133(s1)
	sb t0, 317(s1)
	lbu t0, 134(s1)
	sb t0, 318(s1)
	lbu t0, 135(s1)
	sb t0, 319(s1)
	addi a0, s2, 0
	addi a1, s3, 0
	addi a2, s1, 192
	addi a3, s1, 256
	addi a4, s0, 0
	call {vg_ecdsa_brainpoolp512r1_sign_k}
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
	sd t0, 256(s1)
	sd t0, 264(s1)
	sd t0, 272(s1)
	sd t0, 280(s1)
	sd t0, 288(s1)
	sd t0, 296(s1)
	sd t0, 304(s1)
	sd t0, 312(s1)
	ld ra, 0(s1)
	ld s0, 8(s1)
	ld s2, 24(s1)
	ld s3, 32(s1)
	ld s4, 40(s1)
	ld s5, 48(s1)
	ld s6, 56(s1)
	ld s1, 16(s1)
	addi sp, sp, 320
25:
	j 23f
22:
	addi sp, sp, -320
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
	addi t0, zero, 0
	sb t0, 208(s1)
	addi t0, zero, 0
	sb t0, 209(s1)
	addi t0, zero, 0
	sb t0, 210(s1)
	addi t0, zero, 0
	sb t0, 211(s1)
	addi t0, zero, 0
	sb t0, 212(s1)
	addi t0, zero, 0
	sb t0, 213(s1)
	addi t0, zero, 0
	sb t0, 214(s1)
	addi t0, zero, 0
	sb t0, 215(s1)
	addi t0, zero, 0
	sb t0, 216(s1)
	addi t0, zero, 0
	sb t0, 217(s1)
	addi t0, zero, 0
	sb t0, 218(s1)
	addi t0, zero, 0
	sb t0, 219(s1)
	addi t0, zero, 0
	sb t0, 220(s1)
	addi t0, zero, 0
	sb t0, 221(s1)
	addi t0, zero, 0
	sb t0, 222(s1)
	addi t0, zero, 0
	sb t0, 223(s1)
	addi t0, zero, 0
	sb t0, 224(s1)
	addi t0, zero, 0
	sb t0, 225(s1)
	addi t0, zero, 0
	sb t0, 226(s1)
	addi t0, zero, 0
	sb t0, 227(s1)
	addi t0, zero, 0
	sb t0, 228(s1)
	addi t0, zero, 0
	sb t0, 229(s1)
	addi t0, zero, 0
	sb t0, 230(s1)
	addi t0, zero, 0
	sb t0, 231(s1)
	addi t0, zero, 0
	sb t0, 232(s1)
	addi t0, zero, 0
	sb t0, 233(s1)
	addi t0, zero, 0
	sb t0, 234(s1)
	addi t0, zero, 0
	sb t0, 235(s1)
	lbu t0, 0(s4)
	sb t0, 236(s1)
	lbu t0, 1(s4)
	sb t0, 237(s1)
	lbu t0, 2(s4)
	sb t0, 238(s1)
	lbu t0, 3(s4)
	sb t0, 239(s1)
	lbu t0, 4(s4)
	sb t0, 240(s1)
	lbu t0, 5(s4)
	sb t0, 241(s1)
	lbu t0, 6(s4)
	sb t0, 242(s1)
	lbu t0, 7(s4)
	sb t0, 243(s1)
	lbu t0, 8(s4)
	sb t0, 244(s1)
	lbu t0, 9(s4)
	sb t0, 245(s1)
	lbu t0, 10(s4)
	sb t0, 246(s1)
	lbu t0, 11(s4)
	sb t0, 247(s1)
	lbu t0, 12(s4)
	sb t0, 248(s1)
	lbu t0, 13(s4)
	sb t0, 249(s1)
	lbu t0, 14(s4)
	sb t0, 250(s1)
	lbu t0, 15(s4)
	sb t0, 251(s1)
	lbu t0, 16(s4)
	sb t0, 252(s1)
	lbu t0, 17(s4)
	sb t0, 253(s1)
	lbu t0, 18(s4)
	sb t0, 254(s1)
	lbu t0, 19(s4)
	sb t0, 255(s1)
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
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 149
	addi a2, s1, 192
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 213
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
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 149
	addi a2, s1, 192
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 213
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
	addi s5, zero, 128
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
	sb t0, 256(s1)
	lbu t0, 129(s1)
	sb t0, 257(s1)
	lbu t0, 130(s1)
	sb t0, 258(s1)
	lbu t0, 131(s1)
	sb t0, 259(s1)
	lbu t0, 132(s1)
	sb t0, 260(s1)
	lbu t0, 133(s1)
	sb t0, 261(s1)
	lbu t0, 134(s1)
	sb t0, 262(s1)
	lbu t0, 135(s1)
	sb t0, 263(s1)
	lbu t0, 136(s1)
	sb t0, 264(s1)
	lbu t0, 137(s1)
	sb t0, 265(s1)
	lbu t0, 138(s1)
	sb t0, 266(s1)
	lbu t0, 139(s1)
	sb t0, 267(s1)
	lbu t0, 140(s1)
	sb t0, 268(s1)
	lbu t0, 141(s1)
	sb t0, 269(s1)
	lbu t0, 142(s1)
	sb t0, 270(s1)
	lbu t0, 143(s1)
	sb t0, 271(s1)
	lbu t0, 144(s1)
	sb t0, 272(s1)
	lbu t0, 145(s1)
	sb t0, 273(s1)
	lbu t0, 146(s1)
	sb t0, 274(s1)
	lbu t0, 147(s1)
	sb t0, 275(s1)
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
	sb t0, 276(s1)
	lbu t0, 129(s1)
	sb t0, 277(s1)
	lbu t0, 130(s1)
	sb t0, 278(s1)
	lbu t0, 131(s1)
	sb t0, 279(s1)
	lbu t0, 132(s1)
	sb t0, 280(s1)
	lbu t0, 133(s1)
	sb t0, 281(s1)
	lbu t0, 134(s1)
	sb t0, 282(s1)
	lbu t0, 135(s1)
	sb t0, 283(s1)
	lbu t0, 136(s1)
	sb t0, 284(s1)
	lbu t0, 137(s1)
	sb t0, 285(s1)
	lbu t0, 138(s1)
	sb t0, 286(s1)
	lbu t0, 139(s1)
	sb t0, 287(s1)
	lbu t0, 140(s1)
	sb t0, 288(s1)
	lbu t0, 141(s1)
	sb t0, 289(s1)
	lbu t0, 142(s1)
	sb t0, 290(s1)
	lbu t0, 143(s1)
	sb t0, 291(s1)
	lbu t0, 144(s1)
	sb t0, 292(s1)
	lbu t0, 145(s1)
	sb t0, 293(s1)
	lbu t0, 146(s1)
	sb t0, 294(s1)
	lbu t0, 147(s1)
	sb t0, 295(s1)
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
	sb t0, 296(s1)
	lbu t0, 129(s1)
	sb t0, 297(s1)
	lbu t0, 130(s1)
	sb t0, 298(s1)
	lbu t0, 131(s1)
	sb t0, 299(s1)
	lbu t0, 132(s1)
	sb t0, 300(s1)
	lbu t0, 133(s1)
	sb t0, 301(s1)
	lbu t0, 134(s1)
	sb t0, 302(s1)
	lbu t0, 135(s1)
	sb t0, 303(s1)
	lbu t0, 136(s1)
	sb t0, 304(s1)
	lbu t0, 137(s1)
	sb t0, 305(s1)
	lbu t0, 138(s1)
	sb t0, 306(s1)
	lbu t0, 139(s1)
	sb t0, 307(s1)
	lbu t0, 140(s1)
	sb t0, 308(s1)
	lbu t0, 141(s1)
	sb t0, 309(s1)
	lbu t0, 142(s1)
	sb t0, 310(s1)
	lbu t0, 143(s1)
	sb t0, 311(s1)
	lbu t0, 144(s1)
	sb t0, 312(s1)
	lbu t0, 145(s1)
	sb t0, 313(s1)
	lbu t0, 146(s1)
	sb t0, 314(s1)
	lbu t0, 147(s1)
	sb t0, 315(s1)
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
	sb t0, 316(s1)
	lbu t0, 129(s1)
	sb t0, 317(s1)
	lbu t0, 130(s1)
	sb t0, 318(s1)
	lbu t0, 131(s1)
	sb t0, 319(s1)
	addi a0, s2, 0
	addi a1, s3, 0
	addi a2, s1, 192
	addi a3, s1, 256
	addi a4, s0, 0
	call {vg_ecdsa_brainpoolp512r1_sign_k}
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
	sd t0, 256(s1)
	sd t0, 264(s1)
	sd t0, 272(s1)
	sd t0, 280(s1)
	sd t0, 288(s1)
	sd t0, 296(s1)
	sd t0, 304(s1)
	sd t0, 312(s1)
	ld ra, 0(s1)
	ld s0, 8(s1)
	ld s2, 24(s1)
	ld s3, 32(s1)
	ld s4, 40(s1)
	ld s5, 48(s1)
	ld s6, 56(s1)
	ld s1, 16(s1)
	addi sp, sp, 320
23:
	j 21f
20:
	addi sp, sp, -320
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
	addi t0, zero, 0
	sb t0, 208(s1)
	addi t0, zero, 0
	sb t0, 209(s1)
	addi t0, zero, 0
	sb t0, 210(s1)
	addi t0, zero, 0
	sb t0, 211(s1)
	addi t0, zero, 0
	sb t0, 212(s1)
	addi t0, zero, 0
	sb t0, 213(s1)
	addi t0, zero, 0
	sb t0, 214(s1)
	addi t0, zero, 0
	sb t0, 215(s1)
	addi t0, zero, 0
	sb t0, 216(s1)
	addi t0, zero, 0
	sb t0, 217(s1)
	addi t0, zero, 0
	sb t0, 218(s1)
	addi t0, zero, 0
	sb t0, 219(s1)
	addi t0, zero, 0
	sb t0, 220(s1)
	addi t0, zero, 0
	sb t0, 221(s1)
	addi t0, zero, 0
	sb t0, 222(s1)
	addi t0, zero, 0
	sb t0, 223(s1)
	addi t0, zero, 0
	sb t0, 224(s1)
	addi t0, zero, 0
	sb t0, 225(s1)
	addi t0, zero, 0
	sb t0, 226(s1)
	addi t0, zero, 0
	sb t0, 227(s1)
	addi t0, zero, 0
	sb t0, 228(s1)
	addi t0, zero, 0
	sb t0, 229(s1)
	addi t0, zero, 0
	sb t0, 230(s1)
	addi t0, zero, 0
	sb t0, 231(s1)
	addi t0, zero, 0
	sb t0, 232(s1)
	addi t0, zero, 0
	sb t0, 233(s1)
	addi t0, zero, 0
	sb t0, 234(s1)
	addi t0, zero, 0
	sb t0, 235(s1)
	addi t0, zero, 0
	sb t0, 236(s1)
	addi t0, zero, 0
	sb t0, 237(s1)
	addi t0, zero, 0
	sb t0, 238(s1)
	addi t0, zero, 0
	sb t0, 239(s1)
	lbu t0, 0(s4)
	sb t0, 240(s1)
	lbu t0, 1(s4)
	sb t0, 241(s1)
	lbu t0, 2(s4)
	sb t0, 242(s1)
	lbu t0, 3(s4)
	sb t0, 243(s1)
	lbu t0, 4(s4)
	sb t0, 244(s1)
	lbu t0, 5(s4)
	sb t0, 245(s1)
	lbu t0, 6(s4)
	sb t0, 246(s1)
	lbu t0, 7(s4)
	sb t0, 247(s1)
	lbu t0, 8(s4)
	sb t0, 248(s1)
	lbu t0, 9(s4)
	sb t0, 249(s1)
	lbu t0, 10(s4)
	sb t0, 250(s1)
	lbu t0, 11(s4)
	sb t0, 251(s1)
	lbu t0, 12(s4)
	sb t0, 252(s1)
	lbu t0, 13(s4)
	sb t0, 253(s1)
	lbu t0, 14(s4)
	sb t0, 254(s1)
	lbu t0, 15(s4)
	sb t0, 255(s1)
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
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 145
	addi a2, s1, 192
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 209
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
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 145
	addi a2, s1, 192
	addi a3, zero, 64
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 209
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
	addi s5, zero, 128
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
	sb t0, 256(s1)
	lbu t0, 129(s1)
	sb t0, 257(s1)
	lbu t0, 130(s1)
	sb t0, 258(s1)
	lbu t0, 131(s1)
	sb t0, 259(s1)
	lbu t0, 132(s1)
	sb t0, 260(s1)
	lbu t0, 133(s1)
	sb t0, 261(s1)
	lbu t0, 134(s1)
	sb t0, 262(s1)
	lbu t0, 135(s1)
	sb t0, 263(s1)
	lbu t0, 136(s1)
	sb t0, 264(s1)
	lbu t0, 137(s1)
	sb t0, 265(s1)
	lbu t0, 138(s1)
	sb t0, 266(s1)
	lbu t0, 139(s1)
	sb t0, 267(s1)
	lbu t0, 140(s1)
	sb t0, 268(s1)
	lbu t0, 141(s1)
	sb t0, 269(s1)
	lbu t0, 142(s1)
	sb t0, 270(s1)
	lbu t0, 143(s1)
	sb t0, 271(s1)
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
	sb t0, 272(s1)
	lbu t0, 129(s1)
	sb t0, 273(s1)
	lbu t0, 130(s1)
	sb t0, 274(s1)
	lbu t0, 131(s1)
	sb t0, 275(s1)
	lbu t0, 132(s1)
	sb t0, 276(s1)
	lbu t0, 133(s1)
	sb t0, 277(s1)
	lbu t0, 134(s1)
	sb t0, 278(s1)
	lbu t0, 135(s1)
	sb t0, 279(s1)
	lbu t0, 136(s1)
	sb t0, 280(s1)
	lbu t0, 137(s1)
	sb t0, 281(s1)
	lbu t0, 138(s1)
	sb t0, 282(s1)
	lbu t0, 139(s1)
	sb t0, 283(s1)
	lbu t0, 140(s1)
	sb t0, 284(s1)
	lbu t0, 141(s1)
	sb t0, 285(s1)
	lbu t0, 142(s1)
	sb t0, 286(s1)
	lbu t0, 143(s1)
	sb t0, 287(s1)
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
	sb t0, 288(s1)
	lbu t0, 129(s1)
	sb t0, 289(s1)
	lbu t0, 130(s1)
	sb t0, 290(s1)
	lbu t0, 131(s1)
	sb t0, 291(s1)
	lbu t0, 132(s1)
	sb t0, 292(s1)
	lbu t0, 133(s1)
	sb t0, 293(s1)
	lbu t0, 134(s1)
	sb t0, 294(s1)
	lbu t0, 135(s1)
	sb t0, 295(s1)
	lbu t0, 136(s1)
	sb t0, 296(s1)
	lbu t0, 137(s1)
	sb t0, 297(s1)
	lbu t0, 138(s1)
	sb t0, 298(s1)
	lbu t0, 139(s1)
	sb t0, 299(s1)
	lbu t0, 140(s1)
	sb t0, 300(s1)
	lbu t0, 141(s1)
	sb t0, 301(s1)
	lbu t0, 142(s1)
	sb t0, 302(s1)
	lbu t0, 143(s1)
	sb t0, 303(s1)
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
	sb t0, 304(s1)
	lbu t0, 129(s1)
	sb t0, 305(s1)
	lbu t0, 130(s1)
	sb t0, 306(s1)
	lbu t0, 131(s1)
	sb t0, 307(s1)
	lbu t0, 132(s1)
	sb t0, 308(s1)
	lbu t0, 133(s1)
	sb t0, 309(s1)
	lbu t0, 134(s1)
	sb t0, 310(s1)
	lbu t0, 135(s1)
	sb t0, 311(s1)
	lbu t0, 136(s1)
	sb t0, 312(s1)
	lbu t0, 137(s1)
	sb t0, 313(s1)
	lbu t0, 138(s1)
	sb t0, 314(s1)
	lbu t0, 139(s1)
	sb t0, 315(s1)
	lbu t0, 140(s1)
	sb t0, 316(s1)
	lbu t0, 141(s1)
	sb t0, 317(s1)
	lbu t0, 142(s1)
	sb t0, 318(s1)
	lbu t0, 143(s1)
	sb t0, 319(s1)
	addi a0, s2, 0
	addi a1, s3, 0
	addi a2, s1, 192
	addi a3, s1, 256
	addi a4, s0, 0
	call {vg_ecdsa_brainpoolp512r1_sign_k}
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
	sd t0, 256(s1)
	sd t0, 264(s1)
	sd t0, 272(s1)
	sd t0, 280(s1)
	sd t0, 288(s1)
	sd t0, 296(s1)
	sd t0, 304(s1)
	sd t0, 312(s1)
	ld ra, 0(s1)
	ld s0, 8(s1)
	ld s2, 24(s1)
	ld s3, 32(s1)
	ld s4, 40(s1)
	ld s5, 48(s1)
	ld s6, 56(s1)
	ld s1, 16(s1)
	addi sp, sp, 320
21:
	ret
	.option pop
