// The functions of `src/ec_brainpoolp512r1_compressed.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ec_brainpoolp512r1_compress_public_key:
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
	slli t0, t0, 8
	lbu t1, 8(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 185(s0)
	addi s0, s0, -2047
	lbu t0, 9(a1)
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
	slli t0, t0, 8
	lbu t1, 16(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 177(s0)
	addi s0, s0, -2047
	lbu t0, 17(a1)
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
	slli t0, t0, 8
	lbu t1, 24(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 169(s0)
	addi s0, s0, -2047
	lbu t0, 25(a1)
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
	slli t0, t0, 8
	lbu t1, 32(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 161(s0)
	addi s0, s0, -2047
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
	addi s0, s0, 2047
	sd t0, 153(s0)
	addi s0, s0, -2047
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
	addi s0, s0, 2047
	sd t0, 145(s0)
	addi s0, s0, -2047
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
	addi s0, s0, 2047
	sd t0, 137(s0)
	addi s0, s0, -2047
	lbu t0, 57(a1)
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
	slli t0, t0, 8
	lbu t1, 64(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 129(s0)
	addi s0, s0, -2047
	lbu t0, 65(a1)
	slli t0, t0, 8
	lbu t1, 66(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 67(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 68(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 69(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 70(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 71(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 72(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 377(s0)
	addi s0, s0, -2047
	lbu t0, 73(a1)
	slli t0, t0, 8
	lbu t1, 74(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 75(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 76(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 77(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 78(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 79(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 80(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 369(s0)
	addi s0, s0, -2047
	lbu t0, 81(a1)
	slli t0, t0, 8
	lbu t1, 82(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 83(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 84(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 85(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 86(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 87(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 88(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 361(s0)
	addi s0, s0, -2047
	lbu t0, 89(a1)
	slli t0, t0, 8
	lbu t1, 90(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 91(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 92(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 93(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 94(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 95(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 96(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 353(s0)
	addi s0, s0, -2047
	lbu t0, 97(a1)
	slli t0, t0, 8
	lbu t1, 98(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 99(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 100(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 101(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 102(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 103(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 104(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 345(s0)
	addi s0, s0, -2047
	lbu t0, 105(a1)
	slli t0, t0, 8
	lbu t1, 106(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 107(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 108(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 109(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 110(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 111(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 112(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 337(s0)
	addi s0, s0, -2047
	lbu t0, 113(a1)
	slli t0, t0, 8
	lbu t1, 114(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 115(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 116(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 117(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 118(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 119(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 120(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 329(s0)
	addi s0, s0, -2047
	lbu t0, 121(a1)
	slli t0, t0, 8
	lbu t1, 122(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 123(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 124(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 125(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 126(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 127(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 128(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 321(s0)
	addi s0, s0, -2047
	lbu t0, 0(a1)
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
	addi a0, s0, 0
	call {vg_brainpoolp512r1_check_point}
	addi s0, s3, 0
	addi a7, s0, 2047
	ld a7, 833(a7)
	addi t0, s0, 2047
	ld t0, 321(t0)
	andi t0, t0, 1
	addi t0, t0, 2
	and t0, t0, a7
	sb t0, 0(s2)
	addi t0, s0, 2047
	ld t0, 185(t0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 1(s2)
	srli t1, t0, 48
	sb t1, 2(s2)
	srli t1, t0, 40
	sb t1, 3(s2)
	srli t1, t0, 32
	sb t1, 4(s2)
	srli t1, t0, 24
	sb t1, 5(s2)
	srli t1, t0, 16
	sb t1, 6(s2)
	srli t1, t0, 8
	sb t1, 7(s2)
	srli t1, t0, 0
	sb t1, 8(s2)
	addi t0, s0, 2047
	ld t0, 177(t0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 9(s2)
	srli t1, t0, 48
	sb t1, 10(s2)
	srli t1, t0, 40
	sb t1, 11(s2)
	srli t1, t0, 32
	sb t1, 12(s2)
	srli t1, t0, 24
	sb t1, 13(s2)
	srli t1, t0, 16
	sb t1, 14(s2)
	srli t1, t0, 8
	sb t1, 15(s2)
	srli t1, t0, 0
	sb t1, 16(s2)
	addi t0, s0, 2047
	ld t0, 169(t0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 17(s2)
	srli t1, t0, 48
	sb t1, 18(s2)
	srli t1, t0, 40
	sb t1, 19(s2)
	srli t1, t0, 32
	sb t1, 20(s2)
	srli t1, t0, 24
	sb t1, 21(s2)
	srli t1, t0, 16
	sb t1, 22(s2)
	srli t1, t0, 8
	sb t1, 23(s2)
	srli t1, t0, 0
	sb t1, 24(s2)
	addi t0, s0, 2047
	ld t0, 161(t0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 25(s2)
	srli t1, t0, 48
	sb t1, 26(s2)
	srli t1, t0, 40
	sb t1, 27(s2)
	srli t1, t0, 32
	sb t1, 28(s2)
	srli t1, t0, 24
	sb t1, 29(s2)
	srli t1, t0, 16
	sb t1, 30(s2)
	srli t1, t0, 8
	sb t1, 31(s2)
	srli t1, t0, 0
	sb t1, 32(s2)
	addi t0, s0, 2047
	ld t0, 153(t0)
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
	addi t0, s0, 2047
	ld t0, 145(t0)
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
	addi t0, s0, 2047
	ld t0, 137(t0)
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
	addi t0, s0, 2047
	ld t0, 129(t0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 57(s2)
	srli t1, t0, 48
	sb t1, 58(s2)
	srli t1, t0, 40
	sb t1, 59(s2)
	srli t1, t0, 32
	sb t1, 60(s2)
	srli t1, t0, 24
	sb t1, 61(s2)
	srli t1, t0, 16
	sb t1, 62(s2)
	srli t1, t0, 8
	sb t1, 63(s2)
	srli t1, t0, 0
	sb t1, 64(s2)
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

vg_ec_brainpoolp512r1_decompress_public_key:
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
	slli t0, t0, 8
	lbu t1, 8(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 185(s0)
	addi s0, s0, -2047
	lbu t0, 9(a1)
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
	slli t0, t0, 8
	lbu t1, 16(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 177(s0)
	addi s0, s0, -2047
	lbu t0, 17(a1)
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
	slli t0, t0, 8
	lbu t1, 24(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 169(s0)
	addi s0, s0, -2047
	lbu t0, 25(a1)
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
	slli t0, t0, 8
	lbu t1, 32(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 161(s0)
	addi s0, s0, -2047
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
	addi s0, s0, 2047
	sd t0, 153(s0)
	addi s0, s0, -2047
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
	addi s0, s0, 2047
	sd t0, 145(s0)
	addi s0, s0, -2047
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
	addi s0, s0, 2047
	sd t0, 137(s0)
	addi s0, s0, -2047
	lbu t0, 57(a1)
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
	slli t0, t0, 8
	lbu t1, 64(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 129(s0)
	addi s0, s0, -2047
	lbu t0, 0(a1)
	andi t0, t0, 1
	sd t0, 704(s0)
	lbu t0, 0(a1)
	xori t0, t0, 2
	srli t0, t0, 1
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
	lui t0, 303786
	addiw t0, t0, -2026
	slli t0, t0, 32
	lui t1, 614633
	addiw t1, t1, 573
	add t0, t0, t1
	sd t0, 768(s0)
	lui t0, 565768
	addiw t0, t0, -52
	slli t0, t0, 32
	lui t1, 833035
	addiw t1, t1, 417
	add t0, t0, t1
	sd t0, 776(s0)
	lui t0, 703287
	addiw t0, t0, -1973
	slli t0, t0, 32
	lui t1, 760462
	addiw t1, t1, 57
	add t0, t0, t1
	sd t0, 784(s0)
	lui t0, 390454
	addiw t0, t0, 1728
	slli t0, t0, 32
	lui t1, 159514
	addiw t1, t1, -1520
	add t0, t0, t1
	sd t0, 792(s0)
	lui t0, 743822
	addiw t0, t0, 1843
	slli t0, t0, 32
	lui t1, 639180
	addiw t1, t1, 540
	add t0, t0, t1
	sd t0, 800(s0)
	lui t0, 994498
	addiw t0, t0, 877
	slli t0, t0, 32
	lui t1, 970535
	addiw t1, t1, 1155
	add t0, t0, t1
	sd t0, 808(s0)
	lui t0, 851796
	addiw t0, t0, -1620
	slli t0, t0, 32
	lui t1, 577320
	addiw t1, t1, -255
	add t0, t0, t1
	sd t0, 816(s0)
	lui t0, 174966
	addiw t0, t0, 1902
	slli t0, t0, 32
	lui t1, 225191
	addiw t1, t1, 290
	add t0, t0, t1
	sd t0, 824(s0)
	addi t5, zero, 0
	addi t3, s0, 2047
	ld t3, 129(t3)
	ld t4, 64(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t3, s0, 2047
	ld t3, 137(t3)
	ld t4, 72(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t3, s0, 2047
	ld t3, 145(t3)
	ld t4, 80(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t3, s0, 2047
	ld t3, 153(t3)
	ld t4, 88(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t3, s0, 2047
	ld t3, 161(t3)
	ld t4, 96(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t3, s0, 2047
	ld t3, 169(t3)
	ld t4, 104(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t3, s0, 2047
	ld t3, 177(t3)
	ld t4, 112(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t3, s0, 2047
	ld t3, 185(t3)
	ld t4, 120(s0)
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
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 193
	addi a2, zero, 2047
	addi a2, a2, 129
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 2047
	addi a2, a2, 193
	addi a3, zero, 2047
	addi a3, a3, 193
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1536
	addi a3, zero, 2047
	addi a3, a3, 193
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 448
	addi a3, zero, 2047
	addi a3, a3, 193
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1536
	addi a3, zero, 1600
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 1536
	addi a3, zero, 2047
	addi a3, a3, 577
	call {vg_brainpoolp512r1_add_mod_p}
	ld t0, 384(s0)
	sd t0, 1920(s0)
	ld t0, 392(s0)
	sd t0, 1928(s0)
	ld t0, 400(s0)
	sd t0, 1936(s0)
	ld t0, 408(s0)
	sd t0, 1944(s0)
	ld t0, 416(s0)
	sd t0, 1952(s0)
	ld t0, 424(s0)
	sd t0, 1960(s0)
	ld t0, 432(s0)
	sd t0, 1968(s0)
	ld t0, 440(s0)
	sd t0, 1976(s0)
	addi s1, zero, 512
20:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1984
	addi a2, zero, 1536
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	srli t0, s1, 6
	slli t0, t0, 3
	add t0, t0, s0
	ld t1, 768(t0)
	srl t1, t1, s1
	andi t1, t1, 1
	addi t2, zero, 0
	sub a7, t2, t1
	ld t0, 1920(s0)
	ld t1, 1984(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1920(s0)
	ld t0, 1928(s0)
	ld t1, 1992(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1928(s0)
	ld t0, 1936(s0)
	ld t1, 2000(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1936(s0)
	ld t0, 1944(s0)
	ld t1, 2008(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1944(s0)
	ld t0, 1952(s0)
	ld t1, 2016(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1952(s0)
	ld t0, 1960(s0)
	ld t1, 2024(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1960(s0)
	ld t0, 1968(s0)
	ld t1, 2032(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1968(s0)
	ld t0, 1976(s0)
	ld t1, 2040(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1976(s0)
	bnez s1, 20b
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1664
	addi a3, zero, 1536
	call {vg_brainpoolp512r1_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1280
	addi a2, zero, 1920
	addi a3, zero, 320
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1344
	addi a2, zero, 256
	addi a3, zero, 1280
	call {vg_brainpoolp512r1_sub_mod_p}
	addi t3, zero, 0
	ld t4, 1728(s0)
	or t3, t3, t4
	ld t4, 1736(s0)
	or t3, t3, t4
	ld t4, 1744(s0)
	or t3, t3, t4
	ld t4, 1752(s0)
	or t3, t3, t4
	ld t4, 1760(s0)
	or t3, t3, t4
	ld t4, 1768(s0)
	or t3, t3, t4
	ld t4, 1776(s0)
	or t3, t3, t4
	ld t4, 1784(s0)
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
	ld t0, 1280(s0)
	ld t1, 704(s0)
	xor t0, t0, t1
	andi t0, t0, 1
	addi t1, zero, 0
	sub a7, t1, t0
	ld t0, 1280(s0)
	ld t1, 1344(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1408(s0)
	ld t0, 1288(s0)
	ld t1, 1352(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1416(s0)
	ld t0, 1296(s0)
	ld t1, 1360(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1424(s0)
	ld t0, 1304(s0)
	ld t1, 1368(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1432(s0)
	ld t0, 1312(s0)
	ld t1, 1376(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1440(s0)
	ld t0, 1320(s0)
	ld t1, 1384(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1448(s0)
	ld t0, 1328(s0)
	ld t1, 1392(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1456(s0)
	ld t0, 1336(s0)
	ld t1, 1400(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1464(s0)
	ld t0, 1408(s0)
	ld t1, 704(s0)
	xor t0, t0, t1
	andi t0, t0, 1
	addi a7, t0, -1
	addi t0, s0, 2047
	ld t0, 833(t0)
	and t0, t0, a7
	addi s0, s0, 2047
	sd t0, 833(s0)
	addi s0, s0, -2047
	addi a7, s0, 2047
	ld a7, 833(a7)
	addi t0, zero, 4
	and t0, t0, a7
	sb t0, 0(s2)
	addi t0, s0, 2047
	ld t0, 185(t0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 1(s2)
	srli t1, t0, 48
	sb t1, 2(s2)
	srli t1, t0, 40
	sb t1, 3(s2)
	srli t1, t0, 32
	sb t1, 4(s2)
	srli t1, t0, 24
	sb t1, 5(s2)
	srli t1, t0, 16
	sb t1, 6(s2)
	srli t1, t0, 8
	sb t1, 7(s2)
	srli t1, t0, 0
	sb t1, 8(s2)
	addi t0, s0, 2047
	ld t0, 177(t0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 9(s2)
	srli t1, t0, 48
	sb t1, 10(s2)
	srli t1, t0, 40
	sb t1, 11(s2)
	srli t1, t0, 32
	sb t1, 12(s2)
	srli t1, t0, 24
	sb t1, 13(s2)
	srli t1, t0, 16
	sb t1, 14(s2)
	srli t1, t0, 8
	sb t1, 15(s2)
	srli t1, t0, 0
	sb t1, 16(s2)
	addi t0, s0, 2047
	ld t0, 169(t0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 17(s2)
	srli t1, t0, 48
	sb t1, 18(s2)
	srli t1, t0, 40
	sb t1, 19(s2)
	srli t1, t0, 32
	sb t1, 20(s2)
	srli t1, t0, 24
	sb t1, 21(s2)
	srli t1, t0, 16
	sb t1, 22(s2)
	srli t1, t0, 8
	sb t1, 23(s2)
	srli t1, t0, 0
	sb t1, 24(s2)
	addi t0, s0, 2047
	ld t0, 161(t0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 25(s2)
	srli t1, t0, 48
	sb t1, 26(s2)
	srli t1, t0, 40
	sb t1, 27(s2)
	srli t1, t0, 32
	sb t1, 28(s2)
	srli t1, t0, 24
	sb t1, 29(s2)
	srli t1, t0, 16
	sb t1, 30(s2)
	srli t1, t0, 8
	sb t1, 31(s2)
	srli t1, t0, 0
	sb t1, 32(s2)
	addi t0, s0, 2047
	ld t0, 153(t0)
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
	addi t0, s0, 2047
	ld t0, 145(t0)
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
	addi t0, s0, 2047
	ld t0, 137(t0)
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
	addi t0, s0, 2047
	ld t0, 129(t0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 57(s2)
	srli t1, t0, 48
	sb t1, 58(s2)
	srli t1, t0, 40
	sb t1, 59(s2)
	srli t1, t0, 32
	sb t1, 60(s2)
	srli t1, t0, 24
	sb t1, 61(s2)
	srli t1, t0, 16
	sb t1, 62(s2)
	srli t1, t0, 8
	sb t1, 63(s2)
	srli t1, t0, 0
	sb t1, 64(s2)
	ld t0, 1464(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 65(s2)
	srli t1, t0, 48
	sb t1, 66(s2)
	srli t1, t0, 40
	sb t1, 67(s2)
	srli t1, t0, 32
	sb t1, 68(s2)
	srli t1, t0, 24
	sb t1, 69(s2)
	srli t1, t0, 16
	sb t1, 70(s2)
	srli t1, t0, 8
	sb t1, 71(s2)
	srli t1, t0, 0
	sb t1, 72(s2)
	ld t0, 1456(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 73(s2)
	srli t1, t0, 48
	sb t1, 74(s2)
	srli t1, t0, 40
	sb t1, 75(s2)
	srli t1, t0, 32
	sb t1, 76(s2)
	srli t1, t0, 24
	sb t1, 77(s2)
	srli t1, t0, 16
	sb t1, 78(s2)
	srli t1, t0, 8
	sb t1, 79(s2)
	srli t1, t0, 0
	sb t1, 80(s2)
	ld t0, 1448(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 81(s2)
	srli t1, t0, 48
	sb t1, 82(s2)
	srli t1, t0, 40
	sb t1, 83(s2)
	srli t1, t0, 32
	sb t1, 84(s2)
	srli t1, t0, 24
	sb t1, 85(s2)
	srli t1, t0, 16
	sb t1, 86(s2)
	srli t1, t0, 8
	sb t1, 87(s2)
	srli t1, t0, 0
	sb t1, 88(s2)
	ld t0, 1440(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 89(s2)
	srli t1, t0, 48
	sb t1, 90(s2)
	srli t1, t0, 40
	sb t1, 91(s2)
	srli t1, t0, 32
	sb t1, 92(s2)
	srli t1, t0, 24
	sb t1, 93(s2)
	srli t1, t0, 16
	sb t1, 94(s2)
	srli t1, t0, 8
	sb t1, 95(s2)
	srli t1, t0, 0
	sb t1, 96(s2)
	ld t0, 1432(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 97(s2)
	srli t1, t0, 48
	sb t1, 98(s2)
	srli t1, t0, 40
	sb t1, 99(s2)
	srli t1, t0, 32
	sb t1, 100(s2)
	srli t1, t0, 24
	sb t1, 101(s2)
	srli t1, t0, 16
	sb t1, 102(s2)
	srli t1, t0, 8
	sb t1, 103(s2)
	srli t1, t0, 0
	sb t1, 104(s2)
	ld t0, 1424(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 105(s2)
	srli t1, t0, 48
	sb t1, 106(s2)
	srli t1, t0, 40
	sb t1, 107(s2)
	srli t1, t0, 32
	sb t1, 108(s2)
	srli t1, t0, 24
	sb t1, 109(s2)
	srli t1, t0, 16
	sb t1, 110(s2)
	srli t1, t0, 8
	sb t1, 111(s2)
	srli t1, t0, 0
	sb t1, 112(s2)
	ld t0, 1416(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 113(s2)
	srli t1, t0, 48
	sb t1, 114(s2)
	srli t1, t0, 40
	sb t1, 115(s2)
	srli t1, t0, 32
	sb t1, 116(s2)
	srli t1, t0, 24
	sb t1, 117(s2)
	srli t1, t0, 16
	sb t1, 118(s2)
	srli t1, t0, 8
	sb t1, 119(s2)
	srli t1, t0, 0
	sb t1, 120(s2)
	ld t0, 1408(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 121(s2)
	srli t1, t0, 48
	sb t1, 122(s2)
	srli t1, t0, 40
	sb t1, 123(s2)
	srli t1, t0, 32
	sb t1, 124(s2)
	srli t1, t0, 24
	sb t1, 125(s2)
	srli t1, t0, 16
	sb t1, 126(s2)
	srli t1, t0, 8
	sb t1, 127(s2)
	srli t1, t0, 0
	sb t1, 128(s2)
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
