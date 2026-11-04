// The functions of `src/ecdsa_p384.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_p384_verify:
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
	sd t0, 1688(s0)
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
	sd t0, 1680(s0)
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
	sd t0, 1672(s0)
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
	sd t0, 1664(s0)
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
	sd t0, 1656(s0)
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
	sd t0, 1648(s0)
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
	sd t0, 1832(s0)
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
	sd t0, 1824(s0)
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
	sd t0, 1816(s0)
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
	sd t0, 1808(s0)
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
	sd t0, 1800(s0)
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
	sd t0, 1792(s0)
	lbu t0, 0(a0)
	xori t0, t0, 4
	addi t0, t0, -1
	srli t0, t0, 63
	addi t1, zero, 0
	sub a7, t1, t0
	addi s0, s0, 2047
	sd a7, 129(s0)
	addi s0, s0, -2047
	lui t0, 0
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
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
	addiw t1, t1, -2
	add t0, t0, t1
	sd t0, 80(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 88(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 96(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 104(s0)
	lui t0, 970434
	addiw t0, t0, -1685
	slli t0, t0, 32
	lui t1, 838739
	addiw t1, t1, -1677
	add t0, t0, t1
	sd t0, 112(s0)
	lui t0, 360865
	addiw t0, t0, -590
	slli t0, t0, 32
	lui t1, 297738
	addiw t1, t1, 1914
	add t0, t0, t1
	sd t0, 120(s0)
	lui t0, 816693
	addiw t0, t0, -638
	slli t0, t0, 32
	lui t1, 1000307
	addiw t1, t1, -545
	add t0, t0, t1
	sd t0, 128(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 136(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 144(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 152(s0)
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
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
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
	addiw t1, t1, 1
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
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 1
	add t0, t0, t1
	sd t0, 304(s0)
	lui t0, 0
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
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
	addiw t0, t0, 4
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -4
	add t0, t0, t1
	sd t0, 352(s0)
	lui t0, 0
	addiw t0, t0, -4
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 360(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -5
	add t0, t0, t1
	sd t0, 368(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 376(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 384(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 392(s0)
	lui t0, 99146
	addiw t0, t0, -1709
	slli t0, t0, 32
	lui t1, 883769
	addiw t1, t1, -1690
	add t0, t0, t1
	sd t0, 400(s0)
	lui t0, 939985
	addiw t0, t0, -1653
	slli t0, t0, 32
	lui t1, 454218
	addiw t1, t1, -1852
	add t0, t0, t1
	sd t0, 408(s0)
	lui t0, 425318
	addiw t0, t0, 465
	slli t0, t0, 32
	lui t1, 308736
	addiw t1, t1, 1678
	add t0, t0, t1
	sd t0, 416(s0)
	lui t0, 694878
	addiw t0, t0, 972
	slli t0, t0, 32
	lui t1, 777130
	addiw t1, t1, 167
	add t0, t0, t1
	sd t0, 424(s0)
	lui t0, 141334
	addiw t0, t0, 1500
	slli t0, t0, 32
	lui t1, 381030
	addiw t1, t1, 446
	add t0, t0, t1
	sd t0, 432(s0)
	lui t0, 422275
	addiw t0, t0, 994
	slli t0, t0, 32
	lui t1, 134900
	addiw t1, t1, -19
	add t0, t0, t1
	sd t0, 440(s0)
	lui t0, 253191
	addiw t0, t0, 1382
	slli t0, t0, 32
	lui t1, 302091
	addiw t1, t1, 1320
	add t0, t0, t1
	sd t0, 448(s0)
	lui t0, 134712
	addiw t0, t0, -1821
	slli t0, t0, 32
	lui t1, 658797
	addiw t1, t1, -456
	add t0, t0, t1
	sd t0, 456(s0)
	lui t0, 555460
	addiw t0, t0, -1284
	slli t0, t0, 32
	lui t1, 344501
	addiw t1, t1, -658
	add t0, t0, t1
	sd t0, 464(s0)
	lui t0, 410952
	addiw t0, t0, 1668
	slli t0, t0, 32
	lui t1, 367153
	addiw t1, t1, -257
	add t0, t0, t1
	sd t0, 472(s0)
	lui t0, 529151
	addiw t0, t0, 1827
	slli t0, t0, 32
	lui t1, 398574
	addiw t1, t1, -469
	add t0, t0, t1
	sd t0, 480(s0)
	lui t0, 316331
	addiw t0, t0, -574
	slli t0, t0, 32
	lui t1, 170465
	addiw t1, t1, 1299
	add t0, t0, t1
	sd t0, 488(s0)
	lui t0, 143428
	addiw t0, t0, -595
	slli t0, t0, 32
	lui t1, 307258
	addiw t1, t1, 1278
	add t0, t0, t1
	sd t0, 496(s0)
	lui t0, 662523
	addiw t0, t0, -1857
	slli t0, t0, 32
	lui t1, 506699
	addiw t1, t1, -1620
	add t0, t0, t1
	sd t0, 504(s0)
	lui t0, 572126
	addiw t0, t0, 1878
	slli t0, t0, 32
	lui t1, 190523
	addiw t1, t1, 80
	add t0, t0, t1
	sd t0, 512(s0)
	lui t0, 814133
	addiw t0, t0, 537
	slli t0, t0, 32
	lui t1, 429904
	addiw t1, t1, -39
	add t0, t0, t1
	sd t0, 520(s0)
	lui t0, 907264
	addiw t0, t0, 550
	slli t0, t0, 32
	lui t1, 235163
	addiw t1, t1, -1984
	add t0, t0, t1
	sd t0, 528(s0)
	lui t0, 178059
	addiw t0, t0, -1086
	slli t0, t0, 32
	lui t1, 368988
	addiw t1, t1, 1513
	add t0, t0, t1
	sd t0, 536(s0)
	lui t0, 0
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -3
	add t0, t0, t1
	sd t0, 640(s0)
	lui t0, 0
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 648(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -2
	add t0, t0, t1
	sd t0, 656(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 664(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 672(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 680(s0)
	lui t0, 0
	addiw t0, t0, -2
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 1
	add t0, t0, t1
	sd t0, 1936(s0)
	lui t0, 0
	addiw t0, t0, 2
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1944(s0)
	lui t0, 0
	addiw t0, t0, -2
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1952(s0)
	lui t0, 0
	addiw t0, t0, 2
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1960(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 1
	add t0, t0, t1
	sd t0, 1968(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1976(s0)
	lui t0, 33049
	addiw t0, t0, -1934
	slli t0, t0, 32
	lui t1, 644115
	addiw t1, t1, -564
	add t0, t0, t1
	sd t0, 1984(s0)
	lui t0, 1012379
	addiw t0, t0, -552
	slli t0, t0, 32
	lui t1, 500931
	addiw t1, t1, 748
	add t0, t0, t1
	sd t0, 1992(s0)
	lui t0, 491298
	addiw t0, t0, 155
	slli t0, t0, 32
	lui t1, 102912
	addiw t1, t1, 558
	add t0, t0, t1
	sd t0, 2000(s0)
	lui t0, 930677
	addiw t0, t0, -1041
	slli t0, t0, 32
	lui t1, 608569
	addiw t1, t1, -1310
	add t0, t0, t1
	sd t0, 2008(s0)
	lui t0, 746162
	addiw t0, t0, 500
	slli t0, t0, 32
	lui t1, 127010
	addiw t1, t1, 148
	add t0, t0, t1
	sd t0, 2016(s0)
	lui t0, 839809
	addiw t0, t0, 331
	slli t0, t0, 32
	lui t1, 394492
	addiw t1, t1, -7
	add t0, t0, t1
	sd t0, 2024(s0)
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
	sd t0, 584(s0)
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
	sd t0, 576(s0)
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
	sd t0, 568(s0)
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
	sd t0, 560(s0)
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
	sd t0, 552(s0)
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
	sd t0, 544(s0)
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
	sd t0, 632(s0)
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
	sd t0, 624(s0)
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
	sd t0, 616(s0)
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
	sd t0, 608(s0)
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
	sd t0, 600(s0)
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
	sd t0, 592(s0)
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
	sd t0, 1640(s0)
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
	sd t0, 1632(s0)
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
	sd t0, 1624(s0)
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
	sd t0, 1616(s0)
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
	sd t0, 1608(s0)
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
	sd t0, 1600(s0)
	addi t5, zero, 0
	ld t3, 544(s0)
	ld t4, 112(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 552(s0)
	ld t4, 120(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 560(s0)
	ld t4, 128(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 568(s0)
	ld t4, 136(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 576(s0)
	ld t4, 144(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 584(s0)
	ld t4, 152(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t6, zero, 0
	sub a7, t6, t5
	addi t0, s0, 2047
	ld t0, 129(t0)
	and t0, t0, a7
	addi s0, s0, 2047
	sd t0, 129(s0)
	addi s0, s0, -2047
	addi t3, zero, 0
	ld t4, 544(s0)
	or t3, t3, t4
	ld t4, 552(s0)
	or t3, t3, t4
	ld t4, 560(s0)
	or t3, t3, t4
	ld t4, 568(s0)
	or t3, t3, t4
	ld t4, 576(s0)
	or t3, t3, t4
	ld t4, 584(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	xori a7, a7, -1
	addi t0, s0, 2047
	ld t0, 129(t0)
	and t0, t0, a7
	addi s0, s0, 2047
	sd t0, 129(s0)
	addi s0, s0, -2047
	addi t5, zero, 0
	ld t3, 592(s0)
	ld t4, 112(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 600(s0)
	ld t4, 120(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 608(s0)
	ld t4, 128(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 616(s0)
	ld t4, 136(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 624(s0)
	ld t4, 144(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 632(s0)
	ld t4, 152(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t6, zero, 0
	sub a7, t6, t5
	addi t0, s0, 2047
	ld t0, 129(t0)
	and t0, t0, a7
	addi s0, s0, 2047
	sd t0, 129(s0)
	addi s0, s0, -2047
	addi t3, zero, 0
	ld t4, 592(s0)
	or t3, t3, t4
	ld t4, 600(s0)
	or t3, t3, t4
	ld t4, 608(s0)
	or t3, t3, t4
	ld t4, 616(s0)
	or t3, t3, t4
	ld t4, 624(s0)
	or t3, t3, t4
	ld t4, 632(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	xori a7, a7, -1
	addi t0, s0, 2047
	ld t0, 129(t0)
	and t0, t0, a7
	addi s0, s0, 2047
	sd t0, 129(s0)
	addi s0, s0, -2047
	addi a0, s0, 0
	call {vg_p384_check_point}
	addi s0, s3, 0
	lui t0, 185114
	addiw t0, t0, -1244
	slli t0, t0, 32
	lui t1, 105281
	addiw t1, t1, -1623
	add t0, t0, t1
	sd t0, 1744(s0)
	lui t0, 1045464
	addiw t0, t0, 486
	slli t0, t0, 32
	lui t1, 913834
	addiw t1, t1, 1049
	add t0, t0, t1
	sd t0, 1752(s0)
	lui t0, 771045
	addiw t0, t0, -1989
	slli t0, t0, 32
	lui t1, 1035139
	addiw t1, t1, -1721
	add t0, t0, t1
	sd t0, 1760(s0)
	lui t0, 868565
	addiw t0, t0, -1769
	slli t0, t0, 32
	lui t1, 305842
	addiw t1, t1, -827
	add t0, t0, t1
	sd t0, 1768(s0)
	lui t0, 260870
	addiw t0, t0, -1158
	slli t0, t0, 32
	lui t1, 164455
	addiw t1, t1, -1899
	add t0, t0, t1
	sd t0, 1776(s0)
	lui t0, 51279
	addiw t0, t0, -511
	slli t0, t0, 32
	lui t1, 177052
	addiw t1, t1, -223
	add t0, t0, t1
	sd t0, 1784(s0)
	lui t0, 78142
	addiw t0, t0, 1685
	slli t0, t0, 32
	lui t1, 209837
	addiw t1, t1, 1677
	add t0, t0, t1
	sd t0, 1792(s0)
	lui t0, 687711
	addiw t0, t0, 590
	slli t0, t0, 32
	lui t1, 750838
	addiw t1, t1, -1915
	add t0, t0, t1
	sd t0, 1800(s0)
	lui t0, 231883
	addiw t0, t0, 638
	slli t0, t0, 32
	lui t1, 48269
	addiw t1, t1, 544
	add t0, t0, t1
	sd t0, 1808(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1816(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1824(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1832(s0)
	lui t0, 970434
	addiw t0, t0, -1685
	slli t0, t0, 32
	lui t1, 838739
	addiw t1, t1, -1679
	add t0, t0, t1
	sd t0, 1840(s0)
	lui t0, 360865
	addiw t0, t0, -590
	slli t0, t0, 32
	lui t1, 297738
	addiw t1, t1, 1914
	add t0, t0, t1
	sd t0, 1848(s0)
	lui t0, 816693
	addiw t0, t0, -638
	slli t0, t0, 32
	lui t1, 1000307
	addiw t1, t1, -545
	add t0, t0, t1
	sd t0, 1856(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 1864(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 1872(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 1880(s0)
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 592
	addi a3, zero, 1744
	call {vg_p384_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 225
	addi a2, zero, 1024
	addi a3, zero, 1792
	call {vg_p384_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 609
	addi a2, zero, 2047
	addi a2, a2, 225
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_p384_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 273
	addi a2, zero, 2047
	addi a2, a2, 225
	addi a3, zero, 2047
	addi a3, a3, 609
	call {vg_p384_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 321
	addi a2, zero, 2047
	addi a2, a2, 273
	addi a3, zero, 2047
	addi a3, a3, 609
	call {vg_p384_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 369
	addi a2, zero, 2047
	addi a2, a2, 321
	addi a3, zero, 2047
	addi a3, a3, 609
	call {vg_p384_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 417
	addi a2, zero, 2047
	addi a2, a2, 369
	addi a3, zero, 2047
	addi a3, a3, 609
	call {vg_p384_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 465
	addi a2, zero, 2047
	addi a2, a2, 417
	addi a3, zero, 2047
	addi a3, a3, 609
	call {vg_p384_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 513
	addi a2, zero, 2047
	addi a2, a2, 465
	addi a3, zero, 2047
	addi a3, a3, 609
	call {vg_p384_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 561
	addi a2, zero, 2047
	addi a2, a2, 513
	addi a3, zero, 2047
	addi a3, a3, 609
	call {vg_p384_mul_mod_n}
	addi t0, s0, 2047
	ld t0, 561(t0)
	sd t0, 1456(s0)
	addi t0, s0, 2047
	ld t0, 569(t0)
	sd t0, 1464(s0)
	addi t0, s0, 2047
	ld t0, 577(t0)
	sd t0, 1472(s0)
	addi t0, s0, 2047
	ld t0, 585(t0)
	sd t0, 1480(s0)
	addi t0, s0, 2047
	ld t0, 593(t0)
	sd t0, 1488(s0)
	addi t0, s0, 2047
	ld t0, 601(t0)
	sd t0, 1496(s0)
	addi s1, zero, 4
20:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 20b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
21:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 21b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
22:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 22b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
23:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 23b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
24:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 24b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
25:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 25b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
26:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 26b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
27:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 27b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
28:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 28b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
29:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 29b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
210:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 210b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
211:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 211b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
212:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 212b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
213:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 213b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
214:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 214b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
215:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 215b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
216:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 216b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
217:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 217b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
218:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 218b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
219:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 219b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
220:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 220b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
221:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 221b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
222:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 222b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
223:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 223b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
224:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 224b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
225:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 225b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
226:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 226b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
227:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 227b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
228:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 228b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
229:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 229b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
230:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 230b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
231:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 231b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
232:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 232b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
233:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 233b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
234:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 234b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
235:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 235b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
236:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 236b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
237:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 237b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
238:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 238b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
239:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 239b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
240:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 240b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
241:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 241b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
242:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 242b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
243:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 243b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
244:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 244b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
245:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 245b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
246:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 246b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 2
247:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 247b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 273
	call {vg_p384_mul_mod_n}
	addi s1, zero, 6
248:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 248b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 369
	call {vg_p384_mul_mod_n}
	addi s1, zero, 3
249:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 249b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 273
	call {vg_p384_mul_mod_n}
	addi s1, zero, 7
250:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 250b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_p384_mul_mod_n}
	addi s1, zero, 6
251:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 251b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_p384_mul_mod_n}
	addi s1, zero, 1
252:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 252b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_p384_mul_mod_n}
	addi s1, zero, 10
253:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 253b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 3
254:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 254b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_p384_mul_mod_n}
	addi s1, zero, 8
255:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 255b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_p384_mul_mod_n}
	addi s1, zero, 2
256:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 256b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 273
	call {vg_p384_mul_mod_n}
	addi s1, zero, 6
257:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 257b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 465
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
258:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 258b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 369
	call {vg_p384_mul_mod_n}
	addi s1, zero, 5
259:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 259b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 3
260:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 260b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_p384_mul_mod_n}
	addi s1, zero, 3
261:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 261b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 273
	call {vg_p384_mul_mod_n}
	addi s1, zero, 10
262:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 262b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_p384_mul_mod_n}
	addi s1, zero, 9
263:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 263b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
264:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 264b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 465
	call {vg_p384_mul_mod_n}
	addi s1, zero, 6
265:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 265b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 417
	call {vg_p384_mul_mod_n}
	addi s1, zero, 3
266:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 266b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_p384_mul_mod_n}
	addi s1, zero, 7
267:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 267b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 465
	call {vg_p384_mul_mod_n}
	addi s1, zero, 7
268:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 268b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_p384_mul_mod_n}
	addi s1, zero, 5
269:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 269b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 369
	call {vg_p384_mul_mod_n}
	addi s1, zero, 5
270:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 270b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 5
271:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 271b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 465
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
272:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 272b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 465
	call {vg_p384_mul_mod_n}
	addi s1, zero, 5
273:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 273b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 369
	call {vg_p384_mul_mod_n}
	addi s1, zero, 3
274:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 274b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 273
	call {vg_p384_mul_mod_n}
	addi s1, zero, 7
275:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 275b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 273
	call {vg_p384_mul_mod_n}
	addi s1, zero, 6
276:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 276b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 465
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
277:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 277b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_p384_mul_mod_n}
	addi s1, zero, 3
278:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 278b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 273
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
279:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 279b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 273
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
280:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 280b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 273
	call {vg_p384_mul_mod_n}
	addi s1, zero, 6
281:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 281b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_p384_mul_mod_n}
	addi s1, zero, 5
282:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 282b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_p384_mul_mod_n}
	addi s1, zero, 6
283:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 283b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 465
	call {vg_p384_mul_mod_n}
	addi s1, zero, 1
284:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 284b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
285:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 285b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_p384_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1600
	addi a3, zero, 1744
	call {vg_p384_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1072
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1648
	addi a2, zero, 1120
	addi a3, zero, 256
	call {vg_p384_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 544
	addi a3, zero, 1744
	call {vg_p384_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1120
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1216
	addi a3, zero, 256
	call {vg_p384_mul_mod_n}
	ld t0, 1792(s0)
	sd t0, 1552(s0)
	ld t0, 1800(s0)
	sd t0, 1560(s0)
	ld t0, 1808(s0)
	sd t0, 1568(s0)
	ld t0, 1816(s0)
	sd t0, 1576(s0)
	ld t0, 1824(s0)
	sd t0, 1584(s0)
	ld t0, 1832(s0)
	sd t0, 1592(s0)
	ld t0, 1888(s0)
	sd t0, 736(s0)
	ld t0, 1896(s0)
	sd t0, 744(s0)
	ld t0, 1904(s0)
	sd t0, 752(s0)
	ld t0, 1912(s0)
	sd t0, 760(s0)
	ld t0, 1920(s0)
	sd t0, 768(s0)
	ld t0, 1928(s0)
	sd t0, 776(s0)
	addi t0, s0, 2047
	ld t0, 81(t0)
	sd t0, 784(s0)
	addi t0, s0, 2047
	ld t0, 89(t0)
	sd t0, 792(s0)
	addi t0, s0, 2047
	ld t0, 97(t0)
	sd t0, 800(s0)
	addi t0, s0, 2047
	ld t0, 105(t0)
	sd t0, 808(s0)
	addi t0, s0, 2047
	ld t0, 113(t0)
	sd t0, 816(s0)
	addi t0, s0, 2047
	ld t0, 121(t0)
	sd t0, 824(s0)
	addi a0, s0, 0
	call {vg_p384_mul}
	addi s0, s3, 0
	addi t3, zero, 0
	ld t4, 1792(s0)
	or t3, t3, t4
	ld t4, 1800(s0)
	or t3, t3, t4
	ld t4, 1808(s0)
	or t3, t3, t4
	ld t4, 1816(s0)
	or t3, t3, t4
	ld t4, 1824(s0)
	or t3, t3, t4
	ld t4, 1832(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	ld t0, 736(s0)
	ld t1, 208(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 736(s0)
	ld t0, 744(s0)
	ld t1, 216(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 744(s0)
	ld t0, 752(s0)
	ld t1, 224(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 752(s0)
	ld t0, 760(s0)
	ld t1, 232(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 760(s0)
	ld t0, 768(s0)
	ld t1, 240(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 768(s0)
	ld t0, 776(s0)
	ld t1, 248(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 776(s0)
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
	ld t0, 832(s0)
	ld t1, 208(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 832(s0)
	ld t0, 840(s0)
	ld t1, 216(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 840(s0)
	ld t0, 848(s0)
	ld t1, 224(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 848(s0)
	ld t0, 856(s0)
	ld t1, 232(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 856(s0)
	ld t0, 864(s0)
	ld t1, 240(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 864(s0)
	ld t0, 872(s0)
	ld t1, 248(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 872(s0)
	lui t0, 33049
	addiw t0, t0, -1934
	slli t0, t0, 32
	lui t1, 644115
	addiw t1, t1, -564
	add t0, t0, t1
	sd t0, 1984(s0)
	lui t0, 1012379
	addiw t0, t0, -552
	slli t0, t0, 32
	lui t1, 500931
	addiw t1, t1, 748
	add t0, t0, t1
	sd t0, 1992(s0)
	lui t0, 491298
	addiw t0, t0, 155
	slli t0, t0, 32
	lui t1, 102912
	addiw t1, t1, 558
	add t0, t0, t1
	sd t0, 2000(s0)
	lui t0, 930677
	addiw t0, t0, -1041
	slli t0, t0, 32
	lui t1, 608569
	addiw t1, t1, -1310
	add t0, t0, t1
	sd t0, 2008(s0)
	lui t0, 746162
	addiw t0, t0, 500
	slli t0, t0, 32
	lui t1, 127010
	addiw t1, t1, 148
	add t0, t0, t1
	sd t0, 2016(s0)
	lui t0, 839809
	addiw t0, t0, 331
	slli t0, t0, 32
	lui t1, 394492
	addiw t1, t1, -7
	add t0, t0, t1
	sd t0, 2024(s0)
	ld t0, 736(s0)
	sd t0, 448(s0)
	ld t0, 744(s0)
	sd t0, 456(s0)
	ld t0, 752(s0)
	sd t0, 464(s0)
	ld t0, 760(s0)
	sd t0, 472(s0)
	ld t0, 768(s0)
	sd t0, 480(s0)
	ld t0, 776(s0)
	sd t0, 488(s0)
	ld t0, 784(s0)
	sd t0, 1888(s0)
	ld t0, 792(s0)
	sd t0, 1896(s0)
	ld t0, 800(s0)
	sd t0, 1904(s0)
	ld t0, 808(s0)
	sd t0, 1912(s0)
	ld t0, 816(s0)
	sd t0, 1920(s0)
	ld t0, 824(s0)
	sd t0, 1928(s0)
	ld t0, 832(s0)
	addi s0, s0, 2047
	sd t0, 81(s0)
	addi s0, s0, -2047
	ld t0, 840(s0)
	addi s0, s0, 2047
	sd t0, 89(s0)
	addi s0, s0, -2047
	ld t0, 848(s0)
	addi s0, s0, 2047
	sd t0, 97(s0)
	addi s0, s0, -2047
	ld t0, 856(s0)
	addi s0, s0, 2047
	sd t0, 105(s0)
	addi s0, s0, -2047
	ld t0, 864(s0)
	addi s0, s0, 2047
	sd t0, 113(s0)
	addi s0, s0, -2047
	ld t0, 872(s0)
	addi s0, s0, 2047
	sd t0, 121(s0)
	addi s0, s0, -2047
	ld t0, 1648(s0)
	sd t0, 1552(s0)
	ld t0, 1656(s0)
	sd t0, 1560(s0)
	ld t0, 1664(s0)
	sd t0, 1568(s0)
	ld t0, 1672(s0)
	sd t0, 1576(s0)
	ld t0, 1680(s0)
	sd t0, 1584(s0)
	ld t0, 1688(s0)
	sd t0, 1592(s0)
	addi a0, s0, 0
	call {vg_p384_mul_g}
	addi s0, s3, 0
	addi t3, zero, 0
	ld t4, 1648(s0)
	or t3, t3, t4
	ld t4, 1656(s0)
	or t3, t3, t4
	ld t4, 1664(s0)
	or t3, t3, t4
	ld t4, 1672(s0)
	or t3, t3, t4
	ld t4, 1680(s0)
	or t3, t3, t4
	ld t4, 1688(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	ld t0, 736(s0)
	ld t1, 208(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 736(s0)
	ld t0, 744(s0)
	ld t1, 216(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 744(s0)
	ld t0, 752(s0)
	ld t1, 224(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 752(s0)
	ld t0, 760(s0)
	ld t1, 232(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 760(s0)
	ld t0, 768(s0)
	ld t1, 240(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 768(s0)
	ld t0, 776(s0)
	ld t1, 248(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 776(s0)
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
	ld t0, 832(s0)
	ld t1, 208(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 832(s0)
	ld t0, 840(s0)
	ld t1, 216(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 840(s0)
	ld t0, 848(s0)
	ld t1, 224(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 848(s0)
	ld t0, 856(s0)
	ld t1, 232(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 856(s0)
	ld t0, 864(s0)
	ld t1, 240(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 864(s0)
	ld t0, 872(s0)
	ld t1, 248(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 872(s0)
	lui t0, 33049
	addiw t0, t0, -1934
	slli t0, t0, 32
	lui t1, 644115
	addiw t1, t1, -564
	add t0, t0, t1
	sd t0, 1984(s0)
	lui t0, 1012379
	addiw t0, t0, -552
	slli t0, t0, 32
	lui t1, 500931
	addiw t1, t1, 748
	add t0, t0, t1
	sd t0, 1992(s0)
	lui t0, 491298
	addiw t0, t0, 155
	slli t0, t0, 32
	lui t1, 102912
	addiw t1, t1, 558
	add t0, t0, t1
	sd t0, 2000(s0)
	lui t0, 930677
	addiw t0, t0, -1041
	slli t0, t0, 32
	lui t1, 608569
	addiw t1, t1, -1310
	add t0, t0, t1
	sd t0, 2008(s0)
	lui t0, 746162
	addiw t0, t0, 500
	slli t0, t0, 32
	lui t1, 127010
	addiw t1, t1, 148
	add t0, t0, t1
	sd t0, 2016(s0)
	lui t0, 839809
	addiw t0, t0, 331
	slli t0, t0, 32
	lui t1, 394492
	addiw t1, t1, -7
	add t0, t0, t1
	sd t0, 2024(s0)
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 736
	addi a3, zero, 448
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 784
	addi a3, zero, 1888
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 832
	addi a3, zero, 2047
	addi a3, a3, 81
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 736
	addi a3, zero, 784
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 448
	addi a3, zero, 1888
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
	addi a2, zero, 784
	addi a3, zero, 832
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1888
	addi a3, zero, 2047
	addi a3, a3, 81
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1024
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1024
	call {vg_p384_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 736
	addi a3, zero, 832
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 448
	addi a3, zero, 2047
	addi a3, a3, 81
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1072
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1024
	addi a3, zero, 1072
	call {vg_p384_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1984
	addi a3, zero, 1264
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1072
	addi a3, zero, 1120
	call {vg_p384_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1024
	addi a3, zero, 1024
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1120
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1216
	addi a3, zero, 1024
	call {vg_p384_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1216
	addi a3, zero, 1024
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1984
	addi a3, zero, 1072
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1264
	addi a3, zero, 1264
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1072
	addi a3, zero, 1264
	call {vg_p384_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1072
	addi a3, zero, 1168
	call {vg_p384_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1072
	addi a3, zero, 1072
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1216
	addi a3, zero, 1072
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1168
	addi a3, zero, 1168
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1216
	addi a3, zero, 1168
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_p384_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1360
	addi a3, zero, 1072
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1168
	addi a3, zero, 1072
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1024
	addi a3, zero, 1120
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1072
	addi a3, zero, 1264
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1312
	addi a3, zero, 1024
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1216
	call {vg_p384_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1360
	addi a3, zero, 1120
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1312
	addi a3, zero, 1168
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1120
	addi a3, zero, 1216
	call {vg_p384_add_mod_p}
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
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 225
	addi a2, zero, 832
	addi a3, zero, 304
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 609
	addi a2, zero, 2047
	addi a2, a2, 225
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 273
	addi a2, zero, 2047
	addi a2, a2, 225
	addi a3, zero, 2047
	addi a3, a3, 609
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 321
	addi a2, zero, 2047
	addi a2, a2, 273
	addi a3, zero, 2047
	addi a3, a3, 609
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 369
	addi a2, zero, 2047
	addi a2, a2, 321
	addi a3, zero, 2047
	addi a3, a3, 609
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 417
	addi a2, zero, 2047
	addi a2, a2, 369
	addi a3, zero, 2047
	addi a3, a3, 609
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 465
	addi a2, zero, 2047
	addi a2, a2, 417
	addi a3, zero, 2047
	addi a3, a3, 609
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 513
	addi a2, zero, 2047
	addi a2, a2, 465
	addi a3, zero, 2047
	addi a3, a3, 609
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 561
	addi a2, zero, 2047
	addi a2, a2, 513
	addi a3, zero, 2047
	addi a3, a3, 609
	call {vg_p384_mul_mod_p}
	addi t0, s0, 2047
	ld t0, 561(t0)
	sd t0, 1456(s0)
	addi t0, s0, 2047
	ld t0, 569(t0)
	sd t0, 1464(s0)
	addi t0, s0, 2047
	ld t0, 577(t0)
	sd t0, 1472(s0)
	addi t0, s0, 2047
	ld t0, 585(t0)
	sd t0, 1480(s0)
	addi t0, s0, 2047
	ld t0, 593(t0)
	sd t0, 1488(s0)
	addi t0, s0, 2047
	ld t0, 601(t0)
	sd t0, 1496(s0)
	addi s1, zero, 4
286:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 286b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
287:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 287b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
288:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 288b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
289:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 289b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
290:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 290b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
291:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 291b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
292:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 292b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
293:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 293b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
294:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 294b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
295:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 295b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
296:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 296b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
297:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 297b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
298:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 298b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
299:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 299b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2100:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2100b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2101:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2101b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2102:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2102b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2103:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2103b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2104:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2104b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2105:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2105b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2106:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2106b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2107:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2107b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2108:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2108b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2109:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2109b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2110:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2110b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2111:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2111b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2112:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2112b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2113:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2113b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2114:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2114b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2115:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2115b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2116:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2116b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2117:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2117b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2118:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2118b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2119:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2119b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2120:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2120b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2121:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2121b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2122:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2122b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2123:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2123b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2124:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2124b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2125:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2125b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2126:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2126b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2127:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2127b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2128:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2128b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2129:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2129b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2130:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2130b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2131:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2131b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2132:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2132b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2133:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2133b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2134:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2134b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2135:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2135b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2136:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2136b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2137:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2137b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2138:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2138b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2139:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2139b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2140:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2140b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2141:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2141b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2142:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2142b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2143:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2143b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2144:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2144b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2145:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2145b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2146:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2146b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2147:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2147b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 3
2148:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2148b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 369
	call {vg_p384_mul_mod_p}
	addi s1, zero, 5
2149:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2149b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2150:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2150b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2151:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2151b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2152:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2152b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2153:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2153b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2154:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2154b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2155:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2155b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2156:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2156b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 68
2157:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2157b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2158:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2158b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2159:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2159b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2160:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2160b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2161:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2161b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2162:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2162b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2163:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2163b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_p}
	addi s1, zero, 4
2164:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	bnez s1, 2164b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 880
	addi a2, zero, 736
	addi a3, zero, 1456
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 928
	addi a2, zero, 880
	addi a3, zero, 256
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 976
	addi a2, zero, 928
	addi a3, zero, 208
	call {vg_p384_add_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 544
	addi a3, zero, 208
	call {vg_p384_add_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 976
	addi a3, zero, 1024
	call {vg_p384_sub_mod_n}
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
	xori a7, a7, -1
	addi t0, s0, 2047
	ld t0, 129(t0)
	and t0, t0, a7
	addi s0, s0, 2047
	sd t0, 129(s0)
	addi s0, s0, -2047
	addi t3, zero, 0
	ld t4, 1072(s0)
	or t3, t3, t4
	ld t4, 1080(s0)
	or t3, t3, t4
	ld t4, 1088(s0)
	or t3, t3, t4
	ld t4, 1096(s0)
	or t3, t3, t4
	ld t4, 1104(s0)
	or t3, t3, t4
	ld t4, 1112(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	addi t0, s0, 2047
	ld t0, 129(t0)
	and t0, t0, a7
	addi s0, s0, 2047
	sd t0, 129(s0)
	addi s0, s0, -2047
	addi a0, s0, 2047
	ld a0, 129(a0)
	andi a0, a0, 1
	ld ra, 24(s0)
	ld s2, 16(s0)
	ld s1, 8(s0)
	ld s3, 32(s0)
	ld s0, 0(s0)
	ret
	.option pop

vg_ecdsa_p384_sign:
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
	addi sp, sp, -288
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
	addi a3, zero, 48
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 209
	addi a2, s1, 192
	addi a3, zero, 48
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
	addi a3, zero, 48
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 209
	addi a2, s1, 192
	addi a3, zero, 48
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
	lbu t0, 144(s1)
	sb t0, 256(s1)
	lbu t0, 145(s1)
	sb t0, 257(s1)
	lbu t0, 146(s1)
	sb t0, 258(s1)
	lbu t0, 147(s1)
	sb t0, 259(s1)
	lbu t0, 148(s1)
	sb t0, 260(s1)
	lbu t0, 149(s1)
	sb t0, 261(s1)
	lbu t0, 150(s1)
	sb t0, 262(s1)
	lbu t0, 151(s1)
	sb t0, 263(s1)
	lbu t0, 152(s1)
	sb t0, 264(s1)
	lbu t0, 153(s1)
	sb t0, 265(s1)
	lbu t0, 154(s1)
	sb t0, 266(s1)
	lbu t0, 155(s1)
	sb t0, 267(s1)
	lbu t0, 156(s1)
	sb t0, 268(s1)
	lbu t0, 157(s1)
	sb t0, 269(s1)
	lbu t0, 158(s1)
	sb t0, 270(s1)
	lbu t0, 159(s1)
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
	addi a0, s2, 0
	addi a1, s3, 0
	addi a2, s1, 192
	addi a3, s1, 240
	addi a4, s0, 0
	call {vg_ecdsa_p384_sign_k}
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
	ld ra, 0(s1)
	ld s0, 8(s1)
	ld s2, 24(s1)
	ld s3, 32(s1)
	ld s4, 40(s1)
	ld s5, 48(s1)
	ld s6, 56(s1)
	ld s1, 16(s1)
	addi sp, sp, 288
	j 213f
212:
	addi sp, sp, -288
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
	lbu t0, 0(s4)
	sb t0, 212(s1)
	lbu t0, 1(s4)
	sb t0, 213(s1)
	lbu t0, 2(s4)
	sb t0, 214(s1)
	lbu t0, 3(s4)
	sb t0, 215(s1)
	lbu t0, 4(s4)
	sb t0, 216(s1)
	lbu t0, 5(s4)
	sb t0, 217(s1)
	lbu t0, 6(s4)
	sb t0, 218(s1)
	lbu t0, 7(s4)
	sb t0, 219(s1)
	lbu t0, 8(s4)
	sb t0, 220(s1)
	lbu t0, 9(s4)
	sb t0, 221(s1)
	lbu t0, 10(s4)
	sb t0, 222(s1)
	lbu t0, 11(s4)
	sb t0, 223(s1)
	lbu t0, 12(s4)
	sb t0, 224(s1)
	lbu t0, 13(s4)
	sb t0, 225(s1)
	lbu t0, 14(s4)
	sb t0, 226(s1)
	lbu t0, 15(s4)
	sb t0, 227(s1)
	lbu t0, 16(s4)
	sb t0, 228(s1)
	lbu t0, 17(s4)
	sb t0, 229(s1)
	lbu t0, 18(s4)
	sb t0, 230(s1)
	lbu t0, 19(s4)
	sb t0, 231(s1)
	lbu t0, 20(s4)
	sb t0, 232(s1)
	lbu t0, 21(s4)
	sb t0, 233(s1)
	lbu t0, 22(s4)
	sb t0, 234(s1)
	lbu t0, 23(s4)
	sb t0, 235(s1)
	lbu t0, 24(s4)
	sb t0, 236(s1)
	lbu t0, 25(s4)
	sb t0, 237(s1)
	lbu t0, 26(s4)
	sb t0, 238(s1)
	lbu t0, 27(s4)
	sb t0, 239(s1)
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
	addi a3, zero, 48
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 205
	addi a2, s1, 192
	addi a3, zero, 48
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 253
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
	addi a3, zero, 48
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 205
	addi a2, s1, 192
	addi a3, zero, 48
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 253
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
	lbu t0, 144(s1)
	sb t0, 256(s1)
	lbu t0, 145(s1)
	sb t0, 257(s1)
	lbu t0, 146(s1)
	sb t0, 258(s1)
	lbu t0, 147(s1)
	sb t0, 259(s1)
	lbu t0, 148(s1)
	sb t0, 260(s1)
	lbu t0, 149(s1)
	sb t0, 261(s1)
	lbu t0, 150(s1)
	sb t0, 262(s1)
	lbu t0, 151(s1)
	sb t0, 263(s1)
	lbu t0, 152(s1)
	sb t0, 264(s1)
	lbu t0, 153(s1)
	sb t0, 265(s1)
	lbu t0, 154(s1)
	sb t0, 266(s1)
	lbu t0, 155(s1)
	sb t0, 267(s1)
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
	sb t0, 268(s1)
	lbu t0, 129(s1)
	sb t0, 269(s1)
	lbu t0, 130(s1)
	sb t0, 270(s1)
	lbu t0, 131(s1)
	sb t0, 271(s1)
	lbu t0, 132(s1)
	sb t0, 272(s1)
	lbu t0, 133(s1)
	sb t0, 273(s1)
	lbu t0, 134(s1)
	sb t0, 274(s1)
	lbu t0, 135(s1)
	sb t0, 275(s1)
	lbu t0, 136(s1)
	sb t0, 276(s1)
	lbu t0, 137(s1)
	sb t0, 277(s1)
	lbu t0, 138(s1)
	sb t0, 278(s1)
	lbu t0, 139(s1)
	sb t0, 279(s1)
	lbu t0, 140(s1)
	sb t0, 280(s1)
	lbu t0, 141(s1)
	sb t0, 281(s1)
	lbu t0, 142(s1)
	sb t0, 282(s1)
	lbu t0, 143(s1)
	sb t0, 283(s1)
	lbu t0, 144(s1)
	sb t0, 284(s1)
	lbu t0, 145(s1)
	sb t0, 285(s1)
	lbu t0, 146(s1)
	sb t0, 286(s1)
	lbu t0, 147(s1)
	sb t0, 287(s1)
	addi a0, s2, 0
	addi a1, s3, 0
	addi a2, s1, 192
	addi a3, s1, 240
	addi a4, s0, 0
	call {vg_ecdsa_p384_sign_k}
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
	ld ra, 0(s1)
	ld s0, 8(s1)
	ld s2, 24(s1)
	ld s3, 32(s1)
	ld s4, 40(s1)
	ld s5, 48(s1)
	ld s6, 56(s1)
	ld s1, 16(s1)
	addi sp, sp, 288
213:
	j 211f
210:
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
	sd t0, 40(s0)
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
	sd t0, 32(s0)
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
	sd t0, 24(s0)
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
	sd t0, 16(s0)
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
	sd t0, 8(s0)
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
	sd t0, 0(s0)
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
	addi a0, s0, 0
	addi a1, zero, 96
	addi a2, zero, 0
	addi a3, zero, 48
	call {vg_p384_add_mod_n}
	addi a7, zero, -1
	ld t0, 136(s0)
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
	ld t0, 128(s0)
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
	ld t0, 120(s0)
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
	ld t0, 112(s0)
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
	ld t0, 104(s0)
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
	ld t0, 96(s0)
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
	addi a3, zero, 48
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 241
	addi a2, s1, 208
	addi a3, zero, 48
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
	addi a3, zero, 48
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 241
	addi a2, s1, 208
	addi a3, zero, 48
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
	call {vg_ecdsa_p384_sign_k}
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
	ld ra, 0(s1)
	ld s0, 8(s1)
	ld s2, 24(s1)
	ld s3, 32(s1)
	ld s4, 40(s1)
	ld s5, 48(s1)
	ld s6, 56(s1)
	ld s1, 16(s1)
	addi sp, sp, 256
211:
	j 29f
28:
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
	sd t0, 40(s0)
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
	sd t0, 32(s0)
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
	sd t0, 24(s0)
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
	sd t0, 16(s0)
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
	sd t0, 8(s0)
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
	sd t0, 0(s0)
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
	addi a0, s0, 0
	addi a1, zero, 96
	addi a2, zero, 0
	addi a3, zero, 48
	call {vg_p384_add_mod_n}
	addi a7, zero, -1
	ld t0, 136(s0)
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
	ld t0, 128(s0)
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
	ld t0, 120(s0)
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
	ld t0, 112(s0)
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
	ld t0, 104(s0)
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
	ld t0, 96(s0)
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
	addi a3, zero, 48
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 225
	addi a2, s1, 192
	addi a3, zero, 48
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 273
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
	addi a3, zero, 48
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 225
	addi a2, s1, 192
	addi a3, zero, 48
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 273
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
	call {vg_ecdsa_p384_sign_k}
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
	ld ra, 0(s1)
	ld s0, 8(s1)
	ld s2, 24(s1)
	ld s3, 32(s1)
	ld s4, 40(s1)
	ld s5, 48(s1)
	ld s6, 56(s1)
	ld s1, 16(s1)
	addi sp, sp, 240
29:
	j 27f
26:
	addi sp, sp, -288
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
	addi a3, zero, 48
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 145
	addi a2, s1, 192
	addi a3, zero, 48
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 193
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
	addi a3, zero, 48
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 145
	addi a2, s1, 192
	addi a3, zero, 48
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 193
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
	lbu t0, 144(s1)
	sb t0, 256(s1)
	lbu t0, 145(s1)
	sb t0, 257(s1)
	lbu t0, 146(s1)
	sb t0, 258(s1)
	lbu t0, 147(s1)
	sb t0, 259(s1)
	lbu t0, 148(s1)
	sb t0, 260(s1)
	lbu t0, 149(s1)
	sb t0, 261(s1)
	lbu t0, 150(s1)
	sb t0, 262(s1)
	lbu t0, 151(s1)
	sb t0, 263(s1)
	lbu t0, 152(s1)
	sb t0, 264(s1)
	lbu t0, 153(s1)
	sb t0, 265(s1)
	lbu t0, 154(s1)
	sb t0, 266(s1)
	lbu t0, 155(s1)
	sb t0, 267(s1)
	lbu t0, 156(s1)
	sb t0, 268(s1)
	lbu t0, 157(s1)
	sb t0, 269(s1)
	lbu t0, 158(s1)
	sb t0, 270(s1)
	lbu t0, 159(s1)
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
	addi a0, s2, 0
	addi a1, s3, 0
	addi a2, s1, 192
	addi a3, s1, 240
	addi a4, s0, 0
	call {vg_ecdsa_p384_sign_k}
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
	ld ra, 0(s1)
	ld s0, 8(s1)
	ld s2, 24(s1)
	ld s3, 32(s1)
	ld s4, 40(s1)
	ld s5, 48(s1)
	ld s6, 56(s1)
	ld s1, 16(s1)
	addi sp, sp, 288
27:
	j 25f
24:
	addi sp, sp, -288
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
	lbu t0, 0(s4)
	sb t0, 212(s1)
	lbu t0, 1(s4)
	sb t0, 213(s1)
	lbu t0, 2(s4)
	sb t0, 214(s1)
	lbu t0, 3(s4)
	sb t0, 215(s1)
	lbu t0, 4(s4)
	sb t0, 216(s1)
	lbu t0, 5(s4)
	sb t0, 217(s1)
	lbu t0, 6(s4)
	sb t0, 218(s1)
	lbu t0, 7(s4)
	sb t0, 219(s1)
	lbu t0, 8(s4)
	sb t0, 220(s1)
	lbu t0, 9(s4)
	sb t0, 221(s1)
	lbu t0, 10(s4)
	sb t0, 222(s1)
	lbu t0, 11(s4)
	sb t0, 223(s1)
	lbu t0, 12(s4)
	sb t0, 224(s1)
	lbu t0, 13(s4)
	sb t0, 225(s1)
	lbu t0, 14(s4)
	sb t0, 226(s1)
	lbu t0, 15(s4)
	sb t0, 227(s1)
	lbu t0, 16(s4)
	sb t0, 228(s1)
	lbu t0, 17(s4)
	sb t0, 229(s1)
	lbu t0, 18(s4)
	sb t0, 230(s1)
	lbu t0, 19(s4)
	sb t0, 231(s1)
	lbu t0, 20(s4)
	sb t0, 232(s1)
	lbu t0, 21(s4)
	sb t0, 233(s1)
	lbu t0, 22(s4)
	sb t0, 234(s1)
	lbu t0, 23(s4)
	sb t0, 235(s1)
	lbu t0, 24(s4)
	sb t0, 236(s1)
	lbu t0, 25(s4)
	sb t0, 237(s1)
	lbu t0, 26(s4)
	sb t0, 238(s1)
	lbu t0, 27(s4)
	sb t0, 239(s1)
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
	addi a3, zero, 48
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 141
	addi a2, s1, 192
	addi a3, zero, 48
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 189
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
	addi a3, zero, 48
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 141
	addi a2, s1, 192
	addi a3, zero, 48
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 189
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
	lbu t0, 144(s1)
	sb t0, 256(s1)
	lbu t0, 145(s1)
	sb t0, 257(s1)
	lbu t0, 146(s1)
	sb t0, 258(s1)
	lbu t0, 147(s1)
	sb t0, 259(s1)
	lbu t0, 148(s1)
	sb t0, 260(s1)
	lbu t0, 149(s1)
	sb t0, 261(s1)
	lbu t0, 150(s1)
	sb t0, 262(s1)
	lbu t0, 151(s1)
	sb t0, 263(s1)
	lbu t0, 152(s1)
	sb t0, 264(s1)
	lbu t0, 153(s1)
	sb t0, 265(s1)
	lbu t0, 154(s1)
	sb t0, 266(s1)
	lbu t0, 155(s1)
	sb t0, 267(s1)
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
	sb t0, 268(s1)
	lbu t0, 129(s1)
	sb t0, 269(s1)
	lbu t0, 130(s1)
	sb t0, 270(s1)
	lbu t0, 131(s1)
	sb t0, 271(s1)
	lbu t0, 132(s1)
	sb t0, 272(s1)
	lbu t0, 133(s1)
	sb t0, 273(s1)
	lbu t0, 134(s1)
	sb t0, 274(s1)
	lbu t0, 135(s1)
	sb t0, 275(s1)
	lbu t0, 136(s1)
	sb t0, 276(s1)
	lbu t0, 137(s1)
	sb t0, 277(s1)
	lbu t0, 138(s1)
	sb t0, 278(s1)
	lbu t0, 139(s1)
	sb t0, 279(s1)
	lbu t0, 140(s1)
	sb t0, 280(s1)
	lbu t0, 141(s1)
	sb t0, 281(s1)
	lbu t0, 142(s1)
	sb t0, 282(s1)
	lbu t0, 143(s1)
	sb t0, 283(s1)
	lbu t0, 144(s1)
	sb t0, 284(s1)
	lbu t0, 145(s1)
	sb t0, 285(s1)
	lbu t0, 146(s1)
	sb t0, 286(s1)
	lbu t0, 147(s1)
	sb t0, 287(s1)
	addi a0, s2, 0
	addi a1, s3, 0
	addi a2, s1, 192
	addi a3, s1, 240
	addi a4, s0, 0
	call {vg_ecdsa_p384_sign_k}
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
	ld ra, 0(s1)
	ld s0, 8(s1)
	ld s2, 24(s1)
	ld s3, 32(s1)
	ld s4, 40(s1)
	ld s5, 48(s1)
	ld s6, 56(s1)
	ld s1, 16(s1)
	addi sp, sp, 288
25:
	j 23f
22:
	addi sp, sp, -288
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
	lbu t0, 0(s4)
	sb t0, 220(s1)
	lbu t0, 1(s4)
	sb t0, 221(s1)
	lbu t0, 2(s4)
	sb t0, 222(s1)
	lbu t0, 3(s4)
	sb t0, 223(s1)
	lbu t0, 4(s4)
	sb t0, 224(s1)
	lbu t0, 5(s4)
	sb t0, 225(s1)
	lbu t0, 6(s4)
	sb t0, 226(s1)
	lbu t0, 7(s4)
	sb t0, 227(s1)
	lbu t0, 8(s4)
	sb t0, 228(s1)
	lbu t0, 9(s4)
	sb t0, 229(s1)
	lbu t0, 10(s4)
	sb t0, 230(s1)
	lbu t0, 11(s4)
	sb t0, 231(s1)
	lbu t0, 12(s4)
	sb t0, 232(s1)
	lbu t0, 13(s4)
	sb t0, 233(s1)
	lbu t0, 14(s4)
	sb t0, 234(s1)
	lbu t0, 15(s4)
	sb t0, 235(s1)
	lbu t0, 16(s4)
	sb t0, 236(s1)
	lbu t0, 17(s4)
	sb t0, 237(s1)
	lbu t0, 18(s4)
	sb t0, 238(s1)
	lbu t0, 19(s4)
	sb t0, 239(s1)
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
	addi a3, zero, 48
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 133
	addi a2, s1, 192
	addi a3, zero, 48
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 181
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
	addi a3, zero, 48
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 133
	addi a2, s1, 192
	addi a3, zero, 48
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 181
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
	lbu t0, 144(s1)
	sb t0, 256(s1)
	lbu t0, 145(s1)
	sb t0, 257(s1)
	lbu t0, 146(s1)
	sb t0, 258(s1)
	lbu t0, 147(s1)
	sb t0, 259(s1)
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
	sb t0, 260(s1)
	lbu t0, 129(s1)
	sb t0, 261(s1)
	lbu t0, 130(s1)
	sb t0, 262(s1)
	lbu t0, 131(s1)
	sb t0, 263(s1)
	lbu t0, 132(s1)
	sb t0, 264(s1)
	lbu t0, 133(s1)
	sb t0, 265(s1)
	lbu t0, 134(s1)
	sb t0, 266(s1)
	lbu t0, 135(s1)
	sb t0, 267(s1)
	lbu t0, 136(s1)
	sb t0, 268(s1)
	lbu t0, 137(s1)
	sb t0, 269(s1)
	lbu t0, 138(s1)
	sb t0, 270(s1)
	lbu t0, 139(s1)
	sb t0, 271(s1)
	lbu t0, 140(s1)
	sb t0, 272(s1)
	lbu t0, 141(s1)
	sb t0, 273(s1)
	lbu t0, 142(s1)
	sb t0, 274(s1)
	lbu t0, 143(s1)
	sb t0, 275(s1)
	lbu t0, 144(s1)
	sb t0, 276(s1)
	lbu t0, 145(s1)
	sb t0, 277(s1)
	lbu t0, 146(s1)
	sb t0, 278(s1)
	lbu t0, 147(s1)
	sb t0, 279(s1)
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
	sb t0, 280(s1)
	lbu t0, 129(s1)
	sb t0, 281(s1)
	lbu t0, 130(s1)
	sb t0, 282(s1)
	lbu t0, 131(s1)
	sb t0, 283(s1)
	lbu t0, 132(s1)
	sb t0, 284(s1)
	lbu t0, 133(s1)
	sb t0, 285(s1)
	lbu t0, 134(s1)
	sb t0, 286(s1)
	lbu t0, 135(s1)
	sb t0, 287(s1)
	addi a0, s2, 0
	addi a1, s3, 0
	addi a2, s1, 192
	addi a3, s1, 240
	addi a4, s0, 0
	call {vg_ecdsa_p384_sign_k}
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
	ld ra, 0(s1)
	ld s0, 8(s1)
	ld s2, 24(s1)
	ld s3, 32(s1)
	ld s4, 40(s1)
	ld s5, 48(s1)
	ld s6, 56(s1)
	ld s1, 16(s1)
	addi sp, sp, 288
23:
	j 21f
20:
	addi sp, sp, -288
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
	addi a3, zero, 48
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 129
	addi a2, s1, 192
	addi a3, zero, 48
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 177
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
	addi a3, zero, 48
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 129
	addi a2, s1, 192
	addi a3, zero, 48
	ld t1, 8(s6)
	jalr ra, 0(t1)
	addi a0, s0, 0
	addi a1, zero, 177
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
	addi a0, s2, 0
	addi a1, s3, 0
	addi a2, s1, 192
	addi a3, s1, 240
	addi a4, s0, 0
	call {vg_ecdsa_p384_sign_k}
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
	ld ra, 0(s1)
	ld s0, 8(s1)
	ld s2, 24(s1)
	ld s3, 32(s1)
	ld s4, 40(s1)
	ld s5, 48(s1)
	ld s6, 56(s1)
	ld s1, 16(s1)
	addi sp, sp, 288
21:
	ret
	.option pop
