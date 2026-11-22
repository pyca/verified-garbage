// The functions of `src/ec_p521.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ec_p521_public_key:
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
	addi t0, zero, 0
	slli t0, t0, 8
	lbu t1, 0(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 1(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 313(s0)
	addi s0, s0, -2047
	lbu t0, 2(a1)
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
	slli t0, t0, 8
	lbu t1, 9(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 305(s0)
	addi s0, s0, -2047
	lbu t0, 10(a1)
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
	slli t0, t0, 8
	lbu t1, 17(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 297(s0)
	addi s0, s0, -2047
	lbu t0, 18(a1)
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
	slli t0, t0, 8
	lbu t1, 25(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 289(s0)
	addi s0, s0, -2047
	lbu t0, 26(a1)
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
	slli t0, t0, 8
	lbu t1, 33(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 281(s0)
	addi s0, s0, -2047
	lbu t0, 34(a1)
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
	slli t0, t0, 8
	lbu t1, 41(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 273(s0)
	addi s0, s0, -2047
	lbu t0, 42(a1)
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
	slli t0, t0, 8
	lbu t1, 49(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 265(s0)
	addi s0, s0, -2047
	lbu t0, 50(a1)
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
	slli t0, t0, 8
	lbu t1, 57(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 257(s0)
	addi s0, s0, -2047
	lbu t0, 58(a1)
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
	slli t0, t0, 8
	lbu t1, 65(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 249(s0)
	addi s0, s0, -2047
	addi t0, zero, 0
	addi t0, t0, -1
	addi s0, s0, 2047
	sd t0, 1185(s0)
	addi s0, s0, -2047
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
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
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
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
	addiw t1, t1, 511
	add t0, t0, t1
	sd t0, 128(s0)
	lui t0, 767739
	addiw t0, t0, 1823
	slli t0, t0, 32
	lui t1, 594822
	addiw t1, t1, 1033
	add t0, t0, t1
	sd t0, 136(s0)
	lui t0, 244573
	addiw t0, t0, -1607
	slli t0, t0, 32
	lui t1, 563652
	addiw t1, t1, 1966
	add t0, t0, t1
	sd t0, 144(s0)
	lui t0, 523456
	addiw t0, t0, 329
	slli t0, t0, 32
	lui t1, 1011866
	addiw t1, t1, 1488
	add t0, t0, t1
	sd t0, 152(s0)
	lui t0, 333928
	addiw t0, t0, 1924
	slli t0, t0, 32
	lui t1, 783097
	addiw t1, t1, 1643
	add t0, t0, t1
	sd t0, 160(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -6
	add t0, t0, t1
	sd t0, 168(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 176(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 184(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 192(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 511
	add t0, t0, t1
	sd t0, 200(s0)
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
	addiw t1, t1, 0
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
	addiw t1, t1, 1
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
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 384(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 392(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 400(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 408(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 416(s0)
	lui t0, 2048
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 424(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 432(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 440(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 448(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 456(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 464(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 472(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 480(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 488(s0)
	lui t0, 1042432
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 496(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 504(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 512(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 520(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 528(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 536(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 544(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 552(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 511
	add t0, t0, t1
	sd t0, 560(s0)
	lui t0, 525267
	addiw t0, t0, -17
	slli t0, t0, 32
	lui t1, 45203
	addiw t1, t1, -1387
	add t0, t0, t1
	sd t0, 568(s0)
	lui t0, 437870
	addiw t0, t0, 1968
	slli t0, t0, 32
	lui t1, 780816
	addiw t1, t1, -1954
	add t0, t0, t1
	sd t0, 576(s0)
	lui t0, 568579
	addiw t0, t0, -561
	slli t0, t0, 32
	lui t1, 312764
	addiw t1, t1, 591
	add t0, t0, t1
	sd t0, 584(s0)
	lui t0, 231960
	addiw t0, t0, -991
	slli t0, t0, 32
	lui t1, 114073
	addiw t1, t1, -1378
	add t0, t0, t1
	sd t0, 592(s0)
	lui t0, 860178
	addiw t0, t0, 1494
	slli t0, t0, 32
	lui t1, 1027628
	addiw t1, t1, -547
	add t0, t0, t1
	sd t0, 600(s0)
	lui t0, 973137
	addiw t0, t0, -306
	slli t0, t0, 32
	lui t1, 370023
	addiw t1, t1, -1650
	add t0, t0, t1
	sd t0, 608(s0)
	lui t0, 417604
	addiw t0, t0, 1964
	slli t0, t0, 32
	lui t1, 562793
	addiw t1, t1, -864
	add t0, t0, t1
	sd t0, 616(s0)
	lui t0, 193982
	addiw t0, t0, 1842
	slli t0, t0, 32
	lui t1, 463132
	addiw t1, t1, 2017
	add t0, t0, t1
	sd t0, 624(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 231
	add t0, t0, t1
	sd t0, 632(s0)
	lui t0, 733978
	addiw t0, t0, 356
	slli t0, t0, 32
	lui t1, 531164
	addiw t1, t1, 257
	add t0, t0, t1
	sd t0, 640(s0)
	lui t0, 319436
	addiw t0, t0, -193
	slli t0, t0, 32
	lui t1, 101911
	addiw t1, t1, 734
	add t0, t0, t1
	sd t0, 648(s0)
	lui t0, 455066
	addiw t0, t0, 1114
	slli t0, t0, 32
	lui t1, 920619
	addiw t1, t1, 1313
	add t0, t0, t1
	sd t0, 656(s0)
	lui t0, 608241
	addiw t0, t0, -287
	slli t0, t0, 32
	lui t1, 605464
	addiw t1, t1, -44
	add t0, t0, t1
	sd t0, 664(s0)
	lui t0, 906506
	addiw t0, t0, 1455
	slli t0, t0, 32
	lui t1, 245631
	addiw t1, t1, 940
	add t0, t0, t1
	sd t0, 672(s0)
	lui t0, 593857
	addiw t0, t0, 1112
	slli t0, t0, 32
	lui t1, 721754
	addiw t1, t1, 1694
	add t0, t0, t1
	sd t0, 680(s0)
	lui t0, 136419
	addiw t0, t0, 577
	slli t0, t0, 32
	lui t1, 641066
	addiw t1, t1, -38
	add t0, t0, t1
	sd t0, 688(s0)
	lui t0, 945394
	addiw t0, t0, -154
	slli t0, t0, 32
	lui t1, 733469
	addiw t1, t1, -1318
	add t0, t0, t1
	sd t0, 696(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 116
	add t0, t0, t1
	sd t0, 704(s0)
	lui t0, 164961
	addiw t0, t0, -438
	slli t0, t0, 32
	lui t1, 371170
	addiw t1, t1, 1678
	add t0, t0, t1
	sd t0, 712(s0)
	lui t0, 132166
	addiw t0, t0, -182
	slli t0, t0, 32
	lui t1, 242943
	addiw t1, t1, -1869
	add t0, t0, t1
	sd t0, 720(s0)
	lui t0, 723370
	addiw t0, t0, -456
	slli t0, t0, 32
	lui t1, 275732
	addiw t1, t1, -1695
	add t0, t0, t1
	sd t0, 728(s0)
	lui t0, 132651
	addiw t0, t0, -1955
	slli t0, t0, 32
	lui t1, 526845
	addiw t1, t1, 1667
	add t0, t0, t1
	sd t0, 736(s0)
	lui t0, 91327
	addiw t0, t0, 1849
	slli t0, t0, 32
	lui t1, 314104
	addiw t1, t1, -1517
	add t0, t0, t1
	sd t0, 744(s0)
	lui t0, 213181
	addiw t0, t0, 2015
	slli t0, t0, 32
	lui t1, 571706
	addiw t1, t1, -205
	add t0, t0, t1
	sd t0, 752(s0)
	lui t0, 969928
	addiw t0, t0, -1374
	slli t0, t0, 32
	lui t1, 150205
	addiw t1, t1, -606
	add t0, t0, t1
	sd t0, 760(s0)
	lui t0, 8932
	addiw t0, t0, 1328
	slli t0, t0, 32
	lui t1, 893284
	addiw t1, t1, -371
	add t0, t0, t1
	sd t0, 768(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 480
	add t0, t0, t1
	sd t0, 776(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -3
	add t0, t0, t1
	sd t0, 928(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 936(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 944(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 952(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 960(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 968(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 976(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 984(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 511
	add t0, t0, t1
	sd t0, 992(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 825(s0)
	addi s0, s0, -2047
	lui t0, 4
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 833(s0)
	addi s0, s0, -2047
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 841(s0)
	addi s0, s0, -2047
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 849(s0)
	addi s0, s0, -2047
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 857(s0)
	addi s0, s0, -2047
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 865(s0)
	addi s0, s0, -2047
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 873(s0)
	addi s0, s0, -2047
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 881(s0)
	addi s0, s0, -2047
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 889(s0)
	addi s0, s0, -2047
	lui t0, 524614
	addiw t0, t0, 1360
	slli t0, t0, 32
	lui t1, 714118
	addiw t1, t1, 903
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 897(s0)
	addi s0, s0, -2047
	lui t0, 495482
	addiw t0, t0, 656
	slli t0, t0, 32
	lui t1, 959323
	addiw t1, t1, -2017
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 905(s0)
	addi s0, s0, -2047
	lui t0, 539052
	addiw t0, t0, -1552
	slli t0, t0, 32
	lui t1, 803305
	addiw t1, t1, 1562
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 913(s0)
	addi s0, s0, -2047
	lui t0, 776371
	addiw t0, t0, -1696
	slli t0, t0, 32
	lui t1, 387550
	addiw t1, t1, -1825
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 921(s0)
	addi s0, s0, -2047
	lui t0, 985777
	addiw t0, t0, -867
	slli t0, t0, 32
	lui t1, 692068
	addiw t1, t1, -183
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 929(s0)
	addi s0, s0, -2047
	lui t0, 1023430
	addiw t0, t0, -1467
	slli t0, t0, 32
	lui t1, 822392
	addiw t1, t1, -1916
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 937(s0)
	addi s0, s0, -2047
	lui t0, 488727
	addiw t0, t0, -711
	slli t0, t0, 32
	lui t1, 187598
	addiw t1, t1, -1654
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 945(s0)
	addi s0, s0, -2047
	lui t0, 64661
	addiw t0, t0, -751
	slli t0, t0, 32
	lui t1, 853428
	addiw t1, t1, 672
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 953(s0)
	addi s0, s0, -2047
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 77
	add t0, t0, t1
	addi s0, s0, 2047
	sd t0, 961(s0)
	addi s0, s0, -2047
	ld t0, 640(s0)
	sd t0, 1072(s0)
	ld t0, 648(s0)
	sd t0, 1080(s0)
	ld t0, 656(s0)
	sd t0, 1088(s0)
	ld t0, 664(s0)
	sd t0, 1096(s0)
	ld t0, 672(s0)
	sd t0, 1104(s0)
	ld t0, 680(s0)
	sd t0, 1112(s0)
	ld t0, 688(s0)
	sd t0, 1120(s0)
	ld t0, 696(s0)
	sd t0, 1128(s0)
	ld t0, 704(s0)
	sd t0, 1136(s0)
	ld t0, 712(s0)
	sd t0, 1144(s0)
	ld t0, 720(s0)
	sd t0, 1152(s0)
	ld t0, 728(s0)
	sd t0, 1160(s0)
	ld t0, 736(s0)
	sd t0, 1168(s0)
	ld t0, 744(s0)
	sd t0, 1176(s0)
	ld t0, 752(s0)
	sd t0, 1184(s0)
	ld t0, 760(s0)
	sd t0, 1192(s0)
	ld t0, 768(s0)
	sd t0, 1200(s0)
	ld t0, 776(s0)
	sd t0, 1208(s0)
	addi t5, zero, 0
	addi t3, s0, 2047
	ld t3, 249(t3)
	ld t4, 136(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t3, s0, 2047
	ld t3, 257(t3)
	ld t4, 144(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t3, s0, 2047
	ld t3, 265(t3)
	ld t4, 152(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t3, s0, 2047
	ld t3, 273(t3)
	ld t4, 160(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t3, s0, 2047
	ld t3, 281(t3)
	ld t4, 168(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t3, s0, 2047
	ld t3, 289(t3)
	ld t4, 176(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t3, s0, 2047
	ld t3, 297(t3)
	ld t4, 184(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t3, s0, 2047
	ld t3, 305(t3)
	ld t4, 192(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t3, s0, 2047
	ld t3, 313(t3)
	ld t4, 200(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t6, zero, 0
	sub a7, t6, t5
	addi t0, s0, 2047
	ld t0, 1185(t0)
	and t0, t0, a7
	addi s0, s0, 2047
	sd t0, 1185(s0)
	addi s0, s0, -2047
	addi t3, zero, 0
	addi t4, s0, 2047
	ld t4, 249(t4)
	or t3, t3, t4
	addi t4, s0, 2047
	ld t4, 257(t4)
	or t3, t3, t4
	addi t4, s0, 2047
	ld t4, 265(t4)
	or t3, t3, t4
	addi t4, s0, 2047
	ld t4, 273(t4)
	or t3, t3, t4
	addi t4, s0, 2047
	ld t4, 281(t4)
	or t3, t3, t4
	addi t4, s0, 2047
	ld t4, 289(t4)
	or t3, t3, t4
	addi t4, s0, 2047
	ld t4, 297(t4)
	or t3, t3, t4
	addi t4, s0, 2047
	ld t4, 305(t4)
	or t3, t3, t4
	addi t4, s0, 2047
	ld t4, 313(t4)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	xori a7, a7, -1
	addi t0, s0, 2047
	ld t0, 1185(t0)
	and t0, t0, a7
	addi s0, s0, 2047
	sd t0, 1185(s0)
	addi s0, s0, -2047
	addi a0, s0, 0
	call {vg_p521_mul_g}
	addi s0, s3, 0
	call {vg_p521_inv_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1288
	addi a2, zero, 1072
	addi a3, zero, 2047
	addi a3, a3, 105
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1288
	addi a3, zero, 352
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1432
	addi a2, zero, 1144
	addi a3, zero, 2047
	addi a3, a3, 105
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1504
	addi a2, zero, 1432
	addi a3, zero, 352
	call {vg_p521_mul_mod_p}
	addi t3, zero, 0
	ld t4, 1216(s0)
	or t3, t3, t4
	ld t4, 1224(s0)
	or t3, t3, t4
	ld t4, 1232(s0)
	or t3, t3, t4
	ld t4, 1240(s0)
	or t3, t3, t4
	ld t4, 1248(s0)
	or t3, t3, t4
	ld t4, 1256(s0)
	or t3, t3, t4
	ld t4, 1264(s0)
	or t3, t3, t4
	ld t4, 1272(s0)
	or t3, t3, t4
	ld t4, 1280(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	xori a7, a7, -1
	addi t0, s0, 2047
	ld t0, 1185(t0)
	and t0, t0, a7
	addi s0, s0, 2047
	sd t0, 1185(s0)
	addi s0, s0, -2047
	addi a7, s0, 2047
	ld a7, 1185(a7)
	addi t0, zero, 4
	and t0, t0, a7
	sb t0, 0(s2)
	ld t0, 1424(s0)
	and t0, t0, a7
	srli t1, t0, 8
	sb t1, 1(s2)
	srli t1, t0, 0
	sb t1, 2(s2)
	ld t0, 1416(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 3(s2)
	srli t1, t0, 48
	sb t1, 4(s2)
	srli t1, t0, 40
	sb t1, 5(s2)
	srli t1, t0, 32
	sb t1, 6(s2)
	srli t1, t0, 24
	sb t1, 7(s2)
	srli t1, t0, 16
	sb t1, 8(s2)
	srli t1, t0, 8
	sb t1, 9(s2)
	srli t1, t0, 0
	sb t1, 10(s2)
	ld t0, 1408(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 11(s2)
	srli t1, t0, 48
	sb t1, 12(s2)
	srli t1, t0, 40
	sb t1, 13(s2)
	srli t1, t0, 32
	sb t1, 14(s2)
	srli t1, t0, 24
	sb t1, 15(s2)
	srli t1, t0, 16
	sb t1, 16(s2)
	srli t1, t0, 8
	sb t1, 17(s2)
	srli t1, t0, 0
	sb t1, 18(s2)
	ld t0, 1400(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 19(s2)
	srli t1, t0, 48
	sb t1, 20(s2)
	srli t1, t0, 40
	sb t1, 21(s2)
	srli t1, t0, 32
	sb t1, 22(s2)
	srli t1, t0, 24
	sb t1, 23(s2)
	srli t1, t0, 16
	sb t1, 24(s2)
	srli t1, t0, 8
	sb t1, 25(s2)
	srli t1, t0, 0
	sb t1, 26(s2)
	ld t0, 1392(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 27(s2)
	srli t1, t0, 48
	sb t1, 28(s2)
	srli t1, t0, 40
	sb t1, 29(s2)
	srli t1, t0, 32
	sb t1, 30(s2)
	srli t1, t0, 24
	sb t1, 31(s2)
	srli t1, t0, 16
	sb t1, 32(s2)
	srli t1, t0, 8
	sb t1, 33(s2)
	srli t1, t0, 0
	sb t1, 34(s2)
	ld t0, 1384(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 35(s2)
	srli t1, t0, 48
	sb t1, 36(s2)
	srli t1, t0, 40
	sb t1, 37(s2)
	srli t1, t0, 32
	sb t1, 38(s2)
	srli t1, t0, 24
	sb t1, 39(s2)
	srli t1, t0, 16
	sb t1, 40(s2)
	srli t1, t0, 8
	sb t1, 41(s2)
	srli t1, t0, 0
	sb t1, 42(s2)
	ld t0, 1376(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 43(s2)
	srli t1, t0, 48
	sb t1, 44(s2)
	srli t1, t0, 40
	sb t1, 45(s2)
	srli t1, t0, 32
	sb t1, 46(s2)
	srli t1, t0, 24
	sb t1, 47(s2)
	srli t1, t0, 16
	sb t1, 48(s2)
	srli t1, t0, 8
	sb t1, 49(s2)
	srli t1, t0, 0
	sb t1, 50(s2)
	ld t0, 1368(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 51(s2)
	srli t1, t0, 48
	sb t1, 52(s2)
	srli t1, t0, 40
	sb t1, 53(s2)
	srli t1, t0, 32
	sb t1, 54(s2)
	srli t1, t0, 24
	sb t1, 55(s2)
	srli t1, t0, 16
	sb t1, 56(s2)
	srli t1, t0, 8
	sb t1, 57(s2)
	srli t1, t0, 0
	sb t1, 58(s2)
	ld t0, 1360(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 59(s2)
	srli t1, t0, 48
	sb t1, 60(s2)
	srli t1, t0, 40
	sb t1, 61(s2)
	srli t1, t0, 32
	sb t1, 62(s2)
	srli t1, t0, 24
	sb t1, 63(s2)
	srli t1, t0, 16
	sb t1, 64(s2)
	srli t1, t0, 8
	sb t1, 65(s2)
	srli t1, t0, 0
	sb t1, 66(s2)
	ld t0, 1568(s0)
	and t0, t0, a7
	srli t1, t0, 8
	sb t1, 67(s2)
	srli t1, t0, 0
	sb t1, 68(s2)
	ld t0, 1560(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 69(s2)
	srli t1, t0, 48
	sb t1, 70(s2)
	srli t1, t0, 40
	sb t1, 71(s2)
	srli t1, t0, 32
	sb t1, 72(s2)
	srli t1, t0, 24
	sb t1, 73(s2)
	srli t1, t0, 16
	sb t1, 74(s2)
	srli t1, t0, 8
	sb t1, 75(s2)
	srli t1, t0, 0
	sb t1, 76(s2)
	ld t0, 1552(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 77(s2)
	srli t1, t0, 48
	sb t1, 78(s2)
	srli t1, t0, 40
	sb t1, 79(s2)
	srli t1, t0, 32
	sb t1, 80(s2)
	srli t1, t0, 24
	sb t1, 81(s2)
	srli t1, t0, 16
	sb t1, 82(s2)
	srli t1, t0, 8
	sb t1, 83(s2)
	srli t1, t0, 0
	sb t1, 84(s2)
	ld t0, 1544(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 85(s2)
	srli t1, t0, 48
	sb t1, 86(s2)
	srli t1, t0, 40
	sb t1, 87(s2)
	srli t1, t0, 32
	sb t1, 88(s2)
	srli t1, t0, 24
	sb t1, 89(s2)
	srli t1, t0, 16
	sb t1, 90(s2)
	srli t1, t0, 8
	sb t1, 91(s2)
	srli t1, t0, 0
	sb t1, 92(s2)
	ld t0, 1536(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 93(s2)
	srli t1, t0, 48
	sb t1, 94(s2)
	srli t1, t0, 40
	sb t1, 95(s2)
	srli t1, t0, 32
	sb t1, 96(s2)
	srli t1, t0, 24
	sb t1, 97(s2)
	srli t1, t0, 16
	sb t1, 98(s2)
	srli t1, t0, 8
	sb t1, 99(s2)
	srli t1, t0, 0
	sb t1, 100(s2)
	ld t0, 1528(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 101(s2)
	srli t1, t0, 48
	sb t1, 102(s2)
	srli t1, t0, 40
	sb t1, 103(s2)
	srli t1, t0, 32
	sb t1, 104(s2)
	srli t1, t0, 24
	sb t1, 105(s2)
	srli t1, t0, 16
	sb t1, 106(s2)
	srli t1, t0, 8
	sb t1, 107(s2)
	srli t1, t0, 0
	sb t1, 108(s2)
	ld t0, 1520(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 109(s2)
	srli t1, t0, 48
	sb t1, 110(s2)
	srli t1, t0, 40
	sb t1, 111(s2)
	srli t1, t0, 32
	sb t1, 112(s2)
	srli t1, t0, 24
	sb t1, 113(s2)
	srli t1, t0, 16
	sb t1, 114(s2)
	srli t1, t0, 8
	sb t1, 115(s2)
	srli t1, t0, 0
	sb t1, 116(s2)
	ld t0, 1512(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 117(s2)
	srli t1, t0, 48
	sb t1, 118(s2)
	srli t1, t0, 40
	sb t1, 119(s2)
	srli t1, t0, 32
	sb t1, 120(s2)
	srli t1, t0, 24
	sb t1, 121(s2)
	srli t1, t0, 16
	sb t1, 122(s2)
	srli t1, t0, 8
	sb t1, 123(s2)
	srli t1, t0, 0
	sb t1, 124(s2)
	ld t0, 1504(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 125(s2)
	srli t1, t0, 48
	sb t1, 126(s2)
	srli t1, t0, 40
	sb t1, 127(s2)
	srli t1, t0, 32
	sb t1, 128(s2)
	srli t1, t0, 24
	sb t1, 129(s2)
	srli t1, t0, 16
	sb t1, 130(s2)
	srli t1, t0, 8
	sb t1, 131(s2)
	srli t1, t0, 0
	sb t1, 132(s2)
	addi a0, s0, 2047
	ld a0, 1185(a0)
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
