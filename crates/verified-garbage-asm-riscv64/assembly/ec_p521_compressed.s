// The functions of `src/ec_p521_compressed.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ec_p521_compress_public_key:
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
	lbu t1, 1(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 2(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 457(s0)
	addi s0, s0, -2047
	lbu t0, 3(a1)
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
	slli t0, t0, 8
	lbu t1, 10(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 449(s0)
	addi s0, s0, -2047
	lbu t0, 11(a1)
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
	slli t0, t0, 8
	lbu t1, 18(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 441(s0)
	addi s0, s0, -2047
	lbu t0, 19(a1)
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
	slli t0, t0, 8
	lbu t1, 26(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 433(s0)
	addi s0, s0, -2047
	lbu t0, 27(a1)
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
	slli t0, t0, 8
	lbu t1, 34(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 425(s0)
	addi s0, s0, -2047
	lbu t0, 35(a1)
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
	slli t0, t0, 8
	lbu t1, 42(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 417(s0)
	addi s0, s0, -2047
	lbu t0, 43(a1)
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
	slli t0, t0, 8
	lbu t1, 50(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 409(s0)
	addi s0, s0, -2047
	lbu t0, 51(a1)
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
	slli t0, t0, 8
	lbu t1, 58(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 401(s0)
	addi s0, s0, -2047
	lbu t0, 59(a1)
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
	slli t0, t0, 8
	lbu t1, 66(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 393(s0)
	addi s0, s0, -2047
	addi t0, zero, 0
	slli t0, t0, 8
	lbu t1, 67(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 68(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 673(s0)
	addi s0, s0, -2047
	lbu t0, 69(a1)
	slli t0, t0, 8
	lbu t1, 70(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 71(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 72(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 73(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 74(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 75(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 76(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 665(s0)
	addi s0, s0, -2047
	lbu t0, 77(a1)
	slli t0, t0, 8
	lbu t1, 78(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 79(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 80(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 81(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 82(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 83(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 84(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 657(s0)
	addi s0, s0, -2047
	lbu t0, 85(a1)
	slli t0, t0, 8
	lbu t1, 86(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 87(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 88(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 89(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 90(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 91(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 92(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 649(s0)
	addi s0, s0, -2047
	lbu t0, 93(a1)
	slli t0, t0, 8
	lbu t1, 94(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 95(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 96(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 97(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 98(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 99(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 100(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 641(s0)
	addi s0, s0, -2047
	lbu t0, 101(a1)
	slli t0, t0, 8
	lbu t1, 102(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 103(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 104(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 105(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 106(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 107(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 108(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 633(s0)
	addi s0, s0, -2047
	lbu t0, 109(a1)
	slli t0, t0, 8
	lbu t1, 110(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 111(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 112(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 113(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 114(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 115(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 116(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 625(s0)
	addi s0, s0, -2047
	lbu t0, 117(a1)
	slli t0, t0, 8
	lbu t1, 118(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 119(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 120(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 121(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 122(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 123(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 124(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 617(s0)
	addi s0, s0, -2047
	lbu t0, 125(a1)
	slli t0, t0, 8
	lbu t1, 126(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 127(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 128(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 129(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 130(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 131(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 132(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 609(s0)
	addi s0, s0, -2047
	lbu t0, 0(a1)
	xori t0, t0, 4
	addi t0, t0, -1
	srli t0, t0, 63
	addi t1, zero, 0
	sub a7, t1, t0
	addi s0, s0, 2047
	sd a7, 1185(s0)
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
	addi a0, s0, 0
	call {vg_p521_check_point}
	addi s0, s3, 0
	addi a7, s0, 2047
	ld a7, 1185(a7)
	addi t0, s0, 2047
	ld t0, 609(t0)
	andi t0, t0, 1
	addi t0, t0, 2
	and t0, t0, a7
	sb t0, 0(s2)
	addi t0, s0, 2047
	ld t0, 457(t0)
	and t0, t0, a7
	srli t1, t0, 8
	sb t1, 1(s2)
	srli t1, t0, 0
	sb t1, 2(s2)
	addi t0, s0, 2047
	ld t0, 449(t0)
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
	addi t0, s0, 2047
	ld t0, 441(t0)
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
	addi t0, s0, 2047
	ld t0, 433(t0)
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
	addi t0, s0, 2047
	ld t0, 425(t0)
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
	addi t0, s0, 2047
	ld t0, 417(t0)
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
	addi t0, s0, 2047
	ld t0, 409(t0)
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
	addi t0, s0, 2047
	ld t0, 401(t0)
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
	addi t0, s0, 2047
	ld t0, 393(t0)
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
	addi a0, s0, 2047
	ld a0, 1185(a0)
	andi a0, a0, 1
	ld ra, 24(s0)
	ld s2, 16(s0)
	ld s1, 8(s0)
	ld s3, 32(s0)
	ld s0, 0(s0)
	ret
	.option pop

vg_ec_p521_decompress_public_key:
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
	lbu t1, 1(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 2(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 457(s0)
	addi s0, s0, -2047
	lbu t0, 3(a1)
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
	slli t0, t0, 8
	lbu t1, 10(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 449(s0)
	addi s0, s0, -2047
	lbu t0, 11(a1)
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
	slli t0, t0, 8
	lbu t1, 18(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 441(s0)
	addi s0, s0, -2047
	lbu t0, 19(a1)
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
	slli t0, t0, 8
	lbu t1, 26(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 433(s0)
	addi s0, s0, -2047
	lbu t0, 27(a1)
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
	slli t0, t0, 8
	lbu t1, 34(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 425(s0)
	addi s0, s0, -2047
	lbu t0, 35(a1)
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
	slli t0, t0, 8
	lbu t1, 42(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 417(s0)
	addi s0, s0, -2047
	lbu t0, 43(a1)
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
	slli t0, t0, 8
	lbu t1, 50(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 409(s0)
	addi s0, s0, -2047
	lbu t0, 51(a1)
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
	slli t0, t0, 8
	lbu t1, 58(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 401(s0)
	addi s0, s0, -2047
	lbu t0, 59(a1)
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
	slli t0, t0, 8
	lbu t1, 66(a1)
	or t0, t0, t1
	addi s0, s0, 2047
	sd t0, 393(s0)
	addi s0, s0, -2047
	lbu t0, 0(a1)
	andi t0, t0, 1
	sd t0, 784(s0)
	lbu t0, 0(a1)
	xori t0, t0, 2
	srli t0, t0, 1
	addi t0, t0, -1
	srli t0, t0, 63
	addi t1, zero, 0
	sub a7, t1, t0
	addi s0, s0, 2047
	sd a7, 1185(s0)
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
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 856(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 864(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 872(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 880(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 888(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 896(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 904(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 912(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 128
	add t0, t0, t1
	sd t0, 920(s0)
	addi t5, zero, 0
	addi t3, s0, 2047
	ld t3, 393(t3)
	ld t4, 64(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t3, s0, 2047
	ld t3, 401(t3)
	ld t4, 72(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t3, s0, 2047
	ld t3, 409(t3)
	ld t4, 80(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t3, s0, 2047
	ld t3, 417(t3)
	ld t4, 88(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t3, s0, 2047
	ld t3, 425(t3)
	ld t4, 96(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t3, s0, 2047
	ld t3, 433(t3)
	ld t4, 104(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t3, s0, 2047
	ld t3, 441(t3)
	ld t4, 112(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t3, s0, 2047
	ld t3, 449(t3)
	ld t4, 120(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t3, s0, 2047
	ld t3, 457(t3)
	ld t4, 128(s0)
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
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 465
	addi a2, zero, 2047
	addi a2, a2, 393
	addi a3, zero, 2047
	addi a3, a3, 825
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1720
	addi a2, zero, 2047
	addi a2, a2, 465
	addi a3, zero, 2047
	addi a3, a3, 465
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1720
	addi a2, zero, 1720
	addi a3, zero, 2047
	addi a3, a3, 465
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 496
	addi a3, zero, 2047
	addi a3, a3, 465
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1720
	addi a2, zero, 1720
	addi a3, zero, 1792
	call {vg_p521_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1720
	addi a2, zero, 1720
	addi a3, zero, 2047
	addi a3, a3, 897
	call {vg_p521_add_mod_p}
	ld t0, 424(s0)
	addi s0, s0, 2047
	sd t0, 105(s0)
	addi s0, s0, -2047
	ld t0, 432(s0)
	addi s0, s0, 2047
	sd t0, 113(s0)
	addi s0, s0, -2047
	ld t0, 440(s0)
	addi s0, s0, 2047
	sd t0, 121(s0)
	addi s0, s0, -2047
	ld t0, 448(s0)
	addi s0, s0, 2047
	sd t0, 129(s0)
	addi s0, s0, -2047
	ld t0, 456(s0)
	addi s0, s0, 2047
	sd t0, 137(s0)
	addi s0, s0, -2047
	ld t0, 464(s0)
	addi s0, s0, 2047
	sd t0, 145(s0)
	addi s0, s0, -2047
	ld t0, 472(s0)
	addi s0, s0, 2047
	sd t0, 153(s0)
	addi s0, s0, -2047
	ld t0, 480(s0)
	addi s0, s0, 2047
	sd t0, 161(s0)
	addi s0, s0, -2047
	ld t0, 488(s0)
	addi s0, s0, 2047
	sd t0, 169(s0)
	addi s0, s0, -2047
	addi s1, zero, 576
20:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 105
	addi a2, zero, 2047
	addi a2, a2, 105
	addi a3, zero, 2047
	addi a3, a3, 105
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 177
	addi a2, zero, 1720
	addi a3, zero, 2047
	addi a3, a3, 105
	call {vg_p521_mul_mod_p}
	srli t0, s1, 6
	slli t0, t0, 3
	add t0, t0, s0
	ld t1, 856(t0)
	srl t1, t1, s1
	andi t1, t1, 1
	addi t2, zero, 0
	sub a7, t2, t1
	addi t0, s0, 2047
	ld t0, 105(t0)
	addi t1, s0, 2047
	ld t1, 177(t1)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 105(s0)
	addi s0, s0, -2047
	addi t0, s0, 2047
	ld t0, 113(t0)
	addi t1, s0, 2047
	ld t1, 185(t1)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 113(s0)
	addi s0, s0, -2047
	addi t0, s0, 2047
	ld t0, 121(t0)
	addi t1, s0, 2047
	ld t1, 193(t1)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 121(s0)
	addi s0, s0, -2047
	addi t0, s0, 2047
	ld t0, 129(t0)
	addi t1, s0, 2047
	ld t1, 201(t1)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 129(s0)
	addi s0, s0, -2047
	addi t0, s0, 2047
	ld t0, 137(t0)
	addi t1, s0, 2047
	ld t1, 209(t1)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 137(s0)
	addi s0, s0, -2047
	addi t0, s0, 2047
	ld t0, 145(t0)
	addi t1, s0, 2047
	ld t1, 217(t1)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 145(s0)
	addi s0, s0, -2047
	addi t0, s0, 2047
	ld t0, 153(t0)
	addi t1, s0, 2047
	ld t1, 225(t1)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 153(s0)
	addi s0, s0, -2047
	addi t0, s0, 2047
	ld t0, 161(t0)
	addi t1, s0, 2047
	ld t1, 233(t1)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 161(s0)
	addi s0, s0, -2047
	addi t0, s0, 2047
	ld t0, 169(t0)
	addi t1, s0, 2047
	ld t1, 241(t1)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 169(s0)
	addi s0, s0, -2047
	bnez s1, 20b
	addi a0, s0, 0
	addi a1, zero, 1864
	addi a2, zero, 2047
	addi a2, a2, 105
	addi a3, zero, 2047
	addi a3, a3, 105
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1936
	addi a2, zero, 1864
	addi a3, zero, 1720
	call {vg_p521_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1432
	addi a2, zero, 2047
	addi a2, a2, 105
	addi a3, zero, 352
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1504
	addi a2, zero, 280
	addi a3, zero, 1432
	call {vg_p521_sub_mod_p}
	addi t3, zero, 0
	ld t4, 1936(s0)
	or t3, t3, t4
	ld t4, 1944(s0)
	or t3, t3, t4
	ld t4, 1952(s0)
	or t3, t3, t4
	ld t4, 1960(s0)
	or t3, t3, t4
	ld t4, 1968(s0)
	or t3, t3, t4
	ld t4, 1976(s0)
	or t3, t3, t4
	ld t4, 1984(s0)
	or t3, t3, t4
	ld t4, 1992(s0)
	or t3, t3, t4
	ld t4, 2000(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	addi t0, s0, 2047
	ld t0, 1185(t0)
	and t0, t0, a7
	addi s0, s0, 2047
	sd t0, 1185(s0)
	addi s0, s0, -2047
	ld t0, 1432(s0)
	ld t1, 784(s0)
	xor t0, t0, t1
	andi t0, t0, 1
	addi t1, zero, 0
	sub a7, t1, t0
	ld t0, 1432(s0)
	ld t1, 1504(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1576(s0)
	ld t0, 1440(s0)
	ld t1, 1512(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1584(s0)
	ld t0, 1448(s0)
	ld t1, 1520(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1592(s0)
	ld t0, 1456(s0)
	ld t1, 1528(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1600(s0)
	ld t0, 1464(s0)
	ld t1, 1536(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1608(s0)
	ld t0, 1472(s0)
	ld t1, 1544(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1616(s0)
	ld t0, 1480(s0)
	ld t1, 1552(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1624(s0)
	ld t0, 1488(s0)
	ld t1, 1560(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1632(s0)
	ld t0, 1496(s0)
	ld t1, 1568(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1640(s0)
	ld t0, 1576(s0)
	ld t1, 784(s0)
	xor t0, t0, t1
	andi t0, t0, 1
	addi a7, t0, -1
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
	addi t0, s0, 2047
	ld t0, 457(t0)
	and t0, t0, a7
	srli t1, t0, 8
	sb t1, 1(s2)
	srli t1, t0, 0
	sb t1, 2(s2)
	addi t0, s0, 2047
	ld t0, 449(t0)
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
	addi t0, s0, 2047
	ld t0, 441(t0)
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
	addi t0, s0, 2047
	ld t0, 433(t0)
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
	addi t0, s0, 2047
	ld t0, 425(t0)
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
	addi t0, s0, 2047
	ld t0, 417(t0)
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
	addi t0, s0, 2047
	ld t0, 409(t0)
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
	addi t0, s0, 2047
	ld t0, 401(t0)
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
	addi t0, s0, 2047
	ld t0, 393(t0)
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
	ld t0, 1640(s0)
	and t0, t0, a7
	srli t1, t0, 8
	sb t1, 67(s2)
	srli t1, t0, 0
	sb t1, 68(s2)
	ld t0, 1632(s0)
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
	ld t0, 1624(s0)
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
	ld t0, 1616(s0)
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
	ld t0, 1608(s0)
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
	ld t0, 1600(s0)
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
	ld t0, 1592(s0)
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
	ld t0, 1584(s0)
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
	ld t0, 1576(s0)
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
	ret
	.option pop
