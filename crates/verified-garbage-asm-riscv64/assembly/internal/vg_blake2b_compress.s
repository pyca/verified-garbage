// The functions of `src/internal/vg_blake2b_compress.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_blake2b_compress:
	.option push
	.option arch, +m, +c
	addi a5, a5, 7
	andi a5, a5, -8
	sd s0, 0(a5)
	sd s1, 8(a5)
	sd s2, 16(a5)
	sd s3, 24(a5)
	sd s4, 32(a5)
	sd s5, 40(a5)
	sd s6, 48(a5)
	sd a3, 56(a5)
	addi t6, zero, 0
	sd t6, 64(a5)
	slli a4, a4, 32
	srli a4, a4, 32
	sub a3, t6, a4
	or a4, a4, a3
	srli a4, a4, 63
	sub a4, t6, a4
	sd a4, 72(a5)
	lbu t6, 0(a0)
	lbu a3, 1(a0)
	slli a3, a3, 8
	or t6, t6, a3
	lbu a3, 2(a0)
	slli a3, a3, 16
	or t6, t6, a3
	lbu a3, 3(a0)
	slli a3, a3, 24
	or t6, t6, a3
	lbu a4, 4(a0)
	lbu a3, 5(a0)
	slli a3, a3, 8
	or a4, a4, a3
	lbu a3, 6(a0)
	slli a3, a3, 16
	or a4, a4, a3
	lbu a3, 7(a0)
	slli a3, a3, 24
	or a4, a4, a3
	slli a4, a4, 32
	or t6, t6, a4
	sd t6, 80(a5)
	lbu t6, 8(a0)
	lbu a3, 9(a0)
	slli a3, a3, 8
	or t6, t6, a3
	lbu a3, 10(a0)
	slli a3, a3, 16
	or t6, t6, a3
	lbu a3, 11(a0)
	slli a3, a3, 24
	or t6, t6, a3
	lbu a4, 12(a0)
	lbu a3, 13(a0)
	slli a3, a3, 8
	or a4, a4, a3
	lbu a3, 14(a0)
	slli a3, a3, 16
	or a4, a4, a3
	lbu a3, 15(a0)
	slli a3, a3, 24
	or a4, a4, a3
	slli a4, a4, 32
	or t6, t6, a4
	sd t6, 88(a5)
	lbu t6, 16(a0)
	lbu a3, 17(a0)
	slli a3, a3, 8
	or t6, t6, a3
	lbu a3, 18(a0)
	slli a3, a3, 16
	or t6, t6, a3
	lbu a3, 19(a0)
	slli a3, a3, 24
	or t6, t6, a3
	lbu a4, 20(a0)
	lbu a3, 21(a0)
	slli a3, a3, 8
	or a4, a4, a3
	lbu a3, 22(a0)
	slli a3, a3, 16
	or a4, a4, a3
	lbu a3, 23(a0)
	slli a3, a3, 24
	or a4, a4, a3
	slli a4, a4, 32
	or t6, t6, a4
	sd t6, 96(a5)
	lbu t6, 24(a0)
	lbu a3, 25(a0)
	slli a3, a3, 8
	or t6, t6, a3
	lbu a3, 26(a0)
	slli a3, a3, 16
	or t6, t6, a3
	lbu a3, 27(a0)
	slli a3, a3, 24
	or t6, t6, a3
	lbu a4, 28(a0)
	lbu a3, 29(a0)
	slli a3, a3, 8
	or a4, a4, a3
	lbu a3, 30(a0)
	slli a3, a3, 16
	or a4, a4, a3
	lbu a3, 31(a0)
	slli a3, a3, 24
	or a4, a4, a3
	slli a4, a4, 32
	or t6, t6, a4
	sd t6, 104(a5)
	lbu t6, 32(a0)
	lbu a3, 33(a0)
	slli a3, a3, 8
	or t6, t6, a3
	lbu a3, 34(a0)
	slli a3, a3, 16
	or t6, t6, a3
	lbu a3, 35(a0)
	slli a3, a3, 24
	or t6, t6, a3
	lbu a4, 36(a0)
	lbu a3, 37(a0)
	slli a3, a3, 8
	or a4, a4, a3
	lbu a3, 38(a0)
	slli a3, a3, 16
	or a4, a4, a3
	lbu a3, 39(a0)
	slli a3, a3, 24
	or a4, a4, a3
	slli a4, a4, 32
	or t6, t6, a4
	sd t6, 112(a5)
	lbu t6, 40(a0)
	lbu a3, 41(a0)
	slli a3, a3, 8
	or t6, t6, a3
	lbu a3, 42(a0)
	slli a3, a3, 16
	or t6, t6, a3
	lbu a3, 43(a0)
	slli a3, a3, 24
	or t6, t6, a3
	lbu a4, 44(a0)
	lbu a3, 45(a0)
	slli a3, a3, 8
	or a4, a4, a3
	lbu a3, 46(a0)
	slli a3, a3, 16
	or a4, a4, a3
	lbu a3, 47(a0)
	slli a3, a3, 24
	or a4, a4, a3
	slli a4, a4, 32
	or t6, t6, a4
	sd t6, 120(a5)
	lbu t6, 48(a0)
	lbu a3, 49(a0)
	slli a3, a3, 8
	or t6, t6, a3
	lbu a3, 50(a0)
	slli a3, a3, 16
	or t6, t6, a3
	lbu a3, 51(a0)
	slli a3, a3, 24
	or t6, t6, a3
	lbu a4, 52(a0)
	lbu a3, 53(a0)
	slli a3, a3, 8
	or a4, a4, a3
	lbu a3, 54(a0)
	slli a3, a3, 16
	or a4, a4, a3
	lbu a3, 55(a0)
	slli a3, a3, 24
	or a4, a4, a3
	slli a4, a4, 32
	or t6, t6, a4
	sd t6, 128(a5)
	lbu t6, 56(a0)
	lbu a3, 57(a0)
	slli a3, a3, 8
	or t6, t6, a3
	lbu a3, 58(a0)
	slli a3, a3, 16
	or t6, t6, a3
	lbu a3, 59(a0)
	slli a3, a3, 24
	or t6, t6, a3
	lbu a4, 60(a0)
	lbu a3, 61(a0)
	slli a3, a3, 8
	or a4, a4, a3
	lbu a3, 62(a0)
	slli a3, a3, 16
	or a4, a4, a3
	lbu a3, 63(a0)
	slli a3, a3, 24
	or a4, a4, a3
	slli a4, a4, 32
	or t6, t6, a4
	sd t6, 136(a5)
	beqz a2, 20f
22:
	lbu t6, 0(a1)
	lbu a3, 1(a1)
	slli a3, a3, 8
	or t6, t6, a3
	lbu a3, 2(a1)
	slli a3, a3, 16
	or t6, t6, a3
	lbu a3, 3(a1)
	slli a3, a3, 24
	or t6, t6, a3
	lbu a4, 4(a1)
	lbu a3, 5(a1)
	slli a3, a3, 8
	or a4, a4, a3
	lbu a3, 6(a1)
	slli a3, a3, 16
	or a4, a4, a3
	lbu a3, 7(a1)
	slli a3, a3, 24
	or a4, a4, a3
	slli a4, a4, 32
	or t6, t6, a4
	sd t6, 144(a5)
	lbu t6, 8(a1)
	lbu a3, 9(a1)
	slli a3, a3, 8
	or t6, t6, a3
	lbu a3, 10(a1)
	slli a3, a3, 16
	or t6, t6, a3
	lbu a3, 11(a1)
	slli a3, a3, 24
	or t6, t6, a3
	lbu a4, 12(a1)
	lbu a3, 13(a1)
	slli a3, a3, 8
	or a4, a4, a3
	lbu a3, 14(a1)
	slli a3, a3, 16
	or a4, a4, a3
	lbu a3, 15(a1)
	slli a3, a3, 24
	or a4, a4, a3
	slli a4, a4, 32
	or t6, t6, a4
	sd t6, 152(a5)
	lbu t6, 16(a1)
	lbu a3, 17(a1)
	slli a3, a3, 8
	or t6, t6, a3
	lbu a3, 18(a1)
	slli a3, a3, 16
	or t6, t6, a3
	lbu a3, 19(a1)
	slli a3, a3, 24
	or t6, t6, a3
	lbu a4, 20(a1)
	lbu a3, 21(a1)
	slli a3, a3, 8
	or a4, a4, a3
	lbu a3, 22(a1)
	slli a3, a3, 16
	or a4, a4, a3
	lbu a3, 23(a1)
	slli a3, a3, 24
	or a4, a4, a3
	slli a4, a4, 32
	or t6, t6, a4
	sd t6, 160(a5)
	lbu t6, 24(a1)
	lbu a3, 25(a1)
	slli a3, a3, 8
	or t6, t6, a3
	lbu a3, 26(a1)
	slli a3, a3, 16
	or t6, t6, a3
	lbu a3, 27(a1)
	slli a3, a3, 24
	or t6, t6, a3
	lbu a4, 28(a1)
	lbu a3, 29(a1)
	slli a3, a3, 8
	or a4, a4, a3
	lbu a3, 30(a1)
	slli a3, a3, 16
	or a4, a4, a3
	lbu a3, 31(a1)
	slli a3, a3, 24
	or a4, a4, a3
	slli a4, a4, 32
	or t6, t6, a4
	sd t6, 168(a5)
	lbu t6, 32(a1)
	lbu a3, 33(a1)
	slli a3, a3, 8
	or t6, t6, a3
	lbu a3, 34(a1)
	slli a3, a3, 16
	or t6, t6, a3
	lbu a3, 35(a1)
	slli a3, a3, 24
	or t6, t6, a3
	lbu a4, 36(a1)
	lbu a3, 37(a1)
	slli a3, a3, 8
	or a4, a4, a3
	lbu a3, 38(a1)
	slli a3, a3, 16
	or a4, a4, a3
	lbu a3, 39(a1)
	slli a3, a3, 24
	or a4, a4, a3
	slli a4, a4, 32
	or t6, t6, a4
	sd t6, 176(a5)
	lbu t6, 40(a1)
	lbu a3, 41(a1)
	slli a3, a3, 8
	or t6, t6, a3
	lbu a3, 42(a1)
	slli a3, a3, 16
	or t6, t6, a3
	lbu a3, 43(a1)
	slli a3, a3, 24
	or t6, t6, a3
	lbu a4, 44(a1)
	lbu a3, 45(a1)
	slli a3, a3, 8
	or a4, a4, a3
	lbu a3, 46(a1)
	slli a3, a3, 16
	or a4, a4, a3
	lbu a3, 47(a1)
	slli a3, a3, 24
	or a4, a4, a3
	slli a4, a4, 32
	or t6, t6, a4
	sd t6, 184(a5)
	lbu t6, 48(a1)
	lbu a3, 49(a1)
	slli a3, a3, 8
	or t6, t6, a3
	lbu a3, 50(a1)
	slli a3, a3, 16
	or t6, t6, a3
	lbu a3, 51(a1)
	slli a3, a3, 24
	or t6, t6, a3
	lbu a4, 52(a1)
	lbu a3, 53(a1)
	slli a3, a3, 8
	or a4, a4, a3
	lbu a3, 54(a1)
	slli a3, a3, 16
	or a4, a4, a3
	lbu a3, 55(a1)
	slli a3, a3, 24
	or a4, a4, a3
	slli a4, a4, 32
	or t6, t6, a4
	sd t6, 192(a5)
	lbu t6, 56(a1)
	lbu a3, 57(a1)
	slli a3, a3, 8
	or t6, t6, a3
	lbu a3, 58(a1)
	slli a3, a3, 16
	or t6, t6, a3
	lbu a3, 59(a1)
	slli a3, a3, 24
	or t6, t6, a3
	lbu a4, 60(a1)
	lbu a3, 61(a1)
	slli a3, a3, 8
	or a4, a4, a3
	lbu a3, 62(a1)
	slli a3, a3, 16
	or a4, a4, a3
	lbu a3, 63(a1)
	slli a3, a3, 24
	or a4, a4, a3
	slli a4, a4, 32
	or t6, t6, a4
	sd t6, 200(a5)
	lbu t6, 64(a1)
	lbu a3, 65(a1)
	slli a3, a3, 8
	or t6, t6, a3
	lbu a3, 66(a1)
	slli a3, a3, 16
	or t6, t6, a3
	lbu a3, 67(a1)
	slli a3, a3, 24
	or t6, t6, a3
	lbu a4, 68(a1)
	lbu a3, 69(a1)
	slli a3, a3, 8
	or a4, a4, a3
	lbu a3, 70(a1)
	slli a3, a3, 16
	or a4, a4, a3
	lbu a3, 71(a1)
	slli a3, a3, 24
	or a4, a4, a3
	slli a4, a4, 32
	or t6, t6, a4
	sd t6, 208(a5)
	lbu t6, 72(a1)
	lbu a3, 73(a1)
	slli a3, a3, 8
	or t6, t6, a3
	lbu a3, 74(a1)
	slli a3, a3, 16
	or t6, t6, a3
	lbu a3, 75(a1)
	slli a3, a3, 24
	or t6, t6, a3
	lbu a4, 76(a1)
	lbu a3, 77(a1)
	slli a3, a3, 8
	or a4, a4, a3
	lbu a3, 78(a1)
	slli a3, a3, 16
	or a4, a4, a3
	lbu a3, 79(a1)
	slli a3, a3, 24
	or a4, a4, a3
	slli a4, a4, 32
	or t6, t6, a4
	sd t6, 216(a5)
	lbu t6, 80(a1)
	lbu a3, 81(a1)
	slli a3, a3, 8
	or t6, t6, a3
	lbu a3, 82(a1)
	slli a3, a3, 16
	or t6, t6, a3
	lbu a3, 83(a1)
	slli a3, a3, 24
	or t6, t6, a3
	lbu a4, 84(a1)
	lbu a3, 85(a1)
	slli a3, a3, 8
	or a4, a4, a3
	lbu a3, 86(a1)
	slli a3, a3, 16
	or a4, a4, a3
	lbu a3, 87(a1)
	slli a3, a3, 24
	or a4, a4, a3
	slli a4, a4, 32
	or t6, t6, a4
	sd t6, 224(a5)
	lbu t6, 88(a1)
	lbu a3, 89(a1)
	slli a3, a3, 8
	or t6, t6, a3
	lbu a3, 90(a1)
	slli a3, a3, 16
	or t6, t6, a3
	lbu a3, 91(a1)
	slli a3, a3, 24
	or t6, t6, a3
	lbu a4, 92(a1)
	lbu a3, 93(a1)
	slli a3, a3, 8
	or a4, a4, a3
	lbu a3, 94(a1)
	slli a3, a3, 16
	or a4, a4, a3
	lbu a3, 95(a1)
	slli a3, a3, 24
	or a4, a4, a3
	slli a4, a4, 32
	or t6, t6, a4
	sd t6, 232(a5)
	lbu t6, 96(a1)
	lbu a3, 97(a1)
	slli a3, a3, 8
	or t6, t6, a3
	lbu a3, 98(a1)
	slli a3, a3, 16
	or t6, t6, a3
	lbu a3, 99(a1)
	slli a3, a3, 24
	or t6, t6, a3
	lbu a4, 100(a1)
	lbu a3, 101(a1)
	slli a3, a3, 8
	or a4, a4, a3
	lbu a3, 102(a1)
	slli a3, a3, 16
	or a4, a4, a3
	lbu a3, 103(a1)
	slli a3, a3, 24
	or a4, a4, a3
	slli a4, a4, 32
	or t6, t6, a4
	sd t6, 240(a5)
	lbu t6, 104(a1)
	lbu a3, 105(a1)
	slli a3, a3, 8
	or t6, t6, a3
	lbu a3, 106(a1)
	slli a3, a3, 16
	or t6, t6, a3
	lbu a3, 107(a1)
	slli a3, a3, 24
	or t6, t6, a3
	lbu a4, 108(a1)
	lbu a3, 109(a1)
	slli a3, a3, 8
	or a4, a4, a3
	lbu a3, 110(a1)
	slli a3, a3, 16
	or a4, a4, a3
	lbu a3, 111(a1)
	slli a3, a3, 24
	or a4, a4, a3
	slli a4, a4, 32
	or t6, t6, a4
	sd t6, 248(a5)
	lbu t6, 112(a1)
	lbu a3, 113(a1)
	slli a3, a3, 8
	or t6, t6, a3
	lbu a3, 114(a1)
	slli a3, a3, 16
	or t6, t6, a3
	lbu a3, 115(a1)
	slli a3, a3, 24
	or t6, t6, a3
	lbu a4, 116(a1)
	lbu a3, 117(a1)
	slli a3, a3, 8
	or a4, a4, a3
	lbu a3, 118(a1)
	slli a3, a3, 16
	or a4, a4, a3
	lbu a3, 119(a1)
	slli a3, a3, 24
	or a4, a4, a3
	slli a4, a4, 32
	or t6, t6, a4
	sd t6, 256(a5)
	lbu t6, 120(a1)
	lbu a3, 121(a1)
	slli a3, a3, 8
	or t6, t6, a3
	lbu a3, 122(a1)
	slli a3, a3, 16
	or t6, t6, a3
	lbu a3, 123(a1)
	slli a3, a3, 24
	or t6, t6, a3
	lbu a4, 124(a1)
	lbu a3, 125(a1)
	slli a3, a3, 8
	or a4, a4, a3
	lbu a3, 126(a1)
	slli a3, a3, 16
	or a4, a4, a3
	lbu a3, 127(a1)
	slli a3, a3, 24
	or a4, a4, a3
	slli a4, a4, 32
	or t6, t6, a4
	sd t6, 264(a5)
	ld a3, 80(a5)
	ld a4, 88(a5)
	ld a6, 96(a5)
	ld a7, 104(a5)
	ld t0, 112(a5)
	ld t1, 120(a5)
	ld t2, 128(a5)
	ld t3, 136(a5)
	lui t4, 434334
	addiw t4, t4, 1639
	slli t4, t4, 32
	lui t6, 998349
	addiw t6, t6, -1784
	slli t6, t6, 32
	srli t6, t6, 32
	or t4, t4, t6
	lui t5, 767611
	addiw t5, t5, -379
	slli t5, t5, 32
	lui t6, 543914
	addiw t6, t6, 1851
	slli t6, t6, 32
	srli t6, t6, 32
	or t5, t5, t6
	lui s0, 247535
	addiw s0, s0, 882
	slli s0, s0, 32
	lui t6, 1042768
	addiw t6, t6, -2005
	slli t6, t6, 32
	srli t6, t6, 32
	or s0, s0, t6
	lui s1, 677119
	addiw s1, s1, 1338
	slli s1, s1, 32
	lui t6, 389587
	addiw t6, t6, 1777
	slli t6, t6, 32
	srli t6, t6, 32
	or s1, s1, t6
	lui s2, 332005
	addiw s2, s2, 639
	slli s2, s2, 32
	lui t6, 712296
	addiw t6, t6, 721
	slli t6, t6, 32
	srli t6, t6, 32
	or s2, s2, t6
	lui s3, 634967
	addiw s3, s3, -1908
	slli s3, s3, 32
	lui t6, 177127
	addiw t6, t6, -993
	slli t6, t6, 32
	srli t6, t6, 32
	or s3, s3, t6
	lui s4, 129086
	addiw s4, s4, -1621
	slli s4, s4, 32
	lui t6, 1029148
	addiw t6, t6, -661
	slli t6, t6, 32
	srli t6, t6, 32
	or s4, s4, t6
	lui s5, 376333
	addiw s5, s5, -743
	slli s5, s5, 32
	lui t6, 79842
	addiw t6, t6, 377
	slli t6, t6, 32
	srli t6, t6, 32
	or s5, s5, t6
	ld t6, 56(a5)
	xor s2, s2, t6
	ld t6, 64(a5)
	xor s3, s3, t6
	ld t6, 72(a5)
	xor s4, s4, t6
	ld t6, 144(a5)
	add a3, a3, t0
	add a3, a3, t6
	xor s2, s2, a3
	srli s6, s2, 32
	slli s2, s2, 32
	or s2, s2, s6
	add t4, t4, s2
	xor t0, t0, t4
	srli s6, t0, 24
	slli t0, t0, 40
	or t0, t0, s6
	ld t6, 152(a5)
	add a3, a3, t0
	add a3, a3, t6
	xor s2, s2, a3
	srli s6, s2, 16
	slli s2, s2, 48
	or s2, s2, s6
	add t4, t4, s2
	xor t0, t0, t4
	srli s6, t0, 63
	slli t0, t0, 1
	or t0, t0, s6
	ld t6, 160(a5)
	add a4, a4, t1
	add a4, a4, t6
	xor s3, s3, a4
	srli s6, s3, 32
	slli s3, s3, 32
	or s3, s3, s6
	add t5, t5, s3
	xor t1, t1, t5
	srli s6, t1, 24
	slli t1, t1, 40
	or t1, t1, s6
	ld t6, 168(a5)
	add a4, a4, t1
	add a4, a4, t6
	xor s3, s3, a4
	srli s6, s3, 16
	slli s3, s3, 48
	or s3, s3, s6
	add t5, t5, s3
	xor t1, t1, t5
	srli s6, t1, 63
	slli t1, t1, 1
	or t1, t1, s6
	ld t6, 176(a5)
	add a6, a6, t2
	add a6, a6, t6
	xor s4, s4, a6
	srli s6, s4, 32
	slli s4, s4, 32
	or s4, s4, s6
	add s0, s0, s4
	xor t2, t2, s0
	srli s6, t2, 24
	slli t2, t2, 40
	or t2, t2, s6
	ld t6, 184(a5)
	add a6, a6, t2
	add a6, a6, t6
	xor s4, s4, a6
	srli s6, s4, 16
	slli s4, s4, 48
	or s4, s4, s6
	add s0, s0, s4
	xor t2, t2, s0
	srli s6, t2, 63
	slli t2, t2, 1
	or t2, t2, s6
	ld t6, 192(a5)
	add a7, a7, t3
	add a7, a7, t6
	xor s5, s5, a7
	srli s6, s5, 32
	slli s5, s5, 32
	or s5, s5, s6
	add s1, s1, s5
	xor t3, t3, s1
	srli s6, t3, 24
	slli t3, t3, 40
	or t3, t3, s6
	ld t6, 200(a5)
	add a7, a7, t3
	add a7, a7, t6
	xor s5, s5, a7
	srli s6, s5, 16
	slli s5, s5, 48
	or s5, s5, s6
	add s1, s1, s5
	xor t3, t3, s1
	srli s6, t3, 63
	slli t3, t3, 1
	or t3, t3, s6
	ld t6, 208(a5)
	add a3, a3, t1
	add a3, a3, t6
	xor s5, s5, a3
	srli s6, s5, 32
	slli s5, s5, 32
	or s5, s5, s6
	add s0, s0, s5
	xor t1, t1, s0
	srli s6, t1, 24
	slli t1, t1, 40
	or t1, t1, s6
	ld t6, 216(a5)
	add a3, a3, t1
	add a3, a3, t6
	xor s5, s5, a3
	srli s6, s5, 16
	slli s5, s5, 48
	or s5, s5, s6
	add s0, s0, s5
	xor t1, t1, s0
	srli s6, t1, 63
	slli t1, t1, 1
	or t1, t1, s6
	ld t6, 224(a5)
	add a4, a4, t2
	add a4, a4, t6
	xor s2, s2, a4
	srli s6, s2, 32
	slli s2, s2, 32
	or s2, s2, s6
	add s1, s1, s2
	xor t2, t2, s1
	srli s6, t2, 24
	slli t2, t2, 40
	or t2, t2, s6
	ld t6, 232(a5)
	add a4, a4, t2
	add a4, a4, t6
	xor s2, s2, a4
	srli s6, s2, 16
	slli s2, s2, 48
	or s2, s2, s6
	add s1, s1, s2
	xor t2, t2, s1
	srli s6, t2, 63
	slli t2, t2, 1
	or t2, t2, s6
	ld t6, 240(a5)
	add a6, a6, t3
	add a6, a6, t6
	xor s3, s3, a6
	srli s6, s3, 32
	slli s3, s3, 32
	or s3, s3, s6
	add t4, t4, s3
	xor t3, t3, t4
	srli s6, t3, 24
	slli t3, t3, 40
	or t3, t3, s6
	ld t6, 248(a5)
	add a6, a6, t3
	add a6, a6, t6
	xor s3, s3, a6
	srli s6, s3, 16
	slli s3, s3, 48
	or s3, s3, s6
	add t4, t4, s3
	xor t3, t3, t4
	srli s6, t3, 63
	slli t3, t3, 1
	or t3, t3, s6
	ld t6, 256(a5)
	add a7, a7, t0
	add a7, a7, t6
	xor s4, s4, a7
	srli s6, s4, 32
	slli s4, s4, 32
	or s4, s4, s6
	add t5, t5, s4
	xor t0, t0, t5
	srli s6, t0, 24
	slli t0, t0, 40
	or t0, t0, s6
	ld t6, 264(a5)
	add a7, a7, t0
	add a7, a7, t6
	xor s4, s4, a7
	srli s6, s4, 16
	slli s4, s4, 48
	or s4, s4, s6
	add t5, t5, s4
	xor t0, t0, t5
	srli s6, t0, 63
	slli t0, t0, 1
	or t0, t0, s6
	ld t6, 256(a5)
	add a3, a3, t0
	add a3, a3, t6
	xor s2, s2, a3
	srli s6, s2, 32
	slli s2, s2, 32
	or s2, s2, s6
	add t4, t4, s2
	xor t0, t0, t4
	srli s6, t0, 24
	slli t0, t0, 40
	or t0, t0, s6
	ld t6, 224(a5)
	add a3, a3, t0
	add a3, a3, t6
	xor s2, s2, a3
	srli s6, s2, 16
	slli s2, s2, 48
	or s2, s2, s6
	add t4, t4, s2
	xor t0, t0, t4
	srli s6, t0, 63
	slli t0, t0, 1
	or t0, t0, s6
	ld t6, 176(a5)
	add a4, a4, t1
	add a4, a4, t6
	xor s3, s3, a4
	srli s6, s3, 32
	slli s3, s3, 32
	or s3, s3, s6
	add t5, t5, s3
	xor t1, t1, t5
	srli s6, t1, 24
	slli t1, t1, 40
	or t1, t1, s6
	ld t6, 208(a5)
	add a4, a4, t1
	add a4, a4, t6
	xor s3, s3, a4
	srli s6, s3, 16
	slli s3, s3, 48
	or s3, s3, s6
	add t5, t5, s3
	xor t1, t1, t5
	srli s6, t1, 63
	slli t1, t1, 1
	or t1, t1, s6
	ld t6, 216(a5)
	add a6, a6, t2
	add a6, a6, t6
	xor s4, s4, a6
	srli s6, s4, 32
	slli s4, s4, 32
	or s4, s4, s6
	add s0, s0, s4
	xor t2, t2, s0
	srli s6, t2, 24
	slli t2, t2, 40
	or t2, t2, s6
	ld t6, 264(a5)
	add a6, a6, t2
	add a6, a6, t6
	xor s4, s4, a6
	srli s6, s4, 16
	slli s4, s4, 48
	or s4, s4, s6
	add s0, s0, s4
	xor t2, t2, s0
	srli s6, t2, 63
	slli t2, t2, 1
	or t2, t2, s6
	ld t6, 248(a5)
	add a7, a7, t3
	add a7, a7, t6
	xor s5, s5, a7
	srli s6, s5, 32
	slli s5, s5, 32
	or s5, s5, s6
	add s1, s1, s5
	xor t3, t3, s1
	srli s6, t3, 24
	slli t3, t3, 40
	or t3, t3, s6
	ld t6, 192(a5)
	add a7, a7, t3
	add a7, a7, t6
	xor s5, s5, a7
	srli s6, s5, 16
	slli s5, s5, 48
	or s5, s5, s6
	add s1, s1, s5
	xor t3, t3, s1
	srli s6, t3, 63
	slli t3, t3, 1
	or t3, t3, s6
	ld t6, 152(a5)
	add a3, a3, t1
	add a3, a3, t6
	xor s5, s5, a3
	srli s6, s5, 32
	slli s5, s5, 32
	or s5, s5, s6
	add s0, s0, s5
	xor t1, t1, s0
	srli s6, t1, 24
	slli t1, t1, 40
	or t1, t1, s6
	ld t6, 240(a5)
	add a3, a3, t1
	add a3, a3, t6
	xor s5, s5, a3
	srli s6, s5, 16
	slli s5, s5, 48
	or s5, s5, s6
	add s0, s0, s5
	xor t1, t1, s0
	srli s6, t1, 63
	slli t1, t1, 1
	or t1, t1, s6
	ld t6, 144(a5)
	add a4, a4, t2
	add a4, a4, t6
	xor s2, s2, a4
	srli s6, s2, 32
	slli s2, s2, 32
	or s2, s2, s6
	add s1, s1, s2
	xor t2, t2, s1
	srli s6, t2, 24
	slli t2, t2, 40
	or t2, t2, s6
	ld t6, 160(a5)
	add a4, a4, t2
	add a4, a4, t6
	xor s2, s2, a4
	srli s6, s2, 16
	slli s2, s2, 48
	or s2, s2, s6
	add s1, s1, s2
	xor t2, t2, s1
	srli s6, t2, 63
	slli t2, t2, 1
	or t2, t2, s6
	ld t6, 232(a5)
	add a6, a6, t3
	add a6, a6, t6
	xor s3, s3, a6
	srli s6, s3, 32
	slli s3, s3, 32
	or s3, s3, s6
	add t4, t4, s3
	xor t3, t3, t4
	srli s6, t3, 24
	slli t3, t3, 40
	or t3, t3, s6
	ld t6, 200(a5)
	add a6, a6, t3
	add a6, a6, t6
	xor s3, s3, a6
	srli s6, s3, 16
	slli s3, s3, 48
	or s3, s3, s6
	add t4, t4, s3
	xor t3, t3, t4
	srli s6, t3, 63
	slli t3, t3, 1
	or t3, t3, s6
	ld t6, 184(a5)
	add a7, a7, t0
	add a7, a7, t6
	xor s4, s4, a7
	srli s6, s4, 32
	slli s4, s4, 32
	or s4, s4, s6
	add t5, t5, s4
	xor t0, t0, t5
	srli s6, t0, 24
	slli t0, t0, 40
	or t0, t0, s6
	ld t6, 168(a5)
	add a7, a7, t0
	add a7, a7, t6
	xor s4, s4, a7
	srli s6, s4, 16
	slli s4, s4, 48
	or s4, s4, s6
	add t5, t5, s4
	xor t0, t0, t5
	srli s6, t0, 63
	slli t0, t0, 1
	or t0, t0, s6
	ld t6, 232(a5)
	add a3, a3, t0
	add a3, a3, t6
	xor s2, s2, a3
	srli s6, s2, 32
	slli s2, s2, 32
	or s2, s2, s6
	add t4, t4, s2
	xor t0, t0, t4
	srli s6, t0, 24
	slli t0, t0, 40
	or t0, t0, s6
	ld t6, 208(a5)
	add a3, a3, t0
	add a3, a3, t6
	xor s2, s2, a3
	srli s6, s2, 16
	slli s2, s2, 48
	or s2, s2, s6
	add t4, t4, s2
	xor t0, t0, t4
	srli s6, t0, 63
	slli t0, t0, 1
	or t0, t0, s6
	ld t6, 240(a5)
	add a4, a4, t1
	add a4, a4, t6
	xor s3, s3, a4
	srli s6, s3, 32
	slli s3, s3, 32
	or s3, s3, s6
	add t5, t5, s3
	xor t1, t1, t5
	srli s6, t1, 24
	slli t1, t1, 40
	or t1, t1, s6
	ld t6, 144(a5)
	add a4, a4, t1
	add a4, a4, t6
	xor s3, s3, a4
	srli s6, s3, 16
	slli s3, s3, 48
	or s3, s3, s6
	add t5, t5, s3
	xor t1, t1, t5
	srli s6, t1, 63
	slli t1, t1, 1
	or t1, t1, s6
	ld t6, 184(a5)
	add a6, a6, t2
	add a6, a6, t6
	xor s4, s4, a6
	srli s6, s4, 32
	slli s4, s4, 32
	or s4, s4, s6
	add s0, s0, s4
	xor t2, t2, s0
	srli s6, t2, 24
	slli t2, t2, 40
	or t2, t2, s6
	ld t6, 160(a5)
	add a6, a6, t2
	add a6, a6, t6
	xor s4, s4, a6
	srli s6, s4, 16
	slli s4, s4, 48
	or s4, s4, s6
	add s0, s0, s4
	xor t2, t2, s0
	srli s6, t2, 63
	slli t2, t2, 1
	or t2, t2, s6
	ld t6, 264(a5)
	add a7, a7, t3
	add a7, a7, t6
	xor s5, s5, a7
	srli s6, s5, 32
	slli s5, s5, 32
	or s5, s5, s6
	add s1, s1, s5
	xor t3, t3, s1
	srli s6, t3, 24
	slli t3, t3, 40
	or t3, t3, s6
	ld t6, 248(a5)
	add a7, a7, t3
	add a7, a7, t6
	xor s5, s5, a7
	srli s6, s5, 16
	slli s5, s5, 48
	or s5, s5, s6
	add s1, s1, s5
	xor t3, t3, s1
	srli s6, t3, 63
	slli t3, t3, 1
	or t3, t3, s6
	ld t6, 224(a5)
	add a3, a3, t1
	add a3, a3, t6
	xor s5, s5, a3
	srli s6, s5, 32
	slli s5, s5, 32
	or s5, s5, s6
	add s0, s0, s5
	xor t1, t1, s0
	srli s6, t1, 24
	slli t1, t1, 40
	or t1, t1, s6
	ld t6, 256(a5)
	add a3, a3, t1
	add a3, a3, t6
	xor s5, s5, a3
	srli s6, s5, 16
	slli s5, s5, 48
	or s5, s5, s6
	add s0, s0, s5
	xor t1, t1, s0
	srli s6, t1, 63
	slli t1, t1, 1
	or t1, t1, s6
	ld t6, 168(a5)
	add a4, a4, t2
	add a4, a4, t6
	xor s2, s2, a4
	srli s6, s2, 32
	slli s2, s2, 32
	or s2, s2, s6
	add s1, s1, s2
	xor t2, t2, s1
	srli s6, t2, 24
	slli t2, t2, 40
	or t2, t2, s6
	ld t6, 192(a5)
	add a4, a4, t2
	add a4, a4, t6
	xor s2, s2, a4
	srli s6, s2, 16
	slli s2, s2, 48
	or s2, s2, s6
	add s1, s1, s2
	xor t2, t2, s1
	srli s6, t2, 63
	slli t2, t2, 1
	or t2, t2, s6
	ld t6, 200(a5)
	add a6, a6, t3
	add a6, a6, t6
	xor s3, s3, a6
	srli s6, s3, 32
	slli s3, s3, 32
	or s3, s3, s6
	add t4, t4, s3
	xor t3, t3, t4
	srli s6, t3, 24
	slli t3, t3, 40
	or t3, t3, s6
	ld t6, 152(a5)
	add a6, a6, t3
	add a6, a6, t6
	xor s3, s3, a6
	srli s6, s3, 16
	slli s3, s3, 48
	or s3, s3, s6
	add t4, t4, s3
	xor t3, t3, t4
	srli s6, t3, 63
	slli t3, t3, 1
	or t3, t3, s6
	ld t6, 216(a5)
	add a7, a7, t0
	add a7, a7, t6
	xor s4, s4, a7
	srli s6, s4, 32
	slli s4, s4, 32
	or s4, s4, s6
	add t5, t5, s4
	xor t0, t0, t5
	srli s6, t0, 24
	slli t0, t0, 40
	or t0, t0, s6
	ld t6, 176(a5)
	add a7, a7, t0
	add a7, a7, t6
	xor s4, s4, a7
	srli s6, s4, 16
	slli s4, s4, 48
	or s4, s4, s6
	add t5, t5, s4
	xor t0, t0, t5
	srli s6, t0, 63
	slli t0, t0, 1
	or t0, t0, s6
	ld t6, 200(a5)
	add a3, a3, t0
	add a3, a3, t6
	xor s2, s2, a3
	srli s6, s2, 32
	slli s2, s2, 32
	or s2, s2, s6
	add t4, t4, s2
	xor t0, t0, t4
	srli s6, t0, 24
	slli t0, t0, 40
	or t0, t0, s6
	ld t6, 216(a5)
	add a3, a3, t0
	add a3, a3, t6
	xor s2, s2, a3
	srli s6, s2, 16
	slli s2, s2, 48
	or s2, s2, s6
	add t4, t4, s2
	xor t0, t0, t4
	srli s6, t0, 63
	slli t0, t0, 1
	or t0, t0, s6
	ld t6, 168(a5)
	add a4, a4, t1
	add a4, a4, t6
	xor s3, s3, a4
	srli s6, s3, 32
	slli s3, s3, 32
	or s3, s3, s6
	add t5, t5, s3
	xor t1, t1, t5
	srli s6, t1, 24
	slli t1, t1, 40
	or t1, t1, s6
	ld t6, 152(a5)
	add a4, a4, t1
	add a4, a4, t6
	xor s3, s3, a4
	srli s6, s3, 16
	slli s3, s3, 48
	or s3, s3, s6
	add t5, t5, s3
	xor t1, t1, t5
	srli s6, t1, 63
	slli t1, t1, 1
	or t1, t1, s6
	ld t6, 248(a5)
	add a6, a6, t2
	add a6, a6, t6
	xor s4, s4, a6
	srli s6, s4, 32
	slli s4, s4, 32
	or s4, s4, s6
	add s0, s0, s4
	xor t2, t2, s0
	srli s6, t2, 24
	slli t2, t2, 40
	or t2, t2, s6
	ld t6, 240(a5)
	add a6, a6, t2
	add a6, a6, t6
	xor s4, s4, a6
	srli s6, s4, 16
	slli s4, s4, 48
	or s4, s4, s6
	add s0, s0, s4
	xor t2, t2, s0
	srli s6, t2, 63
	slli t2, t2, 1
	or t2, t2, s6
	ld t6, 232(a5)
	add a7, a7, t3
	add a7, a7, t6
	xor s5, s5, a7
	srli s6, s5, 32
	slli s5, s5, 32
	or s5, s5, s6
	add s1, s1, s5
	xor t3, t3, s1
	srli s6, t3, 24
	slli t3, t3, 40
	or t3, t3, s6
	ld t6, 256(a5)
	add a7, a7, t3
	add a7, a7, t6
	xor s5, s5, a7
	srli s6, s5, 16
	slli s5, s5, 48
	or s5, s5, s6
	add s1, s1, s5
	xor t3, t3, s1
	srli s6, t3, 63
	slli t3, t3, 1
	or t3, t3, s6
	ld t6, 160(a5)
	add a3, a3, t1
	add a3, a3, t6
	xor s5, s5, a3
	srli s6, s5, 32
	slli s5, s5, 32
	or s5, s5, s6
	add s0, s0, s5
	xor t1, t1, s0
	srli s6, t1, 24
	slli t1, t1, 40
	or t1, t1, s6
	ld t6, 192(a5)
	add a3, a3, t1
	add a3, a3, t6
	xor s5, s5, a3
	srli s6, s5, 16
	slli s5, s5, 48
	or s5, s5, s6
	add s0, s0, s5
	xor t1, t1, s0
	srli s6, t1, 63
	slli t1, t1, 1
	or t1, t1, s6
	ld t6, 184(a5)
	add a4, a4, t2
	add a4, a4, t6
	xor s2, s2, a4
	srli s6, s2, 32
	slli s2, s2, 32
	or s2, s2, s6
	add s1, s1, s2
	xor t2, t2, s1
	srli s6, t2, 24
	slli t2, t2, 40
	or t2, t2, s6
	ld t6, 224(a5)
	add a4, a4, t2
	add a4, a4, t6
	xor s2, s2, a4
	srli s6, s2, 16
	slli s2, s2, 48
	or s2, s2, s6
	add s1, s1, s2
	xor t2, t2, s1
	srli s6, t2, 63
	slli t2, t2, 1
	or t2, t2, s6
	ld t6, 176(a5)
	add a6, a6, t3
	add a6, a6, t6
	xor s3, s3, a6
	srli s6, s3, 32
	slli s3, s3, 32
	or s3, s3, s6
	add t4, t4, s3
	xor t3, t3, t4
	srli s6, t3, 24
	slli t3, t3, 40
	or t3, t3, s6
	ld t6, 144(a5)
	add a6, a6, t3
	add a6, a6, t6
	xor s3, s3, a6
	srli s6, s3, 16
	slli s3, s3, 48
	or s3, s3, s6
	add t4, t4, s3
	xor t3, t3, t4
	srli s6, t3, 63
	slli t3, t3, 1
	or t3, t3, s6
	ld t6, 264(a5)
	add a7, a7, t0
	add a7, a7, t6
	xor s4, s4, a7
	srli s6, s4, 32
	slli s4, s4, 32
	or s4, s4, s6
	add t5, t5, s4
	xor t0, t0, t5
	srli s6, t0, 24
	slli t0, t0, 40
	or t0, t0, s6
	ld t6, 208(a5)
	add a7, a7, t0
	add a7, a7, t6
	xor s4, s4, a7
	srli s6, s4, 16
	slli s4, s4, 48
	or s4, s4, s6
	add t5, t5, s4
	xor t0, t0, t5
	srli s6, t0, 63
	slli t0, t0, 1
	or t0, t0, s6
	ld t6, 216(a5)
	add a3, a3, t0
	add a3, a3, t6
	xor s2, s2, a3
	srli s6, s2, 32
	slli s2, s2, 32
	or s2, s2, s6
	add t4, t4, s2
	xor t0, t0, t4
	srli s6, t0, 24
	slli t0, t0, 40
	or t0, t0, s6
	ld t6, 144(a5)
	add a3, a3, t0
	add a3, a3, t6
	xor s2, s2, a3
	srli s6, s2, 16
	slli s2, s2, 48
	or s2, s2, s6
	add t4, t4, s2
	xor t0, t0, t4
	srli s6, t0, 63
	slli t0, t0, 1
	or t0, t0, s6
	ld t6, 184(a5)
	add a4, a4, t1
	add a4, a4, t6
	xor s3, s3, a4
	srli s6, s3, 32
	slli s3, s3, 32
	or s3, s3, s6
	add t5, t5, s3
	xor t1, t1, t5
	srli s6, t1, 24
	slli t1, t1, 40
	or t1, t1, s6
	ld t6, 200(a5)
	add a4, a4, t1
	add a4, a4, t6
	xor s3, s3, a4
	srli s6, s3, 16
	slli s3, s3, 48
	or s3, s3, s6
	add t5, t5, s3
	xor t1, t1, t5
	srli s6, t1, 63
	slli t1, t1, 1
	or t1, t1, s6
	ld t6, 160(a5)
	add a6, a6, t2
	add a6, a6, t6
	xor s4, s4, a6
	srli s6, s4, 32
	slli s4, s4, 32
	or s4, s4, s6
	add s0, s0, s4
	xor t2, t2, s0
	srli s6, t2, 24
	slli t2, t2, 40
	or t2, t2, s6
	ld t6, 176(a5)
	add a6, a6, t2
	add a6, a6, t6
	xor s4, s4, a6
	srli s6, s4, 16
	slli s4, s4, 48
	or s4, s4, s6
	add s0, s0, s4
	xor t2, t2, s0
	srli s6, t2, 63
	slli t2, t2, 1
	or t2, t2, s6
	ld t6, 224(a5)
	add a7, a7, t3
	add a7, a7, t6
	xor s5, s5, a7
	srli s6, s5, 32
	slli s5, s5, 32
	or s5, s5, s6
	add s1, s1, s5
	xor t3, t3, s1
	srli s6, t3, 24
	slli t3, t3, 40
	or t3, t3, s6
	ld t6, 264(a5)
	add a7, a7, t3
	add a7, a7, t6
	xor s5, s5, a7
	srli s6, s5, 16
	slli s5, s5, 48
	or s5, s5, s6
	add s1, s1, s5
	xor t3, t3, s1
	srli s6, t3, 63
	slli t3, t3, 1
	or t3, t3, s6
	ld t6, 256(a5)
	add a3, a3, t1
	add a3, a3, t6
	xor s5, s5, a3
	srli s6, s5, 32
	slli s5, s5, 32
	or s5, s5, s6
	add s0, s0, s5
	xor t1, t1, s0
	srli s6, t1, 24
	slli t1, t1, 40
	or t1, t1, s6
	ld t6, 152(a5)
	add a3, a3, t1
	add a3, a3, t6
	xor s5, s5, a3
	srli s6, s5, 16
	slli s5, s5, 48
	or s5, s5, s6
	add s0, s0, s5
	xor t1, t1, s0
	srli s6, t1, 63
	slli t1, t1, 1
	or t1, t1, s6
	ld t6, 232(a5)
	add a4, a4, t2
	add a4, a4, t6
	xor s2, s2, a4
	srli s6, s2, 32
	slli s2, s2, 32
	or s2, s2, s6
	add s1, s1, s2
	xor t2, t2, s1
	srli s6, t2, 24
	slli t2, t2, 40
	or t2, t2, s6
	ld t6, 240(a5)
	add a4, a4, t2
	add a4, a4, t6
	xor s2, s2, a4
	srli s6, s2, 16
	slli s2, s2, 48
	or s2, s2, s6
	add s1, s1, s2
	xor t2, t2, s1
	srli s6, t2, 63
	slli t2, t2, 1
	or t2, t2, s6
	ld t6, 192(a5)
	add a6, a6, t3
	add a6, a6, t6
	xor s3, s3, a6
	srli s6, s3, 32
	slli s3, s3, 32
	or s3, s3, s6
	add t4, t4, s3
	xor t3, t3, t4
	srli s6, t3, 24
	slli t3, t3, 40
	or t3, t3, s6
	ld t6, 208(a5)
	add a6, a6, t3
	add a6, a6, t6
	xor s3, s3, a6
	srli s6, s3, 16
	slli s3, s3, 48
	or s3, s3, s6
	add t4, t4, s3
	xor t3, t3, t4
	srli s6, t3, 63
	slli t3, t3, 1
	or t3, t3, s6
	ld t6, 168(a5)
	add a7, a7, t0
	add a7, a7, t6
	xor s4, s4, a7
	srli s6, s4, 32
	slli s4, s4, 32
	or s4, s4, s6
	add t5, t5, s4
	xor t0, t0, t5
	srli s6, t0, 24
	slli t0, t0, 40
	or t0, t0, s6
	ld t6, 248(a5)
	add a7, a7, t0
	add a7, a7, t6
	xor s4, s4, a7
	srli s6, s4, 16
	slli s4, s4, 48
	or s4, s4, s6
	add t5, t5, s4
	xor t0, t0, t5
	srli s6, t0, 63
	slli t0, t0, 1
	or t0, t0, s6
	ld t6, 160(a5)
	add a3, a3, t0
	add a3, a3, t6
	xor s2, s2, a3
	srli s6, s2, 32
	slli s2, s2, 32
	or s2, s2, s6
	add t4, t4, s2
	xor t0, t0, t4
	srli s6, t0, 24
	slli t0, t0, 40
	or t0, t0, s6
	ld t6, 240(a5)
	add a3, a3, t0
	add a3, a3, t6
	xor s2, s2, a3
	srli s6, s2, 16
	slli s2, s2, 48
	or s2, s2, s6
	add t4, t4, s2
	xor t0, t0, t4
	srli s6, t0, 63
	slli t0, t0, 1
	or t0, t0, s6
	ld t6, 192(a5)
	add a4, a4, t1
	add a4, a4, t6
	xor s3, s3, a4
	srli s6, s3, 32
	slli s3, s3, 32
	or s3, s3, s6
	add t5, t5, s3
	xor t1, t1, t5
	srli s6, t1, 24
	slli t1, t1, 40
	or t1, t1, s6
	ld t6, 224(a5)
	add a4, a4, t1
	add a4, a4, t6
	xor s3, s3, a4
	srli s6, s3, 16
	slli s3, s3, 48
	or s3, s3, s6
	add t5, t5, s3
	xor t1, t1, t5
	srli s6, t1, 63
	slli t1, t1, 1
	or t1, t1, s6
	ld t6, 144(a5)
	add a6, a6, t2
	add a6, a6, t6
	xor s4, s4, a6
	srli s6, s4, 32
	slli s4, s4, 32
	or s4, s4, s6
	add s0, s0, s4
	xor t2, t2, s0
	srli s6, t2, 24
	slli t2, t2, 40
	or t2, t2, s6
	ld t6, 232(a5)
	add a6, a6, t2
	add a6, a6, t6
	xor s4, s4, a6
	srli s6, s4, 16
	slli s4, s4, 48
	or s4, s4, s6
	add s0, s0, s4
	xor t2, t2, s0
	srli s6, t2, 63
	slli t2, t2, 1
	or t2, t2, s6
	ld t6, 208(a5)
	add a7, a7, t3
	add a7, a7, t6
	xor s5, s5, a7
	srli s6, s5, 32
	slli s5, s5, 32
	or s5, s5, s6
	add s1, s1, s5
	xor t3, t3, s1
	srli s6, t3, 24
	slli t3, t3, 40
	or t3, t3, s6
	ld t6, 168(a5)
	add a7, a7, t3
	add a7, a7, t6
	xor s5, s5, a7
	srli s6, s5, 16
	slli s5, s5, 48
	or s5, s5, s6
	add s1, s1, s5
	xor t3, t3, s1
	srli s6, t3, 63
	slli t3, t3, 1
	or t3, t3, s6
	ld t6, 176(a5)
	add a3, a3, t1
	add a3, a3, t6
	xor s5, s5, a3
	srli s6, s5, 32
	slli s5, s5, 32
	or s5, s5, s6
	add s0, s0, s5
	xor t1, t1, s0
	srli s6, t1, 24
	slli t1, t1, 40
	or t1, t1, s6
	ld t6, 248(a5)
	add a3, a3, t1
	add a3, a3, t6
	xor s5, s5, a3
	srli s6, s5, 16
	slli s5, s5, 48
	or s5, s5, s6
	add s0, s0, s5
	xor t1, t1, s0
	srli s6, t1, 63
	slli t1, t1, 1
	or t1, t1, s6
	ld t6, 200(a5)
	add a4, a4, t2
	add a4, a4, t6
	xor s2, s2, a4
	srli s6, s2, 32
	slli s2, s2, 32
	or s2, s2, s6
	add s1, s1, s2
	xor t2, t2, s1
	srli s6, t2, 24
	slli t2, t2, 40
	or t2, t2, s6
	ld t6, 184(a5)
	add a4, a4, t2
	add a4, a4, t6
	xor s2, s2, a4
	srli s6, s2, 16
	slli s2, s2, 48
	or s2, s2, s6
	add s1, s1, s2
	xor t2, t2, s1
	srli s6, t2, 63
	slli t2, t2, 1
	or t2, t2, s6
	ld t6, 264(a5)
	add a6, a6, t3
	add a6, a6, t6
	xor s3, s3, a6
	srli s6, s3, 32
	slli s3, s3, 32
	or s3, s3, s6
	add t4, t4, s3
	xor t3, t3, t4
	srli s6, t3, 24
	slli t3, t3, 40
	or t3, t3, s6
	ld t6, 256(a5)
	add a6, a6, t3
	add a6, a6, t6
	xor s3, s3, a6
	srli s6, s3, 16
	slli s3, s3, 48
	or s3, s3, s6
	add t4, t4, s3
	xor t3, t3, t4
	srli s6, t3, 63
	slli t3, t3, 1
	or t3, t3, s6
	ld t6, 152(a5)
	add a7, a7, t0
	add a7, a7, t6
	xor s4, s4, a7
	srli s6, s4, 32
	slli s4, s4, 32
	or s4, s4, s6
	add t5, t5, s4
	xor t0, t0, t5
	srli s6, t0, 24
	slli t0, t0, 40
	or t0, t0, s6
	ld t6, 216(a5)
	add a7, a7, t0
	add a7, a7, t6
	xor s4, s4, a7
	srli s6, s4, 16
	slli s4, s4, 48
	or s4, s4, s6
	add t5, t5, s4
	xor t0, t0, t5
	srli s6, t0, 63
	slli t0, t0, 1
	or t0, t0, s6
	ld t6, 240(a5)
	add a3, a3, t0
	add a3, a3, t6
	xor s2, s2, a3
	srli s6, s2, 32
	slli s2, s2, 32
	or s2, s2, s6
	add t4, t4, s2
	xor t0, t0, t4
	srli s6, t0, 24
	slli t0, t0, 40
	or t0, t0, s6
	ld t6, 184(a5)
	add a3, a3, t0
	add a3, a3, t6
	xor s2, s2, a3
	srli s6, s2, 16
	slli s2, s2, 48
	or s2, s2, s6
	add t4, t4, s2
	xor t0, t0, t4
	srli s6, t0, 63
	slli t0, t0, 1
	or t0, t0, s6
	ld t6, 152(a5)
	add a4, a4, t1
	add a4, a4, t6
	xor s3, s3, a4
	srli s6, s3, 32
	slli s3, s3, 32
	or s3, s3, s6
	add t5, t5, s3
	xor t1, t1, t5
	srli s6, t1, 24
	slli t1, t1, 40
	or t1, t1, s6
	ld t6, 264(a5)
	add a4, a4, t1
	add a4, a4, t6
	xor s3, s3, a4
	srli s6, s3, 16
	slli s3, s3, 48
	or s3, s3, s6
	add t5, t5, s3
	xor t1, t1, t5
	srli s6, t1, 63
	slli t1, t1, 1
	or t1, t1, s6
	ld t6, 256(a5)
	add a6, a6, t2
	add a6, a6, t6
	xor s4, s4, a6
	srli s6, s4, 32
	slli s4, s4, 32
	or s4, s4, s6
	add s0, s0, s4
	xor t2, t2, s0
	srli s6, t2, 24
	slli t2, t2, 40
	or t2, t2, s6
	ld t6, 248(a5)
	add a6, a6, t2
	add a6, a6, t6
	xor s4, s4, a6
	srli s6, s4, 16
	slli s4, s4, 48
	or s4, s4, s6
	add s0, s0, s4
	xor t2, t2, s0
	srli s6, t2, 63
	slli t2, t2, 1
	or t2, t2, s6
	ld t6, 176(a5)
	add a7, a7, t3
	add a7, a7, t6
	xor s5, s5, a7
	srli s6, s5, 32
	slli s5, s5, 32
	or s5, s5, s6
	add s1, s1, s5
	xor t3, t3, s1
	srli s6, t3, 24
	slli t3, t3, 40
	or t3, t3, s6
	ld t6, 224(a5)
	add a7, a7, t3
	add a7, a7, t6
	xor s5, s5, a7
	srli s6, s5, 16
	slli s5, s5, 48
	or s5, s5, s6
	add s1, s1, s5
	xor t3, t3, s1
	srli s6, t3, 63
	slli t3, t3, 1
	or t3, t3, s6
	ld t6, 144(a5)
	add a3, a3, t1
	add a3, a3, t6
	xor s5, s5, a3
	srli s6, s5, 32
	slli s5, s5, 32
	or s5, s5, s6
	add s0, s0, s5
	xor t1, t1, s0
	srli s6, t1, 24
	slli t1, t1, 40
	or t1, t1, s6
	ld t6, 200(a5)
	add a3, a3, t1
	add a3, a3, t6
	xor s5, s5, a3
	srli s6, s5, 16
	slli s5, s5, 48
	or s5, s5, s6
	add s0, s0, s5
	xor t1, t1, s0
	srli s6, t1, 63
	slli t1, t1, 1
	or t1, t1, s6
	ld t6, 192(a5)
	add a4, a4, t2
	add a4, a4, t6
	xor s2, s2, a4
	srli s6, s2, 32
	slli s2, s2, 32
	or s2, s2, s6
	add s1, s1, s2
	xor t2, t2, s1
	srli s6, t2, 24
	slli t2, t2, 40
	or t2, t2, s6
	ld t6, 168(a5)
	add a4, a4, t2
	add a4, a4, t6
	xor s2, s2, a4
	srli s6, s2, 16
	slli s2, s2, 48
	or s2, s2, s6
	add s1, s1, s2
	xor t2, t2, s1
	srli s6, t2, 63
	slli t2, t2, 1
	or t2, t2, s6
	ld t6, 216(a5)
	add a6, a6, t3
	add a6, a6, t6
	xor s3, s3, a6
	srli s6, s3, 32
	slli s3, s3, 32
	or s3, s3, s6
	add t4, t4, s3
	xor t3, t3, t4
	srli s6, t3, 24
	slli t3, t3, 40
	or t3, t3, s6
	ld t6, 160(a5)
	add a6, a6, t3
	add a6, a6, t6
	xor s3, s3, a6
	srli s6, s3, 16
	slli s3, s3, 48
	or s3, s3, s6
	add t4, t4, s3
	xor t3, t3, t4
	srli s6, t3, 63
	slli t3, t3, 1
	or t3, t3, s6
	ld t6, 208(a5)
	add a7, a7, t0
	add a7, a7, t6
	xor s4, s4, a7
	srli s6, s4, 32
	slli s4, s4, 32
	or s4, s4, s6
	add t5, t5, s4
	xor t0, t0, t5
	srli s6, t0, 24
	slli t0, t0, 40
	or t0, t0, s6
	ld t6, 232(a5)
	add a7, a7, t0
	add a7, a7, t6
	xor s4, s4, a7
	srli s6, s4, 16
	slli s4, s4, 48
	or s4, s4, s6
	add t5, t5, s4
	xor t0, t0, t5
	srli s6, t0, 63
	slli t0, t0, 1
	or t0, t0, s6
	ld t6, 248(a5)
	add a3, a3, t0
	add a3, a3, t6
	xor s2, s2, a3
	srli s6, s2, 32
	slli s2, s2, 32
	or s2, s2, s6
	add t4, t4, s2
	xor t0, t0, t4
	srli s6, t0, 24
	slli t0, t0, 40
	or t0, t0, s6
	ld t6, 232(a5)
	add a3, a3, t0
	add a3, a3, t6
	xor s2, s2, a3
	srli s6, s2, 16
	slli s2, s2, 48
	or s2, s2, s6
	add t4, t4, s2
	xor t0, t0, t4
	srli s6, t0, 63
	slli t0, t0, 1
	or t0, t0, s6
	ld t6, 200(a5)
	add a4, a4, t1
	add a4, a4, t6
	xor s3, s3, a4
	srli s6, s3, 32
	slli s3, s3, 32
	or s3, s3, s6
	add t5, t5, s3
	xor t1, t1, t5
	srli s6, t1, 24
	slli t1, t1, 40
	or t1, t1, s6
	ld t6, 256(a5)
	add a4, a4, t1
	add a4, a4, t6
	xor s3, s3, a4
	srli s6, s3, 16
	slli s3, s3, 48
	or s3, s3, s6
	add t5, t5, s3
	xor t1, t1, t5
	srli s6, t1, 63
	slli t1, t1, 1
	or t1, t1, s6
	ld t6, 240(a5)
	add a6, a6, t2
	add a6, a6, t6
	xor s4, s4, a6
	srli s6, s4, 32
	slli s4, s4, 32
	or s4, s4, s6
	add s0, s0, s4
	xor t2, t2, s0
	srli s6, t2, 24
	slli t2, t2, 40
	or t2, t2, s6
	ld t6, 152(a5)
	add a6, a6, t2
	add a6, a6, t6
	xor s4, s4, a6
	srli s6, s4, 16
	slli s4, s4, 48
	or s4, s4, s6
	add s0, s0, s4
	xor t2, t2, s0
	srli s6, t2, 63
	slli t2, t2, 1
	or t2, t2, s6
	ld t6, 168(a5)
	add a7, a7, t3
	add a7, a7, t6
	xor s5, s5, a7
	srli s6, s5, 32
	slli s5, s5, 32
	or s5, s5, s6
	add s1, s1, s5
	xor t3, t3, s1
	srli s6, t3, 24
	slli t3, t3, 40
	or t3, t3, s6
	ld t6, 216(a5)
	add a7, a7, t3
	add a7, a7, t6
	xor s5, s5, a7
	srli s6, s5, 16
	slli s5, s5, 48
	or s5, s5, s6
	add s1, s1, s5
	xor t3, t3, s1
	srli s6, t3, 63
	slli t3, t3, 1
	or t3, t3, s6
	ld t6, 184(a5)
	add a3, a3, t1
	add a3, a3, t6
	xor s5, s5, a3
	srli s6, s5, 32
	slli s5, s5, 32
	or s5, s5, s6
	add s0, s0, s5
	xor t1, t1, s0
	srli s6, t1, 24
	slli t1, t1, 40
	or t1, t1, s6
	ld t6, 144(a5)
	add a3, a3, t1
	add a3, a3, t6
	xor s5, s5, a3
	srli s6, s5, 16
	slli s5, s5, 48
	or s5, s5, s6
	add s0, s0, s5
	xor t1, t1, s0
	srli s6, t1, 63
	slli t1, t1, 1
	or t1, t1, s6
	ld t6, 264(a5)
	add a4, a4, t2
	add a4, a4, t6
	xor s2, s2, a4
	srli s6, s2, 32
	slli s2, s2, 32
	or s2, s2, s6
	add s1, s1, s2
	xor t2, t2, s1
	srli s6, t2, 24
	slli t2, t2, 40
	or t2, t2, s6
	ld t6, 176(a5)
	add a4, a4, t2
	add a4, a4, t6
	xor s2, s2, a4
	srli s6, s2, 16
	slli s2, s2, 48
	or s2, s2, s6
	add s1, s1, s2
	xor t2, t2, s1
	srli s6, t2, 63
	slli t2, t2, 1
	or t2, t2, s6
	ld t6, 208(a5)
	add a6, a6, t3
	add a6, a6, t6
	xor s3, s3, a6
	srli s6, s3, 32
	slli s3, s3, 32
	or s3, s3, s6
	add t4, t4, s3
	xor t3, t3, t4
	srli s6, t3, 24
	slli t3, t3, 40
	or t3, t3, s6
	ld t6, 192(a5)
	add a6, a6, t3
	add a6, a6, t6
	xor s3, s3, a6
	srli s6, s3, 16
	slli s3, s3, 48
	or s3, s3, s6
	add t4, t4, s3
	xor t3, t3, t4
	srli s6, t3, 63
	slli t3, t3, 1
	or t3, t3, s6
	ld t6, 160(a5)
	add a7, a7, t0
	add a7, a7, t6
	xor s4, s4, a7
	srli s6, s4, 32
	slli s4, s4, 32
	or s4, s4, s6
	add t5, t5, s4
	xor t0, t0, t5
	srli s6, t0, 24
	slli t0, t0, 40
	or t0, t0, s6
	ld t6, 224(a5)
	add a7, a7, t0
	add a7, a7, t6
	xor s4, s4, a7
	srli s6, s4, 16
	slli s4, s4, 48
	or s4, s4, s6
	add t5, t5, s4
	xor t0, t0, t5
	srli s6, t0, 63
	slli t0, t0, 1
	or t0, t0, s6
	ld t6, 192(a5)
	add a3, a3, t0
	add a3, a3, t6
	xor s2, s2, a3
	srli s6, s2, 32
	slli s2, s2, 32
	or s2, s2, s6
	add t4, t4, s2
	xor t0, t0, t4
	srli s6, t0, 24
	slli t0, t0, 40
	or t0, t0, s6
	ld t6, 264(a5)
	add a3, a3, t0
	add a3, a3, t6
	xor s2, s2, a3
	srli s6, s2, 16
	slli s2, s2, 48
	or s2, s2, s6
	add t4, t4, s2
	xor t0, t0, t4
	srli s6, t0, 63
	slli t0, t0, 1
	or t0, t0, s6
	ld t6, 256(a5)
	add a4, a4, t1
	add a4, a4, t6
	xor s3, s3, a4
	srli s6, s3, 32
	slli s3, s3, 32
	or s3, s3, s6
	add t5, t5, s3
	xor t1, t1, t5
	srli s6, t1, 24
	slli t1, t1, 40
	or t1, t1, s6
	ld t6, 216(a5)
	add a4, a4, t1
	add a4, a4, t6
	xor s3, s3, a4
	srli s6, s3, 16
	slli s3, s3, 48
	or s3, s3, s6
	add t5, t5, s3
	xor t1, t1, t5
	srli s6, t1, 63
	slli t1, t1, 1
	or t1, t1, s6
	ld t6, 232(a5)
	add a6, a6, t2
	add a6, a6, t6
	xor s4, s4, a6
	srli s6, s4, 32
	slli s4, s4, 32
	or s4, s4, s6
	add s0, s0, s4
	xor t2, t2, s0
	srli s6, t2, 24
	slli t2, t2, 40
	or t2, t2, s6
	ld t6, 168(a5)
	add a6, a6, t2
	add a6, a6, t6
	xor s4, s4, a6
	srli s6, s4, 16
	slli s4, s4, 48
	or s4, s4, s6
	add s0, s0, s4
	xor t2, t2, s0
	srli s6, t2, 63
	slli t2, t2, 1
	or t2, t2, s6
	ld t6, 144(a5)
	add a7, a7, t3
	add a7, a7, t6
	xor s5, s5, a7
	srli s6, s5, 32
	slli s5, s5, 32
	or s5, s5, s6
	add s1, s1, s5
	xor t3, t3, s1
	srli s6, t3, 24
	slli t3, t3, 40
	or t3, t3, s6
	ld t6, 208(a5)
	add a7, a7, t3
	add a7, a7, t6
	xor s5, s5, a7
	srli s6, s5, 16
	slli s5, s5, 48
	or s5, s5, s6
	add s1, s1, s5
	xor t3, t3, s1
	srli s6, t3, 63
	slli t3, t3, 1
	or t3, t3, s6
	ld t6, 240(a5)
	add a3, a3, t1
	add a3, a3, t6
	xor s5, s5, a3
	srli s6, s5, 32
	slli s5, s5, 32
	or s5, s5, s6
	add s0, s0, s5
	xor t1, t1, s0
	srli s6, t1, 24
	slli t1, t1, 40
	or t1, t1, s6
	ld t6, 160(a5)
	add a3, a3, t1
	add a3, a3, t6
	xor s5, s5, a3
	srli s6, s5, 16
	slli s5, s5, 48
	or s5, s5, s6
	add s0, s0, s5
	xor t1, t1, s0
	srli s6, t1, 63
	slli t1, t1, 1
	or t1, t1, s6
	ld t6, 248(a5)
	add a4, a4, t2
	add a4, a4, t6
	xor s2, s2, a4
	srli s6, s2, 32
	slli s2, s2, 32
	or s2, s2, s6
	add s1, s1, s2
	xor t2, t2, s1
	srli s6, t2, 24
	slli t2, t2, 40
	or t2, t2, s6
	ld t6, 200(a5)
	add a4, a4, t2
	add a4, a4, t6
	xor s2, s2, a4
	srli s6, s2, 16
	slli s2, s2, 48
	or s2, s2, s6
	add s1, s1, s2
	xor t2, t2, s1
	srli s6, t2, 63
	slli t2, t2, 1
	or t2, t2, s6
	ld t6, 152(a5)
	add a6, a6, t3
	add a6, a6, t6
	xor s3, s3, a6
	srli s6, s3, 32
	slli s3, s3, 32
	or s3, s3, s6
	add t4, t4, s3
	xor t3, t3, t4
	srli s6, t3, 24
	slli t3, t3, 40
	or t3, t3, s6
	ld t6, 176(a5)
	add a6, a6, t3
	add a6, a6, t6
	xor s3, s3, a6
	srli s6, s3, 16
	slli s3, s3, 48
	or s3, s3, s6
	add t4, t4, s3
	xor t3, t3, t4
	srli s6, t3, 63
	slli t3, t3, 1
	or t3, t3, s6
	ld t6, 224(a5)
	add a7, a7, t0
	add a7, a7, t6
	xor s4, s4, a7
	srli s6, s4, 32
	slli s4, s4, 32
	or s4, s4, s6
	add t5, t5, s4
	xor t0, t0, t5
	srli s6, t0, 24
	slli t0, t0, 40
	or t0, t0, s6
	ld t6, 184(a5)
	add a7, a7, t0
	add a7, a7, t6
	xor s4, s4, a7
	srli s6, s4, 16
	slli s4, s4, 48
	or s4, s4, s6
	add t5, t5, s4
	xor t0, t0, t5
	srli s6, t0, 63
	slli t0, t0, 1
	or t0, t0, s6
	ld t6, 224(a5)
	add a3, a3, t0
	add a3, a3, t6
	xor s2, s2, a3
	srli s6, s2, 32
	slli s2, s2, 32
	or s2, s2, s6
	add t4, t4, s2
	xor t0, t0, t4
	srli s6, t0, 24
	slli t0, t0, 40
	or t0, t0, s6
	ld t6, 160(a5)
	add a3, a3, t0
	add a3, a3, t6
	xor s2, s2, a3
	srli s6, s2, 16
	slli s2, s2, 48
	or s2, s2, s6
	add t4, t4, s2
	xor t0, t0, t4
	srli s6, t0, 63
	slli t0, t0, 1
	or t0, t0, s6
	ld t6, 208(a5)
	add a4, a4, t1
	add a4, a4, t6
	xor s3, s3, a4
	srli s6, s3, 32
	slli s3, s3, 32
	or s3, s3, s6
	add t5, t5, s3
	xor t1, t1, t5
	srli s6, t1, 24
	slli t1, t1, 40
	or t1, t1, s6
	ld t6, 176(a5)
	add a4, a4, t1
	add a4, a4, t6
	xor s3, s3, a4
	srli s6, s3, 16
	slli s3, s3, 48
	or s3, s3, s6
	add t5, t5, s3
	xor t1, t1, t5
	srli s6, t1, 63
	slli t1, t1, 1
	or t1, t1, s6
	ld t6, 200(a5)
	add a6, a6, t2
	add a6, a6, t6
	xor s4, s4, a6
	srli s6, s4, 32
	slli s4, s4, 32
	or s4, s4, s6
	add s0, s0, s4
	xor t2, t2, s0
	srli s6, t2, 24
	slli t2, t2, 40
	or t2, t2, s6
	ld t6, 192(a5)
	add a6, a6, t2
	add a6, a6, t6
	xor s4, s4, a6
	srli s6, s4, 16
	slli s4, s4, 48
	or s4, s4, s6
	add s0, s0, s4
	xor t2, t2, s0
	srli s6, t2, 63
	slli t2, t2, 1
	or t2, t2, s6
	ld t6, 152(a5)
	add a7, a7, t3
	add a7, a7, t6
	xor s5, s5, a7
	srli s6, s5, 32
	slli s5, s5, 32
	or s5, s5, s6
	add s1, s1, s5
	xor t3, t3, s1
	srli s6, t3, 24
	slli t3, t3, 40
	or t3, t3, s6
	ld t6, 184(a5)
	add a7, a7, t3
	add a7, a7, t6
	xor s5, s5, a7
	srli s6, s5, 16
	slli s5, s5, 48
	or s5, s5, s6
	add s1, s1, s5
	xor t3, t3, s1
	srli s6, t3, 63
	slli t3, t3, 1
	or t3, t3, s6
	ld t6, 264(a5)
	add a3, a3, t1
	add a3, a3, t6
	xor s5, s5, a3
	srli s6, s5, 32
	slli s5, s5, 32
	or s5, s5, s6
	add s0, s0, s5
	xor t1, t1, s0
	srli s6, t1, 24
	slli t1, t1, 40
	or t1, t1, s6
	ld t6, 232(a5)
	add a3, a3, t1
	add a3, a3, t6
	xor s5, s5, a3
	srli s6, s5, 16
	slli s5, s5, 48
	or s5, s5, s6
	add s0, s0, s5
	xor t1, t1, s0
	srli s6, t1, 63
	slli t1, t1, 1
	or t1, t1, s6
	ld t6, 216(a5)
	add a4, a4, t2
	add a4, a4, t6
	xor s2, s2, a4
	srli s6, s2, 32
	slli s2, s2, 32
	or s2, s2, s6
	add s1, s1, s2
	xor t2, t2, s1
	srli s6, t2, 24
	slli t2, t2, 40
	or t2, t2, s6
	ld t6, 256(a5)
	add a4, a4, t2
	add a4, a4, t6
	xor s2, s2, a4
	srli s6, s2, 16
	slli s2, s2, 48
	or s2, s2, s6
	add s1, s1, s2
	xor t2, t2, s1
	srli s6, t2, 63
	slli t2, t2, 1
	or t2, t2, s6
	ld t6, 168(a5)
	add a6, a6, t3
	add a6, a6, t6
	xor s3, s3, a6
	srli s6, s3, 32
	slli s3, s3, 32
	or s3, s3, s6
	add t4, t4, s3
	xor t3, t3, t4
	srli s6, t3, 24
	slli t3, t3, 40
	or t3, t3, s6
	ld t6, 240(a5)
	add a6, a6, t3
	add a6, a6, t6
	xor s3, s3, a6
	srli s6, s3, 16
	slli s3, s3, 48
	or s3, s3, s6
	add t4, t4, s3
	xor t3, t3, t4
	srli s6, t3, 63
	slli t3, t3, 1
	or t3, t3, s6
	ld t6, 248(a5)
	add a7, a7, t0
	add a7, a7, t6
	xor s4, s4, a7
	srli s6, s4, 32
	slli s4, s4, 32
	or s4, s4, s6
	add t5, t5, s4
	xor t0, t0, t5
	srli s6, t0, 24
	slli t0, t0, 40
	or t0, t0, s6
	ld t6, 144(a5)
	add a7, a7, t0
	add a7, a7, t6
	xor s4, s4, a7
	srli s6, s4, 16
	slli s4, s4, 48
	or s4, s4, s6
	add t5, t5, s4
	xor t0, t0, t5
	srli s6, t0, 63
	slli t0, t0, 1
	or t0, t0, s6
	ld t6, 144(a5)
	add a3, a3, t0
	add a3, a3, t6
	xor s2, s2, a3
	srli s6, s2, 32
	slli s2, s2, 32
	or s2, s2, s6
	add t4, t4, s2
	xor t0, t0, t4
	srli s6, t0, 24
	slli t0, t0, 40
	or t0, t0, s6
	ld t6, 152(a5)
	add a3, a3, t0
	add a3, a3, t6
	xor s2, s2, a3
	srli s6, s2, 16
	slli s2, s2, 48
	or s2, s2, s6
	add t4, t4, s2
	xor t0, t0, t4
	srli s6, t0, 63
	slli t0, t0, 1
	or t0, t0, s6
	ld t6, 160(a5)
	add a4, a4, t1
	add a4, a4, t6
	xor s3, s3, a4
	srli s6, s3, 32
	slli s3, s3, 32
	or s3, s3, s6
	add t5, t5, s3
	xor t1, t1, t5
	srli s6, t1, 24
	slli t1, t1, 40
	or t1, t1, s6
	ld t6, 168(a5)
	add a4, a4, t1
	add a4, a4, t6
	xor s3, s3, a4
	srli s6, s3, 16
	slli s3, s3, 48
	or s3, s3, s6
	add t5, t5, s3
	xor t1, t1, t5
	srli s6, t1, 63
	slli t1, t1, 1
	or t1, t1, s6
	ld t6, 176(a5)
	add a6, a6, t2
	add a6, a6, t6
	xor s4, s4, a6
	srli s6, s4, 32
	slli s4, s4, 32
	or s4, s4, s6
	add s0, s0, s4
	xor t2, t2, s0
	srli s6, t2, 24
	slli t2, t2, 40
	or t2, t2, s6
	ld t6, 184(a5)
	add a6, a6, t2
	add a6, a6, t6
	xor s4, s4, a6
	srli s6, s4, 16
	slli s4, s4, 48
	or s4, s4, s6
	add s0, s0, s4
	xor t2, t2, s0
	srli s6, t2, 63
	slli t2, t2, 1
	or t2, t2, s6
	ld t6, 192(a5)
	add a7, a7, t3
	add a7, a7, t6
	xor s5, s5, a7
	srli s6, s5, 32
	slli s5, s5, 32
	or s5, s5, s6
	add s1, s1, s5
	xor t3, t3, s1
	srli s6, t3, 24
	slli t3, t3, 40
	or t3, t3, s6
	ld t6, 200(a5)
	add a7, a7, t3
	add a7, a7, t6
	xor s5, s5, a7
	srli s6, s5, 16
	slli s5, s5, 48
	or s5, s5, s6
	add s1, s1, s5
	xor t3, t3, s1
	srli s6, t3, 63
	slli t3, t3, 1
	or t3, t3, s6
	ld t6, 208(a5)
	add a3, a3, t1
	add a3, a3, t6
	xor s5, s5, a3
	srli s6, s5, 32
	slli s5, s5, 32
	or s5, s5, s6
	add s0, s0, s5
	xor t1, t1, s0
	srli s6, t1, 24
	slli t1, t1, 40
	or t1, t1, s6
	ld t6, 216(a5)
	add a3, a3, t1
	add a3, a3, t6
	xor s5, s5, a3
	srli s6, s5, 16
	slli s5, s5, 48
	or s5, s5, s6
	add s0, s0, s5
	xor t1, t1, s0
	srli s6, t1, 63
	slli t1, t1, 1
	or t1, t1, s6
	ld t6, 224(a5)
	add a4, a4, t2
	add a4, a4, t6
	xor s2, s2, a4
	srli s6, s2, 32
	slli s2, s2, 32
	or s2, s2, s6
	add s1, s1, s2
	xor t2, t2, s1
	srli s6, t2, 24
	slli t2, t2, 40
	or t2, t2, s6
	ld t6, 232(a5)
	add a4, a4, t2
	add a4, a4, t6
	xor s2, s2, a4
	srli s6, s2, 16
	slli s2, s2, 48
	or s2, s2, s6
	add s1, s1, s2
	xor t2, t2, s1
	srli s6, t2, 63
	slli t2, t2, 1
	or t2, t2, s6
	ld t6, 240(a5)
	add a6, a6, t3
	add a6, a6, t6
	xor s3, s3, a6
	srli s6, s3, 32
	slli s3, s3, 32
	or s3, s3, s6
	add t4, t4, s3
	xor t3, t3, t4
	srli s6, t3, 24
	slli t3, t3, 40
	or t3, t3, s6
	ld t6, 248(a5)
	add a6, a6, t3
	add a6, a6, t6
	xor s3, s3, a6
	srli s6, s3, 16
	slli s3, s3, 48
	or s3, s3, s6
	add t4, t4, s3
	xor t3, t3, t4
	srli s6, t3, 63
	slli t3, t3, 1
	or t3, t3, s6
	ld t6, 256(a5)
	add a7, a7, t0
	add a7, a7, t6
	xor s4, s4, a7
	srli s6, s4, 32
	slli s4, s4, 32
	or s4, s4, s6
	add t5, t5, s4
	xor t0, t0, t5
	srli s6, t0, 24
	slli t0, t0, 40
	or t0, t0, s6
	ld t6, 264(a5)
	add a7, a7, t0
	add a7, a7, t6
	xor s4, s4, a7
	srli s6, s4, 16
	slli s4, s4, 48
	or s4, s4, s6
	add t5, t5, s4
	xor t0, t0, t5
	srli s6, t0, 63
	slli t0, t0, 1
	or t0, t0, s6
	ld t6, 256(a5)
	add a3, a3, t0
	add a3, a3, t6
	xor s2, s2, a3
	srli s6, s2, 32
	slli s2, s2, 32
	or s2, s2, s6
	add t4, t4, s2
	xor t0, t0, t4
	srli s6, t0, 24
	slli t0, t0, 40
	or t0, t0, s6
	ld t6, 224(a5)
	add a3, a3, t0
	add a3, a3, t6
	xor s2, s2, a3
	srli s6, s2, 16
	slli s2, s2, 48
	or s2, s2, s6
	add t4, t4, s2
	xor t0, t0, t4
	srli s6, t0, 63
	slli t0, t0, 1
	or t0, t0, s6
	ld t6, 176(a5)
	add a4, a4, t1
	add a4, a4, t6
	xor s3, s3, a4
	srli s6, s3, 32
	slli s3, s3, 32
	or s3, s3, s6
	add t5, t5, s3
	xor t1, t1, t5
	srli s6, t1, 24
	slli t1, t1, 40
	or t1, t1, s6
	ld t6, 208(a5)
	add a4, a4, t1
	add a4, a4, t6
	xor s3, s3, a4
	srli s6, s3, 16
	slli s3, s3, 48
	or s3, s3, s6
	add t5, t5, s3
	xor t1, t1, t5
	srli s6, t1, 63
	slli t1, t1, 1
	or t1, t1, s6
	ld t6, 216(a5)
	add a6, a6, t2
	add a6, a6, t6
	xor s4, s4, a6
	srli s6, s4, 32
	slli s4, s4, 32
	or s4, s4, s6
	add s0, s0, s4
	xor t2, t2, s0
	srli s6, t2, 24
	slli t2, t2, 40
	or t2, t2, s6
	ld t6, 264(a5)
	add a6, a6, t2
	add a6, a6, t6
	xor s4, s4, a6
	srli s6, s4, 16
	slli s4, s4, 48
	or s4, s4, s6
	add s0, s0, s4
	xor t2, t2, s0
	srli s6, t2, 63
	slli t2, t2, 1
	or t2, t2, s6
	ld t6, 248(a5)
	add a7, a7, t3
	add a7, a7, t6
	xor s5, s5, a7
	srli s6, s5, 32
	slli s5, s5, 32
	or s5, s5, s6
	add s1, s1, s5
	xor t3, t3, s1
	srli s6, t3, 24
	slli t3, t3, 40
	or t3, t3, s6
	ld t6, 192(a5)
	add a7, a7, t3
	add a7, a7, t6
	xor s5, s5, a7
	srli s6, s5, 16
	slli s5, s5, 48
	or s5, s5, s6
	add s1, s1, s5
	xor t3, t3, s1
	srli s6, t3, 63
	slli t3, t3, 1
	or t3, t3, s6
	ld t6, 152(a5)
	add a3, a3, t1
	add a3, a3, t6
	xor s5, s5, a3
	srli s6, s5, 32
	slli s5, s5, 32
	or s5, s5, s6
	add s0, s0, s5
	xor t1, t1, s0
	srli s6, t1, 24
	slli t1, t1, 40
	or t1, t1, s6
	ld t6, 240(a5)
	add a3, a3, t1
	add a3, a3, t6
	xor s5, s5, a3
	srli s6, s5, 16
	slli s5, s5, 48
	or s5, s5, s6
	add s0, s0, s5
	xor t1, t1, s0
	srli s6, t1, 63
	slli t1, t1, 1
	or t1, t1, s6
	ld t6, 144(a5)
	add a4, a4, t2
	add a4, a4, t6
	xor s2, s2, a4
	srli s6, s2, 32
	slli s2, s2, 32
	or s2, s2, s6
	add s1, s1, s2
	xor t2, t2, s1
	srli s6, t2, 24
	slli t2, t2, 40
	or t2, t2, s6
	ld t6, 160(a5)
	add a4, a4, t2
	add a4, a4, t6
	xor s2, s2, a4
	srli s6, s2, 16
	slli s2, s2, 48
	or s2, s2, s6
	add s1, s1, s2
	xor t2, t2, s1
	srli s6, t2, 63
	slli t2, t2, 1
	or t2, t2, s6
	ld t6, 232(a5)
	add a6, a6, t3
	add a6, a6, t6
	xor s3, s3, a6
	srli s6, s3, 32
	slli s3, s3, 32
	or s3, s3, s6
	add t4, t4, s3
	xor t3, t3, t4
	srli s6, t3, 24
	slli t3, t3, 40
	or t3, t3, s6
	ld t6, 200(a5)
	add a6, a6, t3
	add a6, a6, t6
	xor s3, s3, a6
	srli s6, s3, 16
	slli s3, s3, 48
	or s3, s3, s6
	add t4, t4, s3
	xor t3, t3, t4
	srli s6, t3, 63
	slli t3, t3, 1
	or t3, t3, s6
	ld t6, 184(a5)
	add a7, a7, t0
	add a7, a7, t6
	xor s4, s4, a7
	srli s6, s4, 32
	slli s4, s4, 32
	or s4, s4, s6
	add t5, t5, s4
	xor t0, t0, t5
	srli s6, t0, 24
	slli t0, t0, 40
	or t0, t0, s6
	ld t6, 168(a5)
	add a7, a7, t0
	add a7, a7, t6
	xor s4, s4, a7
	srli s6, s4, 16
	slli s4, s4, 48
	or s4, s4, s6
	add t5, t5, s4
	xor t0, t0, t5
	srli s6, t0, 63
	slli t0, t0, 1
	or t0, t0, s6
	ld t6, 80(a5)
	xor t6, t6, a3
	xor t6, t6, t4
	sd t6, 80(a5)
	ld t6, 88(a5)
	xor t6, t6, a4
	xor t6, t6, t5
	sd t6, 88(a5)
	ld t6, 96(a5)
	xor t6, t6, a6
	xor t6, t6, s0
	sd t6, 96(a5)
	ld t6, 104(a5)
	xor t6, t6, a7
	xor t6, t6, s1
	sd t6, 104(a5)
	ld t6, 112(a5)
	xor t6, t6, t0
	xor t6, t6, s2
	sd t6, 112(a5)
	ld t6, 120(a5)
	xor t6, t6, t1
	xor t6, t6, s3
	sd t6, 120(a5)
	ld t6, 128(a5)
	xor t6, t6, t2
	xor t6, t6, s4
	sd t6, 128(a5)
	ld t6, 136(a5)
	xor t6, t6, t3
	xor t6, t6, s5
	sd t6, 136(a5)
	addi a1, a1, 128
	ld a3, 56(a5)
	addi a3, a3, 128
	sd a3, 56(a5)
	srli a4, a3, 7
	addi a4, a4, -1
	srli a4, a4, 63
	ld a6, 64(a5)
	add a6, a6, a4
	sd a6, 64(a5)
	addi a2, a2, -1
	bnez a2, 22b
	j 21f
20:
21:
	ld t6, 80(a5)
	sb t6, 0(a0)
	srli a3, t6, 8
	sb a3, 1(a0)
	srli a3, t6, 16
	sb a3, 2(a0)
	srli a3, t6, 24
	sb a3, 3(a0)
	srli a3, t6, 32
	sb a3, 4(a0)
	srli a4, a3, 8
	sb a4, 5(a0)
	srli a4, a3, 16
	sb a4, 6(a0)
	srli a4, a3, 24
	sb a4, 7(a0)
	ld t6, 88(a5)
	sb t6, 8(a0)
	srli a3, t6, 8
	sb a3, 9(a0)
	srli a3, t6, 16
	sb a3, 10(a0)
	srli a3, t6, 24
	sb a3, 11(a0)
	srli a3, t6, 32
	sb a3, 12(a0)
	srli a4, a3, 8
	sb a4, 13(a0)
	srli a4, a3, 16
	sb a4, 14(a0)
	srli a4, a3, 24
	sb a4, 15(a0)
	ld t6, 96(a5)
	sb t6, 16(a0)
	srli a3, t6, 8
	sb a3, 17(a0)
	srli a3, t6, 16
	sb a3, 18(a0)
	srli a3, t6, 24
	sb a3, 19(a0)
	srli a3, t6, 32
	sb a3, 20(a0)
	srli a4, a3, 8
	sb a4, 21(a0)
	srli a4, a3, 16
	sb a4, 22(a0)
	srli a4, a3, 24
	sb a4, 23(a0)
	ld t6, 104(a5)
	sb t6, 24(a0)
	srli a3, t6, 8
	sb a3, 25(a0)
	srli a3, t6, 16
	sb a3, 26(a0)
	srli a3, t6, 24
	sb a3, 27(a0)
	srli a3, t6, 32
	sb a3, 28(a0)
	srli a4, a3, 8
	sb a4, 29(a0)
	srli a4, a3, 16
	sb a4, 30(a0)
	srli a4, a3, 24
	sb a4, 31(a0)
	ld t6, 112(a5)
	sb t6, 32(a0)
	srli a3, t6, 8
	sb a3, 33(a0)
	srli a3, t6, 16
	sb a3, 34(a0)
	srli a3, t6, 24
	sb a3, 35(a0)
	srli a3, t6, 32
	sb a3, 36(a0)
	srli a4, a3, 8
	sb a4, 37(a0)
	srli a4, a3, 16
	sb a4, 38(a0)
	srli a4, a3, 24
	sb a4, 39(a0)
	ld t6, 120(a5)
	sb t6, 40(a0)
	srli a3, t6, 8
	sb a3, 41(a0)
	srli a3, t6, 16
	sb a3, 42(a0)
	srli a3, t6, 24
	sb a3, 43(a0)
	srli a3, t6, 32
	sb a3, 44(a0)
	srli a4, a3, 8
	sb a4, 45(a0)
	srli a4, a3, 16
	sb a4, 46(a0)
	srli a4, a3, 24
	sb a4, 47(a0)
	ld t6, 128(a5)
	sb t6, 48(a0)
	srli a3, t6, 8
	sb a3, 49(a0)
	srli a3, t6, 16
	sb a3, 50(a0)
	srli a3, t6, 24
	sb a3, 51(a0)
	srli a3, t6, 32
	sb a3, 52(a0)
	srli a4, a3, 8
	sb a4, 53(a0)
	srli a4, a3, 16
	sb a4, 54(a0)
	srli a4, a3, 24
	sb a4, 55(a0)
	ld t6, 136(a5)
	sb t6, 56(a0)
	srli a3, t6, 8
	sb a3, 57(a0)
	srli a3, t6, 16
	sb a3, 58(a0)
	srli a3, t6, 24
	sb a3, 59(a0)
	srli a3, t6, 32
	sb a3, 60(a0)
	srli a4, a3, 8
	sb a4, 61(a0)
	srli a4, a3, 16
	sb a4, 62(a0)
	srli a4, a3, 24
	sb a4, 63(a0)
	ld s0, 0(a5)
	ld s1, 8(a5)
	ld s2, 16(a5)
	ld s3, 24(a5)
	ld s4, 32(a5)
	ld s5, 40(a5)
	ld s6, 48(a5)
	ret
	.option pop
