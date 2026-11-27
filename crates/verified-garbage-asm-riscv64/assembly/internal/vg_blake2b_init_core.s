// The functions of `src/internal/vg_blake2b_init_core.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_blake2b_init_core:
	.option push
	.option arch, +m, +c
	lui t1, 767611
	addiw t1, t1, -379
	slli t1, t1, 32
	lui t6, 543914
	addiw t6, t6, 1851
	slli t6, t6, 32
	srli t6, t6, 32
	or t1, t1, t6
	sb t1, 8(a0)
	srli t2, t1, 8
	sb t2, 9(a0)
	srli t2, t1, 16
	sb t2, 10(a0)
	srli t2, t1, 24
	sb t2, 11(a0)
	srli t2, t1, 32
	sb t2, 12(a0)
	srli t3, t2, 8
	sb t3, 13(a0)
	srli t3, t2, 16
	sb t3, 14(a0)
	srli t3, t2, 24
	sb t3, 15(a0)
	lui t1, 247535
	addiw t1, t1, 882
	slli t1, t1, 32
	lui t6, 1042768
	addiw t6, t6, -2005
	slli t6, t6, 32
	srli t6, t6, 32
	or t1, t1, t6
	sb t1, 16(a0)
	srli t2, t1, 8
	sb t2, 17(a0)
	srli t2, t1, 16
	sb t2, 18(a0)
	srli t2, t1, 24
	sb t2, 19(a0)
	srli t2, t1, 32
	sb t2, 20(a0)
	srli t3, t2, 8
	sb t3, 21(a0)
	srli t3, t2, 16
	sb t3, 22(a0)
	srli t3, t2, 24
	sb t3, 23(a0)
	lui t1, 677119
	addiw t1, t1, 1338
	slli t1, t1, 32
	lui t6, 389587
	addiw t6, t6, 1777
	slli t6, t6, 32
	srli t6, t6, 32
	or t1, t1, t6
	sb t1, 24(a0)
	srli t2, t1, 8
	sb t2, 25(a0)
	srli t2, t1, 16
	sb t2, 26(a0)
	srli t2, t1, 24
	sb t2, 27(a0)
	srli t2, t1, 32
	sb t2, 28(a0)
	srli t3, t2, 8
	sb t3, 29(a0)
	srli t3, t2, 16
	sb t3, 30(a0)
	srli t3, t2, 24
	sb t3, 31(a0)
	lui t1, 332005
	addiw t1, t1, 639
	slli t1, t1, 32
	lui t6, 712296
	addiw t6, t6, 721
	slli t6, t6, 32
	srli t6, t6, 32
	or t1, t1, t6
	sb t1, 32(a0)
	srli t2, t1, 8
	sb t2, 33(a0)
	srli t2, t1, 16
	sb t2, 34(a0)
	srli t2, t1, 24
	sb t2, 35(a0)
	srli t2, t1, 32
	sb t2, 36(a0)
	srli t3, t2, 8
	sb t3, 37(a0)
	srli t3, t2, 16
	sb t3, 38(a0)
	srli t3, t2, 24
	sb t3, 39(a0)
	lui t1, 634967
	addiw t1, t1, -1908
	slli t1, t1, 32
	lui t6, 177127
	addiw t6, t6, -993
	slli t6, t6, 32
	srli t6, t6, 32
	or t1, t1, t6
	sb t1, 40(a0)
	srli t2, t1, 8
	sb t2, 41(a0)
	srli t2, t1, 16
	sb t2, 42(a0)
	srli t2, t1, 24
	sb t2, 43(a0)
	srli t2, t1, 32
	sb t2, 44(a0)
	srli t3, t2, 8
	sb t3, 45(a0)
	srli t3, t2, 16
	sb t3, 46(a0)
	srli t3, t2, 24
	sb t3, 47(a0)
	lui t1, 129086
	addiw t1, t1, -1621
	slli t1, t1, 32
	lui t6, 1029148
	addiw t6, t6, -661
	slli t6, t6, 32
	srli t6, t6, 32
	or t1, t1, t6
	sb t1, 48(a0)
	srli t2, t1, 8
	sb t2, 49(a0)
	srli t2, t1, 16
	sb t2, 50(a0)
	srli t2, t1, 24
	sb t2, 51(a0)
	srli t2, t1, 32
	sb t2, 52(a0)
	srli t3, t2, 8
	sb t3, 53(a0)
	srli t3, t2, 16
	sb t3, 54(a0)
	srli t3, t2, 24
	sb t3, 55(a0)
	lui t1, 376333
	addiw t1, t1, -743
	slli t1, t1, 32
	lui t6, 79842
	addiw t6, t6, 377
	slli t6, t6, 32
	srli t6, t6, 32
	or t1, t1, t6
	sb t1, 56(a0)
	srli t2, t1, 8
	sb t2, 57(a0)
	srli t2, t1, 16
	sb t2, 58(a0)
	srli t2, t1, 24
	sb t2, 59(a0)
	srli t2, t1, 32
	sb t2, 60(a0)
	srli t3, t2, 8
	sb t3, 61(a0)
	srli t3, t2, 16
	sb t3, 62(a0)
	srli t3, t2, 24
	sb t3, 63(a0)
	lui t1, 434334
	addiw t1, t1, 1639
	slli t1, t1, 32
	lui t6, 994269
	addiw t6, t6, -1784
	slli t6, t6, 32
	srli t6, t6, 32
	or t1, t1, t6
	slli t2, a3, 8
	xor t1, t1, t2
	xor t1, t1, a1
	sb t1, 0(a0)
	srli t2, t1, 8
	sb t2, 1(a0)
	srli t2, t1, 16
	sb t2, 2(a0)
	srli t2, t1, 24
	sb t2, 3(a0)
	srli t2, t1, 32
	sb t2, 4(a0)
	srli t3, t2, 8
	sb t3, 5(a0)
	srli t3, t2, 16
	sb t3, 6(a0)
	srli t3, t2, 24
	sb t3, 7(a0)
	beqz a3, 20f
	addi t1, zero, 0
	sb t1, 64(a0)
	sb t1, 65(a0)
	sb t1, 66(a0)
	sb t1, 67(a0)
	sb t1, 68(a0)
	sb t1, 69(a0)
	sb t1, 70(a0)
	sb t1, 71(a0)
	sb t1, 72(a0)
	sb t1, 73(a0)
	sb t1, 74(a0)
	sb t1, 75(a0)
	sb t1, 76(a0)
	sb t1, 77(a0)
	sb t1, 78(a0)
	sb t1, 79(a0)
	sb t1, 80(a0)
	sb t1, 81(a0)
	sb t1, 82(a0)
	sb t1, 83(a0)
	sb t1, 84(a0)
	sb t1, 85(a0)
	sb t1, 86(a0)
	sb t1, 87(a0)
	sb t1, 88(a0)
	sb t1, 89(a0)
	sb t1, 90(a0)
	sb t1, 91(a0)
	sb t1, 92(a0)
	sb t1, 93(a0)
	sb t1, 94(a0)
	sb t1, 95(a0)
	sb t1, 96(a0)
	sb t1, 97(a0)
	sb t1, 98(a0)
	sb t1, 99(a0)
	sb t1, 100(a0)
	sb t1, 101(a0)
	sb t1, 102(a0)
	sb t1, 103(a0)
	sb t1, 104(a0)
	sb t1, 105(a0)
	sb t1, 106(a0)
	sb t1, 107(a0)
	sb t1, 108(a0)
	sb t1, 109(a0)
	sb t1, 110(a0)
	sb t1, 111(a0)
	sb t1, 112(a0)
	sb t1, 113(a0)
	sb t1, 114(a0)
	sb t1, 115(a0)
	sb t1, 116(a0)
	sb t1, 117(a0)
	sb t1, 118(a0)
	sb t1, 119(a0)
	sb t1, 120(a0)
	sb t1, 121(a0)
	sb t1, 122(a0)
	sb t1, 123(a0)
	sb t1, 124(a0)
	sb t1, 125(a0)
	sb t1, 126(a0)
	sb t1, 127(a0)
	sb t1, 128(a0)
	sb t1, 129(a0)
	sb t1, 130(a0)
	sb t1, 131(a0)
	sb t1, 132(a0)
	sb t1, 133(a0)
	sb t1, 134(a0)
	sb t1, 135(a0)
	sb t1, 136(a0)
	sb t1, 137(a0)
	sb t1, 138(a0)
	sb t1, 139(a0)
	sb t1, 140(a0)
	sb t1, 141(a0)
	sb t1, 142(a0)
	sb t1, 143(a0)
	sb t1, 144(a0)
	sb t1, 145(a0)
	sb t1, 146(a0)
	sb t1, 147(a0)
	sb t1, 148(a0)
	sb t1, 149(a0)
	sb t1, 150(a0)
	sb t1, 151(a0)
	sb t1, 152(a0)
	sb t1, 153(a0)
	sb t1, 154(a0)
	sb t1, 155(a0)
	sb t1, 156(a0)
	sb t1, 157(a0)
	sb t1, 158(a0)
	sb t1, 159(a0)
	sb t1, 160(a0)
	sb t1, 161(a0)
	sb t1, 162(a0)
	sb t1, 163(a0)
	sb t1, 164(a0)
	sb t1, 165(a0)
	sb t1, 166(a0)
	sb t1, 167(a0)
	sb t1, 168(a0)
	sb t1, 169(a0)
	sb t1, 170(a0)
	sb t1, 171(a0)
	sb t1, 172(a0)
	sb t1, 173(a0)
	sb t1, 174(a0)
	sb t1, 175(a0)
	sb t1, 176(a0)
	sb t1, 177(a0)
	sb t1, 178(a0)
	sb t1, 179(a0)
	sb t1, 180(a0)
	sb t1, 181(a0)
	sb t1, 182(a0)
	sb t1, 183(a0)
	sb t1, 184(a0)
	sb t1, 185(a0)
	sb t1, 186(a0)
	sb t1, 187(a0)
	sb t1, 188(a0)
	sb t1, 189(a0)
	sb t1, 190(a0)
	sb t1, 191(a0)
	addi t2, a0, 64
22:
	lbu t1, 0(a2)
	sb t1, 0(t2)
	addi a2, a2, 1
	addi t2, t2, 1
	addi a3, a3, -1
	bnez a3, 22b
	j 21f
20:
21:
	ret
	.option pop
