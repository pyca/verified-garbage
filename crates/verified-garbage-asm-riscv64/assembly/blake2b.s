// The functions of `src/blake2b.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_blake2b_init:
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

vg_blake2b_update:
	.option push
	.option arch, +m, +c
	addi sp, sp, -576
	addi a4, sp, 0
	addi t0, a4, 7
	andi t0, t0, -8
	sd ra, 512(t0)
	sd s7, 520(t0)
	sd s9, 528(t0)
	sd s10, 536(t0)
	sd s11, 544(t0)
	sd s8, 552(t0)
	addi s7, a0, 0
	addi s8, t0, 0
	addi s9, a2, 0
	addi s10, a3, 0
	addi s11, a1, 0
	addi a7, s11, -1
	andi a7, a7, 127
	addi a7, a7, 1
	beqz s11, 20f
	j 21f
20:
	addi a7, zero, 0
21:
	beqz s10, 22f
	beqz a7, 24f
	addi t3, zero, 128
	sub t3, t3, a7
	srli t1, s10, 7
	beqz t1, 26f
	j 27f
26:
	add t1, s10, a7
	srli t1, t1, 7
	beqz t1, 28f
	j 29f
28:
	addi t3, s10, 0
29:
27:
	sub s10, s10, t3
	add s11, s11, t3
	beqz t3, 210f
212:
	lbu t1, 0(s9)
	add t2, s7, a7
	sb t1, 64(t2)
	addi s9, s9, 1
	addi a7, a7, 1
	addi t3, t3, -1
	bnez t3, 212b
	j 211f
210:
211:
	beqz s10, 213f
	addi a0, s7, 0
	addi a1, s7, 64
	addi a2, zero, 1
	addi a3, s11, 0
	addi a4, zero, 0
	addi a5, s8, 0
	call {vg_blake2b_compress}
	addi a7, zero, 0
	j 214f
213:
214:
	j 25f
24:
25:
	beqz s10, 215f
	addi t1, s10, -1
	srli t2, t1, 7
	beqz t2, 217f
	addi a0, s7, 0
	addi a1, s9, 0
	addi a2, t2, 0
	addi a3, s11, 128
	addi a4, zero, 0
	addi a5, s8, 0
	call {vg_blake2b_compress}
	addi t1, s10, -1
	andi t1, t1, 127
	addi t1, t1, 1
	sub t2, s10, t1
	add s9, s9, t2
	add s11, s11, t2
	addi s10, t1, 0
	addi a7, zero, 0
	j 218f
217:
218:
	addi t3, s10, 0
	add s11, s11, s10
	addi s10, zero, 0
219:
	lbu t1, 0(s9)
	add t2, s7, a7
	sb t1, 64(t2)
	addi s9, s9, 1
	addi a7, a7, 1
	addi t3, t3, -1
	bnez t3, 219b
	j 216f
215:
216:
	j 23f
22:
23:
	ld ra, 512(s8)
	ld s7, 520(s8)
	ld s9, 528(s8)
	ld s10, 536(s8)
	ld s11, 544(s8)
	ld s8, 552(s8)
	addi sp, sp, 576
	ret
	.option pop

vg_blake2b_finalize:
	.option push
	.option arch, +m, +c
	addi sp, sp, -576
	addi a3, sp, 0
	addi t0, a3, 7
	andi t0, t0, -8
	sd ra, 512(t0)
	sd s7, 520(t0)
	sd s9, 528(t0)
	sd s10, 536(t0)
	sd s11, 544(t0)
	sd s8, 552(t0)
	addi s7, a0, 0
	addi s8, t0, 0
	addi s9, a2, 0
	addi s11, a1, 0
	addi a7, s11, -1
	andi a7, a7, 127
	addi a7, a7, 1
	beqz s11, 20f
	j 21f
20:
	addi a7, zero, 0
21:
	addi t1, zero, 0
	addi t3, zero, 128
	sub t3, t3, a7
	beqz t3, 22f
24:
	add t2, s7, a7
	sb t1, 64(t2)
	addi a7, a7, 1
	addi t3, t3, -1
	bnez t3, 24b
	j 23f
22:
23:
	addi a0, s7, 0
	addi a1, s7, 64
	addi a2, zero, 1
	addi a3, s11, 0
	addi a4, zero, 1
	addi a5, s8, 0
	call {vg_blake2b_compress}
	lbu t1, 0(s7)
	sb t1, 0(s9)
	lbu t1, 1(s7)
	sb t1, 1(s9)
	lbu t1, 2(s7)
	sb t1, 2(s9)
	lbu t1, 3(s7)
	sb t1, 3(s9)
	lbu t1, 4(s7)
	sb t1, 4(s9)
	lbu t1, 5(s7)
	sb t1, 5(s9)
	lbu t1, 6(s7)
	sb t1, 6(s9)
	lbu t1, 7(s7)
	sb t1, 7(s9)
	lbu t1, 8(s7)
	sb t1, 8(s9)
	lbu t1, 9(s7)
	sb t1, 9(s9)
	lbu t1, 10(s7)
	sb t1, 10(s9)
	lbu t1, 11(s7)
	sb t1, 11(s9)
	lbu t1, 12(s7)
	sb t1, 12(s9)
	lbu t1, 13(s7)
	sb t1, 13(s9)
	lbu t1, 14(s7)
	sb t1, 14(s9)
	lbu t1, 15(s7)
	sb t1, 15(s9)
	lbu t1, 16(s7)
	sb t1, 16(s9)
	lbu t1, 17(s7)
	sb t1, 17(s9)
	lbu t1, 18(s7)
	sb t1, 18(s9)
	lbu t1, 19(s7)
	sb t1, 19(s9)
	lbu t1, 20(s7)
	sb t1, 20(s9)
	lbu t1, 21(s7)
	sb t1, 21(s9)
	lbu t1, 22(s7)
	sb t1, 22(s9)
	lbu t1, 23(s7)
	sb t1, 23(s9)
	lbu t1, 24(s7)
	sb t1, 24(s9)
	lbu t1, 25(s7)
	sb t1, 25(s9)
	lbu t1, 26(s7)
	sb t1, 26(s9)
	lbu t1, 27(s7)
	sb t1, 27(s9)
	lbu t1, 28(s7)
	sb t1, 28(s9)
	lbu t1, 29(s7)
	sb t1, 29(s9)
	lbu t1, 30(s7)
	sb t1, 30(s9)
	lbu t1, 31(s7)
	sb t1, 31(s9)
	lbu t1, 32(s7)
	sb t1, 32(s9)
	lbu t1, 33(s7)
	sb t1, 33(s9)
	lbu t1, 34(s7)
	sb t1, 34(s9)
	lbu t1, 35(s7)
	sb t1, 35(s9)
	lbu t1, 36(s7)
	sb t1, 36(s9)
	lbu t1, 37(s7)
	sb t1, 37(s9)
	lbu t1, 38(s7)
	sb t1, 38(s9)
	lbu t1, 39(s7)
	sb t1, 39(s9)
	lbu t1, 40(s7)
	sb t1, 40(s9)
	lbu t1, 41(s7)
	sb t1, 41(s9)
	lbu t1, 42(s7)
	sb t1, 42(s9)
	lbu t1, 43(s7)
	sb t1, 43(s9)
	lbu t1, 44(s7)
	sb t1, 44(s9)
	lbu t1, 45(s7)
	sb t1, 45(s9)
	lbu t1, 46(s7)
	sb t1, 46(s9)
	lbu t1, 47(s7)
	sb t1, 47(s9)
	lbu t1, 48(s7)
	sb t1, 48(s9)
	lbu t1, 49(s7)
	sb t1, 49(s9)
	lbu t1, 50(s7)
	sb t1, 50(s9)
	lbu t1, 51(s7)
	sb t1, 51(s9)
	lbu t1, 52(s7)
	sb t1, 52(s9)
	lbu t1, 53(s7)
	sb t1, 53(s9)
	lbu t1, 54(s7)
	sb t1, 54(s9)
	lbu t1, 55(s7)
	sb t1, 55(s9)
	lbu t1, 56(s7)
	sb t1, 56(s9)
	lbu t1, 57(s7)
	sb t1, 57(s9)
	lbu t1, 58(s7)
	sb t1, 58(s9)
	lbu t1, 59(s7)
	sb t1, 59(s9)
	lbu t1, 60(s7)
	sb t1, 60(s9)
	lbu t1, 61(s7)
	sb t1, 61(s9)
	lbu t1, 62(s7)
	sb t1, 62(s9)
	lbu t1, 63(s7)
	sb t1, 63(s9)
	ld ra, 512(s8)
	ld s7, 520(s8)
	ld s9, 528(s8)
	ld s10, 536(s8)
	ld s11, 544(s8)
	ld s8, 552(s8)
	addi sp, sp, 576
	ret
	.option pop
