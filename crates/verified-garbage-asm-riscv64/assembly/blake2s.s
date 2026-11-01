// The functions of `src/blake2s.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_blake2s_init:
	.option push
	.option arch, +m, +c
	lui t1, 767611
	addiw t1, t1, -379
	sb t1, 4(a0)
	srli t2, t1, 8
	sb t2, 5(a0)
	srli t2, t1, 16
	sb t2, 6(a0)
	srli t2, t1, 24
	sb t2, 7(a0)
	lui t1, 247535
	addiw t1, t1, 882
	sb t1, 8(a0)
	srli t2, t1, 8
	sb t2, 9(a0)
	srli t2, t1, 16
	sb t2, 10(a0)
	srli t2, t1, 24
	sb t2, 11(a0)
	lui t1, 677119
	addiw t1, t1, 1338
	sb t1, 12(a0)
	srli t2, t1, 8
	sb t2, 13(a0)
	srli t2, t1, 16
	sb t2, 14(a0)
	srli t2, t1, 24
	sb t2, 15(a0)
	lui t1, 332005
	addiw t1, t1, 639
	sb t1, 16(a0)
	srli t2, t1, 8
	sb t2, 17(a0)
	srli t2, t1, 16
	sb t2, 18(a0)
	srli t2, t1, 24
	sb t2, 19(a0)
	lui t1, 634967
	addiw t1, t1, -1908
	sb t1, 20(a0)
	srli t2, t1, 8
	sb t2, 21(a0)
	srli t2, t1, 16
	sb t2, 22(a0)
	srli t2, t1, 24
	sb t2, 23(a0)
	lui t1, 129086
	addiw t1, t1, -1621
	sb t1, 24(a0)
	srli t2, t1, 8
	sb t2, 25(a0)
	srli t2, t1, 16
	sb t2, 26(a0)
	srli t2, t1, 24
	sb t2, 27(a0)
	lui t1, 376333
	addiw t1, t1, -743
	sb t1, 28(a0)
	srli t2, t1, 8
	sb t2, 29(a0)
	srli t2, t1, 16
	sb t2, 30(a0)
	srli t2, t1, 24
	sb t2, 31(a0)
	lui t1, 438414
	addiw t1, t1, 1639
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
	beqz a3, 20f
	addi t1, zero, 0
	sb t1, 32(a0)
	sb t1, 33(a0)
	sb t1, 34(a0)
	sb t1, 35(a0)
	sb t1, 36(a0)
	sb t1, 37(a0)
	sb t1, 38(a0)
	sb t1, 39(a0)
	sb t1, 40(a0)
	sb t1, 41(a0)
	sb t1, 42(a0)
	sb t1, 43(a0)
	sb t1, 44(a0)
	sb t1, 45(a0)
	sb t1, 46(a0)
	sb t1, 47(a0)
	sb t1, 48(a0)
	sb t1, 49(a0)
	sb t1, 50(a0)
	sb t1, 51(a0)
	sb t1, 52(a0)
	sb t1, 53(a0)
	sb t1, 54(a0)
	sb t1, 55(a0)
	sb t1, 56(a0)
	sb t1, 57(a0)
	sb t1, 58(a0)
	sb t1, 59(a0)
	sb t1, 60(a0)
	sb t1, 61(a0)
	sb t1, 62(a0)
	sb t1, 63(a0)
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
	addi t2, a0, 32
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

vg_blake2s_update:
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
	andi a7, a7, 63
	addi a7, a7, 1
	beqz s11, 20f
	j 21f
20:
	addi a7, zero, 0
21:
	beqz s10, 22f
	beqz a7, 24f
	addi t3, zero, 64
	sub t3, t3, a7
	srli t1, s10, 6
	beqz t1, 26f
	j 27f
26:
	add t1, s10, a7
	srli t1, t1, 6
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
	sb t1, 32(t2)
	addi s9, s9, 1
	addi a7, a7, 1
	addi t3, t3, -1
	bnez t3, 212b
	j 211f
210:
211:
	beqz s10, 213f
	addi a0, s7, 0
	addi a1, s7, 32
	addi a2, zero, 1
	addi a3, s11, 0
	addi a4, zero, 0
	addi a5, s8, 0
	call {vg_blake2s_compress}
	addi a7, zero, 0
	j 214f
213:
214:
	j 25f
24:
25:
	beqz s10, 215f
	addi t1, s10, -1
	srli t2, t1, 6
	beqz t2, 217f
	addi a0, s7, 0
	addi a1, s9, 0
	addi a2, t2, 0
	addi a3, s11, 64
	addi a4, zero, 0
	addi a5, s8, 0
	call {vg_blake2s_compress}
	addi t1, s10, -1
	andi t1, t1, 63
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
	sb t1, 32(t2)
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

vg_blake2s_finalize:
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
	andi a7, a7, 63
	addi a7, a7, 1
	beqz s11, 20f
	j 21f
20:
	addi a7, zero, 0
21:
	addi t1, zero, 0
	addi t3, zero, 64
	sub t3, t3, a7
	beqz t3, 22f
24:
	add t2, s7, a7
	sb t1, 32(t2)
	addi a7, a7, 1
	addi t3, t3, -1
	bnez t3, 24b
	j 23f
22:
23:
	addi a0, s7, 0
	addi a1, s7, 32
	addi a2, zero, 1
	addi a3, s11, 0
	addi a4, zero, 1
	addi a5, s8, 0
	call {vg_blake2s_compress}
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
	ld ra, 512(s8)
	ld s7, 520(s8)
	ld s9, 528(s8)
	ld s10, 536(s8)
	ld s11, 544(s8)
	ld s8, 552(s8)
	addi sp, sp, 576
	ret
	.option pop
