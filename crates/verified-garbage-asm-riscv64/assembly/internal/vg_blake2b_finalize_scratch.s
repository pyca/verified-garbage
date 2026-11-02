// The functions of `src/internal/vg_blake2b_finalize_scratch.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_blake2b_finalize_scratch:
	.option push
	.option arch, +m, +c
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
	ret
	.option pop
