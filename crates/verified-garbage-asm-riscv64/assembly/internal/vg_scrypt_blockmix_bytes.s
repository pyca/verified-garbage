// The functions of `src/internal/vg_scrypt_blockmix_bytes.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_scrypt_blockmix_bytes:
	.option push
	.option arch, +m, +c
	addi sp, sp, -48
	addi t0, sp, 0
	sd ra, 0(t0)
	sd s4, 8(t0)
	sd s5, 16(t0)
	sd s6, 24(t0)
	sd s7, 32(t0)
	sd s8, 40(t0)
	addi s7, a1, 0
	addi s4, a0, 0
	addi s5, a2, 0
	slli t1, a1, 6
	add s6, a2, t1
	slli t1, a1, 7
	add s8, a0, t1
	addi s8, s8, -64
20:
	lbu t0, 0(s8)
	lbu t1, 0(s4)
	xor t0, t0, t1
	sb t0, 0(s5)
	lbu t0, 1(s8)
	lbu t1, 1(s4)
	xor t0, t0, t1
	sb t0, 1(s5)
	lbu t0, 2(s8)
	lbu t1, 2(s4)
	xor t0, t0, t1
	sb t0, 2(s5)
	lbu t0, 3(s8)
	lbu t1, 3(s4)
	xor t0, t0, t1
	sb t0, 3(s5)
	lbu t0, 4(s8)
	lbu t1, 4(s4)
	xor t0, t0, t1
	sb t0, 4(s5)
	lbu t0, 5(s8)
	lbu t1, 5(s4)
	xor t0, t0, t1
	sb t0, 5(s5)
	lbu t0, 6(s8)
	lbu t1, 6(s4)
	xor t0, t0, t1
	sb t0, 6(s5)
	lbu t0, 7(s8)
	lbu t1, 7(s4)
	xor t0, t0, t1
	sb t0, 7(s5)
	lbu t0, 8(s8)
	lbu t1, 8(s4)
	xor t0, t0, t1
	sb t0, 8(s5)
	lbu t0, 9(s8)
	lbu t1, 9(s4)
	xor t0, t0, t1
	sb t0, 9(s5)
	lbu t0, 10(s8)
	lbu t1, 10(s4)
	xor t0, t0, t1
	sb t0, 10(s5)
	lbu t0, 11(s8)
	lbu t1, 11(s4)
	xor t0, t0, t1
	sb t0, 11(s5)
	lbu t0, 12(s8)
	lbu t1, 12(s4)
	xor t0, t0, t1
	sb t0, 12(s5)
	lbu t0, 13(s8)
	lbu t1, 13(s4)
	xor t0, t0, t1
	sb t0, 13(s5)
	lbu t0, 14(s8)
	lbu t1, 14(s4)
	xor t0, t0, t1
	sb t0, 14(s5)
	lbu t0, 15(s8)
	lbu t1, 15(s4)
	xor t0, t0, t1
	sb t0, 15(s5)
	lbu t0, 16(s8)
	lbu t1, 16(s4)
	xor t0, t0, t1
	sb t0, 16(s5)
	lbu t0, 17(s8)
	lbu t1, 17(s4)
	xor t0, t0, t1
	sb t0, 17(s5)
	lbu t0, 18(s8)
	lbu t1, 18(s4)
	xor t0, t0, t1
	sb t0, 18(s5)
	lbu t0, 19(s8)
	lbu t1, 19(s4)
	xor t0, t0, t1
	sb t0, 19(s5)
	lbu t0, 20(s8)
	lbu t1, 20(s4)
	xor t0, t0, t1
	sb t0, 20(s5)
	lbu t0, 21(s8)
	lbu t1, 21(s4)
	xor t0, t0, t1
	sb t0, 21(s5)
	lbu t0, 22(s8)
	lbu t1, 22(s4)
	xor t0, t0, t1
	sb t0, 22(s5)
	lbu t0, 23(s8)
	lbu t1, 23(s4)
	xor t0, t0, t1
	sb t0, 23(s5)
	lbu t0, 24(s8)
	lbu t1, 24(s4)
	xor t0, t0, t1
	sb t0, 24(s5)
	lbu t0, 25(s8)
	lbu t1, 25(s4)
	xor t0, t0, t1
	sb t0, 25(s5)
	lbu t0, 26(s8)
	lbu t1, 26(s4)
	xor t0, t0, t1
	sb t0, 26(s5)
	lbu t0, 27(s8)
	lbu t1, 27(s4)
	xor t0, t0, t1
	sb t0, 27(s5)
	lbu t0, 28(s8)
	lbu t1, 28(s4)
	xor t0, t0, t1
	sb t0, 28(s5)
	lbu t0, 29(s8)
	lbu t1, 29(s4)
	xor t0, t0, t1
	sb t0, 29(s5)
	lbu t0, 30(s8)
	lbu t1, 30(s4)
	xor t0, t0, t1
	sb t0, 30(s5)
	lbu t0, 31(s8)
	lbu t1, 31(s4)
	xor t0, t0, t1
	sb t0, 31(s5)
	lbu t0, 32(s8)
	lbu t1, 32(s4)
	xor t0, t0, t1
	sb t0, 32(s5)
	lbu t0, 33(s8)
	lbu t1, 33(s4)
	xor t0, t0, t1
	sb t0, 33(s5)
	lbu t0, 34(s8)
	lbu t1, 34(s4)
	xor t0, t0, t1
	sb t0, 34(s5)
	lbu t0, 35(s8)
	lbu t1, 35(s4)
	xor t0, t0, t1
	sb t0, 35(s5)
	lbu t0, 36(s8)
	lbu t1, 36(s4)
	xor t0, t0, t1
	sb t0, 36(s5)
	lbu t0, 37(s8)
	lbu t1, 37(s4)
	xor t0, t0, t1
	sb t0, 37(s5)
	lbu t0, 38(s8)
	lbu t1, 38(s4)
	xor t0, t0, t1
	sb t0, 38(s5)
	lbu t0, 39(s8)
	lbu t1, 39(s4)
	xor t0, t0, t1
	sb t0, 39(s5)
	lbu t0, 40(s8)
	lbu t1, 40(s4)
	xor t0, t0, t1
	sb t0, 40(s5)
	lbu t0, 41(s8)
	lbu t1, 41(s4)
	xor t0, t0, t1
	sb t0, 41(s5)
	lbu t0, 42(s8)
	lbu t1, 42(s4)
	xor t0, t0, t1
	sb t0, 42(s5)
	lbu t0, 43(s8)
	lbu t1, 43(s4)
	xor t0, t0, t1
	sb t0, 43(s5)
	lbu t0, 44(s8)
	lbu t1, 44(s4)
	xor t0, t0, t1
	sb t0, 44(s5)
	lbu t0, 45(s8)
	lbu t1, 45(s4)
	xor t0, t0, t1
	sb t0, 45(s5)
	lbu t0, 46(s8)
	lbu t1, 46(s4)
	xor t0, t0, t1
	sb t0, 46(s5)
	lbu t0, 47(s8)
	lbu t1, 47(s4)
	xor t0, t0, t1
	sb t0, 47(s5)
	lbu t0, 48(s8)
	lbu t1, 48(s4)
	xor t0, t0, t1
	sb t0, 48(s5)
	lbu t0, 49(s8)
	lbu t1, 49(s4)
	xor t0, t0, t1
	sb t0, 49(s5)
	lbu t0, 50(s8)
	lbu t1, 50(s4)
	xor t0, t0, t1
	sb t0, 50(s5)
	lbu t0, 51(s8)
	lbu t1, 51(s4)
	xor t0, t0, t1
	sb t0, 51(s5)
	lbu t0, 52(s8)
	lbu t1, 52(s4)
	xor t0, t0, t1
	sb t0, 52(s5)
	lbu t0, 53(s8)
	lbu t1, 53(s4)
	xor t0, t0, t1
	sb t0, 53(s5)
	lbu t0, 54(s8)
	lbu t1, 54(s4)
	xor t0, t0, t1
	sb t0, 54(s5)
	lbu t0, 55(s8)
	lbu t1, 55(s4)
	xor t0, t0, t1
	sb t0, 55(s5)
	lbu t0, 56(s8)
	lbu t1, 56(s4)
	xor t0, t0, t1
	sb t0, 56(s5)
	lbu t0, 57(s8)
	lbu t1, 57(s4)
	xor t0, t0, t1
	sb t0, 57(s5)
	lbu t0, 58(s8)
	lbu t1, 58(s4)
	xor t0, t0, t1
	sb t0, 58(s5)
	lbu t0, 59(s8)
	lbu t1, 59(s4)
	xor t0, t0, t1
	sb t0, 59(s5)
	lbu t0, 60(s8)
	lbu t1, 60(s4)
	xor t0, t0, t1
	sb t0, 60(s5)
	lbu t0, 61(s8)
	lbu t1, 61(s4)
	xor t0, t0, t1
	sb t0, 61(s5)
	lbu t0, 62(s8)
	lbu t1, 62(s4)
	xor t0, t0, t1
	sb t0, 62(s5)
	lbu t0, 63(s8)
	lbu t1, 63(s4)
	xor t0, t0, t1
	sb t0, 63(s5)
	addi a0, s5, 0
	call {vg_salsa20_8_bytes}
	addi s4, s4, 64
	lbu t0, 0(s5)
	lbu t1, 0(s4)
	xor t0, t0, t1
	sb t0, 0(s6)
	lbu t0, 1(s5)
	lbu t1, 1(s4)
	xor t0, t0, t1
	sb t0, 1(s6)
	lbu t0, 2(s5)
	lbu t1, 2(s4)
	xor t0, t0, t1
	sb t0, 2(s6)
	lbu t0, 3(s5)
	lbu t1, 3(s4)
	xor t0, t0, t1
	sb t0, 3(s6)
	lbu t0, 4(s5)
	lbu t1, 4(s4)
	xor t0, t0, t1
	sb t0, 4(s6)
	lbu t0, 5(s5)
	lbu t1, 5(s4)
	xor t0, t0, t1
	sb t0, 5(s6)
	lbu t0, 6(s5)
	lbu t1, 6(s4)
	xor t0, t0, t1
	sb t0, 6(s6)
	lbu t0, 7(s5)
	lbu t1, 7(s4)
	xor t0, t0, t1
	sb t0, 7(s6)
	lbu t0, 8(s5)
	lbu t1, 8(s4)
	xor t0, t0, t1
	sb t0, 8(s6)
	lbu t0, 9(s5)
	lbu t1, 9(s4)
	xor t0, t0, t1
	sb t0, 9(s6)
	lbu t0, 10(s5)
	lbu t1, 10(s4)
	xor t0, t0, t1
	sb t0, 10(s6)
	lbu t0, 11(s5)
	lbu t1, 11(s4)
	xor t0, t0, t1
	sb t0, 11(s6)
	lbu t0, 12(s5)
	lbu t1, 12(s4)
	xor t0, t0, t1
	sb t0, 12(s6)
	lbu t0, 13(s5)
	lbu t1, 13(s4)
	xor t0, t0, t1
	sb t0, 13(s6)
	lbu t0, 14(s5)
	lbu t1, 14(s4)
	xor t0, t0, t1
	sb t0, 14(s6)
	lbu t0, 15(s5)
	lbu t1, 15(s4)
	xor t0, t0, t1
	sb t0, 15(s6)
	lbu t0, 16(s5)
	lbu t1, 16(s4)
	xor t0, t0, t1
	sb t0, 16(s6)
	lbu t0, 17(s5)
	lbu t1, 17(s4)
	xor t0, t0, t1
	sb t0, 17(s6)
	lbu t0, 18(s5)
	lbu t1, 18(s4)
	xor t0, t0, t1
	sb t0, 18(s6)
	lbu t0, 19(s5)
	lbu t1, 19(s4)
	xor t0, t0, t1
	sb t0, 19(s6)
	lbu t0, 20(s5)
	lbu t1, 20(s4)
	xor t0, t0, t1
	sb t0, 20(s6)
	lbu t0, 21(s5)
	lbu t1, 21(s4)
	xor t0, t0, t1
	sb t0, 21(s6)
	lbu t0, 22(s5)
	lbu t1, 22(s4)
	xor t0, t0, t1
	sb t0, 22(s6)
	lbu t0, 23(s5)
	lbu t1, 23(s4)
	xor t0, t0, t1
	sb t0, 23(s6)
	lbu t0, 24(s5)
	lbu t1, 24(s4)
	xor t0, t0, t1
	sb t0, 24(s6)
	lbu t0, 25(s5)
	lbu t1, 25(s4)
	xor t0, t0, t1
	sb t0, 25(s6)
	lbu t0, 26(s5)
	lbu t1, 26(s4)
	xor t0, t0, t1
	sb t0, 26(s6)
	lbu t0, 27(s5)
	lbu t1, 27(s4)
	xor t0, t0, t1
	sb t0, 27(s6)
	lbu t0, 28(s5)
	lbu t1, 28(s4)
	xor t0, t0, t1
	sb t0, 28(s6)
	lbu t0, 29(s5)
	lbu t1, 29(s4)
	xor t0, t0, t1
	sb t0, 29(s6)
	lbu t0, 30(s5)
	lbu t1, 30(s4)
	xor t0, t0, t1
	sb t0, 30(s6)
	lbu t0, 31(s5)
	lbu t1, 31(s4)
	xor t0, t0, t1
	sb t0, 31(s6)
	lbu t0, 32(s5)
	lbu t1, 32(s4)
	xor t0, t0, t1
	sb t0, 32(s6)
	lbu t0, 33(s5)
	lbu t1, 33(s4)
	xor t0, t0, t1
	sb t0, 33(s6)
	lbu t0, 34(s5)
	lbu t1, 34(s4)
	xor t0, t0, t1
	sb t0, 34(s6)
	lbu t0, 35(s5)
	lbu t1, 35(s4)
	xor t0, t0, t1
	sb t0, 35(s6)
	lbu t0, 36(s5)
	lbu t1, 36(s4)
	xor t0, t0, t1
	sb t0, 36(s6)
	lbu t0, 37(s5)
	lbu t1, 37(s4)
	xor t0, t0, t1
	sb t0, 37(s6)
	lbu t0, 38(s5)
	lbu t1, 38(s4)
	xor t0, t0, t1
	sb t0, 38(s6)
	lbu t0, 39(s5)
	lbu t1, 39(s4)
	xor t0, t0, t1
	sb t0, 39(s6)
	lbu t0, 40(s5)
	lbu t1, 40(s4)
	xor t0, t0, t1
	sb t0, 40(s6)
	lbu t0, 41(s5)
	lbu t1, 41(s4)
	xor t0, t0, t1
	sb t0, 41(s6)
	lbu t0, 42(s5)
	lbu t1, 42(s4)
	xor t0, t0, t1
	sb t0, 42(s6)
	lbu t0, 43(s5)
	lbu t1, 43(s4)
	xor t0, t0, t1
	sb t0, 43(s6)
	lbu t0, 44(s5)
	lbu t1, 44(s4)
	xor t0, t0, t1
	sb t0, 44(s6)
	lbu t0, 45(s5)
	lbu t1, 45(s4)
	xor t0, t0, t1
	sb t0, 45(s6)
	lbu t0, 46(s5)
	lbu t1, 46(s4)
	xor t0, t0, t1
	sb t0, 46(s6)
	lbu t0, 47(s5)
	lbu t1, 47(s4)
	xor t0, t0, t1
	sb t0, 47(s6)
	lbu t0, 48(s5)
	lbu t1, 48(s4)
	xor t0, t0, t1
	sb t0, 48(s6)
	lbu t0, 49(s5)
	lbu t1, 49(s4)
	xor t0, t0, t1
	sb t0, 49(s6)
	lbu t0, 50(s5)
	lbu t1, 50(s4)
	xor t0, t0, t1
	sb t0, 50(s6)
	lbu t0, 51(s5)
	lbu t1, 51(s4)
	xor t0, t0, t1
	sb t0, 51(s6)
	lbu t0, 52(s5)
	lbu t1, 52(s4)
	xor t0, t0, t1
	sb t0, 52(s6)
	lbu t0, 53(s5)
	lbu t1, 53(s4)
	xor t0, t0, t1
	sb t0, 53(s6)
	lbu t0, 54(s5)
	lbu t1, 54(s4)
	xor t0, t0, t1
	sb t0, 54(s6)
	lbu t0, 55(s5)
	lbu t1, 55(s4)
	xor t0, t0, t1
	sb t0, 55(s6)
	lbu t0, 56(s5)
	lbu t1, 56(s4)
	xor t0, t0, t1
	sb t0, 56(s6)
	lbu t0, 57(s5)
	lbu t1, 57(s4)
	xor t0, t0, t1
	sb t0, 57(s6)
	lbu t0, 58(s5)
	lbu t1, 58(s4)
	xor t0, t0, t1
	sb t0, 58(s6)
	lbu t0, 59(s5)
	lbu t1, 59(s4)
	xor t0, t0, t1
	sb t0, 59(s6)
	lbu t0, 60(s5)
	lbu t1, 60(s4)
	xor t0, t0, t1
	sb t0, 60(s6)
	lbu t0, 61(s5)
	lbu t1, 61(s4)
	xor t0, t0, t1
	sb t0, 61(s6)
	lbu t0, 62(s5)
	lbu t1, 62(s4)
	xor t0, t0, t1
	sb t0, 62(s6)
	lbu t0, 63(s5)
	lbu t1, 63(s4)
	xor t0, t0, t1
	sb t0, 63(s6)
	addi a0, s6, 0
	call {vg_salsa20_8_bytes}
	addi s8, s6, 0
	addi s4, s4, 64
	addi s5, s5, 64
	addi s6, s6, 64
	addi s7, s7, -1
	bnez s7, 20b
	addi t0, sp, 0
	ld ra, 0(t0)
	ld s4, 8(t0)
	ld s5, 16(t0)
	ld s6, 24(t0)
	ld s7, 32(t0)
	ld s8, 40(t0)
	addi sp, sp, 48
	ret
	.option pop
