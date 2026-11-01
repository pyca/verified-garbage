// The functions of `src/internal/vg_pbkdf2_hmac_sha256_iterate.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_pbkdf2_hmac_sha256_iterate:
	.option push
	.option arch, +m, +c
	slli a2, a2, 32
	srli a2, a2, 32
	addi a4, a4, 7
	andi a4, a4, -8
	sd ra, 80(a4)
	sd s1, 88(a4)
	sd s2, 96(a4)
	sd s3, 104(a4)
	sd s4, 112(a4)
	sd s5, 120(a4)
	sd s6, 128(a4)
	addi s2, a4, 0
	addi s1, a4, 136
	addi s3, a4, 168
	addi s4, a0, 0
	addi s5, a3, 0
	addi s6, a2, 0
	lbu t1, 0(a1)
	sb t1, 0(s3)
	lbu t1, 1(a1)
	sb t1, 1(s3)
	lbu t1, 2(a1)
	sb t1, 2(s3)
	lbu t1, 3(a1)
	sb t1, 3(s3)
	lbu t1, 4(a1)
	sb t1, 4(s3)
	lbu t1, 5(a1)
	sb t1, 5(s3)
	lbu t1, 6(a1)
	sb t1, 6(s3)
	lbu t1, 7(a1)
	sb t1, 7(s3)
	lbu t1, 8(a1)
	sb t1, 8(s3)
	lbu t1, 9(a1)
	sb t1, 9(s3)
	lbu t1, 10(a1)
	sb t1, 10(s3)
	lbu t1, 11(a1)
	sb t1, 11(s3)
	lbu t1, 12(a1)
	sb t1, 12(s3)
	lbu t1, 13(a1)
	sb t1, 13(s3)
	lbu t1, 14(a1)
	sb t1, 14(s3)
	lbu t1, 15(a1)
	sb t1, 15(s3)
	lbu t1, 16(a1)
	sb t1, 16(s3)
	lbu t1, 17(a1)
	sb t1, 17(s3)
	lbu t1, 18(a1)
	sb t1, 18(s3)
	lbu t1, 19(a1)
	sb t1, 19(s3)
	lbu t1, 20(a1)
	sb t1, 20(s3)
	lbu t1, 21(a1)
	sb t1, 21(s3)
	lbu t1, 22(a1)
	sb t1, 22(s3)
	lbu t1, 23(a1)
	sb t1, 23(s3)
	lbu t1, 24(a1)
	sb t1, 24(s3)
	lbu t1, 25(a1)
	sb t1, 25(s3)
	lbu t1, 26(a1)
	sb t1, 26(s3)
	lbu t1, 27(a1)
	sb t1, 27(s3)
	lbu t1, 28(a1)
	sb t1, 28(s3)
	lbu t1, 29(a1)
	sb t1, 29(s3)
	lbu t1, 30(a1)
	sb t1, 30(s3)
	lbu t1, 31(a1)
	sb t1, 31(s3)
	addi t1, zero, 128
	sb t1, 32(s3)
	addi t1, zero, 0
	sb t1, 33(s3)
	addi t1, zero, 0
	sb t1, 34(s3)
	addi t1, zero, 0
	sb t1, 35(s3)
	addi t1, zero, 0
	sb t1, 36(s3)
	addi t1, zero, 0
	sb t1, 37(s3)
	addi t1, zero, 0
	sb t1, 38(s3)
	addi t1, zero, 0
	sb t1, 39(s3)
	addi t1, zero, 0
	sb t1, 40(s3)
	addi t1, zero, 0
	sb t1, 41(s3)
	addi t1, zero, 0
	sb t1, 42(s3)
	addi t1, zero, 0
	sb t1, 43(s3)
	addi t1, zero, 0
	sb t1, 44(s3)
	addi t1, zero, 0
	sb t1, 45(s3)
	addi t1, zero, 0
	sb t1, 46(s3)
	addi t1, zero, 0
	sb t1, 47(s3)
	addi t1, zero, 0
	sb t1, 48(s3)
	addi t1, zero, 0
	sb t1, 49(s3)
	addi t1, zero, 0
	sb t1, 50(s3)
	addi t1, zero, 0
	sb t1, 51(s3)
	addi t1, zero, 0
	sb t1, 52(s3)
	addi t1, zero, 0
	sb t1, 53(s3)
	addi t1, zero, 0
	sb t1, 54(s3)
	addi t1, zero, 0
	sb t1, 55(s3)
	addi t1, zero, 0
	sb t1, 56(s3)
	addi t1, zero, 0
	sb t1, 57(s3)
	addi t1, zero, 0
	sb t1, 58(s3)
	addi t1, zero, 0
	sb t1, 59(s3)
	addi t1, zero, 0
	sb t1, 60(s3)
	addi t1, zero, 0
	sb t1, 61(s3)
	addi t1, zero, 3
	sb t1, 62(s3)
	addi t1, zero, 0
	sb t1, 63(s3)
	beqz s6, 20f
22:
	lbu t1, 0(s4)
	sb t1, 0(s1)
	lbu t1, 1(s4)
	sb t1, 1(s1)
	lbu t1, 2(s4)
	sb t1, 2(s1)
	lbu t1, 3(s4)
	sb t1, 3(s1)
	lbu t1, 4(s4)
	sb t1, 4(s1)
	lbu t1, 5(s4)
	sb t1, 5(s1)
	lbu t1, 6(s4)
	sb t1, 6(s1)
	lbu t1, 7(s4)
	sb t1, 7(s1)
	lbu t1, 8(s4)
	sb t1, 8(s1)
	lbu t1, 9(s4)
	sb t1, 9(s1)
	lbu t1, 10(s4)
	sb t1, 10(s1)
	lbu t1, 11(s4)
	sb t1, 11(s1)
	lbu t1, 12(s4)
	sb t1, 12(s1)
	lbu t1, 13(s4)
	sb t1, 13(s1)
	lbu t1, 14(s4)
	sb t1, 14(s1)
	lbu t1, 15(s4)
	sb t1, 15(s1)
	lbu t1, 16(s4)
	sb t1, 16(s1)
	lbu t1, 17(s4)
	sb t1, 17(s1)
	lbu t1, 18(s4)
	sb t1, 18(s1)
	lbu t1, 19(s4)
	sb t1, 19(s1)
	lbu t1, 20(s4)
	sb t1, 20(s1)
	lbu t1, 21(s4)
	sb t1, 21(s1)
	lbu t1, 22(s4)
	sb t1, 22(s1)
	lbu t1, 23(s4)
	sb t1, 23(s1)
	lbu t1, 24(s4)
	sb t1, 24(s1)
	lbu t1, 25(s4)
	sb t1, 25(s1)
	lbu t1, 26(s4)
	sb t1, 26(s1)
	lbu t1, 27(s4)
	sb t1, 27(s1)
	lbu t1, 28(s4)
	sb t1, 28(s1)
	lbu t1, 29(s4)
	sb t1, 29(s1)
	lbu t1, 30(s4)
	sb t1, 30(s1)
	lbu t1, 31(s4)
	sb t1, 31(s1)
	addi a0, s1, 0
	addi a1, s3, 0
	addi a2, zero, 1
	addi a3, s2, 0
	call {vg_sha256_compress}
	lbu t1, 0(s1)
	lbu t2, 1(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 2(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 3(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 0(s3)
	srli t2, t1, 16
	sb t2, 1(s3)
	srli t2, t1, 8
	sb t2, 2(s3)
	srli t2, t1, 0
	sb t2, 3(s3)
	lbu t1, 4(s1)
	lbu t2, 5(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 6(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 7(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 4(s3)
	srli t2, t1, 16
	sb t2, 5(s3)
	srli t2, t1, 8
	sb t2, 6(s3)
	srli t2, t1, 0
	sb t2, 7(s3)
	lbu t1, 8(s1)
	lbu t2, 9(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 10(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 11(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 8(s3)
	srli t2, t1, 16
	sb t2, 9(s3)
	srli t2, t1, 8
	sb t2, 10(s3)
	srli t2, t1, 0
	sb t2, 11(s3)
	lbu t1, 12(s1)
	lbu t2, 13(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 14(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 15(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 12(s3)
	srli t2, t1, 16
	sb t2, 13(s3)
	srli t2, t1, 8
	sb t2, 14(s3)
	srli t2, t1, 0
	sb t2, 15(s3)
	lbu t1, 16(s1)
	lbu t2, 17(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 18(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 19(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 16(s3)
	srli t2, t1, 16
	sb t2, 17(s3)
	srli t2, t1, 8
	sb t2, 18(s3)
	srli t2, t1, 0
	sb t2, 19(s3)
	lbu t1, 20(s1)
	lbu t2, 21(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 22(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 23(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 20(s3)
	srli t2, t1, 16
	sb t2, 21(s3)
	srli t2, t1, 8
	sb t2, 22(s3)
	srli t2, t1, 0
	sb t2, 23(s3)
	lbu t1, 24(s1)
	lbu t2, 25(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 26(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 27(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 24(s3)
	srli t2, t1, 16
	sb t2, 25(s3)
	srli t2, t1, 8
	sb t2, 26(s3)
	srli t2, t1, 0
	sb t2, 27(s3)
	lbu t1, 28(s1)
	lbu t2, 29(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 30(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 31(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 28(s3)
	srli t2, t1, 16
	sb t2, 29(s3)
	srli t2, t1, 8
	sb t2, 30(s3)
	srli t2, t1, 0
	sb t2, 31(s3)
	lbu t1, 96(s4)
	sb t1, 0(s1)
	lbu t1, 97(s4)
	sb t1, 1(s1)
	lbu t1, 98(s4)
	sb t1, 2(s1)
	lbu t1, 99(s4)
	sb t1, 3(s1)
	lbu t1, 100(s4)
	sb t1, 4(s1)
	lbu t1, 101(s4)
	sb t1, 5(s1)
	lbu t1, 102(s4)
	sb t1, 6(s1)
	lbu t1, 103(s4)
	sb t1, 7(s1)
	lbu t1, 104(s4)
	sb t1, 8(s1)
	lbu t1, 105(s4)
	sb t1, 9(s1)
	lbu t1, 106(s4)
	sb t1, 10(s1)
	lbu t1, 107(s4)
	sb t1, 11(s1)
	lbu t1, 108(s4)
	sb t1, 12(s1)
	lbu t1, 109(s4)
	sb t1, 13(s1)
	lbu t1, 110(s4)
	sb t1, 14(s1)
	lbu t1, 111(s4)
	sb t1, 15(s1)
	lbu t1, 112(s4)
	sb t1, 16(s1)
	lbu t1, 113(s4)
	sb t1, 17(s1)
	lbu t1, 114(s4)
	sb t1, 18(s1)
	lbu t1, 115(s4)
	sb t1, 19(s1)
	lbu t1, 116(s4)
	sb t1, 20(s1)
	lbu t1, 117(s4)
	sb t1, 21(s1)
	lbu t1, 118(s4)
	sb t1, 22(s1)
	lbu t1, 119(s4)
	sb t1, 23(s1)
	lbu t1, 120(s4)
	sb t1, 24(s1)
	lbu t1, 121(s4)
	sb t1, 25(s1)
	lbu t1, 122(s4)
	sb t1, 26(s1)
	lbu t1, 123(s4)
	sb t1, 27(s1)
	lbu t1, 124(s4)
	sb t1, 28(s1)
	lbu t1, 125(s4)
	sb t1, 29(s1)
	lbu t1, 126(s4)
	sb t1, 30(s1)
	lbu t1, 127(s4)
	sb t1, 31(s1)
	addi a0, s1, 0
	addi a1, s3, 0
	addi a2, zero, 1
	addi a3, s2, 0
	call {vg_sha256_compress}
	lbu t1, 0(s1)
	lbu t2, 1(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 2(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 3(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 0(s3)
	srli t2, t1, 16
	sb t2, 1(s3)
	srli t2, t1, 8
	sb t2, 2(s3)
	srli t2, t1, 0
	sb t2, 3(s3)
	lbu t1, 4(s1)
	lbu t2, 5(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 6(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 7(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 4(s3)
	srli t2, t1, 16
	sb t2, 5(s3)
	srli t2, t1, 8
	sb t2, 6(s3)
	srli t2, t1, 0
	sb t2, 7(s3)
	lbu t1, 8(s1)
	lbu t2, 9(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 10(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 11(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 8(s3)
	srli t2, t1, 16
	sb t2, 9(s3)
	srli t2, t1, 8
	sb t2, 10(s3)
	srli t2, t1, 0
	sb t2, 11(s3)
	lbu t1, 12(s1)
	lbu t2, 13(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 14(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 15(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 12(s3)
	srli t2, t1, 16
	sb t2, 13(s3)
	srli t2, t1, 8
	sb t2, 14(s3)
	srli t2, t1, 0
	sb t2, 15(s3)
	lbu t1, 16(s1)
	lbu t2, 17(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 18(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 19(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 16(s3)
	srli t2, t1, 16
	sb t2, 17(s3)
	srli t2, t1, 8
	sb t2, 18(s3)
	srli t2, t1, 0
	sb t2, 19(s3)
	lbu t1, 20(s1)
	lbu t2, 21(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 22(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 23(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 20(s3)
	srli t2, t1, 16
	sb t2, 21(s3)
	srli t2, t1, 8
	sb t2, 22(s3)
	srli t2, t1, 0
	sb t2, 23(s3)
	lbu t1, 24(s1)
	lbu t2, 25(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 26(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 27(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 24(s3)
	srli t2, t1, 16
	sb t2, 25(s3)
	srli t2, t1, 8
	sb t2, 26(s3)
	srli t2, t1, 0
	sb t2, 27(s3)
	lbu t1, 28(s1)
	lbu t2, 29(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 30(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 31(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 28(s3)
	srli t2, t1, 16
	sb t2, 29(s3)
	srli t2, t1, 8
	sb t2, 30(s3)
	srli t2, t1, 0
	sb t2, 31(s3)
	lbu t1, 0(s5)
	lbu t2, 0(s3)
	xor t1, t1, t2
	sb t1, 0(s5)
	lbu t1, 1(s5)
	lbu t2, 1(s3)
	xor t1, t1, t2
	sb t1, 1(s5)
	lbu t1, 2(s5)
	lbu t2, 2(s3)
	xor t1, t1, t2
	sb t1, 2(s5)
	lbu t1, 3(s5)
	lbu t2, 3(s3)
	xor t1, t1, t2
	sb t1, 3(s5)
	lbu t1, 4(s5)
	lbu t2, 4(s3)
	xor t1, t1, t2
	sb t1, 4(s5)
	lbu t1, 5(s5)
	lbu t2, 5(s3)
	xor t1, t1, t2
	sb t1, 5(s5)
	lbu t1, 6(s5)
	lbu t2, 6(s3)
	xor t1, t1, t2
	sb t1, 6(s5)
	lbu t1, 7(s5)
	lbu t2, 7(s3)
	xor t1, t1, t2
	sb t1, 7(s5)
	lbu t1, 8(s5)
	lbu t2, 8(s3)
	xor t1, t1, t2
	sb t1, 8(s5)
	lbu t1, 9(s5)
	lbu t2, 9(s3)
	xor t1, t1, t2
	sb t1, 9(s5)
	lbu t1, 10(s5)
	lbu t2, 10(s3)
	xor t1, t1, t2
	sb t1, 10(s5)
	lbu t1, 11(s5)
	lbu t2, 11(s3)
	xor t1, t1, t2
	sb t1, 11(s5)
	lbu t1, 12(s5)
	lbu t2, 12(s3)
	xor t1, t1, t2
	sb t1, 12(s5)
	lbu t1, 13(s5)
	lbu t2, 13(s3)
	xor t1, t1, t2
	sb t1, 13(s5)
	lbu t1, 14(s5)
	lbu t2, 14(s3)
	xor t1, t1, t2
	sb t1, 14(s5)
	lbu t1, 15(s5)
	lbu t2, 15(s3)
	xor t1, t1, t2
	sb t1, 15(s5)
	lbu t1, 16(s5)
	lbu t2, 16(s3)
	xor t1, t1, t2
	sb t1, 16(s5)
	lbu t1, 17(s5)
	lbu t2, 17(s3)
	xor t1, t1, t2
	sb t1, 17(s5)
	lbu t1, 18(s5)
	lbu t2, 18(s3)
	xor t1, t1, t2
	sb t1, 18(s5)
	lbu t1, 19(s5)
	lbu t2, 19(s3)
	xor t1, t1, t2
	sb t1, 19(s5)
	lbu t1, 20(s5)
	lbu t2, 20(s3)
	xor t1, t1, t2
	sb t1, 20(s5)
	lbu t1, 21(s5)
	lbu t2, 21(s3)
	xor t1, t1, t2
	sb t1, 21(s5)
	lbu t1, 22(s5)
	lbu t2, 22(s3)
	xor t1, t1, t2
	sb t1, 22(s5)
	lbu t1, 23(s5)
	lbu t2, 23(s3)
	xor t1, t1, t2
	sb t1, 23(s5)
	lbu t1, 24(s5)
	lbu t2, 24(s3)
	xor t1, t1, t2
	sb t1, 24(s5)
	lbu t1, 25(s5)
	lbu t2, 25(s3)
	xor t1, t1, t2
	sb t1, 25(s5)
	lbu t1, 26(s5)
	lbu t2, 26(s3)
	xor t1, t1, t2
	sb t1, 26(s5)
	lbu t1, 27(s5)
	lbu t2, 27(s3)
	xor t1, t1, t2
	sb t1, 27(s5)
	lbu t1, 28(s5)
	lbu t2, 28(s3)
	xor t1, t1, t2
	sb t1, 28(s5)
	lbu t1, 29(s5)
	lbu t2, 29(s3)
	xor t1, t1, t2
	sb t1, 29(s5)
	lbu t1, 30(s5)
	lbu t2, 30(s3)
	xor t1, t1, t2
	sb t1, 30(s5)
	lbu t1, 31(s5)
	lbu t2, 31(s3)
	xor t1, t1, t2
	sb t1, 31(s5)
	addi s6, s6, -1
	bnez s6, 22b
	j 21f
20:
21:
	ld ra, 80(s2)
	ld s1, 88(s2)
	ld s3, 104(s2)
	ld s4, 112(s2)
	ld s5, 120(s2)
	ld s6, 128(s2)
	ld s2, 96(s2)
	ret
	.option pop
