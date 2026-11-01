// The functions of `src/internal/vg_pbkdf2_hmac_sha512_iterate.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_pbkdf2_hmac_sha512_iterate:
	.option push
	.option arch, +m, +c
	slli a2, a2, 32
	srli a2, a2, 32
	addi a4, a4, 7
	andi a4, a4, -8
	sd ra, 144(a4)
	sd s1, 152(a4)
	sd s2, 160(a4)
	sd s3, 168(a4)
	sd s4, 176(a4)
	sd s5, 184(a4)
	sd s6, 192(a4)
	addi s2, a4, 0
	addi s1, a4, 200
	addi s3, a4, 264
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
	lbu t1, 32(a1)
	sb t1, 32(s3)
	lbu t1, 33(a1)
	sb t1, 33(s3)
	lbu t1, 34(a1)
	sb t1, 34(s3)
	lbu t1, 35(a1)
	sb t1, 35(s3)
	lbu t1, 36(a1)
	sb t1, 36(s3)
	lbu t1, 37(a1)
	sb t1, 37(s3)
	lbu t1, 38(a1)
	sb t1, 38(s3)
	lbu t1, 39(a1)
	sb t1, 39(s3)
	lbu t1, 40(a1)
	sb t1, 40(s3)
	lbu t1, 41(a1)
	sb t1, 41(s3)
	lbu t1, 42(a1)
	sb t1, 42(s3)
	lbu t1, 43(a1)
	sb t1, 43(s3)
	lbu t1, 44(a1)
	sb t1, 44(s3)
	lbu t1, 45(a1)
	sb t1, 45(s3)
	lbu t1, 46(a1)
	sb t1, 46(s3)
	lbu t1, 47(a1)
	sb t1, 47(s3)
	lbu t1, 48(a1)
	sb t1, 48(s3)
	lbu t1, 49(a1)
	sb t1, 49(s3)
	lbu t1, 50(a1)
	sb t1, 50(s3)
	lbu t1, 51(a1)
	sb t1, 51(s3)
	lbu t1, 52(a1)
	sb t1, 52(s3)
	lbu t1, 53(a1)
	sb t1, 53(s3)
	lbu t1, 54(a1)
	sb t1, 54(s3)
	lbu t1, 55(a1)
	sb t1, 55(s3)
	lbu t1, 56(a1)
	sb t1, 56(s3)
	lbu t1, 57(a1)
	sb t1, 57(s3)
	lbu t1, 58(a1)
	sb t1, 58(s3)
	lbu t1, 59(a1)
	sb t1, 59(s3)
	lbu t1, 60(a1)
	sb t1, 60(s3)
	lbu t1, 61(a1)
	sb t1, 61(s3)
	lbu t1, 62(a1)
	sb t1, 62(s3)
	lbu t1, 63(a1)
	sb t1, 63(s3)
	addi t1, zero, 128
	sb t1, 64(s3)
	addi t1, zero, 0
	sb t1, 65(s3)
	addi t1, zero, 0
	sb t1, 66(s3)
	addi t1, zero, 0
	sb t1, 67(s3)
	addi t1, zero, 0
	sb t1, 68(s3)
	addi t1, zero, 0
	sb t1, 69(s3)
	addi t1, zero, 0
	sb t1, 70(s3)
	addi t1, zero, 0
	sb t1, 71(s3)
	addi t1, zero, 0
	sb t1, 72(s3)
	addi t1, zero, 0
	sb t1, 73(s3)
	addi t1, zero, 0
	sb t1, 74(s3)
	addi t1, zero, 0
	sb t1, 75(s3)
	addi t1, zero, 0
	sb t1, 76(s3)
	addi t1, zero, 0
	sb t1, 77(s3)
	addi t1, zero, 0
	sb t1, 78(s3)
	addi t1, zero, 0
	sb t1, 79(s3)
	addi t1, zero, 0
	sb t1, 80(s3)
	addi t1, zero, 0
	sb t1, 81(s3)
	addi t1, zero, 0
	sb t1, 82(s3)
	addi t1, zero, 0
	sb t1, 83(s3)
	addi t1, zero, 0
	sb t1, 84(s3)
	addi t1, zero, 0
	sb t1, 85(s3)
	addi t1, zero, 0
	sb t1, 86(s3)
	addi t1, zero, 0
	sb t1, 87(s3)
	addi t1, zero, 0
	sb t1, 88(s3)
	addi t1, zero, 0
	sb t1, 89(s3)
	addi t1, zero, 0
	sb t1, 90(s3)
	addi t1, zero, 0
	sb t1, 91(s3)
	addi t1, zero, 0
	sb t1, 92(s3)
	addi t1, zero, 0
	sb t1, 93(s3)
	addi t1, zero, 0
	sb t1, 94(s3)
	addi t1, zero, 0
	sb t1, 95(s3)
	addi t1, zero, 0
	sb t1, 96(s3)
	addi t1, zero, 0
	sb t1, 97(s3)
	addi t1, zero, 0
	sb t1, 98(s3)
	addi t1, zero, 0
	sb t1, 99(s3)
	addi t1, zero, 0
	sb t1, 100(s3)
	addi t1, zero, 0
	sb t1, 101(s3)
	addi t1, zero, 0
	sb t1, 102(s3)
	addi t1, zero, 0
	sb t1, 103(s3)
	addi t1, zero, 0
	sb t1, 104(s3)
	addi t1, zero, 0
	sb t1, 105(s3)
	addi t1, zero, 0
	sb t1, 106(s3)
	addi t1, zero, 0
	sb t1, 107(s3)
	addi t1, zero, 0
	sb t1, 108(s3)
	addi t1, zero, 0
	sb t1, 109(s3)
	addi t1, zero, 0
	sb t1, 110(s3)
	addi t1, zero, 0
	sb t1, 111(s3)
	addi t1, zero, 0
	sb t1, 112(s3)
	addi t1, zero, 0
	sb t1, 113(s3)
	addi t1, zero, 0
	sb t1, 114(s3)
	addi t1, zero, 0
	sb t1, 115(s3)
	addi t1, zero, 0
	sb t1, 116(s3)
	addi t1, zero, 0
	sb t1, 117(s3)
	addi t1, zero, 0
	sb t1, 118(s3)
	addi t1, zero, 0
	sb t1, 119(s3)
	addi t1, zero, 0
	sb t1, 120(s3)
	addi t1, zero, 0
	sb t1, 121(s3)
	addi t1, zero, 0
	sb t1, 122(s3)
	addi t1, zero, 0
	sb t1, 123(s3)
	addi t1, zero, 0
	sb t1, 124(s3)
	addi t1, zero, 0
	sb t1, 125(s3)
	addi t1, zero, 6
	sb t1, 126(s3)
	addi t1, zero, 0
	sb t1, 127(s3)
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
	lbu t1, 32(s4)
	sb t1, 32(s1)
	lbu t1, 33(s4)
	sb t1, 33(s1)
	lbu t1, 34(s4)
	sb t1, 34(s1)
	lbu t1, 35(s4)
	sb t1, 35(s1)
	lbu t1, 36(s4)
	sb t1, 36(s1)
	lbu t1, 37(s4)
	sb t1, 37(s1)
	lbu t1, 38(s4)
	sb t1, 38(s1)
	lbu t1, 39(s4)
	sb t1, 39(s1)
	lbu t1, 40(s4)
	sb t1, 40(s1)
	lbu t1, 41(s4)
	sb t1, 41(s1)
	lbu t1, 42(s4)
	sb t1, 42(s1)
	lbu t1, 43(s4)
	sb t1, 43(s1)
	lbu t1, 44(s4)
	sb t1, 44(s1)
	lbu t1, 45(s4)
	sb t1, 45(s1)
	lbu t1, 46(s4)
	sb t1, 46(s1)
	lbu t1, 47(s4)
	sb t1, 47(s1)
	lbu t1, 48(s4)
	sb t1, 48(s1)
	lbu t1, 49(s4)
	sb t1, 49(s1)
	lbu t1, 50(s4)
	sb t1, 50(s1)
	lbu t1, 51(s4)
	sb t1, 51(s1)
	lbu t1, 52(s4)
	sb t1, 52(s1)
	lbu t1, 53(s4)
	sb t1, 53(s1)
	lbu t1, 54(s4)
	sb t1, 54(s1)
	lbu t1, 55(s4)
	sb t1, 55(s1)
	lbu t1, 56(s4)
	sb t1, 56(s1)
	lbu t1, 57(s4)
	sb t1, 57(s1)
	lbu t1, 58(s4)
	sb t1, 58(s1)
	lbu t1, 59(s4)
	sb t1, 59(s1)
	lbu t1, 60(s4)
	sb t1, 60(s1)
	lbu t1, 61(s4)
	sb t1, 61(s1)
	lbu t1, 62(s4)
	sb t1, 62(s1)
	lbu t1, 63(s4)
	sb t1, 63(s1)
	addi a0, s1, 0
	addi a1, s3, 0
	addi a2, zero, 1
	addi a3, s2, 0
	call {vg_sha512_compress}
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
	lbu t4, 4(s1)
	lbu t2, 5(s1)
	slli t2, t2, 8
	or t4, t4, t2
	lbu t2, 6(s1)
	slli t2, t2, 16
	or t4, t4, t2
	lbu t2, 7(s1)
	slli t2, t2, 24
	or t4, t4, t2
	slli t4, t4, 32
	or t1, t1, t4
	srli t2, t1, 56
	sb t2, 0(s3)
	srli t2, t1, 48
	sb t2, 1(s3)
	srli t2, t1, 40
	sb t2, 2(s3)
	srli t2, t1, 32
	sb t2, 3(s3)
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
	lbu t4, 12(s1)
	lbu t2, 13(s1)
	slli t2, t2, 8
	or t4, t4, t2
	lbu t2, 14(s1)
	slli t2, t2, 16
	or t4, t4, t2
	lbu t2, 15(s1)
	slli t2, t2, 24
	or t4, t4, t2
	slli t4, t4, 32
	or t1, t1, t4
	srli t2, t1, 56
	sb t2, 8(s3)
	srli t2, t1, 48
	sb t2, 9(s3)
	srli t2, t1, 40
	sb t2, 10(s3)
	srli t2, t1, 32
	sb t2, 11(s3)
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
	lbu t4, 20(s1)
	lbu t2, 21(s1)
	slli t2, t2, 8
	or t4, t4, t2
	lbu t2, 22(s1)
	slli t2, t2, 16
	or t4, t4, t2
	lbu t2, 23(s1)
	slli t2, t2, 24
	or t4, t4, t2
	slli t4, t4, 32
	or t1, t1, t4
	srli t2, t1, 56
	sb t2, 16(s3)
	srli t2, t1, 48
	sb t2, 17(s3)
	srli t2, t1, 40
	sb t2, 18(s3)
	srli t2, t1, 32
	sb t2, 19(s3)
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
	lbu t4, 28(s1)
	lbu t2, 29(s1)
	slli t2, t2, 8
	or t4, t4, t2
	lbu t2, 30(s1)
	slli t2, t2, 16
	or t4, t4, t2
	lbu t2, 31(s1)
	slli t2, t2, 24
	or t4, t4, t2
	slli t4, t4, 32
	or t1, t1, t4
	srli t2, t1, 56
	sb t2, 24(s3)
	srli t2, t1, 48
	sb t2, 25(s3)
	srli t2, t1, 40
	sb t2, 26(s3)
	srli t2, t1, 32
	sb t2, 27(s3)
	srli t2, t1, 24
	sb t2, 28(s3)
	srli t2, t1, 16
	sb t2, 29(s3)
	srli t2, t1, 8
	sb t2, 30(s3)
	srli t2, t1, 0
	sb t2, 31(s3)
	lbu t1, 32(s1)
	lbu t2, 33(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 34(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 35(s1)
	slli t2, t2, 24
	or t1, t1, t2
	lbu t4, 36(s1)
	lbu t2, 37(s1)
	slli t2, t2, 8
	or t4, t4, t2
	lbu t2, 38(s1)
	slli t2, t2, 16
	or t4, t4, t2
	lbu t2, 39(s1)
	slli t2, t2, 24
	or t4, t4, t2
	slli t4, t4, 32
	or t1, t1, t4
	srli t2, t1, 56
	sb t2, 32(s3)
	srli t2, t1, 48
	sb t2, 33(s3)
	srli t2, t1, 40
	sb t2, 34(s3)
	srli t2, t1, 32
	sb t2, 35(s3)
	srli t2, t1, 24
	sb t2, 36(s3)
	srli t2, t1, 16
	sb t2, 37(s3)
	srli t2, t1, 8
	sb t2, 38(s3)
	srli t2, t1, 0
	sb t2, 39(s3)
	lbu t1, 40(s1)
	lbu t2, 41(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 42(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 43(s1)
	slli t2, t2, 24
	or t1, t1, t2
	lbu t4, 44(s1)
	lbu t2, 45(s1)
	slli t2, t2, 8
	or t4, t4, t2
	lbu t2, 46(s1)
	slli t2, t2, 16
	or t4, t4, t2
	lbu t2, 47(s1)
	slli t2, t2, 24
	or t4, t4, t2
	slli t4, t4, 32
	or t1, t1, t4
	srli t2, t1, 56
	sb t2, 40(s3)
	srli t2, t1, 48
	sb t2, 41(s3)
	srli t2, t1, 40
	sb t2, 42(s3)
	srli t2, t1, 32
	sb t2, 43(s3)
	srli t2, t1, 24
	sb t2, 44(s3)
	srli t2, t1, 16
	sb t2, 45(s3)
	srli t2, t1, 8
	sb t2, 46(s3)
	srli t2, t1, 0
	sb t2, 47(s3)
	lbu t1, 48(s1)
	lbu t2, 49(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 50(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 51(s1)
	slli t2, t2, 24
	or t1, t1, t2
	lbu t4, 52(s1)
	lbu t2, 53(s1)
	slli t2, t2, 8
	or t4, t4, t2
	lbu t2, 54(s1)
	slli t2, t2, 16
	or t4, t4, t2
	lbu t2, 55(s1)
	slli t2, t2, 24
	or t4, t4, t2
	slli t4, t4, 32
	or t1, t1, t4
	srli t2, t1, 56
	sb t2, 48(s3)
	srli t2, t1, 48
	sb t2, 49(s3)
	srli t2, t1, 40
	sb t2, 50(s3)
	srli t2, t1, 32
	sb t2, 51(s3)
	srli t2, t1, 24
	sb t2, 52(s3)
	srli t2, t1, 16
	sb t2, 53(s3)
	srli t2, t1, 8
	sb t2, 54(s3)
	srli t2, t1, 0
	sb t2, 55(s3)
	lbu t1, 56(s1)
	lbu t2, 57(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 58(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 59(s1)
	slli t2, t2, 24
	or t1, t1, t2
	lbu t4, 60(s1)
	lbu t2, 61(s1)
	slli t2, t2, 8
	or t4, t4, t2
	lbu t2, 62(s1)
	slli t2, t2, 16
	or t4, t4, t2
	lbu t2, 63(s1)
	slli t2, t2, 24
	or t4, t4, t2
	slli t4, t4, 32
	or t1, t1, t4
	srli t2, t1, 56
	sb t2, 56(s3)
	srli t2, t1, 48
	sb t2, 57(s3)
	srli t2, t1, 40
	sb t2, 58(s3)
	srli t2, t1, 32
	sb t2, 59(s3)
	srli t2, t1, 24
	sb t2, 60(s3)
	srli t2, t1, 16
	sb t2, 61(s3)
	srli t2, t1, 8
	sb t2, 62(s3)
	srli t2, t1, 0
	sb t2, 63(s3)
	lbu t1, 192(s4)
	sb t1, 0(s1)
	lbu t1, 193(s4)
	sb t1, 1(s1)
	lbu t1, 194(s4)
	sb t1, 2(s1)
	lbu t1, 195(s4)
	sb t1, 3(s1)
	lbu t1, 196(s4)
	sb t1, 4(s1)
	lbu t1, 197(s4)
	sb t1, 5(s1)
	lbu t1, 198(s4)
	sb t1, 6(s1)
	lbu t1, 199(s4)
	sb t1, 7(s1)
	lbu t1, 200(s4)
	sb t1, 8(s1)
	lbu t1, 201(s4)
	sb t1, 9(s1)
	lbu t1, 202(s4)
	sb t1, 10(s1)
	lbu t1, 203(s4)
	sb t1, 11(s1)
	lbu t1, 204(s4)
	sb t1, 12(s1)
	lbu t1, 205(s4)
	sb t1, 13(s1)
	lbu t1, 206(s4)
	sb t1, 14(s1)
	lbu t1, 207(s4)
	sb t1, 15(s1)
	lbu t1, 208(s4)
	sb t1, 16(s1)
	lbu t1, 209(s4)
	sb t1, 17(s1)
	lbu t1, 210(s4)
	sb t1, 18(s1)
	lbu t1, 211(s4)
	sb t1, 19(s1)
	lbu t1, 212(s4)
	sb t1, 20(s1)
	lbu t1, 213(s4)
	sb t1, 21(s1)
	lbu t1, 214(s4)
	sb t1, 22(s1)
	lbu t1, 215(s4)
	sb t1, 23(s1)
	lbu t1, 216(s4)
	sb t1, 24(s1)
	lbu t1, 217(s4)
	sb t1, 25(s1)
	lbu t1, 218(s4)
	sb t1, 26(s1)
	lbu t1, 219(s4)
	sb t1, 27(s1)
	lbu t1, 220(s4)
	sb t1, 28(s1)
	lbu t1, 221(s4)
	sb t1, 29(s1)
	lbu t1, 222(s4)
	sb t1, 30(s1)
	lbu t1, 223(s4)
	sb t1, 31(s1)
	lbu t1, 224(s4)
	sb t1, 32(s1)
	lbu t1, 225(s4)
	sb t1, 33(s1)
	lbu t1, 226(s4)
	sb t1, 34(s1)
	lbu t1, 227(s4)
	sb t1, 35(s1)
	lbu t1, 228(s4)
	sb t1, 36(s1)
	lbu t1, 229(s4)
	sb t1, 37(s1)
	lbu t1, 230(s4)
	sb t1, 38(s1)
	lbu t1, 231(s4)
	sb t1, 39(s1)
	lbu t1, 232(s4)
	sb t1, 40(s1)
	lbu t1, 233(s4)
	sb t1, 41(s1)
	lbu t1, 234(s4)
	sb t1, 42(s1)
	lbu t1, 235(s4)
	sb t1, 43(s1)
	lbu t1, 236(s4)
	sb t1, 44(s1)
	lbu t1, 237(s4)
	sb t1, 45(s1)
	lbu t1, 238(s4)
	sb t1, 46(s1)
	lbu t1, 239(s4)
	sb t1, 47(s1)
	lbu t1, 240(s4)
	sb t1, 48(s1)
	lbu t1, 241(s4)
	sb t1, 49(s1)
	lbu t1, 242(s4)
	sb t1, 50(s1)
	lbu t1, 243(s4)
	sb t1, 51(s1)
	lbu t1, 244(s4)
	sb t1, 52(s1)
	lbu t1, 245(s4)
	sb t1, 53(s1)
	lbu t1, 246(s4)
	sb t1, 54(s1)
	lbu t1, 247(s4)
	sb t1, 55(s1)
	lbu t1, 248(s4)
	sb t1, 56(s1)
	lbu t1, 249(s4)
	sb t1, 57(s1)
	lbu t1, 250(s4)
	sb t1, 58(s1)
	lbu t1, 251(s4)
	sb t1, 59(s1)
	lbu t1, 252(s4)
	sb t1, 60(s1)
	lbu t1, 253(s4)
	sb t1, 61(s1)
	lbu t1, 254(s4)
	sb t1, 62(s1)
	lbu t1, 255(s4)
	sb t1, 63(s1)
	addi a0, s1, 0
	addi a1, s3, 0
	addi a2, zero, 1
	addi a3, s2, 0
	call {vg_sha512_compress}
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
	lbu t4, 4(s1)
	lbu t2, 5(s1)
	slli t2, t2, 8
	or t4, t4, t2
	lbu t2, 6(s1)
	slli t2, t2, 16
	or t4, t4, t2
	lbu t2, 7(s1)
	slli t2, t2, 24
	or t4, t4, t2
	slli t4, t4, 32
	or t1, t1, t4
	srli t2, t1, 56
	sb t2, 0(s3)
	srli t2, t1, 48
	sb t2, 1(s3)
	srli t2, t1, 40
	sb t2, 2(s3)
	srli t2, t1, 32
	sb t2, 3(s3)
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
	lbu t4, 12(s1)
	lbu t2, 13(s1)
	slli t2, t2, 8
	or t4, t4, t2
	lbu t2, 14(s1)
	slli t2, t2, 16
	or t4, t4, t2
	lbu t2, 15(s1)
	slli t2, t2, 24
	or t4, t4, t2
	slli t4, t4, 32
	or t1, t1, t4
	srli t2, t1, 56
	sb t2, 8(s3)
	srli t2, t1, 48
	sb t2, 9(s3)
	srli t2, t1, 40
	sb t2, 10(s3)
	srli t2, t1, 32
	sb t2, 11(s3)
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
	lbu t4, 20(s1)
	lbu t2, 21(s1)
	slli t2, t2, 8
	or t4, t4, t2
	lbu t2, 22(s1)
	slli t2, t2, 16
	or t4, t4, t2
	lbu t2, 23(s1)
	slli t2, t2, 24
	or t4, t4, t2
	slli t4, t4, 32
	or t1, t1, t4
	srli t2, t1, 56
	sb t2, 16(s3)
	srli t2, t1, 48
	sb t2, 17(s3)
	srli t2, t1, 40
	sb t2, 18(s3)
	srli t2, t1, 32
	sb t2, 19(s3)
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
	lbu t4, 28(s1)
	lbu t2, 29(s1)
	slli t2, t2, 8
	or t4, t4, t2
	lbu t2, 30(s1)
	slli t2, t2, 16
	or t4, t4, t2
	lbu t2, 31(s1)
	slli t2, t2, 24
	or t4, t4, t2
	slli t4, t4, 32
	or t1, t1, t4
	srli t2, t1, 56
	sb t2, 24(s3)
	srli t2, t1, 48
	sb t2, 25(s3)
	srli t2, t1, 40
	sb t2, 26(s3)
	srli t2, t1, 32
	sb t2, 27(s3)
	srli t2, t1, 24
	sb t2, 28(s3)
	srli t2, t1, 16
	sb t2, 29(s3)
	srli t2, t1, 8
	sb t2, 30(s3)
	srli t2, t1, 0
	sb t2, 31(s3)
	lbu t1, 32(s1)
	lbu t2, 33(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 34(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 35(s1)
	slli t2, t2, 24
	or t1, t1, t2
	lbu t4, 36(s1)
	lbu t2, 37(s1)
	slli t2, t2, 8
	or t4, t4, t2
	lbu t2, 38(s1)
	slli t2, t2, 16
	or t4, t4, t2
	lbu t2, 39(s1)
	slli t2, t2, 24
	or t4, t4, t2
	slli t4, t4, 32
	or t1, t1, t4
	srli t2, t1, 56
	sb t2, 32(s3)
	srli t2, t1, 48
	sb t2, 33(s3)
	srli t2, t1, 40
	sb t2, 34(s3)
	srli t2, t1, 32
	sb t2, 35(s3)
	srli t2, t1, 24
	sb t2, 36(s3)
	srli t2, t1, 16
	sb t2, 37(s3)
	srli t2, t1, 8
	sb t2, 38(s3)
	srli t2, t1, 0
	sb t2, 39(s3)
	lbu t1, 40(s1)
	lbu t2, 41(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 42(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 43(s1)
	slli t2, t2, 24
	or t1, t1, t2
	lbu t4, 44(s1)
	lbu t2, 45(s1)
	slli t2, t2, 8
	or t4, t4, t2
	lbu t2, 46(s1)
	slli t2, t2, 16
	or t4, t4, t2
	lbu t2, 47(s1)
	slli t2, t2, 24
	or t4, t4, t2
	slli t4, t4, 32
	or t1, t1, t4
	srli t2, t1, 56
	sb t2, 40(s3)
	srli t2, t1, 48
	sb t2, 41(s3)
	srli t2, t1, 40
	sb t2, 42(s3)
	srli t2, t1, 32
	sb t2, 43(s3)
	srli t2, t1, 24
	sb t2, 44(s3)
	srli t2, t1, 16
	sb t2, 45(s3)
	srli t2, t1, 8
	sb t2, 46(s3)
	srli t2, t1, 0
	sb t2, 47(s3)
	lbu t1, 48(s1)
	lbu t2, 49(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 50(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 51(s1)
	slli t2, t2, 24
	or t1, t1, t2
	lbu t4, 52(s1)
	lbu t2, 53(s1)
	slli t2, t2, 8
	or t4, t4, t2
	lbu t2, 54(s1)
	slli t2, t2, 16
	or t4, t4, t2
	lbu t2, 55(s1)
	slli t2, t2, 24
	or t4, t4, t2
	slli t4, t4, 32
	or t1, t1, t4
	srli t2, t1, 56
	sb t2, 48(s3)
	srli t2, t1, 48
	sb t2, 49(s3)
	srli t2, t1, 40
	sb t2, 50(s3)
	srli t2, t1, 32
	sb t2, 51(s3)
	srli t2, t1, 24
	sb t2, 52(s3)
	srli t2, t1, 16
	sb t2, 53(s3)
	srli t2, t1, 8
	sb t2, 54(s3)
	srli t2, t1, 0
	sb t2, 55(s3)
	lbu t1, 56(s1)
	lbu t2, 57(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 58(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 59(s1)
	slli t2, t2, 24
	or t1, t1, t2
	lbu t4, 60(s1)
	lbu t2, 61(s1)
	slli t2, t2, 8
	or t4, t4, t2
	lbu t2, 62(s1)
	slli t2, t2, 16
	or t4, t4, t2
	lbu t2, 63(s1)
	slli t2, t2, 24
	or t4, t4, t2
	slli t4, t4, 32
	or t1, t1, t4
	srli t2, t1, 56
	sb t2, 56(s3)
	srli t2, t1, 48
	sb t2, 57(s3)
	srli t2, t1, 40
	sb t2, 58(s3)
	srli t2, t1, 32
	sb t2, 59(s3)
	srli t2, t1, 24
	sb t2, 60(s3)
	srli t2, t1, 16
	sb t2, 61(s3)
	srli t2, t1, 8
	sb t2, 62(s3)
	srli t2, t1, 0
	sb t2, 63(s3)
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
	lbu t1, 32(s5)
	lbu t2, 32(s3)
	xor t1, t1, t2
	sb t1, 32(s5)
	lbu t1, 33(s5)
	lbu t2, 33(s3)
	xor t1, t1, t2
	sb t1, 33(s5)
	lbu t1, 34(s5)
	lbu t2, 34(s3)
	xor t1, t1, t2
	sb t1, 34(s5)
	lbu t1, 35(s5)
	lbu t2, 35(s3)
	xor t1, t1, t2
	sb t1, 35(s5)
	lbu t1, 36(s5)
	lbu t2, 36(s3)
	xor t1, t1, t2
	sb t1, 36(s5)
	lbu t1, 37(s5)
	lbu t2, 37(s3)
	xor t1, t1, t2
	sb t1, 37(s5)
	lbu t1, 38(s5)
	lbu t2, 38(s3)
	xor t1, t1, t2
	sb t1, 38(s5)
	lbu t1, 39(s5)
	lbu t2, 39(s3)
	xor t1, t1, t2
	sb t1, 39(s5)
	lbu t1, 40(s5)
	lbu t2, 40(s3)
	xor t1, t1, t2
	sb t1, 40(s5)
	lbu t1, 41(s5)
	lbu t2, 41(s3)
	xor t1, t1, t2
	sb t1, 41(s5)
	lbu t1, 42(s5)
	lbu t2, 42(s3)
	xor t1, t1, t2
	sb t1, 42(s5)
	lbu t1, 43(s5)
	lbu t2, 43(s3)
	xor t1, t1, t2
	sb t1, 43(s5)
	lbu t1, 44(s5)
	lbu t2, 44(s3)
	xor t1, t1, t2
	sb t1, 44(s5)
	lbu t1, 45(s5)
	lbu t2, 45(s3)
	xor t1, t1, t2
	sb t1, 45(s5)
	lbu t1, 46(s5)
	lbu t2, 46(s3)
	xor t1, t1, t2
	sb t1, 46(s5)
	lbu t1, 47(s5)
	lbu t2, 47(s3)
	xor t1, t1, t2
	sb t1, 47(s5)
	lbu t1, 48(s5)
	lbu t2, 48(s3)
	xor t1, t1, t2
	sb t1, 48(s5)
	lbu t1, 49(s5)
	lbu t2, 49(s3)
	xor t1, t1, t2
	sb t1, 49(s5)
	lbu t1, 50(s5)
	lbu t2, 50(s3)
	xor t1, t1, t2
	sb t1, 50(s5)
	lbu t1, 51(s5)
	lbu t2, 51(s3)
	xor t1, t1, t2
	sb t1, 51(s5)
	lbu t1, 52(s5)
	lbu t2, 52(s3)
	xor t1, t1, t2
	sb t1, 52(s5)
	lbu t1, 53(s5)
	lbu t2, 53(s3)
	xor t1, t1, t2
	sb t1, 53(s5)
	lbu t1, 54(s5)
	lbu t2, 54(s3)
	xor t1, t1, t2
	sb t1, 54(s5)
	lbu t1, 55(s5)
	lbu t2, 55(s3)
	xor t1, t1, t2
	sb t1, 55(s5)
	lbu t1, 56(s5)
	lbu t2, 56(s3)
	xor t1, t1, t2
	sb t1, 56(s5)
	lbu t1, 57(s5)
	lbu t2, 57(s3)
	xor t1, t1, t2
	sb t1, 57(s5)
	lbu t1, 58(s5)
	lbu t2, 58(s3)
	xor t1, t1, t2
	sb t1, 58(s5)
	lbu t1, 59(s5)
	lbu t2, 59(s3)
	xor t1, t1, t2
	sb t1, 59(s5)
	lbu t1, 60(s5)
	lbu t2, 60(s3)
	xor t1, t1, t2
	sb t1, 60(s5)
	lbu t1, 61(s5)
	lbu t2, 61(s3)
	xor t1, t1, t2
	sb t1, 61(s5)
	lbu t1, 62(s5)
	lbu t2, 62(s3)
	xor t1, t1, t2
	sb t1, 62(s5)
	lbu t1, 63(s5)
	lbu t2, 63(s3)
	xor t1, t1, t2
	sb t1, 63(s5)
	addi s6, s6, -1
	bnez s6, 22b
	j 21f
20:
21:
	ld ra, 144(s2)
	ld s1, 152(s2)
	ld s3, 168(s2)
	ld s4, 176(s2)
	ld s5, 184(s2)
	ld s6, 192(s2)
	ld s2, 160(s2)
	ret
	.option pop
