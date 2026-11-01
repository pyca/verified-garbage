// The functions of `src/pbkdf2_sha512_256.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_pbkdf2_hmac_sha512_256_iterate:
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
	addi t1, zero, 0
	sb t1, 62(s3)
	addi t1, zero, 0
	sb t1, 63(s3)
	addi t1, zero, 0
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
	addi t1, zero, 5
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
	ld ra, 144(s2)
	ld s1, 152(s2)
	ld s3, 168(s2)
	ld s4, 176(s2)
	ld s5, 184(s2)
	ld s6, 192(s2)
	ld s2, 160(s2)
	ret
	.option pop

vg_pbkdf2_hmac_sha512_256:
	.option push
	.option arch, +m, +c
	addi sp, sp, -400
	addi sp, sp, -720
	addi t0, sp, 0
	sd ra, 0(t0)
	sd s1, 8(t0)
	sd s2, 16(t0)
	sd s3, 24(t0)
	sd s4, 32(t0)
	sd s5, 40(t0)
	sd s6, 48(t0)
	sd s7, 56(t0)
	addi s1, t0, 0
	addi s2, a3, 0
	addi s3, a4, 0
	addi s4, a5, 0
	addi s5, a6, 0
	addi s6, a2, 0
	addi a2, a0, 0
	addi a3, a1, 0
	addi a0, s1, 64
	addi a1, s1, 256
	call {vg_hmac_sha512_256_init}
	addi s7, zero, 1
	beqz s5, 20f
22:
	lbu t1, 64(s1)
	sb t1, 448(s1)
	lbu t1, 65(s1)
	sb t1, 449(s1)
	lbu t1, 66(s1)
	sb t1, 450(s1)
	lbu t1, 67(s1)
	sb t1, 451(s1)
	lbu t1, 68(s1)
	sb t1, 452(s1)
	lbu t1, 69(s1)
	sb t1, 453(s1)
	lbu t1, 70(s1)
	sb t1, 454(s1)
	lbu t1, 71(s1)
	sb t1, 455(s1)
	lbu t1, 72(s1)
	sb t1, 456(s1)
	lbu t1, 73(s1)
	sb t1, 457(s1)
	lbu t1, 74(s1)
	sb t1, 458(s1)
	lbu t1, 75(s1)
	sb t1, 459(s1)
	lbu t1, 76(s1)
	sb t1, 460(s1)
	lbu t1, 77(s1)
	sb t1, 461(s1)
	lbu t1, 78(s1)
	sb t1, 462(s1)
	lbu t1, 79(s1)
	sb t1, 463(s1)
	lbu t1, 80(s1)
	sb t1, 464(s1)
	lbu t1, 81(s1)
	sb t1, 465(s1)
	lbu t1, 82(s1)
	sb t1, 466(s1)
	lbu t1, 83(s1)
	sb t1, 467(s1)
	lbu t1, 84(s1)
	sb t1, 468(s1)
	lbu t1, 85(s1)
	sb t1, 469(s1)
	lbu t1, 86(s1)
	sb t1, 470(s1)
	lbu t1, 87(s1)
	sb t1, 471(s1)
	lbu t1, 88(s1)
	sb t1, 472(s1)
	lbu t1, 89(s1)
	sb t1, 473(s1)
	lbu t1, 90(s1)
	sb t1, 474(s1)
	lbu t1, 91(s1)
	sb t1, 475(s1)
	lbu t1, 92(s1)
	sb t1, 476(s1)
	lbu t1, 93(s1)
	sb t1, 477(s1)
	lbu t1, 94(s1)
	sb t1, 478(s1)
	lbu t1, 95(s1)
	sb t1, 479(s1)
	lbu t1, 96(s1)
	sb t1, 480(s1)
	lbu t1, 97(s1)
	sb t1, 481(s1)
	lbu t1, 98(s1)
	sb t1, 482(s1)
	lbu t1, 99(s1)
	sb t1, 483(s1)
	lbu t1, 100(s1)
	sb t1, 484(s1)
	lbu t1, 101(s1)
	sb t1, 485(s1)
	lbu t1, 102(s1)
	sb t1, 486(s1)
	lbu t1, 103(s1)
	sb t1, 487(s1)
	lbu t1, 104(s1)
	sb t1, 488(s1)
	lbu t1, 105(s1)
	sb t1, 489(s1)
	lbu t1, 106(s1)
	sb t1, 490(s1)
	lbu t1, 107(s1)
	sb t1, 491(s1)
	lbu t1, 108(s1)
	sb t1, 492(s1)
	lbu t1, 109(s1)
	sb t1, 493(s1)
	lbu t1, 110(s1)
	sb t1, 494(s1)
	lbu t1, 111(s1)
	sb t1, 495(s1)
	lbu t1, 112(s1)
	sb t1, 496(s1)
	lbu t1, 113(s1)
	sb t1, 497(s1)
	lbu t1, 114(s1)
	sb t1, 498(s1)
	lbu t1, 115(s1)
	sb t1, 499(s1)
	lbu t1, 116(s1)
	sb t1, 500(s1)
	lbu t1, 117(s1)
	sb t1, 501(s1)
	lbu t1, 118(s1)
	sb t1, 502(s1)
	lbu t1, 119(s1)
	sb t1, 503(s1)
	lbu t1, 120(s1)
	sb t1, 504(s1)
	lbu t1, 121(s1)
	sb t1, 505(s1)
	lbu t1, 122(s1)
	sb t1, 506(s1)
	lbu t1, 123(s1)
	sb t1, 507(s1)
	lbu t1, 124(s1)
	sb t1, 508(s1)
	lbu t1, 125(s1)
	sb t1, 509(s1)
	lbu t1, 126(s1)
	sb t1, 510(s1)
	lbu t1, 127(s1)
	sb t1, 511(s1)
	lbu t1, 128(s1)
	sb t1, 512(s1)
	lbu t1, 129(s1)
	sb t1, 513(s1)
	lbu t1, 130(s1)
	sb t1, 514(s1)
	lbu t1, 131(s1)
	sb t1, 515(s1)
	lbu t1, 132(s1)
	sb t1, 516(s1)
	lbu t1, 133(s1)
	sb t1, 517(s1)
	lbu t1, 134(s1)
	sb t1, 518(s1)
	lbu t1, 135(s1)
	sb t1, 519(s1)
	lbu t1, 136(s1)
	sb t1, 520(s1)
	lbu t1, 137(s1)
	sb t1, 521(s1)
	lbu t1, 138(s1)
	sb t1, 522(s1)
	lbu t1, 139(s1)
	sb t1, 523(s1)
	lbu t1, 140(s1)
	sb t1, 524(s1)
	lbu t1, 141(s1)
	sb t1, 525(s1)
	lbu t1, 142(s1)
	sb t1, 526(s1)
	lbu t1, 143(s1)
	sb t1, 527(s1)
	lbu t1, 144(s1)
	sb t1, 528(s1)
	lbu t1, 145(s1)
	sb t1, 529(s1)
	lbu t1, 146(s1)
	sb t1, 530(s1)
	lbu t1, 147(s1)
	sb t1, 531(s1)
	lbu t1, 148(s1)
	sb t1, 532(s1)
	lbu t1, 149(s1)
	sb t1, 533(s1)
	lbu t1, 150(s1)
	sb t1, 534(s1)
	lbu t1, 151(s1)
	sb t1, 535(s1)
	lbu t1, 152(s1)
	sb t1, 536(s1)
	lbu t1, 153(s1)
	sb t1, 537(s1)
	lbu t1, 154(s1)
	sb t1, 538(s1)
	lbu t1, 155(s1)
	sb t1, 539(s1)
	lbu t1, 156(s1)
	sb t1, 540(s1)
	lbu t1, 157(s1)
	sb t1, 541(s1)
	lbu t1, 158(s1)
	sb t1, 542(s1)
	lbu t1, 159(s1)
	sb t1, 543(s1)
	lbu t1, 160(s1)
	sb t1, 544(s1)
	lbu t1, 161(s1)
	sb t1, 545(s1)
	lbu t1, 162(s1)
	sb t1, 546(s1)
	lbu t1, 163(s1)
	sb t1, 547(s1)
	lbu t1, 164(s1)
	sb t1, 548(s1)
	lbu t1, 165(s1)
	sb t1, 549(s1)
	lbu t1, 166(s1)
	sb t1, 550(s1)
	lbu t1, 167(s1)
	sb t1, 551(s1)
	lbu t1, 168(s1)
	sb t1, 552(s1)
	lbu t1, 169(s1)
	sb t1, 553(s1)
	lbu t1, 170(s1)
	sb t1, 554(s1)
	lbu t1, 171(s1)
	sb t1, 555(s1)
	lbu t1, 172(s1)
	sb t1, 556(s1)
	lbu t1, 173(s1)
	sb t1, 557(s1)
	lbu t1, 174(s1)
	sb t1, 558(s1)
	lbu t1, 175(s1)
	sb t1, 559(s1)
	lbu t1, 176(s1)
	sb t1, 560(s1)
	lbu t1, 177(s1)
	sb t1, 561(s1)
	lbu t1, 178(s1)
	sb t1, 562(s1)
	lbu t1, 179(s1)
	sb t1, 563(s1)
	lbu t1, 180(s1)
	sb t1, 564(s1)
	lbu t1, 181(s1)
	sb t1, 565(s1)
	lbu t1, 182(s1)
	sb t1, 566(s1)
	lbu t1, 183(s1)
	sb t1, 567(s1)
	lbu t1, 184(s1)
	sb t1, 568(s1)
	lbu t1, 185(s1)
	sb t1, 569(s1)
	lbu t1, 186(s1)
	sb t1, 570(s1)
	lbu t1, 187(s1)
	sb t1, 571(s1)
	lbu t1, 188(s1)
	sb t1, 572(s1)
	lbu t1, 189(s1)
	sb t1, 573(s1)
	lbu t1, 190(s1)
	sb t1, 574(s1)
	lbu t1, 191(s1)
	sb t1, 575(s1)
	lbu t1, 192(s1)
	sb t1, 576(s1)
	lbu t1, 193(s1)
	sb t1, 577(s1)
	lbu t1, 194(s1)
	sb t1, 578(s1)
	lbu t1, 195(s1)
	sb t1, 579(s1)
	lbu t1, 196(s1)
	sb t1, 580(s1)
	lbu t1, 197(s1)
	sb t1, 581(s1)
	lbu t1, 198(s1)
	sb t1, 582(s1)
	lbu t1, 199(s1)
	sb t1, 583(s1)
	lbu t1, 200(s1)
	sb t1, 584(s1)
	lbu t1, 201(s1)
	sb t1, 585(s1)
	lbu t1, 202(s1)
	sb t1, 586(s1)
	lbu t1, 203(s1)
	sb t1, 587(s1)
	lbu t1, 204(s1)
	sb t1, 588(s1)
	lbu t1, 205(s1)
	sb t1, 589(s1)
	lbu t1, 206(s1)
	sb t1, 590(s1)
	lbu t1, 207(s1)
	sb t1, 591(s1)
	lbu t1, 208(s1)
	sb t1, 592(s1)
	lbu t1, 209(s1)
	sb t1, 593(s1)
	lbu t1, 210(s1)
	sb t1, 594(s1)
	lbu t1, 211(s1)
	sb t1, 595(s1)
	lbu t1, 212(s1)
	sb t1, 596(s1)
	lbu t1, 213(s1)
	sb t1, 597(s1)
	lbu t1, 214(s1)
	sb t1, 598(s1)
	lbu t1, 215(s1)
	sb t1, 599(s1)
	lbu t1, 216(s1)
	sb t1, 600(s1)
	lbu t1, 217(s1)
	sb t1, 601(s1)
	lbu t1, 218(s1)
	sb t1, 602(s1)
	lbu t1, 219(s1)
	sb t1, 603(s1)
	lbu t1, 220(s1)
	sb t1, 604(s1)
	lbu t1, 221(s1)
	sb t1, 605(s1)
	lbu t1, 222(s1)
	sb t1, 606(s1)
	lbu t1, 223(s1)
	sb t1, 607(s1)
	lbu t1, 224(s1)
	sb t1, 608(s1)
	lbu t1, 225(s1)
	sb t1, 609(s1)
	lbu t1, 226(s1)
	sb t1, 610(s1)
	lbu t1, 227(s1)
	sb t1, 611(s1)
	lbu t1, 228(s1)
	sb t1, 612(s1)
	lbu t1, 229(s1)
	sb t1, 613(s1)
	lbu t1, 230(s1)
	sb t1, 614(s1)
	lbu t1, 231(s1)
	sb t1, 615(s1)
	lbu t1, 232(s1)
	sb t1, 616(s1)
	lbu t1, 233(s1)
	sb t1, 617(s1)
	lbu t1, 234(s1)
	sb t1, 618(s1)
	lbu t1, 235(s1)
	sb t1, 619(s1)
	lbu t1, 236(s1)
	sb t1, 620(s1)
	lbu t1, 237(s1)
	sb t1, 621(s1)
	lbu t1, 238(s1)
	sb t1, 622(s1)
	lbu t1, 239(s1)
	sb t1, 623(s1)
	lbu t1, 240(s1)
	sb t1, 624(s1)
	lbu t1, 241(s1)
	sb t1, 625(s1)
	lbu t1, 242(s1)
	sb t1, 626(s1)
	lbu t1, 243(s1)
	sb t1, 627(s1)
	lbu t1, 244(s1)
	sb t1, 628(s1)
	lbu t1, 245(s1)
	sb t1, 629(s1)
	lbu t1, 246(s1)
	sb t1, 630(s1)
	lbu t1, 247(s1)
	sb t1, 631(s1)
	lbu t1, 248(s1)
	sb t1, 632(s1)
	lbu t1, 249(s1)
	sb t1, 633(s1)
	lbu t1, 250(s1)
	sb t1, 634(s1)
	lbu t1, 251(s1)
	sb t1, 635(s1)
	lbu t1, 252(s1)
	sb t1, 636(s1)
	lbu t1, 253(s1)
	sb t1, 637(s1)
	lbu t1, 254(s1)
	sb t1, 638(s1)
	lbu t1, 255(s1)
	sb t1, 639(s1)
	addi a0, s1, 448
	addi a1, zero, 128
	addi a2, s6, 0
	addi a3, s2, 0
	call {vg_sha512_update}
	srli t1, s7, 24
	sb t1, 704(s1)
	srli t1, s7, 16
	sb t1, 705(s1)
	srli t1, s7, 8
	sb t1, 706(s1)
	sb s7, 707(s1)
	addi a0, s1, 448
	addi a1, s2, 128
	addi a2, s1, 704
	addi a3, zero, 4
	call {vg_sha512_update}
	addi a0, s1, 448
	addi a1, s1, 256
	addi a2, s2, 132
	addi a3, s1, 640
	call {vg_hmac_sha512_256_finalize}
	lbu t1, 640(s1)
	sb t1, 672(s1)
	lbu t1, 641(s1)
	sb t1, 673(s1)
	lbu t1, 642(s1)
	sb t1, 674(s1)
	lbu t1, 643(s1)
	sb t1, 675(s1)
	lbu t1, 644(s1)
	sb t1, 676(s1)
	lbu t1, 645(s1)
	sb t1, 677(s1)
	lbu t1, 646(s1)
	sb t1, 678(s1)
	lbu t1, 647(s1)
	sb t1, 679(s1)
	lbu t1, 648(s1)
	sb t1, 680(s1)
	lbu t1, 649(s1)
	sb t1, 681(s1)
	lbu t1, 650(s1)
	sb t1, 682(s1)
	lbu t1, 651(s1)
	sb t1, 683(s1)
	lbu t1, 652(s1)
	sb t1, 684(s1)
	lbu t1, 653(s1)
	sb t1, 685(s1)
	lbu t1, 654(s1)
	sb t1, 686(s1)
	lbu t1, 655(s1)
	sb t1, 687(s1)
	lbu t1, 656(s1)
	sb t1, 688(s1)
	lbu t1, 657(s1)
	sb t1, 689(s1)
	lbu t1, 658(s1)
	sb t1, 690(s1)
	lbu t1, 659(s1)
	sb t1, 691(s1)
	lbu t1, 660(s1)
	sb t1, 692(s1)
	lbu t1, 661(s1)
	sb t1, 693(s1)
	lbu t1, 662(s1)
	sb t1, 694(s1)
	lbu t1, 663(s1)
	sb t1, 695(s1)
	lbu t1, 664(s1)
	sb t1, 696(s1)
	lbu t1, 665(s1)
	sb t1, 697(s1)
	lbu t1, 666(s1)
	sb t1, 698(s1)
	lbu t1, 667(s1)
	sb t1, 699(s1)
	lbu t1, 668(s1)
	sb t1, 700(s1)
	lbu t1, 669(s1)
	sb t1, 701(s1)
	lbu t1, 670(s1)
	sb t1, 702(s1)
	lbu t1, 671(s1)
	sb t1, 703(s1)
	addi a0, s1, 64
	addi a1, s1, 640
	addi a2, s3, -1
	addi a3, s1, 672
	addi a4, s1, 720
	call {vg_pbkdf2_hmac_sha512_256_iterate}
	addi t1, s5, -32
	srli t1, t1, 63
	addi t2, s5, 0
	bnez t1, 23f
	addi t2, zero, 32
	j 24f
23:
24:
	addi t3, zero, 0
25:
	add t4, s1, t3
	lbu t1, 672(t4)
	add t4, s4, t3
	sb t1, 0(t4)
	addi t3, t3, 1
	addi t2, t2, -1
	bnez t2, 25b
	add s4, s4, t3
	sub s5, s5, t3
	addi s7, s7, 1
	bnez s5, 22b
	j 21f
20:
21:
	ld ra, 0(s1)
	ld s2, 16(s1)
	ld s3, 24(s1)
	ld s4, 32(s1)
	ld s5, 40(s1)
	ld s6, 48(s1)
	ld s7, 56(s1)
	ld s1, 8(s1)
	addi sp, sp, 720
	addi sp, sp, 400
	ret
	.option pop
