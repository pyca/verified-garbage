// The functions of `src/pbkdf2_md5.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_pbkdf2_hmac_md5_iterate:
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
	addi s3, a4, 152
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
	addi t1, zero, 128
	sb t1, 16(s3)
	addi t1, zero, 0
	sb t1, 17(s3)
	addi t1, zero, 0
	sb t1, 18(s3)
	addi t1, zero, 0
	sb t1, 19(s3)
	addi t1, zero, 0
	sb t1, 20(s3)
	addi t1, zero, 0
	sb t1, 21(s3)
	addi t1, zero, 0
	sb t1, 22(s3)
	addi t1, zero, 0
	sb t1, 23(s3)
	addi t1, zero, 0
	sb t1, 24(s3)
	addi t1, zero, 0
	sb t1, 25(s3)
	addi t1, zero, 0
	sb t1, 26(s3)
	addi t1, zero, 0
	sb t1, 27(s3)
	addi t1, zero, 0
	sb t1, 28(s3)
	addi t1, zero, 0
	sb t1, 29(s3)
	addi t1, zero, 0
	sb t1, 30(s3)
	addi t1, zero, 0
	sb t1, 31(s3)
	addi t1, zero, 0
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
	addi t1, zero, 128
	sb t1, 56(s3)
	addi t1, zero, 2
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
	addi a0, s1, 0
	addi a1, s3, 0
	addi a2, zero, 1
	addi a3, s2, 0
	call {vg_md5_compress}
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
	sb t1, 0(s3)
	srli t2, t1, 8
	sb t2, 1(s3)
	srli t2, t1, 16
	sb t2, 2(s3)
	srli t2, t1, 24
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
	sb t1, 4(s3)
	srli t2, t1, 8
	sb t2, 5(s3)
	srli t2, t1, 16
	sb t2, 6(s3)
	srli t2, t1, 24
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
	sb t1, 8(s3)
	srli t2, t1, 8
	sb t2, 9(s3)
	srli t2, t1, 16
	sb t2, 10(s3)
	srli t2, t1, 24
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
	sb t1, 12(s3)
	srli t2, t1, 8
	sb t2, 13(s3)
	srli t2, t1, 16
	sb t2, 14(s3)
	srli t2, t1, 24
	sb t2, 15(s3)
	lbu t1, 80(s4)
	sb t1, 0(s1)
	lbu t1, 81(s4)
	sb t1, 1(s1)
	lbu t1, 82(s4)
	sb t1, 2(s1)
	lbu t1, 83(s4)
	sb t1, 3(s1)
	lbu t1, 84(s4)
	sb t1, 4(s1)
	lbu t1, 85(s4)
	sb t1, 5(s1)
	lbu t1, 86(s4)
	sb t1, 6(s1)
	lbu t1, 87(s4)
	sb t1, 7(s1)
	lbu t1, 88(s4)
	sb t1, 8(s1)
	lbu t1, 89(s4)
	sb t1, 9(s1)
	lbu t1, 90(s4)
	sb t1, 10(s1)
	lbu t1, 91(s4)
	sb t1, 11(s1)
	lbu t1, 92(s4)
	sb t1, 12(s1)
	lbu t1, 93(s4)
	sb t1, 13(s1)
	lbu t1, 94(s4)
	sb t1, 14(s1)
	lbu t1, 95(s4)
	sb t1, 15(s1)
	addi a0, s1, 0
	addi a1, s3, 0
	addi a2, zero, 1
	addi a3, s2, 0
	call {vg_md5_compress}
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
	sb t1, 0(s3)
	srli t2, t1, 8
	sb t2, 1(s3)
	srli t2, t1, 16
	sb t2, 2(s3)
	srli t2, t1, 24
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
	sb t1, 4(s3)
	srli t2, t1, 8
	sb t2, 5(s3)
	srli t2, t1, 16
	sb t2, 6(s3)
	srli t2, t1, 24
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
	sb t1, 8(s3)
	srli t2, t1, 8
	sb t2, 9(s3)
	srli t2, t1, 16
	sb t2, 10(s3)
	srli t2, t1, 24
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
	sb t1, 12(s3)
	srli t2, t1, 8
	sb t2, 13(s3)
	srli t2, t1, 16
	sb t2, 14(s3)
	srli t2, t1, 24
	sb t2, 15(s3)
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

vg_pbkdf2_hmac_md5:
	.option push
	.option arch, +m, +c
	addi sp, sp, -224
	addi sp, sp, -352
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
	addi a1, s1, 144
	call {vg_hmac_md5_init}
	addi s7, zero, 1
	beqz s5, 20f
22:
	lbu t1, 64(s1)
	sb t1, 224(s1)
	lbu t1, 65(s1)
	sb t1, 225(s1)
	lbu t1, 66(s1)
	sb t1, 226(s1)
	lbu t1, 67(s1)
	sb t1, 227(s1)
	lbu t1, 68(s1)
	sb t1, 228(s1)
	lbu t1, 69(s1)
	sb t1, 229(s1)
	lbu t1, 70(s1)
	sb t1, 230(s1)
	lbu t1, 71(s1)
	sb t1, 231(s1)
	lbu t1, 72(s1)
	sb t1, 232(s1)
	lbu t1, 73(s1)
	sb t1, 233(s1)
	lbu t1, 74(s1)
	sb t1, 234(s1)
	lbu t1, 75(s1)
	sb t1, 235(s1)
	lbu t1, 76(s1)
	sb t1, 236(s1)
	lbu t1, 77(s1)
	sb t1, 237(s1)
	lbu t1, 78(s1)
	sb t1, 238(s1)
	lbu t1, 79(s1)
	sb t1, 239(s1)
	lbu t1, 80(s1)
	sb t1, 240(s1)
	lbu t1, 81(s1)
	sb t1, 241(s1)
	lbu t1, 82(s1)
	sb t1, 242(s1)
	lbu t1, 83(s1)
	sb t1, 243(s1)
	lbu t1, 84(s1)
	sb t1, 244(s1)
	lbu t1, 85(s1)
	sb t1, 245(s1)
	lbu t1, 86(s1)
	sb t1, 246(s1)
	lbu t1, 87(s1)
	sb t1, 247(s1)
	lbu t1, 88(s1)
	sb t1, 248(s1)
	lbu t1, 89(s1)
	sb t1, 249(s1)
	lbu t1, 90(s1)
	sb t1, 250(s1)
	lbu t1, 91(s1)
	sb t1, 251(s1)
	lbu t1, 92(s1)
	sb t1, 252(s1)
	lbu t1, 93(s1)
	sb t1, 253(s1)
	lbu t1, 94(s1)
	sb t1, 254(s1)
	lbu t1, 95(s1)
	sb t1, 255(s1)
	lbu t1, 96(s1)
	sb t1, 256(s1)
	lbu t1, 97(s1)
	sb t1, 257(s1)
	lbu t1, 98(s1)
	sb t1, 258(s1)
	lbu t1, 99(s1)
	sb t1, 259(s1)
	lbu t1, 100(s1)
	sb t1, 260(s1)
	lbu t1, 101(s1)
	sb t1, 261(s1)
	lbu t1, 102(s1)
	sb t1, 262(s1)
	lbu t1, 103(s1)
	sb t1, 263(s1)
	lbu t1, 104(s1)
	sb t1, 264(s1)
	lbu t1, 105(s1)
	sb t1, 265(s1)
	lbu t1, 106(s1)
	sb t1, 266(s1)
	lbu t1, 107(s1)
	sb t1, 267(s1)
	lbu t1, 108(s1)
	sb t1, 268(s1)
	lbu t1, 109(s1)
	sb t1, 269(s1)
	lbu t1, 110(s1)
	sb t1, 270(s1)
	lbu t1, 111(s1)
	sb t1, 271(s1)
	lbu t1, 112(s1)
	sb t1, 272(s1)
	lbu t1, 113(s1)
	sb t1, 273(s1)
	lbu t1, 114(s1)
	sb t1, 274(s1)
	lbu t1, 115(s1)
	sb t1, 275(s1)
	lbu t1, 116(s1)
	sb t1, 276(s1)
	lbu t1, 117(s1)
	sb t1, 277(s1)
	lbu t1, 118(s1)
	sb t1, 278(s1)
	lbu t1, 119(s1)
	sb t1, 279(s1)
	lbu t1, 120(s1)
	sb t1, 280(s1)
	lbu t1, 121(s1)
	sb t1, 281(s1)
	lbu t1, 122(s1)
	sb t1, 282(s1)
	lbu t1, 123(s1)
	sb t1, 283(s1)
	lbu t1, 124(s1)
	sb t1, 284(s1)
	lbu t1, 125(s1)
	sb t1, 285(s1)
	lbu t1, 126(s1)
	sb t1, 286(s1)
	lbu t1, 127(s1)
	sb t1, 287(s1)
	lbu t1, 128(s1)
	sb t1, 288(s1)
	lbu t1, 129(s1)
	sb t1, 289(s1)
	lbu t1, 130(s1)
	sb t1, 290(s1)
	lbu t1, 131(s1)
	sb t1, 291(s1)
	lbu t1, 132(s1)
	sb t1, 292(s1)
	lbu t1, 133(s1)
	sb t1, 293(s1)
	lbu t1, 134(s1)
	sb t1, 294(s1)
	lbu t1, 135(s1)
	sb t1, 295(s1)
	lbu t1, 136(s1)
	sb t1, 296(s1)
	lbu t1, 137(s1)
	sb t1, 297(s1)
	lbu t1, 138(s1)
	sb t1, 298(s1)
	lbu t1, 139(s1)
	sb t1, 299(s1)
	lbu t1, 140(s1)
	sb t1, 300(s1)
	lbu t1, 141(s1)
	sb t1, 301(s1)
	lbu t1, 142(s1)
	sb t1, 302(s1)
	lbu t1, 143(s1)
	sb t1, 303(s1)
	addi a0, s1, 224
	addi a1, zero, 64
	addi a2, s6, 0
	addi a3, s2, 0
	call {vg_md5_update}
	srli t1, s7, 24
	sb t1, 336(s1)
	srli t1, s7, 16
	sb t1, 337(s1)
	srli t1, s7, 8
	sb t1, 338(s1)
	sb s7, 339(s1)
	addi a0, s1, 224
	addi a1, s2, 64
	addi a2, s1, 336
	addi a3, zero, 4
	call {vg_md5_update}
	addi a0, s1, 224
	addi a1, s1, 144
	addi a2, s2, 68
	addi a3, s1, 304
	call {vg_hmac_md5_finalize}
	lbu t1, 304(s1)
	sb t1, 320(s1)
	lbu t1, 305(s1)
	sb t1, 321(s1)
	lbu t1, 306(s1)
	sb t1, 322(s1)
	lbu t1, 307(s1)
	sb t1, 323(s1)
	lbu t1, 308(s1)
	sb t1, 324(s1)
	lbu t1, 309(s1)
	sb t1, 325(s1)
	lbu t1, 310(s1)
	sb t1, 326(s1)
	lbu t1, 311(s1)
	sb t1, 327(s1)
	lbu t1, 312(s1)
	sb t1, 328(s1)
	lbu t1, 313(s1)
	sb t1, 329(s1)
	lbu t1, 314(s1)
	sb t1, 330(s1)
	lbu t1, 315(s1)
	sb t1, 331(s1)
	lbu t1, 316(s1)
	sb t1, 332(s1)
	lbu t1, 317(s1)
	sb t1, 333(s1)
	lbu t1, 318(s1)
	sb t1, 334(s1)
	lbu t1, 319(s1)
	sb t1, 335(s1)
	addi a0, s1, 64
	addi a1, s1, 304
	addi a2, s3, -1
	addi a3, s1, 320
	addi a4, s1, 352
	call {vg_pbkdf2_hmac_md5_iterate}
	addi t1, s5, -16
	srli t1, t1, 63
	addi t2, s5, 0
	bnez t1, 23f
	addi t2, zero, 16
	j 24f
23:
24:
	addi t3, zero, 0
25:
	add t4, s1, t3
	lbu t1, 320(t4)
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
	addi sp, sp, 352
	addi sp, sp, 224
	ret
	.option pop
