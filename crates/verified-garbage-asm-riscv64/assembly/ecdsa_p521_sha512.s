// The functions of `src/ecdsa_p521_sha512.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_p521_sha512_sign:
	.option push
	.option arch, +m, +c
	addi sp, sp, -352
	addi t0, sp, 0
	sd ra, 0(t0)
	sd s0, 8(t0)
	sd s1, 16(t0)
	sd s2, 24(t0)
	sd s3, 32(t0)
	sd s4, 40(t0)
	sd s5, 48(t0)
	addi s1, t0, 0
	addi s2, a0, 0
	addi s3, a1, 0
	addi s4, a2, 0
	addi s0, a3, 0
	addi t0, zero, 0
	sb t0, 208(s1)
	addi t0, zero, 0
	sb t0, 209(s1)
	lbu t0, 0(s4)
	sb t0, 210(s1)
	lbu t0, 1(s4)
	sb t0, 211(s1)
	lbu t0, 2(s4)
	sb t0, 212(s1)
	lbu t0, 3(s4)
	sb t0, 213(s1)
	lbu t0, 4(s4)
	sb t0, 214(s1)
	lbu t0, 5(s4)
	sb t0, 215(s1)
	lbu t0, 6(s4)
	sb t0, 216(s1)
	lbu t0, 7(s4)
	sb t0, 217(s1)
	lbu t0, 8(s4)
	sb t0, 218(s1)
	lbu t0, 9(s4)
	sb t0, 219(s1)
	lbu t0, 10(s4)
	sb t0, 220(s1)
	lbu t0, 11(s4)
	sb t0, 221(s1)
	lbu t0, 12(s4)
	sb t0, 222(s1)
	lbu t0, 13(s4)
	sb t0, 223(s1)
	lbu t0, 14(s4)
	sb t0, 224(s1)
	lbu t0, 15(s4)
	sb t0, 225(s1)
	lbu t0, 16(s4)
	sb t0, 226(s1)
	lbu t0, 17(s4)
	sb t0, 227(s1)
	lbu t0, 18(s4)
	sb t0, 228(s1)
	lbu t0, 19(s4)
	sb t0, 229(s1)
	lbu t0, 20(s4)
	sb t0, 230(s1)
	lbu t0, 21(s4)
	sb t0, 231(s1)
	lbu t0, 22(s4)
	sb t0, 232(s1)
	lbu t0, 23(s4)
	sb t0, 233(s1)
	lbu t0, 24(s4)
	sb t0, 234(s1)
	lbu t0, 25(s4)
	sb t0, 235(s1)
	lbu t0, 26(s4)
	sb t0, 236(s1)
	lbu t0, 27(s4)
	sb t0, 237(s1)
	lbu t0, 28(s4)
	sb t0, 238(s1)
	lbu t0, 29(s4)
	sb t0, 239(s1)
	lbu t0, 30(s4)
	sb t0, 240(s1)
	lbu t0, 31(s4)
	sb t0, 241(s1)
	lbu t0, 32(s4)
	sb t0, 242(s1)
	lbu t0, 33(s4)
	sb t0, 243(s1)
	lbu t0, 34(s4)
	sb t0, 244(s1)
	lbu t0, 35(s4)
	sb t0, 245(s1)
	lbu t0, 36(s4)
	sb t0, 246(s1)
	lbu t0, 37(s4)
	sb t0, 247(s1)
	lbu t0, 38(s4)
	sb t0, 248(s1)
	lbu t0, 39(s4)
	sb t0, 249(s1)
	lbu t0, 40(s4)
	sb t0, 250(s1)
	lbu t0, 41(s4)
	sb t0, 251(s1)
	lbu t0, 42(s4)
	sb t0, 252(s1)
	lbu t0, 43(s4)
	sb t0, 253(s1)
	lbu t0, 44(s4)
	sb t0, 254(s1)
	lbu t0, 45(s4)
	sb t0, 255(s1)
	lbu t0, 46(s4)
	sb t0, 256(s1)
	lbu t0, 47(s4)
	sb t0, 257(s1)
	lbu t0, 48(s4)
	sb t0, 258(s1)
	lbu t0, 49(s4)
	sb t0, 259(s1)
	lbu t0, 50(s4)
	sb t0, 260(s1)
	lbu t0, 51(s4)
	sb t0, 261(s1)
	lbu t0, 52(s4)
	sb t0, 262(s1)
	lbu t0, 53(s4)
	sb t0, 263(s1)
	lbu t0, 54(s4)
	sb t0, 264(s1)
	lbu t0, 55(s4)
	sb t0, 265(s1)
	lbu t0, 56(s4)
	sb t0, 266(s1)
	lbu t0, 57(s4)
	sb t0, 267(s1)
	lbu t0, 58(s4)
	sb t0, 268(s1)
	lbu t0, 59(s4)
	sb t0, 269(s1)
	lbu t0, 60(s4)
	sb t0, 270(s1)
	lbu t0, 61(s4)
	sb t0, 271(s1)
	lbu t0, 62(s4)
	sb t0, 272(s1)
	lbu t0, 63(s4)
	sb t0, 273(s1)
	addi t0, zero, 0
	sb t0, 64(s1)
	addi t0, zero, 0
	sb t0, 65(s1)
	addi t0, zero, 0
	sb t0, 66(s1)
	addi t0, zero, 0
	sb t0, 67(s1)
	addi t0, zero, 0
	sb t0, 68(s1)
	addi t0, zero, 0
	sb t0, 69(s1)
	addi t0, zero, 0
	sb t0, 70(s1)
	addi t0, zero, 0
	sb t0, 71(s1)
	addi t0, zero, 0
	sb t0, 72(s1)
	addi t0, zero, 0
	sb t0, 73(s1)
	addi t0, zero, 0
	sb t0, 74(s1)
	addi t0, zero, 0
	sb t0, 75(s1)
	addi t0, zero, 0
	sb t0, 76(s1)
	addi t0, zero, 0
	sb t0, 77(s1)
	addi t0, zero, 0
	sb t0, 78(s1)
	addi t0, zero, 0
	sb t0, 79(s1)
	addi t0, zero, 0
	sb t0, 80(s1)
	addi t0, zero, 0
	sb t0, 81(s1)
	addi t0, zero, 0
	sb t0, 82(s1)
	addi t0, zero, 0
	sb t0, 83(s1)
	addi t0, zero, 0
	sb t0, 84(s1)
	addi t0, zero, 0
	sb t0, 85(s1)
	addi t0, zero, 0
	sb t0, 86(s1)
	addi t0, zero, 0
	sb t0, 87(s1)
	addi t0, zero, 0
	sb t0, 88(s1)
	addi t0, zero, 0
	sb t0, 89(s1)
	addi t0, zero, 0
	sb t0, 90(s1)
	addi t0, zero, 0
	sb t0, 91(s1)
	addi t0, zero, 0
	sb t0, 92(s1)
	addi t0, zero, 0
	sb t0, 93(s1)
	addi t0, zero, 0
	sb t0, 94(s1)
	addi t0, zero, 0
	sb t0, 95(s1)
	addi t0, zero, 0
	sb t0, 96(s1)
	addi t0, zero, 0
	sb t0, 97(s1)
	addi t0, zero, 0
	sb t0, 98(s1)
	addi t0, zero, 0
	sb t0, 99(s1)
	addi t0, zero, 0
	sb t0, 100(s1)
	addi t0, zero, 0
	sb t0, 101(s1)
	addi t0, zero, 0
	sb t0, 102(s1)
	addi t0, zero, 0
	sb t0, 103(s1)
	addi t0, zero, 0
	sb t0, 104(s1)
	addi t0, zero, 0
	sb t0, 105(s1)
	addi t0, zero, 0
	sb t0, 106(s1)
	addi t0, zero, 0
	sb t0, 107(s1)
	addi t0, zero, 0
	sb t0, 108(s1)
	addi t0, zero, 0
	sb t0, 109(s1)
	addi t0, zero, 0
	sb t0, 110(s1)
	addi t0, zero, 0
	sb t0, 111(s1)
	addi t0, zero, 0
	sb t0, 112(s1)
	addi t0, zero, 0
	sb t0, 113(s1)
	addi t0, zero, 0
	sb t0, 114(s1)
	addi t0, zero, 0
	sb t0, 115(s1)
	addi t0, zero, 0
	sb t0, 116(s1)
	addi t0, zero, 0
	sb t0, 117(s1)
	addi t0, zero, 0
	sb t0, 118(s1)
	addi t0, zero, 0
	sb t0, 119(s1)
	addi t0, zero, 0
	sb t0, 120(s1)
	addi t0, zero, 0
	sb t0, 121(s1)
	addi t0, zero, 0
	sb t0, 122(s1)
	addi t0, zero, 0
	sb t0, 123(s1)
	addi t0, zero, 0
	sb t0, 124(s1)
	addi t0, zero, 0
	sb t0, 125(s1)
	addi t0, zero, 0
	sb t0, 126(s1)
	addi t0, zero, 0
	sb t0, 127(s1)
	addi t0, zero, 1
	sb t0, 128(s1)
	addi t0, zero, 1
	sb t0, 129(s1)
	addi t0, zero, 1
	sb t0, 130(s1)
	addi t0, zero, 1
	sb t0, 131(s1)
	addi t0, zero, 1
	sb t0, 132(s1)
	addi t0, zero, 1
	sb t0, 133(s1)
	addi t0, zero, 1
	sb t0, 134(s1)
	addi t0, zero, 1
	sb t0, 135(s1)
	addi t0, zero, 1
	sb t0, 136(s1)
	addi t0, zero, 1
	sb t0, 137(s1)
	addi t0, zero, 1
	sb t0, 138(s1)
	addi t0, zero, 1
	sb t0, 139(s1)
	addi t0, zero, 1
	sb t0, 140(s1)
	addi t0, zero, 1
	sb t0, 141(s1)
	addi t0, zero, 1
	sb t0, 142(s1)
	addi t0, zero, 1
	sb t0, 143(s1)
	addi t0, zero, 1
	sb t0, 144(s1)
	addi t0, zero, 1
	sb t0, 145(s1)
	addi t0, zero, 1
	sb t0, 146(s1)
	addi t0, zero, 1
	sb t0, 147(s1)
	addi t0, zero, 1
	sb t0, 148(s1)
	addi t0, zero, 1
	sb t0, 149(s1)
	addi t0, zero, 1
	sb t0, 150(s1)
	addi t0, zero, 1
	sb t0, 151(s1)
	addi t0, zero, 1
	sb t0, 152(s1)
	addi t0, zero, 1
	sb t0, 153(s1)
	addi t0, zero, 1
	sb t0, 154(s1)
	addi t0, zero, 1
	sb t0, 155(s1)
	addi t0, zero, 1
	sb t0, 156(s1)
	addi t0, zero, 1
	sb t0, 157(s1)
	addi t0, zero, 1
	sb t0, 158(s1)
	addi t0, zero, 1
	sb t0, 159(s1)
	addi t0, zero, 1
	sb t0, 160(s1)
	addi t0, zero, 1
	sb t0, 161(s1)
	addi t0, zero, 1
	sb t0, 162(s1)
	addi t0, zero, 1
	sb t0, 163(s1)
	addi t0, zero, 1
	sb t0, 164(s1)
	addi t0, zero, 1
	sb t0, 165(s1)
	addi t0, zero, 1
	sb t0, 166(s1)
	addi t0, zero, 1
	sb t0, 167(s1)
	addi t0, zero, 1
	sb t0, 168(s1)
	addi t0, zero, 1
	sb t0, 169(s1)
	addi t0, zero, 1
	sb t0, 170(s1)
	addi t0, zero, 1
	sb t0, 171(s1)
	addi t0, zero, 1
	sb t0, 172(s1)
	addi t0, zero, 1
	sb t0, 173(s1)
	addi t0, zero, 1
	sb t0, 174(s1)
	addi t0, zero, 1
	sb t0, 175(s1)
	addi t0, zero, 1
	sb t0, 176(s1)
	addi t0, zero, 1
	sb t0, 177(s1)
	addi t0, zero, 1
	sb t0, 178(s1)
	addi t0, zero, 1
	sb t0, 179(s1)
	addi t0, zero, 1
	sb t0, 180(s1)
	addi t0, zero, 1
	sb t0, 181(s1)
	addi t0, zero, 1
	sb t0, 182(s1)
	addi t0, zero, 1
	sb t0, 183(s1)
	addi t0, zero, 1
	sb t0, 184(s1)
	addi t0, zero, 1
	sb t0, 185(s1)
	addi t0, zero, 1
	sb t0, 186(s1)
	addi t0, zero, 1
	sb t0, 187(s1)
	addi t0, zero, 1
	sb t0, 188(s1)
	addi t0, zero, 1
	sb t0, 189(s1)
	addi t0, zero, 1
	sb t0, 190(s1)
	addi t0, zero, 1
	sb t0, 191(s1)
	addi t0, zero, 0
	sb t0, 192(s1)
	addi a0, s0, 0
	addi a1, s0, 192
	addi a2, s1, 64
	addi a3, zero, 64
	call {vg_hmac_sha512_init}
	addi a0, s0, 0
	addi a1, zero, 128
	addi a2, s1, 128
	addi a3, zero, 65
	call {vg_sha512_update}
	addi a0, s0, 0
	addi a1, zero, 193
	addi a2, s3, 0
	addi a3, zero, 66
	call {vg_sha512_update}
	addi a0, s0, 0
	addi a1, zero, 259
	addi a2, s1, 208
	addi a3, zero, 66
	call {vg_sha512_update}
	addi a0, s0, 0
	addi a1, s0, 192
	addi a2, zero, 325
	addi a3, s1, 64
	call {vg_hmac_sha512_finalize}
	addi a0, s0, 0
	addi a1, s0, 192
	addi a2, s1, 64
	addi a3, zero, 64
	call {vg_hmac_sha512_init}
	addi a0, s0, 0
	addi a1, zero, 128
	addi a2, s1, 128
	addi a3, zero, 64
	call {vg_sha512_update}
	addi a0, s0, 0
	addi a1, s0, 192
	addi a2, zero, 192
	addi a3, s1, 128
	call {vg_hmac_sha512_finalize}
	addi t0, zero, 1
	sb t0, 192(s1)
	addi a0, s0, 0
	addi a1, s0, 192
	addi a2, s1, 64
	addi a3, zero, 64
	call {vg_hmac_sha512_init}
	addi a0, s0, 0
	addi a1, zero, 128
	addi a2, s1, 128
	addi a3, zero, 65
	call {vg_sha512_update}
	addi a0, s0, 0
	addi a1, zero, 193
	addi a2, s3, 0
	addi a3, zero, 66
	call {vg_sha512_update}
	addi a0, s0, 0
	addi a1, zero, 259
	addi a2, s1, 208
	addi a3, zero, 66
	call {vg_sha512_update}
	addi a0, s0, 0
	addi a1, s0, 192
	addi a2, zero, 325
	addi a3, s1, 64
	call {vg_hmac_sha512_finalize}
	addi a0, s0, 0
	addi a1, s0, 192
	addi a2, s1, 64
	addi a3, zero, 64
	call {vg_hmac_sha512_init}
	addi a0, s0, 0
	addi a1, zero, 128
	addi a2, s1, 128
	addi a3, zero, 64
	call {vg_sha512_update}
	addi a0, s0, 0
	addi a1, s0, 192
	addi a2, zero, 192
	addi a3, s1, 128
	call {vg_hmac_sha512_finalize}
	addi s5, zero, 8
20:
	addi a0, s0, 0
	addi a1, s0, 192
	addi a2, s1, 64
	addi a3, zero, 64
	call {vg_hmac_sha512_init}
	addi a0, s0, 0
	addi a1, zero, 128
	addi a2, s1, 128
	addi a3, zero, 64
	call {vg_sha512_update}
	addi a0, s0, 0
	addi a1, s0, 192
	addi a2, zero, 192
	addi a3, s1, 280
	call {vg_hmac_sha512_finalize}
	addi a0, s0, 0
	addi a1, s0, 192
	addi a2, s1, 64
	addi a3, zero, 64
	call {vg_hmac_sha512_init}
	addi a0, s0, 0
	addi a1, zero, 128
	addi a2, s1, 280
	addi a3, zero, 64
	call {vg_sha512_update}
	addi a0, s0, 0
	addi a1, s0, 192
	addi a2, zero, 192
	addi a3, s1, 128
	call {vg_hmac_sha512_finalize}
	lbu t0, 128(s1)
	sb t0, 344(s1)
	lbu t0, 129(s1)
	sb t0, 345(s1)
	addi a0, s2, 0
	addi a1, s3, 0
	addi a2, s4, 0
	addi a3, s1, 280
	addi a4, s0, 0
	call {vg_ecdsa_p521_sign}
	addi s5, s5, -1
	andi t0, a0, 1
	addi t0, t0, -1
	and t6, t0, s5
	bnez t6, 21f
	addi t6, zero, 0
	j 22f
21:
	addi t0, zero, 0
	sb t0, 192(s1)
	addi a0, s0, 0
	addi a1, s0, 192
	addi a2, s1, 64
	addi a3, zero, 64
	call {vg_hmac_sha512_init}
	addi a0, s0, 0
	addi a1, zero, 128
	addi a2, s1, 128
	addi a3, zero, 65
	call {vg_sha512_update}
	addi a0, s0, 0
	addi a1, s0, 192
	addi a2, zero, 193
	addi a3, s1, 64
	call {vg_hmac_sha512_finalize}
	addi a0, s0, 0
	addi a1, s0, 192
	addi a2, s1, 64
	addi a3, zero, 64
	call {vg_hmac_sha512_init}
	addi a0, s0, 0
	addi a1, zero, 128
	addi a2, s1, 128
	addi a3, zero, 64
	call {vg_sha512_update}
	addi a0, s0, 0
	addi a1, s0, 192
	addi a2, zero, 192
	addi a3, s1, 128
	call {vg_hmac_sha512_finalize}
	addi t6, zero, 1
22:
	bnez t6, 20b
	addi t0, zero, 0
	sd t0, 64(s1)
	sd t0, 72(s1)
	sd t0, 80(s1)
	sd t0, 88(s1)
	sd t0, 96(s1)
	sd t0, 104(s1)
	sd t0, 112(s1)
	sd t0, 120(s1)
	sd t0, 128(s1)
	sd t0, 136(s1)
	sd t0, 144(s1)
	sd t0, 152(s1)
	sd t0, 160(s1)
	sd t0, 168(s1)
	sd t0, 176(s1)
	sd t0, 184(s1)
	sd t0, 192(s1)
	sd t0, 200(s1)
	sd t0, 208(s1)
	sd t0, 216(s1)
	sd t0, 224(s1)
	sd t0, 232(s1)
	sd t0, 240(s1)
	sd t0, 248(s1)
	sd t0, 256(s1)
	sd t0, 264(s1)
	sd t0, 272(s1)
	sd t0, 280(s1)
	sd t0, 288(s1)
	sd t0, 296(s1)
	sd t0, 304(s1)
	sd t0, 312(s1)
	sd t0, 320(s1)
	sd t0, 328(s1)
	sd t0, 336(s1)
	sd t0, 344(s1)
	ld ra, 0(s1)
	ld s0, 8(s1)
	ld s2, 24(s1)
	ld s3, 32(s1)
	ld s4, 40(s1)
	ld s5, 48(s1)
	ld s1, 16(s1)
	addi sp, sp, 352
	ret
	.option pop
