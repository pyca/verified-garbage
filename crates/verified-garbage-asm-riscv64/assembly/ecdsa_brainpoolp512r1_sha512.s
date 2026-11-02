// The functions of `src/ecdsa_brainpoolp512r1_sha512.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_brainpoolp512r1_sha512_sign:
	.option push
	.option arch, +m, +c
	addi sp, sp, -272
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
	lbu t0, 0(s4)
	slli t0, t0, 8
	lbu t1, 1(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 2(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 3(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 4(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 5(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 6(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 7(s4)
	or t0, t0, t1
	sd t0, 56(s0)
	lbu t0, 8(s4)
	slli t0, t0, 8
	lbu t1, 9(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 10(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 11(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 12(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 13(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 14(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 15(s4)
	or t0, t0, t1
	sd t0, 48(s0)
	lbu t0, 16(s4)
	slli t0, t0, 8
	lbu t1, 17(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 18(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 19(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 20(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 21(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 22(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 23(s4)
	or t0, t0, t1
	sd t0, 40(s0)
	lbu t0, 24(s4)
	slli t0, t0, 8
	lbu t1, 25(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 26(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 27(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 28(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 29(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 30(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 31(s4)
	or t0, t0, t1
	sd t0, 32(s0)
	lbu t0, 32(s4)
	slli t0, t0, 8
	lbu t1, 33(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 34(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 35(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 36(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 37(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 38(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 39(s4)
	or t0, t0, t1
	sd t0, 24(s0)
	lbu t0, 40(s4)
	slli t0, t0, 8
	lbu t1, 41(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 42(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 43(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 44(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 45(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 46(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 47(s4)
	or t0, t0, t1
	sd t0, 16(s0)
	lbu t0, 48(s4)
	slli t0, t0, 8
	lbu t1, 49(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 50(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 51(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 52(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 53(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 54(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 55(s4)
	or t0, t0, t1
	sd t0, 8(s0)
	lbu t0, 56(s4)
	slli t0, t0, 8
	lbu t1, 57(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 58(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 59(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 60(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 61(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 62(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 63(s4)
	or t0, t0, t1
	sd t0, 0(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 64(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 72(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 80(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 88(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 96(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 104(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 112(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 120(s0)
	addi a0, s0, 0
	addi a1, zero, 128
	addi a2, zero, 0
	addi a3, zero, 64
	call {vg_brainpoolp512r1_add_mod_n}
	addi a7, zero, -1
	ld t0, 184(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 208(s1)
	srli t1, t0, 48
	sb t1, 209(s1)
	srli t1, t0, 40
	sb t1, 210(s1)
	srli t1, t0, 32
	sb t1, 211(s1)
	srli t1, t0, 24
	sb t1, 212(s1)
	srli t1, t0, 16
	sb t1, 213(s1)
	srli t1, t0, 8
	sb t1, 214(s1)
	srli t1, t0, 0
	sb t1, 215(s1)
	ld t0, 176(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 216(s1)
	srli t1, t0, 48
	sb t1, 217(s1)
	srli t1, t0, 40
	sb t1, 218(s1)
	srli t1, t0, 32
	sb t1, 219(s1)
	srli t1, t0, 24
	sb t1, 220(s1)
	srli t1, t0, 16
	sb t1, 221(s1)
	srli t1, t0, 8
	sb t1, 222(s1)
	srli t1, t0, 0
	sb t1, 223(s1)
	ld t0, 168(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 224(s1)
	srli t1, t0, 48
	sb t1, 225(s1)
	srli t1, t0, 40
	sb t1, 226(s1)
	srli t1, t0, 32
	sb t1, 227(s1)
	srli t1, t0, 24
	sb t1, 228(s1)
	srli t1, t0, 16
	sb t1, 229(s1)
	srli t1, t0, 8
	sb t1, 230(s1)
	srli t1, t0, 0
	sb t1, 231(s1)
	ld t0, 160(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 232(s1)
	srli t1, t0, 48
	sb t1, 233(s1)
	srli t1, t0, 40
	sb t1, 234(s1)
	srli t1, t0, 32
	sb t1, 235(s1)
	srli t1, t0, 24
	sb t1, 236(s1)
	srli t1, t0, 16
	sb t1, 237(s1)
	srli t1, t0, 8
	sb t1, 238(s1)
	srli t1, t0, 0
	sb t1, 239(s1)
	ld t0, 152(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 240(s1)
	srli t1, t0, 48
	sb t1, 241(s1)
	srli t1, t0, 40
	sb t1, 242(s1)
	srli t1, t0, 32
	sb t1, 243(s1)
	srli t1, t0, 24
	sb t1, 244(s1)
	srli t1, t0, 16
	sb t1, 245(s1)
	srli t1, t0, 8
	sb t1, 246(s1)
	srli t1, t0, 0
	sb t1, 247(s1)
	ld t0, 144(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 248(s1)
	srli t1, t0, 48
	sb t1, 249(s1)
	srli t1, t0, 40
	sb t1, 250(s1)
	srli t1, t0, 32
	sb t1, 251(s1)
	srli t1, t0, 24
	sb t1, 252(s1)
	srli t1, t0, 16
	sb t1, 253(s1)
	srli t1, t0, 8
	sb t1, 254(s1)
	srli t1, t0, 0
	sb t1, 255(s1)
	ld t0, 136(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 256(s1)
	srli t1, t0, 48
	sb t1, 257(s1)
	srli t1, t0, 40
	sb t1, 258(s1)
	srli t1, t0, 32
	sb t1, 259(s1)
	srli t1, t0, 24
	sb t1, 260(s1)
	srli t1, t0, 16
	sb t1, 261(s1)
	srli t1, t0, 8
	sb t1, 262(s1)
	srli t1, t0, 0
	sb t1, 263(s1)
	ld t0, 128(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 264(s1)
	srli t1, t0, 48
	sb t1, 265(s1)
	srli t1, t0, 40
	sb t1, 266(s1)
	srli t1, t0, 32
	sb t1, 267(s1)
	srli t1, t0, 24
	sb t1, 268(s1)
	srli t1, t0, 16
	sb t1, 269(s1)
	srli t1, t0, 8
	sb t1, 270(s1)
	srli t1, t0, 0
	sb t1, 271(s1)
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
	addi a3, zero, 64
	call {vg_sha512_update}
	addi a0, s0, 0
	addi a1, zero, 257
	addi a2, s1, 208
	addi a3, zero, 64
	call {vg_sha512_update}
	addi a0, s0, 0
	addi a1, s0, 192
	addi a2, zero, 321
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
	addi a3, zero, 64
	call {vg_sha512_update}
	addi a0, s0, 0
	addi a1, zero, 257
	addi a2, s1, 208
	addi a3, zero, 64
	call {vg_sha512_update}
	addi a0, s0, 0
	addi a1, s0, 192
	addi a2, zero, 321
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
	addi s5, zero, 128
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
	addi a3, s1, 128
	call {vg_hmac_sha512_finalize}
	addi a0, s2, 0
	addi a1, s3, 0
	addi a2, s4, 0
	addi a3, s1, 128
	addi a4, s0, 0
	call {vg_ecdsa_brainpoolp512r1_sign}
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
	ld ra, 0(s1)
	ld s0, 8(s1)
	ld s2, 24(s1)
	ld s3, 32(s1)
	ld s4, 40(s1)
	ld s5, 48(s1)
	ld s1, 16(s1)
	addi sp, sp, 272
	ret
	.option pop
