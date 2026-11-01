// The functions of `src/pbkdf2_sha1.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_pbkdf2_hmac_sha1:
	.option push
	.option arch, +m, +c
	addi sp, sp, -240
	addi sp, sp, -368
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
	addi a1, s1, 148
	call {vg_hmac_sha1_init}
	addi s7, zero, 1
	beqz s5, 20f
22:
	lbu t1, 64(s1)
	sb t1, 232(s1)
	lbu t1, 65(s1)
	sb t1, 233(s1)
	lbu t1, 66(s1)
	sb t1, 234(s1)
	lbu t1, 67(s1)
	sb t1, 235(s1)
	lbu t1, 68(s1)
	sb t1, 236(s1)
	lbu t1, 69(s1)
	sb t1, 237(s1)
	lbu t1, 70(s1)
	sb t1, 238(s1)
	lbu t1, 71(s1)
	sb t1, 239(s1)
	lbu t1, 72(s1)
	sb t1, 240(s1)
	lbu t1, 73(s1)
	sb t1, 241(s1)
	lbu t1, 74(s1)
	sb t1, 242(s1)
	lbu t1, 75(s1)
	sb t1, 243(s1)
	lbu t1, 76(s1)
	sb t1, 244(s1)
	lbu t1, 77(s1)
	sb t1, 245(s1)
	lbu t1, 78(s1)
	sb t1, 246(s1)
	lbu t1, 79(s1)
	sb t1, 247(s1)
	lbu t1, 80(s1)
	sb t1, 248(s1)
	lbu t1, 81(s1)
	sb t1, 249(s1)
	lbu t1, 82(s1)
	sb t1, 250(s1)
	lbu t1, 83(s1)
	sb t1, 251(s1)
	lbu t1, 84(s1)
	sb t1, 252(s1)
	lbu t1, 85(s1)
	sb t1, 253(s1)
	lbu t1, 86(s1)
	sb t1, 254(s1)
	lbu t1, 87(s1)
	sb t1, 255(s1)
	lbu t1, 88(s1)
	sb t1, 256(s1)
	lbu t1, 89(s1)
	sb t1, 257(s1)
	lbu t1, 90(s1)
	sb t1, 258(s1)
	lbu t1, 91(s1)
	sb t1, 259(s1)
	lbu t1, 92(s1)
	sb t1, 260(s1)
	lbu t1, 93(s1)
	sb t1, 261(s1)
	lbu t1, 94(s1)
	sb t1, 262(s1)
	lbu t1, 95(s1)
	sb t1, 263(s1)
	lbu t1, 96(s1)
	sb t1, 264(s1)
	lbu t1, 97(s1)
	sb t1, 265(s1)
	lbu t1, 98(s1)
	sb t1, 266(s1)
	lbu t1, 99(s1)
	sb t1, 267(s1)
	lbu t1, 100(s1)
	sb t1, 268(s1)
	lbu t1, 101(s1)
	sb t1, 269(s1)
	lbu t1, 102(s1)
	sb t1, 270(s1)
	lbu t1, 103(s1)
	sb t1, 271(s1)
	lbu t1, 104(s1)
	sb t1, 272(s1)
	lbu t1, 105(s1)
	sb t1, 273(s1)
	lbu t1, 106(s1)
	sb t1, 274(s1)
	lbu t1, 107(s1)
	sb t1, 275(s1)
	lbu t1, 108(s1)
	sb t1, 276(s1)
	lbu t1, 109(s1)
	sb t1, 277(s1)
	lbu t1, 110(s1)
	sb t1, 278(s1)
	lbu t1, 111(s1)
	sb t1, 279(s1)
	lbu t1, 112(s1)
	sb t1, 280(s1)
	lbu t1, 113(s1)
	sb t1, 281(s1)
	lbu t1, 114(s1)
	sb t1, 282(s1)
	lbu t1, 115(s1)
	sb t1, 283(s1)
	lbu t1, 116(s1)
	sb t1, 284(s1)
	lbu t1, 117(s1)
	sb t1, 285(s1)
	lbu t1, 118(s1)
	sb t1, 286(s1)
	lbu t1, 119(s1)
	sb t1, 287(s1)
	lbu t1, 120(s1)
	sb t1, 288(s1)
	lbu t1, 121(s1)
	sb t1, 289(s1)
	lbu t1, 122(s1)
	sb t1, 290(s1)
	lbu t1, 123(s1)
	sb t1, 291(s1)
	lbu t1, 124(s1)
	sb t1, 292(s1)
	lbu t1, 125(s1)
	sb t1, 293(s1)
	lbu t1, 126(s1)
	sb t1, 294(s1)
	lbu t1, 127(s1)
	sb t1, 295(s1)
	lbu t1, 128(s1)
	sb t1, 296(s1)
	lbu t1, 129(s1)
	sb t1, 297(s1)
	lbu t1, 130(s1)
	sb t1, 298(s1)
	lbu t1, 131(s1)
	sb t1, 299(s1)
	lbu t1, 132(s1)
	sb t1, 300(s1)
	lbu t1, 133(s1)
	sb t1, 301(s1)
	lbu t1, 134(s1)
	sb t1, 302(s1)
	lbu t1, 135(s1)
	sb t1, 303(s1)
	lbu t1, 136(s1)
	sb t1, 304(s1)
	lbu t1, 137(s1)
	sb t1, 305(s1)
	lbu t1, 138(s1)
	sb t1, 306(s1)
	lbu t1, 139(s1)
	sb t1, 307(s1)
	lbu t1, 140(s1)
	sb t1, 308(s1)
	lbu t1, 141(s1)
	sb t1, 309(s1)
	lbu t1, 142(s1)
	sb t1, 310(s1)
	lbu t1, 143(s1)
	sb t1, 311(s1)
	lbu t1, 144(s1)
	sb t1, 312(s1)
	lbu t1, 145(s1)
	sb t1, 313(s1)
	lbu t1, 146(s1)
	sb t1, 314(s1)
	lbu t1, 147(s1)
	sb t1, 315(s1)
	addi a0, s1, 232
	addi a1, zero, 64
	addi a2, s6, 0
	addi a3, s2, 0
	call {vg_sha1_update}
	srli t1, s7, 24
	sb t1, 356(s1)
	srli t1, s7, 16
	sb t1, 357(s1)
	srli t1, s7, 8
	sb t1, 358(s1)
	sb s7, 359(s1)
	addi a0, s1, 232
	addi a1, s2, 64
	addi a2, s1, 356
	addi a3, zero, 4
	call {vg_sha1_update}
	addi a0, s1, 232
	addi a1, s1, 148
	addi a2, s2, 68
	addi a3, s1, 316
	call {vg_hmac_sha1_finalize}
	lbu t1, 316(s1)
	sb t1, 336(s1)
	lbu t1, 317(s1)
	sb t1, 337(s1)
	lbu t1, 318(s1)
	sb t1, 338(s1)
	lbu t1, 319(s1)
	sb t1, 339(s1)
	lbu t1, 320(s1)
	sb t1, 340(s1)
	lbu t1, 321(s1)
	sb t1, 341(s1)
	lbu t1, 322(s1)
	sb t1, 342(s1)
	lbu t1, 323(s1)
	sb t1, 343(s1)
	lbu t1, 324(s1)
	sb t1, 344(s1)
	lbu t1, 325(s1)
	sb t1, 345(s1)
	lbu t1, 326(s1)
	sb t1, 346(s1)
	lbu t1, 327(s1)
	sb t1, 347(s1)
	lbu t1, 328(s1)
	sb t1, 348(s1)
	lbu t1, 329(s1)
	sb t1, 349(s1)
	lbu t1, 330(s1)
	sb t1, 350(s1)
	lbu t1, 331(s1)
	sb t1, 351(s1)
	lbu t1, 332(s1)
	sb t1, 352(s1)
	lbu t1, 333(s1)
	sb t1, 353(s1)
	lbu t1, 334(s1)
	sb t1, 354(s1)
	lbu t1, 335(s1)
	sb t1, 355(s1)
	addi a0, s1, 64
	addi a1, s1, 316
	addi a2, s3, -1
	addi a3, s1, 336
	addi a4, s1, 368
	call {vg_pbkdf2_hmac_sha1_iterate}
	addi t1, s5, -20
	srli t1, t1, 63
	addi t2, s5, 0
	bnez t1, 23f
	addi t2, zero, 20
	j 24f
23:
24:
	addi t3, zero, 0
25:
	add t4, s1, t3
	lbu t1, 336(t4)
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
	addi sp, sp, 368
	addi sp, sp, 240
	ret
	.option pop
