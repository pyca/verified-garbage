// The functions of `src/ed448.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed448_public_key:
	.option push
	.option arch, +m, +c
	addi sp, sp, -160
	addi a3, sp, 0
	sd s7, 120(a3)
	sd s8, 128(a3)
	sd s9, 136(a3)
	sd s10, 144(a3)
	sd ra, 152(a3)
	addi s7, a0, 0
	addi s8, a1, 0
	addi s9, a2, 0
	addi s10, a3, 0
	addi t0, zero, 0
	sd t0, 0(s9)
	sd t0, 8(s9)
	sd t0, 16(s9)
	sd t0, 24(s9)
	sd t0, 32(s9)
	sd t0, 40(s9)
	sd t0, 48(s9)
	sd t0, 56(s9)
	sd t0, 64(s9)
	sd t0, 72(s9)
	sd t0, 80(s9)
	sd t0, 88(s9)
	sd t0, 96(s9)
	sd t0, 104(s9)
	sd t0, 112(s9)
	sd t0, 120(s9)
	sd t0, 128(s9)
	sd t0, 136(s9)
	sd t0, 144(s9)
	sd t0, 152(s9)
	sd t0, 160(s9)
	sd t0, 168(s9)
	sd t0, 176(s9)
	sd t0, 184(s9)
	sd t0, 192(s9)
	addi a3, s8, 0
	addi a2, zero, 0
	addi a0, s9, 0
	addi a1, zero, 136
	addi a4, zero, 57
	call {vg_keccak_absorb}
	addi a2, a0, 0
	addi a0, s9, 0
	addi a1, zero, 136
	addi a3, zero, 31
	call {vg_keccak_pad}
	addi a0, s9, 0
	addi a1, zero, 136
	addi a2, zero, 0
	addi a3, s10, 0
	addi a4, zero, 114
	call {vg_keccak_squeeze}
	lbu a5, 0(s10)
	srli a5, a5, 2
	slli a5, a5, 2
	sb a5, 0(s10)
	lbu a5, 55(s10)
	ori a5, a5, 128
	sb a5, 55(s10)
	addi a5, zero, 0
	sb a5, 56(s10)
	addi a0, s7, 0
	addi a1, s10, 0
	addi a2, s9, 0
	call {vg_ed448_scalar_base}
	ld ra, 152(s10)
	ld s7, 120(s10)
	ld s8, 128(s10)
	ld s9, 136(s10)
	ld s10, 144(s10)
	addi t5, sp, 0
	addi t6, zero, 0
	sd t6, 0(t5)
	sd t6, 8(t5)
	sd t6, 16(t5)
	sd t6, 24(t5)
	sd t6, 32(t5)
	sd t6, 40(t5)
	sd t6, 48(t5)
	sd t6, 56(t5)
	sd t6, 64(t5)
	sd t6, 72(t5)
	sd t6, 80(t5)
	sd t6, 88(t5)
	sd t6, 96(t5)
	sd t6, 104(t5)
	sd t6, 112(t5)
	addi sp, sp, 160
	ret
	.option pop

vg_ed448_sign_cached:
	.option push
	.option arch, +m, +c
	addi sp, sp, -528
	addi t0, sp, 0
	addi t1, t0, 8
	sd t1, 0(t0)
	addi t0, sp, 0
	ld t0, 0(t0)
	sd s0, 448(t0)
	sd s1, 456(t0)
	sd s2, 464(t0)
	sd s7, 472(t0)
	sd s8, 480(t0)
	sd s9, 488(t0)
	sd s10, 496(t0)
	sd s11, 504(t0)
	sd ra, 512(t0)
	addi s0, a0, 0
	addi s1, a7, 0
	addi s2, a1, 0
	addi s7, a3, 0
	addi s8, a4, 0
	addi s9, a5, 0
	addi s10, a6, 0
	addi s11, t0, 0
	lbu a5, 0(a2)
	sb a5, 384(s11)
	lbu a5, 1(a2)
	sb a5, 385(s11)
	lbu a5, 2(a2)
	sb a5, 386(s11)
	lbu a5, 3(a2)
	sb a5, 387(s11)
	lbu a5, 4(a2)
	sb a5, 388(s11)
	lbu a5, 5(a2)
	sb a5, 389(s11)
	lbu a5, 6(a2)
	sb a5, 390(s11)
	lbu a5, 7(a2)
	sb a5, 391(s11)
	lbu a5, 8(a2)
	sb a5, 392(s11)
	lbu a5, 9(a2)
	sb a5, 393(s11)
	lbu a5, 10(a2)
	sb a5, 394(s11)
	lbu a5, 11(a2)
	sb a5, 395(s11)
	lbu a5, 12(a2)
	sb a5, 396(s11)
	lbu a5, 13(a2)
	sb a5, 397(s11)
	lbu a5, 14(a2)
	sb a5, 398(s11)
	lbu a5, 15(a2)
	sb a5, 399(s11)
	lbu a5, 16(a2)
	sb a5, 400(s11)
	lbu a5, 17(a2)
	sb a5, 401(s11)
	lbu a5, 18(a2)
	sb a5, 402(s11)
	lbu a5, 19(a2)
	sb a5, 403(s11)
	lbu a5, 20(a2)
	sb a5, 404(s11)
	lbu a5, 21(a2)
	sb a5, 405(s11)
	lbu a5, 22(a2)
	sb a5, 406(s11)
	lbu a5, 23(a2)
	sb a5, 407(s11)
	lbu a5, 24(a2)
	sb a5, 408(s11)
	lbu a5, 25(a2)
	sb a5, 409(s11)
	lbu a5, 26(a2)
	sb a5, 410(s11)
	lbu a5, 27(a2)
	sb a5, 411(s11)
	lbu a5, 28(a2)
	sb a5, 412(s11)
	lbu a5, 29(a2)
	sb a5, 413(s11)
	lbu a5, 30(a2)
	sb a5, 414(s11)
	lbu a5, 31(a2)
	sb a5, 415(s11)
	lbu a5, 32(a2)
	sb a5, 416(s11)
	lbu a5, 33(a2)
	sb a5, 417(s11)
	lbu a5, 34(a2)
	sb a5, 418(s11)
	lbu a5, 35(a2)
	sb a5, 419(s11)
	lbu a5, 36(a2)
	sb a5, 420(s11)
	lbu a5, 37(a2)
	sb a5, 421(s11)
	lbu a5, 38(a2)
	sb a5, 422(s11)
	lbu a5, 39(a2)
	sb a5, 423(s11)
	lbu a5, 40(a2)
	sb a5, 424(s11)
	lbu a5, 41(a2)
	sb a5, 425(s11)
	lbu a5, 42(a2)
	sb a5, 426(s11)
	lbu a5, 43(a2)
	sb a5, 427(s11)
	lbu a5, 44(a2)
	sb a5, 428(s11)
	lbu a5, 45(a2)
	sb a5, 429(s11)
	lbu a5, 46(a2)
	sb a5, 430(s11)
	lbu a5, 47(a2)
	sb a5, 431(s11)
	lbu a5, 48(a2)
	sb a5, 432(s11)
	lbu a5, 49(a2)
	sb a5, 433(s11)
	lbu a5, 50(a2)
	sb a5, 434(s11)
	lbu a5, 51(a2)
	sb a5, 435(s11)
	lbu a5, 52(a2)
	sb a5, 436(s11)
	lbu a5, 53(a2)
	sb a5, 437(s11)
	lbu a5, 54(a2)
	sb a5, 438(s11)
	lbu a5, 55(a2)
	sb a5, 439(s11)
	lbu a5, 56(a2)
	sb a5, 440(s11)
	lui a5, 230211
	addiw a5, a5, 1124
	slli a5, a5, 32
	lui a6, 284279
	addiw a6, a6, -1709
	or a5, a5, a6
	sd a5, 0(s11)
	addi a5, zero, 0
	sb a5, 8(s11)
	sb s8, 9(s11)
	addi t0, zero, 0
	sd t0, 0(s1)
	sd t0, 8(s1)
	sd t0, 16(s1)
	sd t0, 24(s1)
	sd t0, 32(s1)
	sd t0, 40(s1)
	sd t0, 48(s1)
	sd t0, 56(s1)
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
	addi a3, s2, 0
	addi a2, zero, 0
	addi a0, s1, 0
	addi a1, zero, 136
	addi a4, zero, 57
	call {vg_keccak_absorb}
	addi a2, a0, 0
	addi a0, s1, 0
	addi a1, zero, 136
	addi a3, zero, 31
	call {vg_keccak_pad}
	addi a0, s1, 0
	addi a1, zero, 136
	addi a2, zero, 0
	addi a3, s11, 136
	addi a4, zero, 114
	call {vg_keccak_squeeze}
	lbu a5, 136(s11)
	srli a5, a5, 2
	slli a5, a5, 2
	sb a5, 136(s11)
	lbu a5, 191(s11)
	ori a5, a5, 128
	sb a5, 191(s11)
	addi a5, zero, 0
	sb a5, 192(s11)
	addi t0, zero, 0
	sd t0, 0(s1)
	sd t0, 8(s1)
	sd t0, 16(s1)
	sd t0, 24(s1)
	sd t0, 32(s1)
	sd t0, 40(s1)
	sd t0, 48(s1)
	sd t0, 56(s1)
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
	addi a3, s11, 0
	addi a2, zero, 0
	addi a0, s1, 0
	addi a1, zero, 136
	addi a4, zero, 10
	call {vg_keccak_absorb}
	addi a3, s7, 0
	addi a2, a0, 0
	addi a0, s1, 0
	addi a1, zero, 136
	addi a4, s8, 0
	call {vg_keccak_absorb}
	addi a3, s11, 193
	addi a2, a0, 0
	addi a0, s1, 0
	addi a1, zero, 136
	addi a4, zero, 57
	call {vg_keccak_absorb}
	addi a3, s9, 0
	addi a2, a0, 0
	addi a0, s1, 0
	addi a1, zero, 136
	addi a4, s10, 0
	call {vg_keccak_absorb}
	addi a2, a0, 0
	addi a0, s1, 0
	addi a1, zero, 136
	addi a3, zero, 31
	call {vg_keccak_pad}
	addi a0, s1, 0
	addi a1, zero, 136
	addi a2, zero, 0
	addi a3, s11, 16
	addi a4, zero, 114
	call {vg_keccak_squeeze}
	addi a0, s11, 256
	addi a1, s11, 16
	addi a2, s1, 0
	call {vg_ed448_scalar_reduce}
	addi a0, s0, 0
	addi a1, s11, 256
	addi a2, s1, 0
	call {vg_ed448_scalar_base}
	addi t0, zero, 0
	sd t0, 0(s1)
	sd t0, 8(s1)
	sd t0, 16(s1)
	sd t0, 24(s1)
	sd t0, 32(s1)
	sd t0, 40(s1)
	sd t0, 48(s1)
	sd t0, 56(s1)
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
	addi a3, s11, 0
	addi a2, zero, 0
	addi a0, s1, 0
	addi a1, zero, 136
	addi a4, zero, 10
	call {vg_keccak_absorb}
	addi a3, s7, 0
	addi a2, a0, 0
	addi a0, s1, 0
	addi a1, zero, 136
	addi a4, s8, 0
	call {vg_keccak_absorb}
	addi a3, s0, 0
	addi a2, a0, 0
	addi a0, s1, 0
	addi a1, zero, 136
	addi a4, zero, 57
	call {vg_keccak_absorb}
	addi a3, s11, 384
	addi a2, a0, 0
	addi a0, s1, 0
	addi a1, zero, 136
	addi a4, zero, 57
	call {vg_keccak_absorb}
	addi a3, s9, 0
	addi a2, a0, 0
	addi a0, s1, 0
	addi a1, zero, 136
	addi a4, s10, 0
	call {vg_keccak_absorb}
	addi a2, a0, 0
	addi a0, s1, 0
	addi a1, zero, 136
	addi a3, zero, 31
	call {vg_keccak_pad}
	addi a0, s1, 0
	addi a1, zero, 136
	addi a2, zero, 0
	addi a3, s11, 16
	addi a4, zero, 114
	call {vg_keccak_squeeze}
	addi a0, s11, 320
	addi a1, s11, 16
	addi a2, s1, 0
	call {vg_ed448_scalar_reduce}
	addi a0, s0, 57
	addi a1, s11, 256
	addi a2, s11, 320
	addi a3, s11, 136
	addi a4, s1, 0
	call {vg_ed448_scalar_mul_add}
	addi a5, zero, 0
	sd a5, 16(s11)
	sd a5, 24(s11)
	sd a5, 32(s11)
	sd a5, 40(s11)
	sd a5, 48(s11)
	sd a5, 56(s11)
	sd a5, 64(s11)
	sd a5, 72(s11)
	sd a5, 80(s11)
	sd a5, 88(s11)
	sd a5, 96(s11)
	sd a5, 104(s11)
	sd a5, 112(s11)
	sd a5, 120(s11)
	sd a5, 128(s11)
	sd a5, 136(s11)
	sd a5, 144(s11)
	sd a5, 152(s11)
	sd a5, 160(s11)
	sd a5, 168(s11)
	sd a5, 176(s11)
	sd a5, 184(s11)
	sd a5, 192(s11)
	sd a5, 200(s11)
	sd a5, 208(s11)
	sd a5, 216(s11)
	sd a5, 224(s11)
	sd a5, 232(s11)
	sd a5, 240(s11)
	sd a5, 248(s11)
	sd a5, 256(s11)
	sd a5, 264(s11)
	sd a5, 272(s11)
	sd a5, 280(s11)
	sd a5, 288(s11)
	sd a5, 296(s11)
	sd a5, 304(s11)
	sd a5, 312(s11)
	sd a5, 320(s11)
	sd a5, 328(s11)
	sd a5, 336(s11)
	sd a5, 344(s11)
	sd a5, 352(s11)
	sd a5, 360(s11)
	sd a5, 368(s11)
	sd a5, 376(s11)
	ld ra, 512(s11)
	ld s0, 448(s11)
	ld s1, 456(s11)
	ld s2, 464(s11)
	ld s7, 472(s11)
	ld s8, 480(s11)
	ld s9, 488(s11)
	ld s10, 496(s11)
	ld s11, 504(s11)
	addi sp, sp, 528
	ret
	.option pop

vg_ed448_verify:
	.option push
	.option arch, +m, +c
	addi sp, sp, -448
	addi a7, sp, 0
	srli t0, a2, 8
	beqz t0, 20f
	addi a0, zero, 0
	j 21f
20:
	sd s1, 384(a7)
	sd s7, 392(a7)
	sd s8, 400(a7)
	sd s9, 408(a7)
	sd s10, 416(a7)
	sd s11, 424(a7)
	sd ra, 432(a7)
	addi s1, a6, 0
	addi s7, a1, 0
	addi s8, a2, 0
	addi s9, a3, 0
	addi s10, a4, 0
	addi s11, a7, 0
	addi t1, a5, 0
	lbu a5, 0(t1)
	sb a5, 200(s11)
	lbu a5, 1(t1)
	sb a5, 201(s11)
	lbu a5, 2(t1)
	sb a5, 202(s11)
	lbu a5, 3(t1)
	sb a5, 203(s11)
	lbu a5, 4(t1)
	sb a5, 204(s11)
	lbu a5, 5(t1)
	sb a5, 205(s11)
	lbu a5, 6(t1)
	sb a5, 206(s11)
	lbu a5, 7(t1)
	sb a5, 207(s11)
	lbu a5, 8(t1)
	sb a5, 208(s11)
	lbu a5, 9(t1)
	sb a5, 209(s11)
	lbu a5, 10(t1)
	sb a5, 210(s11)
	lbu a5, 11(t1)
	sb a5, 211(s11)
	lbu a5, 12(t1)
	sb a5, 212(s11)
	lbu a5, 13(t1)
	sb a5, 213(s11)
	lbu a5, 14(t1)
	sb a5, 214(s11)
	lbu a5, 15(t1)
	sb a5, 215(s11)
	lbu a5, 16(t1)
	sb a5, 216(s11)
	lbu a5, 17(t1)
	sb a5, 217(s11)
	lbu a5, 18(t1)
	sb a5, 218(s11)
	lbu a5, 19(t1)
	sb a5, 219(s11)
	lbu a5, 20(t1)
	sb a5, 220(s11)
	lbu a5, 21(t1)
	sb a5, 221(s11)
	lbu a5, 22(t1)
	sb a5, 222(s11)
	lbu a5, 23(t1)
	sb a5, 223(s11)
	lbu a5, 24(t1)
	sb a5, 224(s11)
	lbu a5, 25(t1)
	sb a5, 225(s11)
	lbu a5, 26(t1)
	sb a5, 226(s11)
	lbu a5, 27(t1)
	sb a5, 227(s11)
	lbu a5, 28(t1)
	sb a5, 228(s11)
	lbu a5, 29(t1)
	sb a5, 229(s11)
	lbu a5, 30(t1)
	sb a5, 230(s11)
	lbu a5, 31(t1)
	sb a5, 231(s11)
	lbu a5, 32(t1)
	sb a5, 232(s11)
	lbu a5, 33(t1)
	sb a5, 233(s11)
	lbu a5, 34(t1)
	sb a5, 234(s11)
	lbu a5, 35(t1)
	sb a5, 235(s11)
	lbu a5, 36(t1)
	sb a5, 236(s11)
	lbu a5, 37(t1)
	sb a5, 237(s11)
	lbu a5, 38(t1)
	sb a5, 238(s11)
	lbu a5, 39(t1)
	sb a5, 239(s11)
	lbu a5, 40(t1)
	sb a5, 240(s11)
	lbu a5, 41(t1)
	sb a5, 241(s11)
	lbu a5, 42(t1)
	sb a5, 242(s11)
	lbu a5, 43(t1)
	sb a5, 243(s11)
	lbu a5, 44(t1)
	sb a5, 244(s11)
	lbu a5, 45(t1)
	sb a5, 245(s11)
	lbu a5, 46(t1)
	sb a5, 246(s11)
	lbu a5, 47(t1)
	sb a5, 247(s11)
	lbu a5, 48(t1)
	sb a5, 248(s11)
	lbu a5, 49(t1)
	sb a5, 249(s11)
	lbu a5, 50(t1)
	sb a5, 250(s11)
	lbu a5, 51(t1)
	sb a5, 251(s11)
	lbu a5, 52(t1)
	sb a5, 252(s11)
	lbu a5, 53(t1)
	sb a5, 253(s11)
	lbu a5, 54(t1)
	sb a5, 254(s11)
	lbu a5, 55(t1)
	sb a5, 255(s11)
	lbu a5, 56(t1)
	sb a5, 256(s11)
	lbu a5, 57(t1)
	sb a5, 257(s11)
	lbu a5, 58(t1)
	sb a5, 258(s11)
	lbu a5, 59(t1)
	sb a5, 259(s11)
	lbu a5, 60(t1)
	sb a5, 260(s11)
	lbu a5, 61(t1)
	sb a5, 261(s11)
	lbu a5, 62(t1)
	sb a5, 262(s11)
	lbu a5, 63(t1)
	sb a5, 263(s11)
	lbu a5, 64(t1)
	sb a5, 264(s11)
	lbu a5, 65(t1)
	sb a5, 265(s11)
	lbu a5, 66(t1)
	sb a5, 266(s11)
	lbu a5, 67(t1)
	sb a5, 267(s11)
	lbu a5, 68(t1)
	sb a5, 268(s11)
	lbu a5, 69(t1)
	sb a5, 269(s11)
	lbu a5, 70(t1)
	sb a5, 270(s11)
	lbu a5, 71(t1)
	sb a5, 271(s11)
	lbu a5, 72(t1)
	sb a5, 272(s11)
	lbu a5, 73(t1)
	sb a5, 273(s11)
	lbu a5, 74(t1)
	sb a5, 274(s11)
	lbu a5, 75(t1)
	sb a5, 275(s11)
	lbu a5, 76(t1)
	sb a5, 276(s11)
	lbu a5, 77(t1)
	sb a5, 277(s11)
	lbu a5, 78(t1)
	sb a5, 278(s11)
	lbu a5, 79(t1)
	sb a5, 279(s11)
	lbu a5, 80(t1)
	sb a5, 280(s11)
	lbu a5, 81(t1)
	sb a5, 281(s11)
	lbu a5, 82(t1)
	sb a5, 282(s11)
	lbu a5, 83(t1)
	sb a5, 283(s11)
	lbu a5, 84(t1)
	sb a5, 284(s11)
	lbu a5, 85(t1)
	sb a5, 285(s11)
	lbu a5, 86(t1)
	sb a5, 286(s11)
	lbu a5, 87(t1)
	sb a5, 287(s11)
	lbu a5, 88(t1)
	sb a5, 288(s11)
	lbu a5, 89(t1)
	sb a5, 289(s11)
	lbu a5, 90(t1)
	sb a5, 290(s11)
	lbu a5, 91(t1)
	sb a5, 291(s11)
	lbu a5, 92(t1)
	sb a5, 292(s11)
	lbu a5, 93(t1)
	sb a5, 293(s11)
	lbu a5, 94(t1)
	sb a5, 294(s11)
	lbu a5, 95(t1)
	sb a5, 295(s11)
	lbu a5, 96(t1)
	sb a5, 296(s11)
	lbu a5, 97(t1)
	sb a5, 297(s11)
	lbu a5, 98(t1)
	sb a5, 298(s11)
	lbu a5, 99(t1)
	sb a5, 299(s11)
	lbu a5, 100(t1)
	sb a5, 300(s11)
	lbu a5, 101(t1)
	sb a5, 301(s11)
	lbu a5, 102(t1)
	sb a5, 302(s11)
	lbu a5, 103(t1)
	sb a5, 303(s11)
	lbu a5, 104(t1)
	sb a5, 304(s11)
	lbu a5, 105(t1)
	sb a5, 305(s11)
	lbu a5, 106(t1)
	sb a5, 306(s11)
	lbu a5, 107(t1)
	sb a5, 307(s11)
	lbu a5, 108(t1)
	sb a5, 308(s11)
	lbu a5, 109(t1)
	sb a5, 309(s11)
	lbu a5, 110(t1)
	sb a5, 310(s11)
	lbu a5, 111(t1)
	sb a5, 311(s11)
	lbu a5, 112(t1)
	sb a5, 312(s11)
	lbu a5, 113(t1)
	sb a5, 313(s11)
	lbu a5, 0(a0)
	sb a5, 320(s11)
	lbu a5, 1(a0)
	sb a5, 321(s11)
	lbu a5, 2(a0)
	sb a5, 322(s11)
	lbu a5, 3(a0)
	sb a5, 323(s11)
	lbu a5, 4(a0)
	sb a5, 324(s11)
	lbu a5, 5(a0)
	sb a5, 325(s11)
	lbu a5, 6(a0)
	sb a5, 326(s11)
	lbu a5, 7(a0)
	sb a5, 327(s11)
	lbu a5, 8(a0)
	sb a5, 328(s11)
	lbu a5, 9(a0)
	sb a5, 329(s11)
	lbu a5, 10(a0)
	sb a5, 330(s11)
	lbu a5, 11(a0)
	sb a5, 331(s11)
	lbu a5, 12(a0)
	sb a5, 332(s11)
	lbu a5, 13(a0)
	sb a5, 333(s11)
	lbu a5, 14(a0)
	sb a5, 334(s11)
	lbu a5, 15(a0)
	sb a5, 335(s11)
	lbu a5, 16(a0)
	sb a5, 336(s11)
	lbu a5, 17(a0)
	sb a5, 337(s11)
	lbu a5, 18(a0)
	sb a5, 338(s11)
	lbu a5, 19(a0)
	sb a5, 339(s11)
	lbu a5, 20(a0)
	sb a5, 340(s11)
	lbu a5, 21(a0)
	sb a5, 341(s11)
	lbu a5, 22(a0)
	sb a5, 342(s11)
	lbu a5, 23(a0)
	sb a5, 343(s11)
	lbu a5, 24(a0)
	sb a5, 344(s11)
	lbu a5, 25(a0)
	sb a5, 345(s11)
	lbu a5, 26(a0)
	sb a5, 346(s11)
	lbu a5, 27(a0)
	sb a5, 347(s11)
	lbu a5, 28(a0)
	sb a5, 348(s11)
	lbu a5, 29(a0)
	sb a5, 349(s11)
	lbu a5, 30(a0)
	sb a5, 350(s11)
	lbu a5, 31(a0)
	sb a5, 351(s11)
	lbu a5, 32(a0)
	sb a5, 352(s11)
	lbu a5, 33(a0)
	sb a5, 353(s11)
	lbu a5, 34(a0)
	sb a5, 354(s11)
	lbu a5, 35(a0)
	sb a5, 355(s11)
	lbu a5, 36(a0)
	sb a5, 356(s11)
	lbu a5, 37(a0)
	sb a5, 357(s11)
	lbu a5, 38(a0)
	sb a5, 358(s11)
	lbu a5, 39(a0)
	sb a5, 359(s11)
	lbu a5, 40(a0)
	sb a5, 360(s11)
	lbu a5, 41(a0)
	sb a5, 361(s11)
	lbu a5, 42(a0)
	sb a5, 362(s11)
	lbu a5, 43(a0)
	sb a5, 363(s11)
	lbu a5, 44(a0)
	sb a5, 364(s11)
	lbu a5, 45(a0)
	sb a5, 365(s11)
	lbu a5, 46(a0)
	sb a5, 366(s11)
	lbu a5, 47(a0)
	sb a5, 367(s11)
	lbu a5, 48(a0)
	sb a5, 368(s11)
	lbu a5, 49(a0)
	sb a5, 369(s11)
	lbu a5, 50(a0)
	sb a5, 370(s11)
	lbu a5, 51(a0)
	sb a5, 371(s11)
	lbu a5, 52(a0)
	sb a5, 372(s11)
	lbu a5, 53(a0)
	sb a5, 373(s11)
	lbu a5, 54(a0)
	sb a5, 374(s11)
	lbu a5, 55(a0)
	sb a5, 375(s11)
	lbu a5, 56(a0)
	sb a5, 376(s11)
	lui a5, 230211
	addiw a5, a5, 1124
	slli a5, a5, 32
	lui a6, 284279
	addiw a6, a6, -1709
	or a5, a5, a6
	sd a5, 0(s11)
	addi a5, zero, 0
	sb a5, 8(s11)
	sb s8, 9(s11)
	addi t0, zero, 0
	sd t0, 0(s1)
	sd t0, 8(s1)
	sd t0, 16(s1)
	sd t0, 24(s1)
	sd t0, 32(s1)
	sd t0, 40(s1)
	sd t0, 48(s1)
	sd t0, 56(s1)
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
	addi a3, s11, 0
	addi a2, zero, 0
	addi a0, s1, 0
	addi a1, zero, 136
	addi a4, zero, 10
	call {vg_keccak_absorb}
	addi a3, s7, 0
	addi a2, a0, 0
	addi a0, s1, 0
	addi a1, zero, 136
	addi a4, s8, 0
	call {vg_keccak_absorb}
	addi a3, s11, 200
	addi a2, a0, 0
	addi a0, s1, 0
	addi a1, zero, 136
	addi a4, zero, 57
	call {vg_keccak_absorb}
	addi a3, s11, 320
	addi a2, a0, 0
	addi a0, s1, 0
	addi a1, zero, 136
	addi a4, zero, 57
	call {vg_keccak_absorb}
	addi a3, s9, 0
	addi a2, a0, 0
	addi a0, s1, 0
	addi a1, zero, 136
	addi a4, s10, 0
	call {vg_keccak_absorb}
	addi a2, a0, 0
	addi a0, s1, 0
	addi a1, zero, 136
	addi a3, zero, 31
	call {vg_keccak_pad}
	addi a0, s1, 0
	addi a1, zero, 136
	addi a2, zero, 0
	addi a3, s11, 16
	addi a4, zero, 114
	call {vg_keccak_squeeze}
	addi a0, s11, 136
	addi a1, s11, 16
	addi a2, s1, 0
	call {vg_ed448_scalar_reduce}
	addi a0, s11, 320
	addi a1, s11, 200
	addi a2, s11, 136
	addi a3, s1, 0
	call {vg_ed448_verify_equation}
	ld ra, 432(s11)
	ld s1, 384(s11)
	ld s7, 392(s11)
	ld s8, 400(s11)
	ld s9, 408(s11)
	ld s10, 416(s11)
	ld s11, 424(s11)
21:
	addi sp, sp, 448
	ret
	.option pop
