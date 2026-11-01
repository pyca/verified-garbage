// The functions of `src/ed25519.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed25519_public_key:
	.option push
	.option arch, +m, +c
	addi sp, sp, -144
	addi a3, sp, 0
	sd s7, 96(a3)
	sd s8, 104(a3)
	sd s9, 112(a3)
	sd s10, 120(a3)
	sd ra, 128(a3)
	addi s7, a0, 0
	addi s8, a1, 0
	addi s9, a2, 0
	addi s10, a3, 0
	addi a0, s9, 0
	call {vg_sha512_init}
	addi a0, s9, 0
	addi a1, zero, 0
	addi a2, s8, 0
	addi a3, zero, 32
	call {vg_sha512_update}
	addi a0, s9, 0
	addi a1, zero, 32
	addi a2, s10, 0
	call {vg_sha512_finalize}
	ld a5, 0(s10)
	srli a5, a5, 3
	slli a5, a5, 3
	sd a5, 64(s10)
	ld a5, 8(s10)
	sd a5, 72(s10)
	ld a5, 16(s10)
	sd a5, 80(s10)
	ld a5, 24(s10)
	slli a5, a5, 2
	srli a5, a5, 2
	addi a6, zero, 1
	slli a6, a6, 62
	or a5, a5, a6
	sd a5, 88(s10)
	addi a0, s7, 0
	addi a1, s10, 64
	addi a2, s9, 0
	call {vg_ed25519_scalar_base}
	ld ra, 128(s10)
	ld s7, 96(s10)
	ld s8, 104(s10)
	ld s9, 112(s10)
	ld s10, 120(s10)
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
	sd t6, 120(t5)
	sd t6, 128(t5)
	addi sp, sp, 144
	ret
	.option pop

vg_ed25519_sign_cached:
	.option push
	.option arch, +m, +c
	addi sp, sp, -288
	addi a6, sp, 0
	sd s1, 224(a6)
	sd s7, 232(a6)
	sd s8, 240(a6)
	sd s9, 248(a6)
	sd s10, 256(a6)
	sd s11, 264(a6)
	sd ra, 272(a6)
	addi s7, a0, 0
	addi s1, a1, 0
	addi s8, a3, 0
	addi s9, a4, 0
	addi s10, a5, 0
	addi s11, a6, 0
	lbu a5, 0(a2)
	sb a5, 192(s11)
	lbu a5, 1(a2)
	sb a5, 193(s11)
	lbu a5, 2(a2)
	sb a5, 194(s11)
	lbu a5, 3(a2)
	sb a5, 195(s11)
	lbu a5, 4(a2)
	sb a5, 196(s11)
	lbu a5, 5(a2)
	sb a5, 197(s11)
	lbu a5, 6(a2)
	sb a5, 198(s11)
	lbu a5, 7(a2)
	sb a5, 199(s11)
	lbu a5, 8(a2)
	sb a5, 200(s11)
	lbu a5, 9(a2)
	sb a5, 201(s11)
	lbu a5, 10(a2)
	sb a5, 202(s11)
	lbu a5, 11(a2)
	sb a5, 203(s11)
	lbu a5, 12(a2)
	sb a5, 204(s11)
	lbu a5, 13(a2)
	sb a5, 205(s11)
	lbu a5, 14(a2)
	sb a5, 206(s11)
	lbu a5, 15(a2)
	sb a5, 207(s11)
	lbu a5, 16(a2)
	sb a5, 208(s11)
	lbu a5, 17(a2)
	sb a5, 209(s11)
	lbu a5, 18(a2)
	sb a5, 210(s11)
	lbu a5, 19(a2)
	sb a5, 211(s11)
	lbu a5, 20(a2)
	sb a5, 212(s11)
	lbu a5, 21(a2)
	sb a5, 213(s11)
	lbu a5, 22(a2)
	sb a5, 214(s11)
	lbu a5, 23(a2)
	sb a5, 215(s11)
	lbu a5, 24(a2)
	sb a5, 216(s11)
	lbu a5, 25(a2)
	sb a5, 217(s11)
	lbu a5, 26(a2)
	sb a5, 218(s11)
	lbu a5, 27(a2)
	sb a5, 219(s11)
	lbu a5, 28(a2)
	sb a5, 220(s11)
	lbu a5, 29(a2)
	sb a5, 221(s11)
	lbu a5, 30(a2)
	sb a5, 222(s11)
	lbu a5, 31(a2)
	sb a5, 223(s11)
	addi a0, s10, 0
	call {vg_sha512_init}
	addi a0, s10, 0
	addi a1, zero, 0
	addi a2, s1, 0
	addi a3, zero, 32
	call {vg_sha512_update}
	addi a0, s10, 0
	addi a1, zero, 32
	addi a2, s11, 128
	call {vg_sha512_finalize}
	ld a5, 128(s11)
	srli a5, a5, 3
	slli a5, a5, 3
	sd a5, 0(s11)
	ld a5, 136(s11)
	sd a5, 8(s11)
	ld a5, 144(s11)
	sd a5, 16(s11)
	ld a5, 152(s11)
	slli a5, a5, 2
	srli a5, a5, 2
	addi a6, zero, 1
	slli a6, a6, 62
	or a5, a5, a6
	sd a5, 24(s11)
	ld a5, 160(s11)
	sd a5, 32(s11)
	ld a5, 168(s11)
	sd a5, 40(s11)
	ld a5, 176(s11)
	sd a5, 48(s11)
	ld a5, 184(s11)
	sd a5, 56(s11)
	addi a0, s10, 0
	call {vg_sha512_init}
	addi a0, s10, 0
	addi a1, zero, 0
	addi a2, s11, 32
	addi a3, zero, 32
	call {vg_sha512_update}
	addi a0, s10, 0
	addi a1, zero, 32
	addi a2, s8, 0
	addi a3, s9, 0
	call {vg_sha512_update}
	addi a0, s10, 0
	addi a1, s9, 32
	addi a2, s11, 128
	call {vg_sha512_finalize}
	addi a0, s11, 64
	addi a1, s11, 128
	addi a2, s10, 0
	call {vg_ed25519_scalar_reduce}
	addi a0, s7, 0
	addi a1, s11, 64
	addi a2, s10, 0
	call {vg_ed25519_scalar_base}
	addi a0, s10, 0
	call {vg_sha512_init}
	addi a0, s10, 0
	addi a1, zero, 0
	addi a2, s7, 0
	addi a3, zero, 32
	call {vg_sha512_update}
	addi a0, s10, 0
	addi a1, zero, 32
	addi a2, s11, 192
	addi a3, zero, 32
	call {vg_sha512_update}
	addi a0, s10, 0
	addi a1, zero, 64
	addi a2, s8, 0
	addi a3, s9, 0
	call {vg_sha512_update}
	addi a0, s10, 0
	addi a1, s9, 64
	addi a2, s11, 128
	call {vg_sha512_finalize}
	addi a0, s11, 96
	addi a1, s11, 128
	addi a2, s10, 0
	call {vg_ed25519_scalar_reduce}
	addi a0, s7, 32
	addi a1, s11, 64
	addi a2, s11, 96
	addi a3, s11, 0
	addi a4, s10, 0
	call {vg_ed25519_scalar_mul_add}
	ld ra, 272(s11)
	ld s1, 224(s11)
	ld s7, 232(s11)
	ld s8, 240(s11)
	ld s9, 248(s11)
	ld s10, 256(s11)
	ld s11, 264(s11)
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
	sd t6, 120(t5)
	sd t6, 128(t5)
	sd t6, 136(t5)
	sd t6, 144(t5)
	sd t6, 152(t5)
	sd t6, 160(t5)
	sd t6, 168(t5)
	sd t6, 176(t5)
	sd t6, 184(t5)
	sd t6, 192(t5)
	sd t6, 200(t5)
	sd t6, 208(t5)
	sd t6, 216(t5)
	addi sp, sp, 288
	ret
	.option pop

vg_ed25519_verify:
	.option push
	.option arch, +m, +c
	addi sp, sp, -272
	addi a5, sp, 0
	sd s7, 224(a5)
	sd s8, 232(a5)
	sd s9, 240(a5)
	sd s10, 248(a5)
	sd ra, 256(a5)
	addi s7, a1, 0
	addi s8, a2, 0
	addi s9, a4, 0
	addi s10, a5, 0
	lbu a5, 0(a3)
	sb a5, 128(s10)
	lbu a5, 1(a3)
	sb a5, 129(s10)
	lbu a5, 2(a3)
	sb a5, 130(s10)
	lbu a5, 3(a3)
	sb a5, 131(s10)
	lbu a5, 4(a3)
	sb a5, 132(s10)
	lbu a5, 5(a3)
	sb a5, 133(s10)
	lbu a5, 6(a3)
	sb a5, 134(s10)
	lbu a5, 7(a3)
	sb a5, 135(s10)
	lbu a5, 8(a3)
	sb a5, 136(s10)
	lbu a5, 9(a3)
	sb a5, 137(s10)
	lbu a5, 10(a3)
	sb a5, 138(s10)
	lbu a5, 11(a3)
	sb a5, 139(s10)
	lbu a5, 12(a3)
	sb a5, 140(s10)
	lbu a5, 13(a3)
	sb a5, 141(s10)
	lbu a5, 14(a3)
	sb a5, 142(s10)
	lbu a5, 15(a3)
	sb a5, 143(s10)
	lbu a5, 16(a3)
	sb a5, 144(s10)
	lbu a5, 17(a3)
	sb a5, 145(s10)
	lbu a5, 18(a3)
	sb a5, 146(s10)
	lbu a5, 19(a3)
	sb a5, 147(s10)
	lbu a5, 20(a3)
	sb a5, 148(s10)
	lbu a5, 21(a3)
	sb a5, 149(s10)
	lbu a5, 22(a3)
	sb a5, 150(s10)
	lbu a5, 23(a3)
	sb a5, 151(s10)
	lbu a5, 24(a3)
	sb a5, 152(s10)
	lbu a5, 25(a3)
	sb a5, 153(s10)
	lbu a5, 26(a3)
	sb a5, 154(s10)
	lbu a5, 27(a3)
	sb a5, 155(s10)
	lbu a5, 28(a3)
	sb a5, 156(s10)
	lbu a5, 29(a3)
	sb a5, 157(s10)
	lbu a5, 30(a3)
	sb a5, 158(s10)
	lbu a5, 31(a3)
	sb a5, 159(s10)
	lbu a5, 32(a3)
	sb a5, 160(s10)
	lbu a5, 33(a3)
	sb a5, 161(s10)
	lbu a5, 34(a3)
	sb a5, 162(s10)
	lbu a5, 35(a3)
	sb a5, 163(s10)
	lbu a5, 36(a3)
	sb a5, 164(s10)
	lbu a5, 37(a3)
	sb a5, 165(s10)
	lbu a5, 38(a3)
	sb a5, 166(s10)
	lbu a5, 39(a3)
	sb a5, 167(s10)
	lbu a5, 40(a3)
	sb a5, 168(s10)
	lbu a5, 41(a3)
	sb a5, 169(s10)
	lbu a5, 42(a3)
	sb a5, 170(s10)
	lbu a5, 43(a3)
	sb a5, 171(s10)
	lbu a5, 44(a3)
	sb a5, 172(s10)
	lbu a5, 45(a3)
	sb a5, 173(s10)
	lbu a5, 46(a3)
	sb a5, 174(s10)
	lbu a5, 47(a3)
	sb a5, 175(s10)
	lbu a5, 48(a3)
	sb a5, 176(s10)
	lbu a5, 49(a3)
	sb a5, 177(s10)
	lbu a5, 50(a3)
	sb a5, 178(s10)
	lbu a5, 51(a3)
	sb a5, 179(s10)
	lbu a5, 52(a3)
	sb a5, 180(s10)
	lbu a5, 53(a3)
	sb a5, 181(s10)
	lbu a5, 54(a3)
	sb a5, 182(s10)
	lbu a5, 55(a3)
	sb a5, 183(s10)
	lbu a5, 56(a3)
	sb a5, 184(s10)
	lbu a5, 57(a3)
	sb a5, 185(s10)
	lbu a5, 58(a3)
	sb a5, 186(s10)
	lbu a5, 59(a3)
	sb a5, 187(s10)
	lbu a5, 60(a3)
	sb a5, 188(s10)
	lbu a5, 61(a3)
	sb a5, 189(s10)
	lbu a5, 62(a3)
	sb a5, 190(s10)
	lbu a5, 63(a3)
	sb a5, 191(s10)
	lbu a5, 0(a0)
	sb a5, 192(s10)
	lbu a5, 1(a0)
	sb a5, 193(s10)
	lbu a5, 2(a0)
	sb a5, 194(s10)
	lbu a5, 3(a0)
	sb a5, 195(s10)
	lbu a5, 4(a0)
	sb a5, 196(s10)
	lbu a5, 5(a0)
	sb a5, 197(s10)
	lbu a5, 6(a0)
	sb a5, 198(s10)
	lbu a5, 7(a0)
	sb a5, 199(s10)
	lbu a5, 8(a0)
	sb a5, 200(s10)
	lbu a5, 9(a0)
	sb a5, 201(s10)
	lbu a5, 10(a0)
	sb a5, 202(s10)
	lbu a5, 11(a0)
	sb a5, 203(s10)
	lbu a5, 12(a0)
	sb a5, 204(s10)
	lbu a5, 13(a0)
	sb a5, 205(s10)
	lbu a5, 14(a0)
	sb a5, 206(s10)
	lbu a5, 15(a0)
	sb a5, 207(s10)
	lbu a5, 16(a0)
	sb a5, 208(s10)
	lbu a5, 17(a0)
	sb a5, 209(s10)
	lbu a5, 18(a0)
	sb a5, 210(s10)
	lbu a5, 19(a0)
	sb a5, 211(s10)
	lbu a5, 20(a0)
	sb a5, 212(s10)
	lbu a5, 21(a0)
	sb a5, 213(s10)
	lbu a5, 22(a0)
	sb a5, 214(s10)
	lbu a5, 23(a0)
	sb a5, 215(s10)
	lbu a5, 24(a0)
	sb a5, 216(s10)
	lbu a5, 25(a0)
	sb a5, 217(s10)
	lbu a5, 26(a0)
	sb a5, 218(s10)
	lbu a5, 27(a0)
	sb a5, 219(s10)
	lbu a5, 28(a0)
	sb a5, 220(s10)
	lbu a5, 29(a0)
	sb a5, 221(s10)
	lbu a5, 30(a0)
	sb a5, 222(s10)
	lbu a5, 31(a0)
	sb a5, 223(s10)
	addi a0, s9, 0
	call {vg_sha512_init}
	addi a0, s9, 0
	addi a1, zero, 0
	addi a2, s10, 128
	addi a3, zero, 32
	call {vg_sha512_update}
	addi a0, s9, 0
	addi a1, zero, 32
	addi a2, s10, 192
	addi a3, zero, 32
	call {vg_sha512_update}
	addi a0, s9, 0
	addi a1, zero, 64
	addi a2, s7, 0
	addi a3, s8, 0
	call {vg_sha512_update}
	addi a0, s9, 0
	addi a1, s8, 64
	addi a2, s10, 64
	call {vg_sha512_finalize}
	addi a0, s10, 0
	addi a1, s10, 64
	addi a2, s9, 0
	call {vg_ed25519_scalar_reduce}
	addi a5, zero, 0
	sd a5, 32(s10)
	sd a5, 40(s10)
	sd a5, 48(s10)
	sd a5, 56(s10)
	addi a0, s10, 192
	addi a1, s10, 128
	addi a2, s10, 0
	addi a3, s9, 0
	call {vg_ed25519_verify_equation}
	ld ra, 256(s10)
	ld s7, 224(s10)
	ld s8, 232(s10)
	ld s9, 240(s10)
	ld s10, 248(s10)
	addi sp, sp, 272
	ret
	.option pop
