// The functions of `src/ecdsa_p256_sha256.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_p256_sha256_sign:
	.option push
	.option arch, +m, +c
	addi sp, sp, -224
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
	sd t0, 24(s0)
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
	sd t0, 16(s0)
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
	sd t0, 8(s0)
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
	sd t0, 0(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 32(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 40(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 48(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 56(s0)
	addi a0, s0, 0
	addi a1, zero, 64
	addi a2, zero, 0
	addi a3, zero, 32
	call {vg_p256_add_mod_n}
	addi a7, zero, -1
	ld t0, 88(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 192(s1)
	srli t1, t0, 48
	sb t1, 193(s1)
	srli t1, t0, 40
	sb t1, 194(s1)
	srli t1, t0, 32
	sb t1, 195(s1)
	srli t1, t0, 24
	sb t1, 196(s1)
	srli t1, t0, 16
	sb t1, 197(s1)
	srli t1, t0, 8
	sb t1, 198(s1)
	srli t1, t0, 0
	sb t1, 199(s1)
	ld t0, 80(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 200(s1)
	srli t1, t0, 48
	sb t1, 201(s1)
	srli t1, t0, 40
	sb t1, 202(s1)
	srli t1, t0, 32
	sb t1, 203(s1)
	srli t1, t0, 24
	sb t1, 204(s1)
	srli t1, t0, 16
	sb t1, 205(s1)
	srli t1, t0, 8
	sb t1, 206(s1)
	srli t1, t0, 0
	sb t1, 207(s1)
	ld t0, 72(s0)
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
	ld t0, 64(s0)
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
	addi t0, zero, 0
	sb t0, 160(s1)
	addi a0, s0, 0
	addi a1, s0, 192
	addi a2, s1, 64
	addi a3, zero, 32
	call {vg_hmac_sha256_init}
	addi a0, s0, 0
	addi a1, zero, 64
	addi a2, s1, 128
	addi a3, zero, 33
	call {vg_sha256_update}
	addi a0, s0, 0
	addi a1, zero, 97
	addi a2, s3, 0
	addi a3, zero, 32
	call {vg_sha256_update}
	addi a0, s0, 0
	addi a1, zero, 129
	addi a2, s1, 192
	addi a3, zero, 32
	call {vg_sha256_update}
	addi a0, s0, 0
	addi a1, s0, 192
	addi a2, zero, 161
	addi a3, s1, 64
	call {vg_hmac_sha256_finalize}
	addi a0, s0, 0
	addi a1, s0, 192
	addi a2, s1, 64
	addi a3, zero, 32
	call {vg_hmac_sha256_init}
	addi a0, s0, 0
	addi a1, zero, 64
	addi a2, s1, 128
	addi a3, zero, 32
	call {vg_sha256_update}
	addi a0, s0, 0
	addi a1, s0, 192
	addi a2, zero, 96
	addi a3, s1, 128
	call {vg_hmac_sha256_finalize}
	addi t0, zero, 1
	sb t0, 160(s1)
	addi a0, s0, 0
	addi a1, s0, 192
	addi a2, s1, 64
	addi a3, zero, 32
	call {vg_hmac_sha256_init}
	addi a0, s0, 0
	addi a1, zero, 64
	addi a2, s1, 128
	addi a3, zero, 33
	call {vg_sha256_update}
	addi a0, s0, 0
	addi a1, zero, 97
	addi a2, s3, 0
	addi a3, zero, 32
	call {vg_sha256_update}
	addi a0, s0, 0
	addi a1, zero, 129
	addi a2, s1, 192
	addi a3, zero, 32
	call {vg_sha256_update}
	addi a0, s0, 0
	addi a1, s0, 192
	addi a2, zero, 161
	addi a3, s1, 64
	call {vg_hmac_sha256_finalize}
	addi a0, s0, 0
	addi a1, s0, 192
	addi a2, s1, 64
	addi a3, zero, 32
	call {vg_hmac_sha256_init}
	addi a0, s0, 0
	addi a1, zero, 64
	addi a2, s1, 128
	addi a3, zero, 32
	call {vg_sha256_update}
	addi a0, s0, 0
	addi a1, s0, 192
	addi a2, zero, 96
	addi a3, s1, 128
	call {vg_hmac_sha256_finalize}
	addi s5, zero, 8
20:
	addi a0, s0, 0
	addi a1, s0, 192
	addi a2, s1, 64
	addi a3, zero, 32
	call {vg_hmac_sha256_init}
	addi a0, s0, 0
	addi a1, zero, 64
	addi a2, s1, 128
	addi a3, zero, 32
	call {vg_sha256_update}
	addi a0, s0, 0
	addi a1, s0, 192
	addi a2, zero, 96
	addi a3, s1, 128
	call {vg_hmac_sha256_finalize}
	addi a0, s2, 0
	addi a1, s3, 0
	addi a2, s4, 0
	addi a3, s1, 128
	addi a4, s0, 0
	call {vg_ecdsa_p256_sign}
	addi s5, s5, -1
	andi t0, a0, 1
	addi t0, t0, -1
	and t6, t0, s5
	bnez t6, 21f
	addi t6, zero, 0
	j 22f
21:
	addi t0, zero, 0
	sb t0, 160(s1)
	addi a0, s0, 0
	addi a1, s0, 192
	addi a2, s1, 64
	addi a3, zero, 32
	call {vg_hmac_sha256_init}
	addi a0, s0, 0
	addi a1, zero, 64
	addi a2, s1, 128
	addi a3, zero, 33
	call {vg_sha256_update}
	addi a0, s0, 0
	addi a1, s0, 192
	addi a2, zero, 97
	addi a3, s1, 64
	call {vg_hmac_sha256_finalize}
	addi a0, s0, 0
	addi a1, s0, 192
	addi a2, s1, 64
	addi a3, zero, 32
	call {vg_hmac_sha256_init}
	addi a0, s0, 0
	addi a1, zero, 64
	addi a2, s1, 128
	addi a3, zero, 32
	call {vg_sha256_update}
	addi a0, s0, 0
	addi a1, s0, 192
	addi a2, zero, 96
	addi a3, s1, 128
	call {vg_hmac_sha256_finalize}
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
	ld ra, 0(s1)
	ld s0, 8(s1)
	ld s2, 24(s1)
	ld s3, 32(s1)
	ld s4, 40(s1)
	ld s5, 48(s1)
	ld s1, 16(s1)
	addi sp, sp, 224
	ret
	.option pop
