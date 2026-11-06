// The functions of `src/rsa_pkcs1_enc.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_pkcs1_encrypt_precomputed:
	.option push
	.option arch, +m, +c
	addi sp, sp, -2032
	addi sp, sp, -96
	addi t0, sp, 0
	sd s1, 16(t0)
	sd s2, 24(t0)
	sd s3, 32(t0)
	sd s4, 40(t0)
	sd ra, 48(t0)
	addi s1, a0, 0
	addi s2, a3, 0
	addi s3, a4, 0
	addi s4, a5, 0
	addi t1, zero, 0
	sb t1, 72(t0)
	addi t1, zero, 2
	sb t1, 73(t0)
	addi t6, sp, 2032
	addi t6, t6, 96
	ld t2, 0(t6)
	ld t3, 8(t6)
	addi t4, t0, 74
	addi t5, zero, 0
20:
	lbu t1, 0(t2)
	sb t1, 0(t4)
	addi t1, t1, -1
	srli t1, t1, 63
	or t5, t5, t1
	addi t2, t2, 1
	addi t4, t4, 1
	addi t3, t3, -1
	bnez t3, 20b
	addi t1, zero, 0
	sb t1, 0(t4)
	addi t4, t4, 1
	bnez a7, 21f
	j 22f
21:
	addi a4, a6, 0
	addi a1, t4, 0
	addi a5, a7, 0
23:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 23b
22:
	addi t0, sp, 0
	sd t5, 56(t0)
	addi a0, s1, 0
	addi a1, s2, 0
	addi a4, s3, 0
	addi a5, s4, 0
	addi a6, t0, 72
	addi a7, s2, 0
	addi t6, sp, 2032
	addi t6, t6, 96
	ld t1, 16(t6)
	sd t1, 0(t0)
	ld t1, 24(t6)
	sd t1, 8(t0)
	ld a2, 32(t6)
	ld a3, 40(t6)
	call {vg_rsa_public_precomputed_checked}
	addi t0, sp, 0
	ld a3, 56(t0)
	addi a3, a3, -1
	and a0, a0, a3
	addi a1, s1, 0
	addi a5, s2, 0
24:
	lbu t1, 0(a1)
	and t1, t1, a3
	sb t1, 0(a1)
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 24b
	addi t0, sp, 0
	addi a1, t0, 72
	addi t5, s2, 0
	addi t0, zero, 0
25:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 25b
	addi t0, sp, 0
	ld s1, 16(t0)
	ld s2, 24(t0)
	ld s3, 32(t0)
	ld s4, 40(t0)
	ld ra, 48(t0)
	addi sp, sp, 96
	addi sp, sp, 2032
	ret
	.option pop

vg_rsa_pkcs1_decrypt:
	.option push
	.option arch, +m, +c
	addi sp, sp, -192
	addi t0, sp, 0
	sd s0, 96(t0)
	sd s1, 104(t0)
	sd s2, 112(t0)
	sd s3, 120(t0)
	sd s4, 128(t0)
	sd s5, 136(t0)
	sd s6, 144(t0)
	sd s7, 152(t0)
	sd s8, 160(t0)
	sd s9, 168(t0)
	sd ra, 176(t0)
	addi t6, sp, 192
	addi s1, a4, 0
	addi s2, a0, 0
	addi s3, a2, 0
	addi s4, a7, 0
	ld s5, 0(t6)
	ld s6, 8(t6)
	ld s0, 104(t6)
	ld t1, 24(t6)
	sd t1, 0(t0)
	ld t1, 32(t6)
	sd t1, 8(t0)
	ld t1, 40(t6)
	sd t1, 16(t0)
	ld t1, 48(t6)
	sd t1, 24(t0)
	ld t1, 56(t6)
	sd t1, 32(t0)
	ld t1, 64(t6)
	sd t1, 40(t0)
	ld t1, 72(t6)
	sd t1, 48(t0)
	ld t1, 80(t6)
	sd t1, 56(t0)
	ld t1, 88(t6)
	sd t1, 64(t0)
	ld t1, 96(t6)
	sd t1, 72(t0)
	ld t1, 104(t6)
	sd t1, 80(t0)
	ld t1, 112(t6)
	sd t1, 88(t0)
	addi a1, s1, 0
	addi a2, a3, 0
	addi a3, s1, 0
	addi a4, a5, 0
	addi a5, a6, 0
	addi a6, s6, 0
	addi a7, s1, 0
	call {vg_rsa_private_checked}
	slli s7, a0, 32
	srli s7, s7, 32
	addi a1, s0, 1552
	addi t5, s1, 0
	addi t0, zero, 0
20:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 20b
	addi a4, s4, 0
	addi a5, s5, 0
	addi a1, s0, 1552
	add a1, a1, s1
	sub a1, a1, s5
21:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 21b
	addi a0, s0, 0
	call {vg_sha256_init}
	addi a0, s0, 0
	addi a1, zero, 0
	addi a2, s0, 1552
	addi a3, s1, 0
	call {vg_sha256_update}
	addi a0, s0, 0
	addi a1, s1, 0
	addi a2, s0, 208
	call {vg_sha256_finalize}
	addi a0, s0, 0
	addi a1, s0, 96
	addi a2, s0, 208
	addi a3, zero, 32
	call {vg_hmac_sha256_init}
	addi a0, s0, 0
	addi a1, zero, 64
	addi a2, s6, 0
	addi a3, s1, 0
	call {vg_sha256_update}
	addi a0, s0, 0
	addi a1, s0, 96
	addi a2, s1, 64
	addi a3, s0, 240
	call {vg_hmac_sha256_finalize}
	addi s8, zero, 0
	addi s9, s1, 31
	srli s9, s9, 5
22:
	addi t1, s0, 192
	addi t2, zero, 0
	sb t2, 0(t1)
	sb s8, 1(t1)
	addi t2, zero, 108
	sb t2, 2(t1)
	addi t2, zero, 101
	sb t2, 3(t1)
	addi t2, zero, 110
	sb t2, 4(t1)
	addi t2, zero, 103
	sb t2, 5(t1)
	addi t2, zero, 116
	sb t2, 6(t1)
	addi t2, zero, 104
	sb t2, 7(t1)
	addi t2, zero, 8
	sb t2, 8(t1)
	addi t2, zero, 0
	sb t2, 9(t1)
	addi a0, s0, 0
	addi a1, s0, 96
	addi a2, s0, 240
	addi a3, zero, 32
	call {vg_hmac_sha256_init}
	addi a0, s0, 0
	addi a1, zero, 64
	addi a2, s0, 192
	addi a3, zero, 10
	call {vg_sha256_update}
	addi a0, s0, 0
	addi a1, s0, 96
	addi a2, zero, 74
	slli a3, s8, 5
	add a3, a3, s0
	addi a3, a3, 272
	call {vg_hmac_sha256_finalize}
	addi s8, s8, 1
	addi t1, zero, 8
	sub t1, t1, s8
	bnez t1, 22b
	addi s8, zero, 0
23:
	addi t1, s0, 192
	addi t2, zero, 0
	sb t2, 0(t1)
	sb s8, 1(t1)
	addi t2, zero, 109
	sb t2, 2(t1)
	addi t2, zero, 101
	sb t2, 3(t1)
	addi t2, zero, 115
	sb t2, 4(t1)
	addi t2, zero, 115
	sb t2, 5(t1)
	addi t2, zero, 97
	sb t2, 6(t1)
	addi t2, zero, 103
	sb t2, 7(t1)
	addi t2, zero, 101
	sb t2, 8(t1)
	slli t2, s1, 3
	sb t2, 10(t1)
	srli t2, t2, 8
	sb t2, 9(t1)
	addi a0, s0, 0
	addi a1, s0, 96
	addi a2, s0, 240
	addi a3, zero, 32
	call {vg_hmac_sha256_init}
	addi a0, s0, 0
	addi a1, zero, 64
	addi a2, s0, 192
	addi a3, zero, 11
	call {vg_sha256_update}
	addi a0, s0, 0
	addi a1, s0, 96
	addi a2, zero, 75
	slli a3, s8, 5
	add a3, a3, s0
	addi a3, a3, 528
	call {vg_hmac_sha256_finalize}
	addi s8, s8, 1
	addi t1, s9, 0
	sub t1, t1, s8
	bnez t1, 23b
	addi t3, s1, -11
	addi t4, zero, 0
24:
	add t4, t4, t4
	addi t4, t4, 1
	sub t5, t4, t3
	srli t5, t5, 63
	bnez t5, 24b
	addi t1, s0, 272
	addi t2, zero, 128
	addi t6, zero, 0
25:
	lbu a0, 0(t1)
	slli a0, a0, 8
	lbu a1, 1(t1)
	add a0, a0, a1
	and a0, a0, t4
	sub a1, t3, a0
	srli a1, a1, 63
	addi a1, a1, -1
	xor a2, t6, a0
	and a2, a2, a1
	xor t6, t6, a2
	addi t1, t1, 2
	addi t2, t2, -1
	bnez t2, 25b
	addi t1, s2, 2
	addi t2, s1, -2
	addi a3, zero, 2
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	addi a7, zero, 0
	addi a7, a7, -1
26:
	lbu a0, 0(t1)
	addi a0, a0, -1
	srli a0, a0, 63
	sub a0, a6, a0
	xor a1, a4, a7
	and a1, a1, a0
	and a1, a1, a3
	or a5, a5, a1
	or a4, a4, a0
	addi a3, a3, 1
	addi t1, t1, 1
	addi t2, t2, -1
	bnez t2, 26b
	addi t1, s2, 0
	addi t2, s1, 0
	lbu a0, 0(t1)
	addi a0, a0, -1
	srli a0, a0, 63
	sub a0, a6, a0
	lbu a1, 1(t1)
	addi a3, zero, 2
	xor a1, a1, a3
	addi a1, a1, -1
	srli a1, a1, 63
	sub a1, a6, a1
	and a0, a0, a1
	and a4, a4, a0
	addi a3, zero, 10
	sub a1, a5, a3
	srli a1, a1, 63
	sub a1, a6, a1
	xor a1, a1, a7
	and a4, a4, a1
	sub a1, t2, a5
	addi a1, a1, -1
	xor a1, a1, t6
	and a1, a1, a4
	xor t6, t6, a1
	addi a3, s7, 0
	addi a1, zero, 1
	xor a3, a3, a1
	addi a3, a3, -1
	srli a3, a3, 63
	sub a3, a6, a3
	sub a5, t2, t6
	and t6, t6, a3
	sd t6, 0(s3)
	addi a0, s0, 528
	addi a1, zero, 0
27:
	lbu t6, 0(t1)
	lbu a2, 0(a0)
	xor t6, t6, a2
	and t6, t6, a4
	xor t6, t6, a2
	sub a2, a1, a5
	srli a2, a2, 63
	sub a2, a6, a2
	xor a2, a2, a7
	and a2, a2, a3
	and t6, t6, a2
	sb t6, 0(t1)
	addi a1, a1, 1
	addi t1, t1, 1
	addi a0, a0, 1
	addi t2, t2, -1
	bnez t2, 27b
	addi a0, s7, 0
	addi t0, sp, 0
	ld s0, 96(t0)
	ld s1, 104(t0)
	ld s2, 112(t0)
	ld s3, 120(t0)
	ld s4, 128(t0)
	ld s5, 136(t0)
	ld s6, 144(t0)
	ld s7, 152(t0)
	ld s8, 160(t0)
	ld s9, 168(t0)
	ld ra, 176(t0)
	addi sp, sp, 192
	ret
	.option pop

vg_rsa_pkcs1_encrypt_random:
	.option push
	.option arch, +m, +c
	addi sp, sp, -2032
	addi sp, sp, -96
	addi t0, sp, 0
	sd s1, 16(t0)
	sd s2, 24(t0)
	sd s3, 32(t0)
	sd s4, 40(t0)
	sd ra, 48(t0)
	addi t6, sp, 2032
	addi t6, t6, 96
	ld t2, 0(t6)
	ld t3, 8(t6)
	ld t4, 16(t6)
	sub t5, a4, t2
	addi s1, t5, -3
	addi t1, t0, 72
	addi t2, zero, 0
	addi t5, zero, 0
	bnez t4, 20f
	j 21f
20:
22:
	add t6, t3, t2
	lbu t6, 0(t6)
	addi t2, t2, 1
	bnez t6, 23f
	j 24f
23:
	add t0, t1, t5
	sb t6, 0(t0)
	addi t5, t5, 1
24:
	beq t5, s1, 25f
	sub t0, t4, t2
	j 26f
25:
	addi t0, zero, 0
26:
	bnez t0, 22b
21:
	beq t5, s1, 27f
	addi t3, t5, 0
	addi a1, a0, 0
	addi t5, a4, 0
	addi t0, zero, 0
29:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 29b
	bnez t3, 210f
	j 211f
210:
	addi t0, sp, 0
	addi a1, t0, 72
	addi t5, t3, 0
	addi t0, zero, 0
212:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 212b
211:
	addi t0, s1, 128
	bltu t4, t0, 213f
	sd t4, 0(a2)
	addi t1, zero, 0
	sd t1, 8(a2)
	addi a0, zero, 3
	j 214f
213:
	addi t1, zero, 0
	sd t1, 0(a2)
	add t1, s1, t4
	sub t1, t1, t3
	bltu t0, t1, 215f
	j 216f
215:
	addi t1, t0, 0
216:
	sd t1, 8(a2)
	addi a0, zero, 0
214:
	addi t0, sp, 0
	ld s1, 16(t0)
	ld s2, 24(t0)
	ld s3, 32(t0)
	ld s4, 40(t0)
	ld ra, 48(t0)
	j 28f
27:
	sd t2, 0(a2)
	addi t0, zero, 0
	sd t0, 8(a2)
	addi a1, a4, 0
	addi a2, a3, 0
	addi a3, a4, 0
	addi a4, a5, 0
	addi a5, a6, 0
	addi a6, a7, 0
	addi t6, sp, 2032
	addi t6, t6, 96
	ld a7, 0(t6)
	ld t2, 24(t6)
	ld t3, 32(t6)
	ld t4, 40(t6)
	ld t5, 48(t6)
	addi sp, sp, -48
	addi t0, sp, 0
	sd t1, 0(t0)
	sd s1, 8(t0)
	sd t2, 16(t0)
	sd t3, 24(t0)
	sd t4, 32(t0)
	sd t5, 40(t0)
	call {vg_rsa_pkcs1_encrypt_precomputed}
	addi sp, sp, 48
	addi t0, zero, 2
	sub a0, t0, a0
	addi t0, sp, 0
	addi a1, t0, 72
	addi t5, s1, 0
	addi t0, zero, 0
217:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 217b
	addi t0, sp, 0
	ld s1, 16(t0)
	ld s2, 24(t0)
	ld s3, 32(t0)
	ld s4, 40(t0)
	ld ra, 48(t0)
28:
	addi sp, sp, 96
	addi sp, sp, 2032
	ret
	.option pop
