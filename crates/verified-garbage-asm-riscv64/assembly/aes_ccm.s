// The functions of `src/aes_ccm.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_ccm_seal:
	.option push
	.option arch, +m, +c
	addi sp, sp, -2032
	addi sp, sp, -560
	addi t0, sp, 0
	addi t2, sp, 1296
	addi t2, t2, 1296
	ld t1, 0(t2)
	sd t1, 0(t0)
	ld t1, 8(t2)
	sd t1, 8(t0)
	addi t1, t0, 24
	sd t1, 16(t0)
	addi t0, sp, 0
	ld t1, 16(t0)
	sd s2, 136(t1)
	sd s3, 144(t1)
	sd s4, 152(t1)
	sd s5, 160(t1)
	sd s6, 168(t1)
	sd s7, 176(t1)
	sd s8, 184(t1)
	sd s9, 192(t1)
	sd s10, 200(t1)
	sd s1, 128(t1)
	sd ra, 208(t1)
	addi s1, t1, 0
	ld s2, 8(t0)
	ld t1, 0(t0)
	addi s3, a0, 0
	addi s4, a1, 0
	sd a4, 216(s1)
	sd a5, 224(s1)
	sd a3, 232(s1)
	sd t1, 240(s1)
	addi s9, a6, 0
	addi s10, a7, 0
	addi t0, zero, 0
	sd t0, 48(s1)
	sd t0, 56(s1)
	addi t1, zero, 14
	sub t1, t1, a3
	sb t1, 48(s1)
	addi a0, a2, 0
	addi a1, s1, 49
	addi a2, a3, 0
20:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 20b
	ld s5, 216(s1)
	ld s6, 224(s1)
	addi t3, s2, -2
	slli t3, t3, 2
	ld t1, 232(s1)
	addi t2, zero, 14
	sub t2, t2, t1
	add t3, t3, t2
	beqz s6, 21f
	addi t3, t3, 64
	j 22f
21:
22:
	ld t1, 48(s1)
	ld t2, 56(s1)
	sd t1, 32(s1)
	sd t2, 40(s1)
	sb t3, 32(s1)
	lbu t1, 40(s1)
	slli t1, t1, 8
	lbu t2, 41(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 42(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 43(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 44(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 45(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 46(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 47(s1)
	or t1, t1, t2
	or t1, t1, s10
	srli t2, t1, 56
	sb t2, 40(s1)
	srli t2, t1, 48
	sb t2, 41(s1)
	srli t2, t1, 40
	sb t2, 42(s1)
	srli t2, t1, 32
	sb t2, 43(s1)
	srli t2, t1, 24
	sb t2, 44(s1)
	srli t2, t1, 16
	sb t2, 45(s1)
	srli t2, t1, 8
	sb t2, 46(s1)
	srli t2, t1, 0
	sb t2, 47(s1)
	addi t0, zero, 0
	sd t0, 0(s1)
	sd t0, 8(s1)
	addi a0, s3, 0
	addi a1, s4, 0
	addi a2, s1, 0
	addi a5, s1, 384
	addi a3, s1, 32
	addi a4, zero, 1
	call {vg_cmac_aes_update}
	beqz s6, 23f
	addi t0, zero, 0
	sd t0, 32(s1)
	sd t0, 40(s1)
	srli t1, s6, 32
	beqz t1, 25f
	addi t1, zero, 255
	sb t1, 32(s1)
	sb t1, 33(s1)
	srli t2, s6, 56
	sb t2, 34(s1)
	srli t2, s6, 48
	sb t2, 35(s1)
	srli t2, s6, 40
	sb t2, 36(s1)
	srli t2, s6, 32
	sb t2, 37(s1)
	srli t2, s6, 24
	sb t2, 38(s1)
	srli t2, s6, 16
	sb t2, 39(s1)
	srli t2, s6, 8
	sb t2, 40(s1)
	srli t2, s6, 0
	sb t2, 41(s1)
	addi s7, zero, 10
	j 26f
25:
	srli t1, s6, 8
	addi t2, zero, 255
	sltu t1, t1, t2
	beqz t1, 27f
	slli t1, s6, 48
	srli t2, t1, 56
	sb t2, 32(s1)
	srli t2, t1, 48
	sb t2, 33(s1)
	srli t2, t1, 40
	sb t2, 34(s1)
	srli t2, t1, 32
	sb t2, 35(s1)
	srli t2, t1, 24
	sb t2, 36(s1)
	srli t2, t1, 16
	sb t2, 37(s1)
	srli t2, t1, 8
	sb t2, 38(s1)
	srli t2, t1, 0
	sb t2, 39(s1)
	addi s7, zero, 2
	j 28f
27:
	slli t1, s6, 16
	addi t2, zero, -2
	slli t2, t2, 48
	or t1, t1, t2
	srli t2, t1, 56
	sb t2, 32(s1)
	srli t2, t1, 48
	sb t2, 33(s1)
	srli t2, t1, 40
	sb t2, 34(s1)
	srli t2, t1, 32
	sb t2, 35(s1)
	srli t2, t1, 24
	sb t2, 36(s1)
	srli t2, t1, 16
	sb t2, 37(s1)
	srli t2, t1, 8
	sb t2, 38(s1)
	srli t2, t1, 0
	sb t2, 39(s1)
	addi s7, zero, 6
28:
26:
	srli t1, s6, 4
	beqz t1, 29f
	addi t1, zero, 16
	j 210f
29:
	addi t1, s6, 0
210:
	addi t2, zero, 16
	sub t2, t2, s7
	sltu t3, t1, t2
	beqz t3, 211f
	addi s8, t1, 0
	j 212f
211:
	addi s8, t2, 0
212:
	add a1, s1, s7
	addi a1, a1, 32
	addi a0, s5, 0
	addi a2, s8, 0
213:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 213b
	add s5, s5, s8
	sub s6, s6, s8
	addi a0, s3, 0
	addi a1, s4, 0
	addi a2, s1, 0
	addi a5, s1, 384
	addi a3, s1, 32
	addi a4, zero, 1
	call {vg_cmac_aes_update}
	addi a0, s3, 0
	addi a1, s4, 0
	addi a2, s1, 0
	addi a5, s1, 384
	addi a3, s5, 0
	srli a4, s6, 4
	call {vg_cmac_aes_update}
	andi s8, s6, 15
	beqz s8, 214f
	addi t0, zero, 0
	sd t0, 32(s1)
	sd t0, 40(s1)
	srli t0, s6, 4
	slli t0, t0, 4
	add a0, s5, t0
	addi a1, s1, 32
	addi a2, s8, 0
216:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 216b
	addi a0, s3, 0
	addi a1, s4, 0
	addi a2, s1, 0
	addi a5, s1, 384
	addi a3, s1, 32
	addi a4, zero, 1
	call {vg_cmac_aes_update}
	j 215f
214:
215:
	j 24f
23:
24:
	addi s5, s9, 0
	addi s6, s10, 0
	addi a0, s3, 0
	addi a1, s4, 0
	addi a2, s1, 0
	addi a5, s1, 384
	addi a3, s5, 0
	srli a4, s6, 4
	call {vg_cmac_aes_update}
	andi s8, s6, 15
	beqz s8, 217f
	addi t0, zero, 0
	sd t0, 32(s1)
	sd t0, 40(s1)
	srli t0, s6, 4
	slli t0, t0, 4
	add a0, s5, t0
	addi a1, s1, 32
	addi a2, s8, 0
219:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 219b
	addi a0, s3, 0
	addi a1, s4, 0
	addi a2, s1, 0
	addi a5, s1, 384
	addi a3, s1, 32
	addi a4, zero, 1
	call {vg_cmac_aes_update}
	j 218f
217:
218:
	addi t3, zero, 0
	ld t1, 48(s1)
	sd t1, 64(s1)
	lbu t1, 56(s1)
	slli t1, t1, 8
	lbu t2, 57(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 58(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 59(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 60(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 61(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 62(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 63(s1)
	or t1, t1, t2
	or t1, t1, t3
	srli t2, t1, 56
	sb t2, 72(s1)
	srli t2, t1, 48
	sb t2, 73(s1)
	srli t2, t1, 40
	sb t2, 74(s1)
	srli t2, t1, 32
	sb t2, 75(s1)
	srli t2, t1, 24
	sb t2, 76(s1)
	srli t2, t1, 16
	sb t2, 77(s1)
	srli t2, t1, 8
	sb t2, 78(s1)
	srli t2, t1, 0
	sb t2, 79(s1)
	addi a0, s3, 0
	addi a1, s4, 0
	addi a2, s1, 64
	addi a5, s1, 384
	addi a3, s1, 0
	addi a4, zero, 1
	call {vg_aes_ctr32}
	addi s5, s9, 0
	srli s6, s10, 4
	addi s7, zero, 1
	beqz s6, 220f
222:
	slli t1, s7, 32
	srli t1, t1, 32
	addi t2, zero, 1
	slli t2, t2, 32
	sub t2, t2, t1
	sltu t1, s6, t2
	beqz t1, 223f
	addi s8, s6, 0
	j 224f
223:
	addi s8, t2, 0
224:
	addi t3, s7, 0
	ld t1, 48(s1)
	sd t1, 64(s1)
	lbu t1, 56(s1)
	slli t1, t1, 8
	lbu t2, 57(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 58(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 59(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 60(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 61(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 62(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 63(s1)
	or t1, t1, t2
	or t1, t1, t3
	srli t2, t1, 56
	sb t2, 72(s1)
	srli t2, t1, 48
	sb t2, 73(s1)
	srli t2, t1, 40
	sb t2, 74(s1)
	srli t2, t1, 32
	sb t2, 75(s1)
	srli t2, t1, 24
	sb t2, 76(s1)
	srli t2, t1, 16
	sb t2, 77(s1)
	srli t2, t1, 8
	sb t2, 78(s1)
	srli t2, t1, 0
	sb t2, 79(s1)
	addi a0, s3, 0
	addi a1, s4, 0
	addi a2, s1, 64
	addi a5, s1, 384
	addi a3, s5, 0
	addi a4, s8, 0
	call {vg_aes_ctr32}
	sub s6, s6, s8
	add s7, s7, s8
	slli t1, s8, 4
	add s5, s5, t1
	bnez s6, 222b
	j 221f
220:
221:
	andi s8, s10, 15
	beqz s8, 225f
	addi t3, s7, 0
	ld t1, 48(s1)
	sd t1, 64(s1)
	lbu t1, 56(s1)
	slli t1, t1, 8
	lbu t2, 57(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 58(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 59(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 60(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 61(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 62(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 63(s1)
	or t1, t1, t2
	or t1, t1, t3
	srli t2, t1, 56
	sb t2, 72(s1)
	srli t2, t1, 48
	sb t2, 73(s1)
	srli t2, t1, 40
	sb t2, 74(s1)
	srli t2, t1, 32
	sb t2, 75(s1)
	srli t2, t1, 24
	sb t2, 76(s1)
	srli t2, t1, 16
	sb t2, 77(s1)
	srli t2, t1, 8
	sb t2, 78(s1)
	srli t2, t1, 0
	sb t2, 79(s1)
	addi t0, zero, 0
	sd t0, 80(s1)
	sd t0, 88(s1)
	addi a0, s3, 0
	addi a1, s4, 0
	addi a2, s1, 64
	addi a5, s1, 384
	addi a3, s1, 80
	addi a4, zero, 1
	call {vg_aes_ctr32}
	addi a0, s1, 80
	addi a1, s5, 0
	addi a2, s8, 0
227:
	lbu t0, 0(a0)
	lbu t1, 0(a1)
	xor t0, t0, t1
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 227b
	j 226f
225:
226:
	ld a1, 240(s1)
	addi a0, s1, 0
	addi a2, s2, 0
228:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 228b
	ld ra, 208(s1)
	ld s2, 136(s1)
	ld s3, 144(s1)
	ld s4, 152(s1)
	ld s5, 160(s1)
	ld s6, 168(s1)
	ld s7, 176(s1)
	ld s8, 184(s1)
	ld s9, 192(s1)
	ld s10, 200(s1)
	ld s1, 128(s1)
	addi sp, sp, 560
	addi sp, sp, 2032
	ret
	.option pop

vg_aes_ccm_open:
	.option push
	.option arch, +m, +c
	addi sp, sp, -2032
	addi sp, sp, -560
	addi t0, sp, 0
	addi t2, sp, 1296
	addi t2, t2, 1296
	ld t1, 0(t2)
	sd t1, 0(t0)
	ld t1, 8(t2)
	sd t1, 8(t0)
	addi t1, t0, 24
	sd t1, 16(t0)
	addi t0, sp, 0
	ld t1, 16(t0)
	sd s2, 136(t1)
	sd s3, 144(t1)
	sd s4, 152(t1)
	sd s5, 160(t1)
	sd s6, 168(t1)
	sd s7, 176(t1)
	sd s8, 184(t1)
	sd s9, 192(t1)
	sd s10, 200(t1)
	sd s1, 128(t1)
	sd ra, 208(t1)
	addi s1, t1, 0
	ld s2, 8(t0)
	ld t1, 0(t0)
	addi s3, a0, 0
	addi s4, a1, 0
	sd a4, 216(s1)
	sd a5, 224(s1)
	sd a3, 232(s1)
	sd t1, 240(s1)
	addi s9, a6, 0
	addi s10, a7, 0
	addi t0, zero, 0
	sd t0, 48(s1)
	sd t0, 56(s1)
	addi t1, zero, 14
	sub t1, t1, a3
	sb t1, 48(s1)
	addi a0, a2, 0
	addi a1, s1, 49
	addi a2, a3, 0
20:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 20b
	addi s5, s9, 0
	srli s6, s10, 4
	addi s7, zero, 1
	beqz s6, 21f
23:
	slli t1, s7, 32
	srli t1, t1, 32
	addi t2, zero, 1
	slli t2, t2, 32
	sub t2, t2, t1
	sltu t1, s6, t2
	beqz t1, 24f
	addi s8, s6, 0
	j 25f
24:
	addi s8, t2, 0
25:
	addi t3, s7, 0
	ld t1, 48(s1)
	sd t1, 64(s1)
	lbu t1, 56(s1)
	slli t1, t1, 8
	lbu t2, 57(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 58(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 59(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 60(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 61(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 62(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 63(s1)
	or t1, t1, t2
	or t1, t1, t3
	srli t2, t1, 56
	sb t2, 72(s1)
	srli t2, t1, 48
	sb t2, 73(s1)
	srli t2, t1, 40
	sb t2, 74(s1)
	srli t2, t1, 32
	sb t2, 75(s1)
	srli t2, t1, 24
	sb t2, 76(s1)
	srli t2, t1, 16
	sb t2, 77(s1)
	srli t2, t1, 8
	sb t2, 78(s1)
	srli t2, t1, 0
	sb t2, 79(s1)
	addi a0, s3, 0
	addi a1, s4, 0
	addi a2, s1, 64
	addi a5, s1, 384
	addi a3, s5, 0
	addi a4, s8, 0
	call {vg_aes_ctr32}
	sub s6, s6, s8
	add s7, s7, s8
	slli t1, s8, 4
	add s5, s5, t1
	bnez s6, 23b
	j 22f
21:
22:
	andi s8, s10, 15
	beqz s8, 26f
	addi t3, s7, 0
	ld t1, 48(s1)
	sd t1, 64(s1)
	lbu t1, 56(s1)
	slli t1, t1, 8
	lbu t2, 57(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 58(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 59(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 60(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 61(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 62(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 63(s1)
	or t1, t1, t2
	or t1, t1, t3
	srli t2, t1, 56
	sb t2, 72(s1)
	srli t2, t1, 48
	sb t2, 73(s1)
	srli t2, t1, 40
	sb t2, 74(s1)
	srli t2, t1, 32
	sb t2, 75(s1)
	srli t2, t1, 24
	sb t2, 76(s1)
	srli t2, t1, 16
	sb t2, 77(s1)
	srli t2, t1, 8
	sb t2, 78(s1)
	srli t2, t1, 0
	sb t2, 79(s1)
	addi t0, zero, 0
	sd t0, 80(s1)
	sd t0, 88(s1)
	addi a0, s3, 0
	addi a1, s4, 0
	addi a2, s1, 64
	addi a5, s1, 384
	addi a3, s1, 80
	addi a4, zero, 1
	call {vg_aes_ctr32}
	addi a0, s1, 80
	addi a1, s5, 0
	addi a2, s8, 0
28:
	lbu t0, 0(a0)
	lbu t1, 0(a1)
	xor t0, t0, t1
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 28b
	j 27f
26:
27:
	ld s5, 216(s1)
	ld s6, 224(s1)
	addi t3, s2, -2
	slli t3, t3, 2
	ld t1, 232(s1)
	addi t2, zero, 14
	sub t2, t2, t1
	add t3, t3, t2
	beqz s6, 29f
	addi t3, t3, 64
	j 210f
29:
210:
	ld t1, 48(s1)
	ld t2, 56(s1)
	sd t1, 32(s1)
	sd t2, 40(s1)
	sb t3, 32(s1)
	lbu t1, 40(s1)
	slli t1, t1, 8
	lbu t2, 41(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 42(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 43(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 44(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 45(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 46(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 47(s1)
	or t1, t1, t2
	or t1, t1, s10
	srli t2, t1, 56
	sb t2, 40(s1)
	srli t2, t1, 48
	sb t2, 41(s1)
	srli t2, t1, 40
	sb t2, 42(s1)
	srli t2, t1, 32
	sb t2, 43(s1)
	srli t2, t1, 24
	sb t2, 44(s1)
	srli t2, t1, 16
	sb t2, 45(s1)
	srli t2, t1, 8
	sb t2, 46(s1)
	srli t2, t1, 0
	sb t2, 47(s1)
	addi t0, zero, 0
	sd t0, 96(s1)
	sd t0, 104(s1)
	addi a0, s3, 0
	addi a1, s4, 0
	addi a2, s1, 96
	addi a5, s1, 384
	addi a3, s1, 32
	addi a4, zero, 1
	call {vg_cmac_aes_update}
	beqz s6, 211f
	addi t0, zero, 0
	sd t0, 32(s1)
	sd t0, 40(s1)
	srli t1, s6, 32
	beqz t1, 213f
	addi t1, zero, 255
	sb t1, 32(s1)
	sb t1, 33(s1)
	srli t2, s6, 56
	sb t2, 34(s1)
	srli t2, s6, 48
	sb t2, 35(s1)
	srli t2, s6, 40
	sb t2, 36(s1)
	srli t2, s6, 32
	sb t2, 37(s1)
	srli t2, s6, 24
	sb t2, 38(s1)
	srli t2, s6, 16
	sb t2, 39(s1)
	srli t2, s6, 8
	sb t2, 40(s1)
	srli t2, s6, 0
	sb t2, 41(s1)
	addi s7, zero, 10
	j 214f
213:
	srli t1, s6, 8
	addi t2, zero, 255
	sltu t1, t1, t2
	beqz t1, 215f
	slli t1, s6, 48
	srli t2, t1, 56
	sb t2, 32(s1)
	srli t2, t1, 48
	sb t2, 33(s1)
	srli t2, t1, 40
	sb t2, 34(s1)
	srli t2, t1, 32
	sb t2, 35(s1)
	srli t2, t1, 24
	sb t2, 36(s1)
	srli t2, t1, 16
	sb t2, 37(s1)
	srli t2, t1, 8
	sb t2, 38(s1)
	srli t2, t1, 0
	sb t2, 39(s1)
	addi s7, zero, 2
	j 216f
215:
	slli t1, s6, 16
	addi t2, zero, -2
	slli t2, t2, 48
	or t1, t1, t2
	srli t2, t1, 56
	sb t2, 32(s1)
	srli t2, t1, 48
	sb t2, 33(s1)
	srli t2, t1, 40
	sb t2, 34(s1)
	srli t2, t1, 32
	sb t2, 35(s1)
	srli t2, t1, 24
	sb t2, 36(s1)
	srli t2, t1, 16
	sb t2, 37(s1)
	srli t2, t1, 8
	sb t2, 38(s1)
	srli t2, t1, 0
	sb t2, 39(s1)
	addi s7, zero, 6
216:
214:
	srli t1, s6, 4
	beqz t1, 217f
	addi t1, zero, 16
	j 218f
217:
	addi t1, s6, 0
218:
	addi t2, zero, 16
	sub t2, t2, s7
	sltu t3, t1, t2
	beqz t3, 219f
	addi s8, t1, 0
	j 220f
219:
	addi s8, t2, 0
220:
	add a1, s1, s7
	addi a1, a1, 32
	addi a0, s5, 0
	addi a2, s8, 0
221:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 221b
	add s5, s5, s8
	sub s6, s6, s8
	addi a0, s3, 0
	addi a1, s4, 0
	addi a2, s1, 96
	addi a5, s1, 384
	addi a3, s1, 32
	addi a4, zero, 1
	call {vg_cmac_aes_update}
	addi a0, s3, 0
	addi a1, s4, 0
	addi a2, s1, 96
	addi a5, s1, 384
	addi a3, s5, 0
	srli a4, s6, 4
	call {vg_cmac_aes_update}
	andi s8, s6, 15
	beqz s8, 222f
	addi t0, zero, 0
	sd t0, 32(s1)
	sd t0, 40(s1)
	srli t0, s6, 4
	slli t0, t0, 4
	add a0, s5, t0
	addi a1, s1, 32
	addi a2, s8, 0
224:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 224b
	addi a0, s3, 0
	addi a1, s4, 0
	addi a2, s1, 96
	addi a5, s1, 384
	addi a3, s1, 32
	addi a4, zero, 1
	call {vg_cmac_aes_update}
	j 223f
222:
223:
	j 212f
211:
212:
	addi s5, s9, 0
	addi s6, s10, 0
	addi a0, s3, 0
	addi a1, s4, 0
	addi a2, s1, 96
	addi a5, s1, 384
	addi a3, s5, 0
	srli a4, s6, 4
	call {vg_cmac_aes_update}
	andi s8, s6, 15
	beqz s8, 225f
	addi t0, zero, 0
	sd t0, 32(s1)
	sd t0, 40(s1)
	srli t0, s6, 4
	slli t0, t0, 4
	add a0, s5, t0
	addi a1, s1, 32
	addi a2, s8, 0
227:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 227b
	addi a0, s3, 0
	addi a1, s4, 0
	addi a2, s1, 96
	addi a5, s1, 384
	addi a3, s1, 32
	addi a4, zero, 1
	call {vg_cmac_aes_update}
	j 226f
225:
226:
	addi t3, zero, 0
	ld t1, 48(s1)
	sd t1, 64(s1)
	lbu t1, 56(s1)
	slli t1, t1, 8
	lbu t2, 57(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 58(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 59(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 60(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 61(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 62(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 63(s1)
	or t1, t1, t2
	or t1, t1, t3
	srli t2, t1, 56
	sb t2, 72(s1)
	srli t2, t1, 48
	sb t2, 73(s1)
	srli t2, t1, 40
	sb t2, 74(s1)
	srli t2, t1, 32
	sb t2, 75(s1)
	srli t2, t1, 24
	sb t2, 76(s1)
	srli t2, t1, 16
	sb t2, 77(s1)
	srli t2, t1, 8
	sb t2, 78(s1)
	srli t2, t1, 0
	sb t2, 79(s1)
	addi a0, s3, 0
	addi a1, s4, 0
	addi a2, s1, 64
	addi a5, s1, 384
	addi a3, s1, 96
	addi a4, zero, 1
	call {vg_aes_ctr32}
	ld s5, 240(s1)
	addi t0, zero, 0
	sd t0, 256(s1)
	sd t0, 264(s1)
	addi t0, zero, 0
	sd t0, 272(s1)
	sd t0, 280(s1)
	addi a0, s5, 0
	addi a1, s1, 272
	addi a2, s2, 0
228:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 228b
	addi a0, s1, 96
	addi a1, s1, 256
	addi a2, s2, 0
229:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 229b
	ld t0, 256(s1)
	ld t1, 272(s1)
	xor t0, t0, t1
	ld t1, 264(s1)
	ld t2, 280(s1)
	xor t1, t1, t2
	or t0, t0, t1
	addi t1, zero, 0
	sltu t0, t1, t0
	addi s8, zero, 1
	sub s8, s8, t0
	addi t1, zero, 0
	sub t1, t1, s8
	addi a0, s9, 0
	addi a2, s10, 0
	beqz a2, 230f
232:
	lbu t0, 0(a0)
	and t0, t0, t1
	sb t0, 0(a0)
	addi a0, a0, 1
	addi a2, a2, -1
	bnez a2, 232b
	j 231f
230:
231:
	addi a0, s8, 0
	ld ra, 208(s1)
	ld s2, 136(s1)
	ld s3, 144(s1)
	ld s4, 152(s1)
	ld s5, 160(s1)
	ld s6, 168(s1)
	ld s7, 176(s1)
	ld s8, 184(s1)
	ld s9, 192(s1)
	ld s10, 200(s1)
	ld s1, 128(s1)
	addi sp, sp, 560
	addi sp, sp, 2032
	ret
	.option pop
