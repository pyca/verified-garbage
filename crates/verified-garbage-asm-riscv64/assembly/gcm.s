// The functions of `src/gcm.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_gcm_init:
	.option push
	.option arch, +m, +c
	addi sp, sp, -2032
	addi sp, sp, -528
	addi a3, sp, 0
	sd s0, 128(a3)
	sd s1, 136(a3)
	sd s2, 144(a3)
	sd s3, 152(a3)
	sd s4, 160(a3)
	sd s5, 168(a3)
	sd s6, 176(a3)
	sd s7, 184(a3)
	sd s8, 192(a3)
	sd s9, 200(a3)
	sd s10, 208(a3)
	sd s11, 216(a3)
	sd ra, 224(a3)
	addi s0, a3, 0
	addi s2, a2, 0
	srli s3, a1, 2
	addi s3, s3, 6
	addi a3, s0, 512
	call {vg_aes_expand_key_scratch}
	addi t0, zero, 0
	sd t0, 240(s2)
	sd t0, 248(s2)
	sd t0, 96(s0)
	sd t0, 104(s0)
	addi a0, s2, 0
	addi a1, s3, 0
	addi a2, s0, 96
	addi a3, s2, 240
	addi a4, zero, 1
	addi a5, s0, 512
	call {vg_aes_ctr32}
	addi t1, s0, 0
	ld s0, 128(t1)
	ld s1, 136(t1)
	ld s2, 144(t1)
	ld s3, 152(t1)
	ld s4, 160(t1)
	ld s5, 168(t1)
	ld s6, 176(t1)
	ld s7, 184(t1)
	ld s8, 192(t1)
	ld s9, 200(t1)
	ld s10, 208(t1)
	ld s11, 216(t1)
	ld ra, 224(t1)
	addi sp, sp, 528
	addi sp, sp, 2032
	ret
	.option pop

vg_aes_gcm_stream_init:
	.option push
	.option arch, +m, +c
	addi sp, sp, -2032
	addi sp, sp, -528
	addi a4, sp, 0
	sd s0, 128(a4)
	sd s1, 136(a4)
	sd s2, 144(a4)
	sd s3, 152(a4)
	sd s4, 160(a4)
	sd s5, 168(a4)
	sd s6, 176(a4)
	sd s7, 184(a4)
	sd s8, 192(a4)
	sd s9, 200(a4)
	sd s10, 208(a4)
	sd s11, 216(a4)
	sd ra, 224(a4)
	addi s0, a4, 0
	addi s1, a3, 0
	addi s2, a0, 0
	addi s4, a1, 0
	addi s5, a2, 0
	addi s7, a2, 0
	addi a2, s5, -12
	beqz a2, 20f
	addi t0, zero, 0
	sd t0, 0(s1)
	sd t0, 8(s1)
	addi s6, zero, 0
	beqz s5, 22f
	beqz s6, 24f
	addi a2, zero, 16
	sub a2, a2, s6
	srli a3, s5, 4
	bnez a3, 26f
	sub a3, s5, a2
	srli a3, a3, 63
	bnez a3, 28f
	j 29f
28:
	addi a2, s5, 0
29:
	j 27f
26:
27:
	addi a1, s1, 32
	add a1, a1, s6
	addi a0, s4, 0
	add s4, s4, a2
	sub s5, s5, a2
	add s6, s6, a2
210:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 210b
	addi a3, s6, -16
	beqz a3, 211f
	j 212f
211:
	addi a0, s2, 240
	addi a1, s1, 0
	addi a2, s1, 32
	addi a3, zero, 1
	addi a4, s0, 512
	call {vg_ghash}
212:
	j 25f
24:
25:
	addi a2, s4, 0
	srli a3, s5, 4
	andi a5, s5, 15
	sub a6, s5, a5
	add s4, s4, a6
	addi s5, a5, 0
	beqz a3, 213f
	addi a0, s2, 240
	addi a1, s1, 0
	addi a4, s0, 512
	call {vg_ghash}
	j 214f
213:
214:
	beqz s5, 215f
	addi a0, s4, 0
	addi a1, s1, 32
	addi a2, s5, 0
217:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 217b
	j 216f
215:
216:
	j 23f
22:
23:
	andi s6, s7, 15
	beqz s6, 218f
	addi t0, zero, 0
	sd t0, 96(s0)
	sd t0, 104(s0)
	addi a0, s1, 32
	addi a1, s0, 96
	addi a2, s6, 0
220:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 220b
	addi a0, s2, 240
	addi a1, s1, 0
	addi a2, s0, 96
	addi a3, zero, 1
	addi a4, s0, 512
	call {vg_ghash}
	j 219f
218:
219:
	addi s4, zero, 0
	addi s6, s7, 0
	slli a0, s4, 3
	slli a1, s6, 3
	srli t0, a0, 56
	sb t0, 96(s0)
	srli t0, a0, 48
	sb t0, 97(s0)
	srli t0, a0, 40
	sb t0, 98(s0)
	srli t0, a0, 32
	sb t0, 99(s0)
	srli t0, a0, 24
	sb t0, 100(s0)
	srli t0, a0, 16
	sb t0, 101(s0)
	srli t0, a0, 8
	sb t0, 102(s0)
	srli t0, a0, 0
	sb t0, 103(s0)
	srli t0, a1, 56
	sb t0, 104(s0)
	srli t0, a1, 48
	sb t0, 105(s0)
	srli t0, a1, 40
	sb t0, 106(s0)
	srli t0, a1, 32
	sb t0, 107(s0)
	srli t0, a1, 24
	sb t0, 108(s0)
	srli t0, a1, 16
	sb t0, 109(s0)
	srli t0, a1, 8
	sb t0, 110(s0)
	srli t0, a1, 0
	sb t0, 111(s0)
	addi a0, s2, 240
	addi a1, s1, 0
	addi a2, s0, 96
	addi a3, zero, 1
	addi a4, s0, 512
	call {vg_ghash}
	j 21f
20:
	lbu t0, 0(s4)
	sb t0, 0(s1)
	lbu t0, 1(s4)
	sb t0, 1(s1)
	lbu t0, 2(s4)
	sb t0, 2(s1)
	lbu t0, 3(s4)
	sb t0, 3(s1)
	lbu t0, 4(s4)
	sb t0, 4(s1)
	lbu t0, 5(s4)
	sb t0, 5(s1)
	lbu t0, 6(s4)
	sb t0, 6(s1)
	lbu t0, 7(s4)
	sb t0, 7(s1)
	lbu t0, 8(s4)
	sb t0, 8(s1)
	lbu t0, 9(s4)
	sb t0, 9(s1)
	lbu t0, 10(s4)
	sb t0, 10(s1)
	lbu t0, 11(s4)
	sb t0, 11(s1)
	addi t0, zero, 0
	sb t0, 12(s1)
	addi t0, zero, 0
	sb t0, 13(s1)
	addi t0, zero, 0
	sb t0, 14(s1)
	addi t0, zero, 1
	sb t0, 15(s1)
21:
	ld t0, 0(s1)
	sd t0, 48(s1)
	lwu t0, 8(s1)
	sw t0, 56(s1)
	lbu a0, 12(s1)
	slli a0, a0, 24
	lbu t0, 13(s1)
	slli t0, t0, 16
	or a0, a0, t0
	lbu t0, 14(s1)
	slli t0, t0, 8
	or a0, a0, t0
	lbu t0, 15(s1)
	or a0, a0, t0
	addi a0, a0, 1
	srli t0, a0, 24
	sb t0, 60(s1)
	srli t0, a0, 16
	sb t0, 61(s1)
	srli t0, a0, 8
	sb t0, 62(s1)
	srli t0, a0, 0
	sb t0, 63(s1)
	addi t0, zero, 0
	sd t0, 16(s1)
	sd t0, 24(s1)
	addi t1, s0, 0
	ld s0, 128(t1)
	ld s1, 136(t1)
	ld s2, 144(t1)
	ld s3, 152(t1)
	ld s4, 160(t1)
	ld s5, 168(t1)
	ld s6, 176(t1)
	ld s7, 184(t1)
	ld s8, 192(t1)
	ld s9, 200(t1)
	ld s10, 208(t1)
	ld s11, 216(t1)
	ld ra, 224(t1)
	addi sp, sp, 528
	addi sp, sp, 2032
	ret
	.option pop

vg_aes_gcm_stream_aad:
	.option push
	.option arch, +m, +c
	addi sp, sp, -2032
	addi sp, sp, -528
	addi a5, sp, 0
	sd s0, 128(a5)
	sd s1, 136(a5)
	sd s2, 144(a5)
	sd s3, 152(a5)
	sd s4, 160(a5)
	sd s5, 168(a5)
	sd s6, 176(a5)
	sd s7, 184(a5)
	sd s8, 192(a5)
	sd s9, 200(a5)
	sd s10, 208(a5)
	sd s11, 216(a5)
	sd ra, 224(a5)
	addi s0, a5, 0
	addi s1, a1, 0
	addi s2, a0, 0
	addi s4, a3, 0
	addi s5, a4, 0
	andi s6, a2, 15
	beqz s5, 20f
	beqz s6, 22f
	addi a2, zero, 16
	sub a2, a2, s6
	srli a3, s5, 4
	bnez a3, 24f
	sub a3, s5, a2
	srli a3, a3, 63
	bnez a3, 26f
	j 27f
26:
	addi a2, s5, 0
27:
	j 25f
24:
25:
	addi a1, s1, 32
	add a1, a1, s6
	addi a0, s4, 0
	add s4, s4, a2
	sub s5, s5, a2
	add s6, s6, a2
28:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 28b
	addi a3, s6, -16
	beqz a3, 29f
	j 210f
29:
	addi a0, s2, 240
	addi a1, s1, 16
	addi a2, s1, 32
	addi a3, zero, 1
	addi a4, s0, 512
	call {vg_ghash}
210:
	j 23f
22:
23:
	addi a2, s4, 0
	srli a3, s5, 4
	andi a5, s5, 15
	sub a6, s5, a5
	add s4, s4, a6
	addi s5, a5, 0
	beqz a3, 211f
	addi a0, s2, 240
	addi a1, s1, 16
	addi a4, s0, 512
	call {vg_ghash}
	j 212f
211:
212:
	beqz s5, 213f
	addi a0, s4, 0
	addi a1, s1, 32
	addi a2, s5, 0
215:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 215b
	j 214f
213:
214:
	j 21f
20:
21:
	addi t1, s0, 0
	ld s0, 128(t1)
	ld s1, 136(t1)
	ld s2, 144(t1)
	ld s3, 152(t1)
	ld s4, 160(t1)
	ld s5, 168(t1)
	ld s6, 176(t1)
	ld s7, 184(t1)
	ld s8, 192(t1)
	ld s9, 200(t1)
	ld s10, 208(t1)
	ld s11, 216(t1)
	ld ra, 224(t1)
	addi sp, sp, 528
	addi sp, sp, 2032
	ret
	.option pop

vg_aes_gcm_stream_encrypt:
	.option push
	.option arch, +m, +c
	addi sp, sp, -2032
	addi sp, sp, -528
	addi a7, sp, 0
	sd s0, 128(a7)
	sd s1, 136(a7)
	sd s2, 144(a7)
	sd s3, 152(a7)
	sd s4, 160(a7)
	sd s5, 168(a7)
	sd s6, 176(a7)
	sd s7, 184(a7)
	sd s8, 192(a7)
	sd s9, 200(a7)
	sd s10, 208(a7)
	sd s11, 216(a7)
	sd ra, 224(a7)
	addi s0, a7, 0
	addi s1, a2, 0
	addi s2, a0, 0
	addi s3, a1, 0
	addi s10, a3, 0
	addi s11, a4, 0
	addi s9, a5, 0
	addi s8, a6, 0
	addi s4, s9, 0
	addi s5, s8, 0
	andi s6, s11, 15
	beqz s5, 20f
	beqz s6, 22f
	addi a2, zero, 16
	sub a2, a2, s6
	srli a3, s5, 4
	bnez a3, 24f
	sub a3, s5, a2
	srli a3, a3, 63
	bnez a3, 26f
	j 27f
26:
	addi a2, s5, 0
27:
	j 25f
24:
25:
	addi a0, s1, 64
	add a0, a0, s6
	addi a1, s4, 0
	add s4, s4, a2
	sub s5, s5, a2
28:
	lbu t0, 0(a1)
	lbu a3, 0(a0)
	xor t0, t0, a3
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 28b
	j 23f
22:
23:
	addi a3, s4, 0
	srli a4, s5, 4
	andi a5, s5, 15
	sub a6, s5, a5
	add s4, s4, a6
	addi s5, a5, 0
	beqz a4, 29f
	addi a0, s2, 0
	addi a1, s3, 0
	addi a2, s1, 48
	addi a5, s0, 512
	call {vg_aes_ctr32}
	j 210f
29:
210:
	beqz s5, 211f
	addi t0, zero, 0
	sd t0, 64(s1)
	sd t0, 72(s1)
	addi a3, s1, 64
	addi a4, zero, 1
	addi a0, s2, 0
	addi a1, s3, 0
	addi a2, s1, 48
	addi a5, s0, 512
	call {vg_aes_ctr32}
	addi a0, s1, 64
	addi a1, s4, 0
	addi a2, s5, 0
213:
	lbu t0, 0(a1)
	lbu a3, 0(a0)
	xor t0, t0, a3
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 213b
	j 212f
211:
212:
	j 21f
20:
21:
	beqz s8, 214f
	beqz s11, 216f
	j 217f
216:
	andi s6, s10, 15
	beqz s6, 218f
	addi t0, zero, 0
	sd t0, 96(s0)
	sd t0, 104(s0)
	addi a0, s1, 32
	addi a1, s0, 96
	addi a2, s6, 0
220:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 220b
	addi a0, s2, 240
	addi a1, s1, 16
	addi a2, s0, 96
	addi a3, zero, 1
	addi a4, s0, 512
	call {vg_ghash}
	j 219f
218:
219:
217:
	addi s4, s9, 0
	addi s5, s8, 0
	andi s6, s11, 15
	beqz s5, 221f
	beqz s6, 223f
	addi a2, zero, 16
	sub a2, a2, s6
	srli a3, s5, 4
	bnez a3, 225f
	sub a3, s5, a2
	srli a3, a3, 63
	bnez a3, 227f
	j 228f
227:
	addi a2, s5, 0
228:
	j 226f
225:
226:
	addi a1, s1, 32
	add a1, a1, s6
	addi a0, s4, 0
	add s4, s4, a2
	sub s5, s5, a2
	add s6, s6, a2
229:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 229b
	addi a3, s6, -16
	beqz a3, 230f
	j 231f
230:
	addi a0, s2, 240
	addi a1, s1, 16
	addi a2, s1, 32
	addi a3, zero, 1
	addi a4, s0, 512
	call {vg_ghash}
231:
	j 224f
223:
224:
	addi a2, s4, 0
	srli a3, s5, 4
	andi a5, s5, 15
	sub a6, s5, a5
	add s4, s4, a6
	addi s5, a5, 0
	beqz a3, 232f
	addi a0, s2, 240
	addi a1, s1, 16
	addi a4, s0, 512
	call {vg_ghash}
	j 233f
232:
233:
	beqz s5, 234f
	addi a0, s4, 0
	addi a1, s1, 32
	addi a2, s5, 0
236:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 236b
	j 235f
234:
235:
	j 222f
221:
222:
	j 215f
214:
215:
	addi t1, s0, 0
	ld s0, 128(t1)
	ld s1, 136(t1)
	ld s2, 144(t1)
	ld s3, 152(t1)
	ld s4, 160(t1)
	ld s5, 168(t1)
	ld s6, 176(t1)
	ld s7, 184(t1)
	ld s8, 192(t1)
	ld s9, 200(t1)
	ld s10, 208(t1)
	ld s11, 216(t1)
	ld ra, 224(t1)
	addi sp, sp, 528
	addi sp, sp, 2032
	ret
	.option pop

vg_aes_gcm_stream_decrypt:
	.option push
	.option arch, +m, +c
	addi sp, sp, -2032
	addi sp, sp, -528
	addi a7, sp, 0
	sd s0, 128(a7)
	sd s1, 136(a7)
	sd s2, 144(a7)
	sd s3, 152(a7)
	sd s4, 160(a7)
	sd s5, 168(a7)
	sd s6, 176(a7)
	sd s7, 184(a7)
	sd s8, 192(a7)
	sd s9, 200(a7)
	sd s10, 208(a7)
	sd s11, 216(a7)
	sd ra, 224(a7)
	addi s0, a7, 0
	addi s1, a2, 0
	addi s2, a0, 0
	addi s3, a1, 0
	addi s10, a3, 0
	addi s11, a4, 0
	addi s9, a5, 0
	addi s8, a6, 0
	beqz s8, 20f
	beqz s11, 22f
	j 23f
22:
	andi s6, s10, 15
	beqz s6, 24f
	addi t0, zero, 0
	sd t0, 96(s0)
	sd t0, 104(s0)
	addi a0, s1, 32
	addi a1, s0, 96
	addi a2, s6, 0
26:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 26b
	addi a0, s2, 240
	addi a1, s1, 16
	addi a2, s0, 96
	addi a3, zero, 1
	addi a4, s0, 512
	call {vg_ghash}
	j 25f
24:
25:
23:
	addi s4, s9, 0
	addi s5, s8, 0
	andi s6, s11, 15
	beqz s5, 27f
	beqz s6, 29f
	addi a2, zero, 16
	sub a2, a2, s6
	srli a3, s5, 4
	bnez a3, 211f
	sub a3, s5, a2
	srli a3, a3, 63
	bnez a3, 213f
	j 214f
213:
	addi a2, s5, 0
214:
	j 212f
211:
212:
	addi a1, s1, 32
	add a1, a1, s6
	addi a0, s4, 0
	add s4, s4, a2
	sub s5, s5, a2
	add s6, s6, a2
215:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 215b
	addi a3, s6, -16
	beqz a3, 216f
	j 217f
216:
	addi a0, s2, 240
	addi a1, s1, 16
	addi a2, s1, 32
	addi a3, zero, 1
	addi a4, s0, 512
	call {vg_ghash}
217:
	j 210f
29:
210:
	addi a2, s4, 0
	srli a3, s5, 4
	andi a5, s5, 15
	sub a6, s5, a5
	add s4, s4, a6
	addi s5, a5, 0
	beqz a3, 218f
	addi a0, s2, 240
	addi a1, s1, 16
	addi a4, s0, 512
	call {vg_ghash}
	j 219f
218:
219:
	beqz s5, 220f
	addi a0, s4, 0
	addi a1, s1, 32
	addi a2, s5, 0
222:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 222b
	j 221f
220:
221:
	j 28f
27:
28:
	j 21f
20:
21:
	addi s4, s9, 0
	addi s5, s8, 0
	andi s6, s11, 15
	beqz s5, 223f
	beqz s6, 225f
	addi a2, zero, 16
	sub a2, a2, s6
	srli a3, s5, 4
	bnez a3, 227f
	sub a3, s5, a2
	srli a3, a3, 63
	bnez a3, 229f
	j 230f
229:
	addi a2, s5, 0
230:
	j 228f
227:
228:
	addi a0, s1, 64
	add a0, a0, s6
	addi a1, s4, 0
	add s4, s4, a2
	sub s5, s5, a2
231:
	lbu t0, 0(a1)
	lbu a3, 0(a0)
	xor t0, t0, a3
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 231b
	j 226f
225:
226:
	addi a3, s4, 0
	srli a4, s5, 4
	andi a5, s5, 15
	sub a6, s5, a5
	add s4, s4, a6
	addi s5, a5, 0
	beqz a4, 232f
	addi a0, s2, 0
	addi a1, s3, 0
	addi a2, s1, 48
	addi a5, s0, 512
	call {vg_aes_ctr32}
	j 233f
232:
233:
	beqz s5, 234f
	addi t0, zero, 0
	sd t0, 64(s1)
	sd t0, 72(s1)
	addi a3, s1, 64
	addi a4, zero, 1
	addi a0, s2, 0
	addi a1, s3, 0
	addi a2, s1, 48
	addi a5, s0, 512
	call {vg_aes_ctr32}
	addi a0, s1, 64
	addi a1, s4, 0
	addi a2, s5, 0
236:
	lbu t0, 0(a1)
	lbu a3, 0(a0)
	xor t0, t0, a3
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 236b
	j 235f
234:
235:
	j 224f
223:
224:
	addi t1, s0, 0
	ld s0, 128(t1)
	ld s1, 136(t1)
	ld s2, 144(t1)
	ld s3, 152(t1)
	ld s4, 160(t1)
	ld s5, 168(t1)
	ld s6, 176(t1)
	ld s7, 184(t1)
	ld s8, 192(t1)
	ld s9, 200(t1)
	ld s10, 208(t1)
	ld s11, 216(t1)
	ld ra, 224(t1)
	addi sp, sp, 528
	addi sp, sp, 2032
	ret
	.option pop

vg_aes_gcm_stream_finish:
	.option push
	.option arch, +m, +c
	addi sp, sp, -2032
	addi sp, sp, -528
	addi a6, sp, 0
	sd s0, 128(a6)
	sd s1, 136(a6)
	sd s2, 144(a6)
	sd s3, 152(a6)
	sd s4, 160(a6)
	sd s5, 168(a6)
	sd s6, 176(a6)
	sd s7, 184(a6)
	sd s8, 192(a6)
	sd s9, 200(a6)
	sd s10, 208(a6)
	sd s11, 216(a6)
	sd ra, 224(a6)
	addi s0, a6, 0
	addi s1, a2, 0
	addi s2, a0, 0
	addi s3, a1, 0
	addi s10, a3, 0
	addi s11, a4, 0
	addi s9, a5, 0
	beqz s11, 20f
	andi s6, s11, 15
	j 21f
20:
	andi s6, s10, 15
21:
	beqz s6, 22f
	addi t0, zero, 0
	sd t0, 96(s0)
	sd t0, 104(s0)
	addi a0, s1, 32
	addi a1, s0, 96
	addi a2, s6, 0
24:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 24b
	addi a0, s2, 240
	addi a1, s1, 16
	addi a2, s0, 96
	addi a3, zero, 1
	addi a4, s0, 512
	call {vg_ghash}
	j 23f
22:
23:
	addi s4, s10, 0
	addi s6, s11, 0
	slli a0, s4, 3
	slli a1, s6, 3
	srli t0, a0, 56
	sb t0, 96(s0)
	srli t0, a0, 48
	sb t0, 97(s0)
	srli t0, a0, 40
	sb t0, 98(s0)
	srli t0, a0, 32
	sb t0, 99(s0)
	srli t0, a0, 24
	sb t0, 100(s0)
	srli t0, a0, 16
	sb t0, 101(s0)
	srli t0, a0, 8
	sb t0, 102(s0)
	srli t0, a0, 0
	sb t0, 103(s0)
	srli t0, a1, 56
	sb t0, 104(s0)
	srli t0, a1, 48
	sb t0, 105(s0)
	srli t0, a1, 40
	sb t0, 106(s0)
	srli t0, a1, 32
	sb t0, 107(s0)
	srli t0, a1, 24
	sb t0, 108(s0)
	srli t0, a1, 16
	sb t0, 109(s0)
	srli t0, a1, 8
	sb t0, 110(s0)
	srli t0, a1, 0
	sb t0, 111(s0)
	addi a0, s2, 240
	addi a1, s1, 16
	addi a2, s0, 96
	addi a3, zero, 1
	addi a4, s0, 512
	call {vg_ghash}
	ld t0, 16(s1)
	sd t0, 0(s0)
	ld t0, 24(s1)
	sd t0, 8(s0)
	addi a0, s2, 0
	addi a1, s3, 0
	addi a2, s1, 0
	addi a3, s0, 0
	addi a4, zero, 1
	addi a5, s0, 512
	call {vg_aes_ctr32}
	lbu t0, 0(s0)
	sb t0, 0(s9)
	lbu t0, 1(s0)
	sb t0, 1(s9)
	lbu t0, 2(s0)
	sb t0, 2(s9)
	lbu t0, 3(s0)
	sb t0, 3(s9)
	lbu t0, 4(s0)
	sb t0, 4(s9)
	lbu t0, 5(s0)
	sb t0, 5(s9)
	lbu t0, 6(s0)
	sb t0, 6(s9)
	lbu t0, 7(s0)
	sb t0, 7(s9)
	lbu t0, 8(s0)
	sb t0, 8(s9)
	lbu t0, 9(s0)
	sb t0, 9(s9)
	lbu t0, 10(s0)
	sb t0, 10(s9)
	lbu t0, 11(s0)
	sb t0, 11(s9)
	lbu t0, 12(s0)
	sb t0, 12(s9)
	lbu t0, 13(s0)
	sb t0, 13(s9)
	lbu t0, 14(s0)
	sb t0, 14(s9)
	lbu t0, 15(s0)
	sb t0, 15(s9)
	addi t1, s0, 0
	ld s0, 128(t1)
	ld s1, 136(t1)
	ld s2, 144(t1)
	ld s3, 152(t1)
	ld s4, 160(t1)
	ld s5, 168(t1)
	ld s6, 176(t1)
	ld s7, 184(t1)
	ld s8, 192(t1)
	ld s9, 200(t1)
	ld s10, 208(t1)
	ld s11, 216(t1)
	ld ra, 224(t1)
	addi sp, sp, 528
	addi sp, sp, 2032
	ret
	.option pop

vg_aes_gcm_stream_verify:
	.option push
	.option arch, +m, +c
	addi sp, sp, -2032
	addi sp, sp, -528
	addi a7, sp, 0
	sd s0, 128(a7)
	sd s1, 136(a7)
	sd s2, 144(a7)
	sd s3, 152(a7)
	sd s4, 160(a7)
	sd s5, 168(a7)
	sd s6, 176(a7)
	sd s7, 184(a7)
	sd s8, 192(a7)
	sd s9, 200(a7)
	sd s10, 208(a7)
	sd s11, 216(a7)
	sd ra, 224(a7)
	addi s0, a7, 0
	addi s1, a2, 0
	addi s2, a0, 0
	addi s3, a1, 0
	addi s10, a3, 0
	addi s11, a4, 0
	addi s9, a5, 0
	addi s8, a6, 0
	addi s5, zero, 0
	srli t0, s8, 2
	beqz t0, 20f
	srli t0, s8, 4
	beqz t0, 22f
	addi t0, s8, -16
	beqz t0, 24f
	j 25f
24:
	addi s5, zero, 1
25:
	j 23f
22:
	addi s5, zero, 1
23:
	j 21f
20:
21:
	beqz s5, 26f
	addi t0, zero, 0
	sd t0, 256(s0)
	sd t0, 264(s0)
	addi a0, s9, 0
	addi a1, s0, 256
	addi a2, s8, 0
28:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 28b
	beqz s11, 29f
	andi s6, s11, 15
	j 210f
29:
	andi s6, s10, 15
210:
	beqz s6, 211f
	addi t0, zero, 0
	sd t0, 96(s0)
	sd t0, 104(s0)
	addi a0, s1, 32
	addi a1, s0, 96
	addi a2, s6, 0
213:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 213b
	addi a0, s2, 240
	addi a1, s1, 16
	addi a2, s0, 96
	addi a3, zero, 1
	addi a4, s0, 512
	call {vg_ghash}
	j 212f
211:
212:
	addi s4, s10, 0
	addi s6, s11, 0
	slli a0, s4, 3
	slli a1, s6, 3
	srli t0, a0, 56
	sb t0, 96(s0)
	srli t0, a0, 48
	sb t0, 97(s0)
	srli t0, a0, 40
	sb t0, 98(s0)
	srli t0, a0, 32
	sb t0, 99(s0)
	srli t0, a0, 24
	sb t0, 100(s0)
	srli t0, a0, 16
	sb t0, 101(s0)
	srli t0, a0, 8
	sb t0, 102(s0)
	srli t0, a0, 0
	sb t0, 103(s0)
	srli t0, a1, 56
	sb t0, 104(s0)
	srli t0, a1, 48
	sb t0, 105(s0)
	srli t0, a1, 40
	sb t0, 106(s0)
	srli t0, a1, 32
	sb t0, 107(s0)
	srli t0, a1, 24
	sb t0, 108(s0)
	srli t0, a1, 16
	sb t0, 109(s0)
	srli t0, a1, 8
	sb t0, 110(s0)
	srli t0, a1, 0
	sb t0, 111(s0)
	addi a0, s2, 240
	addi a1, s1, 16
	addi a2, s0, 96
	addi a3, zero, 1
	addi a4, s0, 512
	call {vg_ghash}
	ld t0, 16(s1)
	sd t0, 0(s0)
	ld t0, 24(s1)
	sd t0, 8(s0)
	addi a0, s2, 0
	addi a1, s3, 0
	addi a2, s1, 0
	addi a3, s0, 0
	addi a4, zero, 1
	addi a5, s0, 512
	call {vg_aes_ctr32}
	addi t0, zero, 0
	sd t0, 272(s0)
	sd t0, 280(s0)
	addi a0, s0, 0
	addi a1, s0, 272
	addi a2, s8, 0
214:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 214b
	ld a0, 272(s0)
	ld a1, 256(s0)
	xor a0, a0, a1
	ld a1, 280(s0)
	ld a2, 264(s0)
	xor a1, a1, a2
	or a0, a0, a1
	addi a1, zero, 0
	sub a1, a1, a0
	or a0, a0, a1
	srli a0, a0, 63
	addi a1, zero, 1
	sub a0, a1, a0
	j 27f
26:
	addi a0, zero, 0
27:
	addi t1, s0, 0
	ld s0, 128(t1)
	ld s1, 136(t1)
	ld s2, 144(t1)
	ld s3, 152(t1)
	ld s4, 160(t1)
	ld s5, 168(t1)
	ld s6, 176(t1)
	ld s7, 184(t1)
	ld s8, 192(t1)
	ld s9, 200(t1)
	ld s10, 208(t1)
	ld s11, 216(t1)
	ld ra, 224(t1)
	addi sp, sp, 528
	addi sp, sp, 2032
	ret
	.option pop

vg_aes_gcm_seal:
	.option push
	.option arch, +m, +c
	addi sp, sp, -2032
	addi sp, sp, -544
	addi t0, sp, 0
	addi t1, t0, 2032
	ld t1, 544(t1)
	sd t1, 0(t0)
	addi t1, t0, 16
	sd t1, 8(t0)
	addi t1, sp, 0
	ld t1, 8(t1)
	sd s0, 128(t1)
	sd s1, 136(t1)
	sd s2, 144(t1)
	sd s3, 152(t1)
	sd s4, 160(t1)
	sd s5, 168(t1)
	sd s6, 176(t1)
	sd s7, 184(t1)
	sd s8, 192(t1)
	sd s9, 200(t1)
	sd s10, 208(t1)
	sd s11, 216(t1)
	sd ra, 224(t1)
	addi s0, t1, 0
	addi s2, a0, 0
	addi s3, a1, 0
	addi s1, s0, 16
	addi s4, a2, 0
	addi s5, a3, 0
	addi s7, a3, 0
	sd a4, 232(s0)
	addi s10, a5, 0
	sd a6, 240(s0)
	addi s11, a7, 0
	addi t1, sp, 0
	ld s9, 0(t1)
	addi a2, s5, -12
	beqz a2, 20f
	addi t0, zero, 0
	sd t0, 0(s1)
	sd t0, 8(s1)
	addi s6, zero, 0
	beqz s5, 22f
	beqz s6, 24f
	addi a2, zero, 16
	sub a2, a2, s6
	srli a3, s5, 4
	bnez a3, 26f
	sub a3, s5, a2
	srli a3, a3, 63
	bnez a3, 28f
	j 29f
28:
	addi a2, s5, 0
29:
	j 27f
26:
27:
	addi a1, s1, 32
	add a1, a1, s6
	addi a0, s4, 0
	add s4, s4, a2
	sub s5, s5, a2
	add s6, s6, a2
210:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 210b
	addi a3, s6, -16
	beqz a3, 211f
	j 212f
211:
	addi a0, s2, 240
	addi a1, s1, 0
	addi a2, s1, 32
	addi a3, zero, 1
	addi a4, s0, 512
	call {vg_ghash}
212:
	j 25f
24:
25:
	addi a2, s4, 0
	srli a3, s5, 4
	andi a5, s5, 15
	sub a6, s5, a5
	add s4, s4, a6
	addi s5, a5, 0
	beqz a3, 213f
	addi a0, s2, 240
	addi a1, s1, 0
	addi a4, s0, 512
	call {vg_ghash}
	j 214f
213:
214:
	beqz s5, 215f
	addi a0, s4, 0
	addi a1, s1, 32
	addi a2, s5, 0
217:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 217b
	j 216f
215:
216:
	j 23f
22:
23:
	andi s6, s7, 15
	beqz s6, 218f
	addi t0, zero, 0
	sd t0, 96(s0)
	sd t0, 104(s0)
	addi a0, s1, 32
	addi a1, s0, 96
	addi a2, s6, 0
220:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 220b
	addi a0, s2, 240
	addi a1, s1, 0
	addi a2, s0, 96
	addi a3, zero, 1
	addi a4, s0, 512
	call {vg_ghash}
	j 219f
218:
219:
	addi s4, zero, 0
	addi s6, s7, 0
	slli a0, s4, 3
	slli a1, s6, 3
	srli t0, a0, 56
	sb t0, 96(s0)
	srli t0, a0, 48
	sb t0, 97(s0)
	srli t0, a0, 40
	sb t0, 98(s0)
	srli t0, a0, 32
	sb t0, 99(s0)
	srli t0, a0, 24
	sb t0, 100(s0)
	srli t0, a0, 16
	sb t0, 101(s0)
	srli t0, a0, 8
	sb t0, 102(s0)
	srli t0, a0, 0
	sb t0, 103(s0)
	srli t0, a1, 56
	sb t0, 104(s0)
	srli t0, a1, 48
	sb t0, 105(s0)
	srli t0, a1, 40
	sb t0, 106(s0)
	srli t0, a1, 32
	sb t0, 107(s0)
	srli t0, a1, 24
	sb t0, 108(s0)
	srli t0, a1, 16
	sb t0, 109(s0)
	srli t0, a1, 8
	sb t0, 110(s0)
	srli t0, a1, 0
	sb t0, 111(s0)
	addi a0, s2, 240
	addi a1, s1, 0
	addi a2, s0, 96
	addi a3, zero, 1
	addi a4, s0, 512
	call {vg_ghash}
	j 21f
20:
	lbu t0, 0(s4)
	sb t0, 0(s1)
	lbu t0, 1(s4)
	sb t0, 1(s1)
	lbu t0, 2(s4)
	sb t0, 2(s1)
	lbu t0, 3(s4)
	sb t0, 3(s1)
	lbu t0, 4(s4)
	sb t0, 4(s1)
	lbu t0, 5(s4)
	sb t0, 5(s1)
	lbu t0, 6(s4)
	sb t0, 6(s1)
	lbu t0, 7(s4)
	sb t0, 7(s1)
	lbu t0, 8(s4)
	sb t0, 8(s1)
	lbu t0, 9(s4)
	sb t0, 9(s1)
	lbu t0, 10(s4)
	sb t0, 10(s1)
	lbu t0, 11(s4)
	sb t0, 11(s1)
	addi t0, zero, 0
	sb t0, 12(s1)
	addi t0, zero, 0
	sb t0, 13(s1)
	addi t0, zero, 0
	sb t0, 14(s1)
	addi t0, zero, 1
	sb t0, 15(s1)
21:
	ld t0, 0(s1)
	sd t0, 48(s1)
	lwu t0, 8(s1)
	sw t0, 56(s1)
	lbu a0, 12(s1)
	slli a0, a0, 24
	lbu t0, 13(s1)
	slli t0, t0, 16
	or a0, a0, t0
	lbu t0, 14(s1)
	slli t0, t0, 8
	or a0, a0, t0
	lbu t0, 15(s1)
	or a0, a0, t0
	addi a0, a0, 1
	srli t0, a0, 24
	sb t0, 60(s1)
	srli t0, a0, 16
	sb t0, 61(s1)
	srli t0, a0, 8
	sb t0, 62(s1)
	srli t0, a0, 0
	sb t0, 63(s1)
	addi t0, zero, 0
	sd t0, 16(s1)
	sd t0, 24(s1)
	ld s4, 232(s0)
	addi s5, s10, 0
	addi s6, zero, 0
	beqz s5, 221f
	beqz s6, 223f
	addi a2, zero, 16
	sub a2, a2, s6
	srli a3, s5, 4
	bnez a3, 225f
	sub a3, s5, a2
	srli a3, a3, 63
	bnez a3, 227f
	j 228f
227:
	addi a2, s5, 0
228:
	j 226f
225:
226:
	addi a1, s1, 32
	add a1, a1, s6
	addi a0, s4, 0
	add s4, s4, a2
	sub s5, s5, a2
	add s6, s6, a2
229:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 229b
	addi a3, s6, -16
	beqz a3, 230f
	j 231f
230:
	addi a0, s2, 240
	addi a1, s1, 16
	addi a2, s1, 32
	addi a3, zero, 1
	addi a4, s0, 512
	call {vg_ghash}
231:
	j 224f
223:
224:
	addi a2, s4, 0
	srli a3, s5, 4
	andi a5, s5, 15
	sub a6, s5, a5
	add s4, s4, a6
	addi s5, a5, 0
	beqz a3, 232f
	addi a0, s2, 240
	addi a1, s1, 16
	addi a4, s0, 512
	call {vg_ghash}
	j 233f
232:
233:
	beqz s5, 234f
	addi a0, s4, 0
	addi a1, s1, 32
	addi a2, s5, 0
236:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 236b
	j 235f
234:
235:
	j 222f
221:
222:
	andi s6, s10, 15
	beqz s6, 237f
	addi t0, zero, 0
	sd t0, 96(s0)
	sd t0, 104(s0)
	addi a0, s1, 32
	addi a1, s0, 96
	addi a2, s6, 0
239:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 239b
	addi a0, s2, 240
	addi a1, s1, 16
	addi a2, s0, 96
	addi a3, zero, 1
	addi a4, s0, 512
	call {vg_ghash}
	j 238f
237:
238:
	ld s4, 240(s0)
	addi s5, s11, 0
	addi s6, zero, 0
	beqz s5, 240f
	beqz s6, 242f
	addi a2, zero, 16
	sub a2, a2, s6
	srli a3, s5, 4
	bnez a3, 244f
	sub a3, s5, a2
	srli a3, a3, 63
	bnez a3, 246f
	j 247f
246:
	addi a2, s5, 0
247:
	j 245f
244:
245:
	addi a0, s1, 64
	add a0, a0, s6
	addi a1, s4, 0
	add s4, s4, a2
	sub s5, s5, a2
248:
	lbu t0, 0(a1)
	lbu a3, 0(a0)
	xor t0, t0, a3
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 248b
	j 243f
242:
243:
	addi a3, s4, 0
	srli a4, s5, 4
	andi a5, s5, 15
	sub a6, s5, a5
	add s4, s4, a6
	addi s5, a5, 0
	beqz a4, 249f
	addi a0, s2, 0
	addi a1, s3, 0
	addi a2, s1, 48
	addi a5, s0, 512
	call {vg_aes_ctr32}
	j 250f
249:
250:
	beqz s5, 251f
	addi t0, zero, 0
	sd t0, 64(s1)
	sd t0, 72(s1)
	addi a3, s1, 64
	addi a4, zero, 1
	addi a0, s2, 0
	addi a1, s3, 0
	addi a2, s1, 48
	addi a5, s0, 512
	call {vg_aes_ctr32}
	addi a0, s1, 64
	addi a1, s4, 0
	addi a2, s5, 0
253:
	lbu t0, 0(a1)
	lbu a3, 0(a0)
	xor t0, t0, a3
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 253b
	j 252f
251:
252:
	j 241f
240:
241:
	ld s4, 240(s0)
	addi s5, s11, 0
	addi s6, zero, 0
	beqz s5, 254f
	beqz s6, 256f
	addi a2, zero, 16
	sub a2, a2, s6
	srli a3, s5, 4
	bnez a3, 258f
	sub a3, s5, a2
	srli a3, a3, 63
	bnez a3, 260f
	j 261f
260:
	addi a2, s5, 0
261:
	j 259f
258:
259:
	addi a1, s1, 32
	add a1, a1, s6
	addi a0, s4, 0
	add s4, s4, a2
	sub s5, s5, a2
	add s6, s6, a2
262:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 262b
	addi a3, s6, -16
	beqz a3, 263f
	j 264f
263:
	addi a0, s2, 240
	addi a1, s1, 16
	addi a2, s1, 32
	addi a3, zero, 1
	addi a4, s0, 512
	call {vg_ghash}
264:
	j 257f
256:
257:
	addi a2, s4, 0
	srli a3, s5, 4
	andi a5, s5, 15
	sub a6, s5, a5
	add s4, s4, a6
	addi s5, a5, 0
	beqz a3, 265f
	addi a0, s2, 240
	addi a1, s1, 16
	addi a4, s0, 512
	call {vg_ghash}
	j 266f
265:
266:
	beqz s5, 267f
	addi a0, s4, 0
	addi a1, s1, 32
	addi a2, s5, 0
269:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 269b
	j 268f
267:
268:
	j 255f
254:
255:
	andi s6, s11, 15
	beqz s6, 270f
	addi t0, zero, 0
	sd t0, 96(s0)
	sd t0, 104(s0)
	addi a0, s1, 32
	addi a1, s0, 96
	addi a2, s6, 0
272:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 272b
	addi a0, s2, 240
	addi a1, s1, 16
	addi a2, s0, 96
	addi a3, zero, 1
	addi a4, s0, 512
	call {vg_ghash}
	j 271f
270:
271:
	addi s4, s10, 0
	addi s6, s11, 0
	slli a0, s4, 3
	slli a1, s6, 3
	srli t0, a0, 56
	sb t0, 96(s0)
	srli t0, a0, 48
	sb t0, 97(s0)
	srli t0, a0, 40
	sb t0, 98(s0)
	srli t0, a0, 32
	sb t0, 99(s0)
	srli t0, a0, 24
	sb t0, 100(s0)
	srli t0, a0, 16
	sb t0, 101(s0)
	srli t0, a0, 8
	sb t0, 102(s0)
	srli t0, a0, 0
	sb t0, 103(s0)
	srli t0, a1, 56
	sb t0, 104(s0)
	srli t0, a1, 48
	sb t0, 105(s0)
	srli t0, a1, 40
	sb t0, 106(s0)
	srli t0, a1, 32
	sb t0, 107(s0)
	srli t0, a1, 24
	sb t0, 108(s0)
	srli t0, a1, 16
	sb t0, 109(s0)
	srli t0, a1, 8
	sb t0, 110(s0)
	srli t0, a1, 0
	sb t0, 111(s0)
	addi a0, s2, 240
	addi a1, s1, 16
	addi a2, s0, 96
	addi a3, zero, 1
	addi a4, s0, 512
	call {vg_ghash}
	ld t0, 16(s1)
	sd t0, 0(s0)
	ld t0, 24(s1)
	sd t0, 8(s0)
	addi a0, s2, 0
	addi a1, s3, 0
	addi a2, s1, 0
	addi a3, s0, 0
	addi a4, zero, 1
	addi a5, s0, 512
	call {vg_aes_ctr32}
	lbu t0, 0(s0)
	sb t0, 0(s9)
	lbu t0, 1(s0)
	sb t0, 1(s9)
	lbu t0, 2(s0)
	sb t0, 2(s9)
	lbu t0, 3(s0)
	sb t0, 3(s9)
	lbu t0, 4(s0)
	sb t0, 4(s9)
	lbu t0, 5(s0)
	sb t0, 5(s9)
	lbu t0, 6(s0)
	sb t0, 6(s9)
	lbu t0, 7(s0)
	sb t0, 7(s9)
	lbu t0, 8(s0)
	sb t0, 8(s9)
	lbu t0, 9(s0)
	sb t0, 9(s9)
	lbu t0, 10(s0)
	sb t0, 10(s9)
	lbu t0, 11(s0)
	sb t0, 11(s9)
	lbu t0, 12(s0)
	sb t0, 12(s9)
	lbu t0, 13(s0)
	sb t0, 13(s9)
	lbu t0, 14(s0)
	sb t0, 14(s9)
	lbu t0, 15(s0)
	sb t0, 15(s9)
	addi t1, s0, 0
	ld s0, 128(t1)
	ld s1, 136(t1)
	ld s2, 144(t1)
	ld s3, 152(t1)
	ld s4, 160(t1)
	ld s5, 168(t1)
	ld s6, 176(t1)
	ld s7, 184(t1)
	ld s8, 192(t1)
	ld s9, 200(t1)
	ld s10, 208(t1)
	ld s11, 216(t1)
	ld ra, 224(t1)
	addi sp, sp, 544
	addi sp, sp, 2032
	ret
	.option pop

vg_aes_gcm_open:
	.option push
	.option arch, +m, +c
	addi sp, sp, -2032
	addi sp, sp, -560
	addi t0, sp, 0
	addi t1, t0, 2032
	ld t1, 560(t1)
	sd t1, 0(t0)
	addi t1, t0, 2032
	ld t1, 568(t1)
	sd t1, 8(t0)
	addi t1, t0, 24
	sd t1, 16(t0)
	addi t1, sp, 0
	ld t1, 16(t1)
	sd s0, 128(t1)
	sd s1, 136(t1)
	sd s2, 144(t1)
	sd s3, 152(t1)
	sd s4, 160(t1)
	sd s5, 168(t1)
	sd s6, 176(t1)
	sd s7, 184(t1)
	sd s8, 192(t1)
	sd s9, 200(t1)
	sd s10, 208(t1)
	sd s11, 216(t1)
	sd ra, 224(t1)
	addi s0, t1, 0
	addi s2, a0, 0
	addi s3, a1, 0
	addi s1, s0, 16
	addi s4, a2, 0
	addi s5, a3, 0
	addi s7, a3, 0
	sd a4, 232(s0)
	addi s10, a5, 0
	sd a6, 240(s0)
	addi s11, a7, 0
	addi t1, sp, 0
	ld s9, 0(t1)
	ld s8, 8(t1)
	addi s5, zero, 0
	srli t0, s8, 2
	beqz t0, 20f
	srli t0, s8, 4
	beqz t0, 22f
	addi t0, s8, -16
	beqz t0, 24f
	j 25f
24:
	addi s5, zero, 1
25:
	j 23f
22:
	addi s5, zero, 1
23:
	j 21f
20:
21:
	beqz s5, 26f
	addi s5, s7, 0
	addi a2, s5, -12
	beqz a2, 28f
	addi t0, zero, 0
	sd t0, 0(s1)
	sd t0, 8(s1)
	addi s6, zero, 0
	beqz s5, 210f
	beqz s6, 212f
	addi a2, zero, 16
	sub a2, a2, s6
	srli a3, s5, 4
	bnez a3, 214f
	sub a3, s5, a2
	srli a3, a3, 63
	bnez a3, 216f
	j 217f
216:
	addi a2, s5, 0
217:
	j 215f
214:
215:
	addi a1, s1, 32
	add a1, a1, s6
	addi a0, s4, 0
	add s4, s4, a2
	sub s5, s5, a2
	add s6, s6, a2
218:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 218b
	addi a3, s6, -16
	beqz a3, 219f
	j 220f
219:
	addi a0, s2, 240
	addi a1, s1, 0
	addi a2, s1, 32
	addi a3, zero, 1
	addi a4, s0, 512
	call {vg_ghash}
220:
	j 213f
212:
213:
	addi a2, s4, 0
	srli a3, s5, 4
	andi a5, s5, 15
	sub a6, s5, a5
	add s4, s4, a6
	addi s5, a5, 0
	beqz a3, 221f
	addi a0, s2, 240
	addi a1, s1, 0
	addi a4, s0, 512
	call {vg_ghash}
	j 222f
221:
222:
	beqz s5, 223f
	addi a0, s4, 0
	addi a1, s1, 32
	addi a2, s5, 0
225:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 225b
	j 224f
223:
224:
	j 211f
210:
211:
	andi s6, s7, 15
	beqz s6, 226f
	addi t0, zero, 0
	sd t0, 96(s0)
	sd t0, 104(s0)
	addi a0, s1, 32
	addi a1, s0, 96
	addi a2, s6, 0
228:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 228b
	addi a0, s2, 240
	addi a1, s1, 0
	addi a2, s0, 96
	addi a3, zero, 1
	addi a4, s0, 512
	call {vg_ghash}
	j 227f
226:
227:
	addi s4, zero, 0
	addi s6, s7, 0
	slli a0, s4, 3
	slli a1, s6, 3
	srli t0, a0, 56
	sb t0, 96(s0)
	srli t0, a0, 48
	sb t0, 97(s0)
	srli t0, a0, 40
	sb t0, 98(s0)
	srli t0, a0, 32
	sb t0, 99(s0)
	srli t0, a0, 24
	sb t0, 100(s0)
	srli t0, a0, 16
	sb t0, 101(s0)
	srli t0, a0, 8
	sb t0, 102(s0)
	srli t0, a0, 0
	sb t0, 103(s0)
	srli t0, a1, 56
	sb t0, 104(s0)
	srli t0, a1, 48
	sb t0, 105(s0)
	srli t0, a1, 40
	sb t0, 106(s0)
	srli t0, a1, 32
	sb t0, 107(s0)
	srli t0, a1, 24
	sb t0, 108(s0)
	srli t0, a1, 16
	sb t0, 109(s0)
	srli t0, a1, 8
	sb t0, 110(s0)
	srli t0, a1, 0
	sb t0, 111(s0)
	addi a0, s2, 240
	addi a1, s1, 0
	addi a2, s0, 96
	addi a3, zero, 1
	addi a4, s0, 512
	call {vg_ghash}
	j 29f
28:
	lbu t0, 0(s4)
	sb t0, 0(s1)
	lbu t0, 1(s4)
	sb t0, 1(s1)
	lbu t0, 2(s4)
	sb t0, 2(s1)
	lbu t0, 3(s4)
	sb t0, 3(s1)
	lbu t0, 4(s4)
	sb t0, 4(s1)
	lbu t0, 5(s4)
	sb t0, 5(s1)
	lbu t0, 6(s4)
	sb t0, 6(s1)
	lbu t0, 7(s4)
	sb t0, 7(s1)
	lbu t0, 8(s4)
	sb t0, 8(s1)
	lbu t0, 9(s4)
	sb t0, 9(s1)
	lbu t0, 10(s4)
	sb t0, 10(s1)
	lbu t0, 11(s4)
	sb t0, 11(s1)
	addi t0, zero, 0
	sb t0, 12(s1)
	addi t0, zero, 0
	sb t0, 13(s1)
	addi t0, zero, 0
	sb t0, 14(s1)
	addi t0, zero, 1
	sb t0, 15(s1)
29:
	ld t0, 0(s1)
	sd t0, 48(s1)
	lwu t0, 8(s1)
	sw t0, 56(s1)
	lbu a0, 12(s1)
	slli a0, a0, 24
	lbu t0, 13(s1)
	slli t0, t0, 16
	or a0, a0, t0
	lbu t0, 14(s1)
	slli t0, t0, 8
	or a0, a0, t0
	lbu t0, 15(s1)
	or a0, a0, t0
	addi a0, a0, 1
	srli t0, a0, 24
	sb t0, 60(s1)
	srli t0, a0, 16
	sb t0, 61(s1)
	srli t0, a0, 8
	sb t0, 62(s1)
	srli t0, a0, 0
	sb t0, 63(s1)
	addi t0, zero, 0
	sd t0, 16(s1)
	sd t0, 24(s1)
	ld s4, 232(s0)
	addi s5, s10, 0
	addi s6, zero, 0
	beqz s5, 229f
	beqz s6, 231f
	addi a2, zero, 16
	sub a2, a2, s6
	srli a3, s5, 4
	bnez a3, 233f
	sub a3, s5, a2
	srli a3, a3, 63
	bnez a3, 235f
	j 236f
235:
	addi a2, s5, 0
236:
	j 234f
233:
234:
	addi a1, s1, 32
	add a1, a1, s6
	addi a0, s4, 0
	add s4, s4, a2
	sub s5, s5, a2
	add s6, s6, a2
237:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 237b
	addi a3, s6, -16
	beqz a3, 238f
	j 239f
238:
	addi a0, s2, 240
	addi a1, s1, 16
	addi a2, s1, 32
	addi a3, zero, 1
	addi a4, s0, 512
	call {vg_ghash}
239:
	j 232f
231:
232:
	addi a2, s4, 0
	srli a3, s5, 4
	andi a5, s5, 15
	sub a6, s5, a5
	add s4, s4, a6
	addi s5, a5, 0
	beqz a3, 240f
	addi a0, s2, 240
	addi a1, s1, 16
	addi a4, s0, 512
	call {vg_ghash}
	j 241f
240:
241:
	beqz s5, 242f
	addi a0, s4, 0
	addi a1, s1, 32
	addi a2, s5, 0
244:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 244b
	j 243f
242:
243:
	j 230f
229:
230:
	andi s6, s10, 15
	beqz s6, 245f
	addi t0, zero, 0
	sd t0, 96(s0)
	sd t0, 104(s0)
	addi a0, s1, 32
	addi a1, s0, 96
	addi a2, s6, 0
247:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 247b
	addi a0, s2, 240
	addi a1, s1, 16
	addi a2, s0, 96
	addi a3, zero, 1
	addi a4, s0, 512
	call {vg_ghash}
	j 246f
245:
246:
	ld s4, 240(s0)
	addi s5, s11, 0
	addi s6, zero, 0
	beqz s5, 248f
	beqz s6, 250f
	addi a2, zero, 16
	sub a2, a2, s6
	srli a3, s5, 4
	bnez a3, 252f
	sub a3, s5, a2
	srli a3, a3, 63
	bnez a3, 254f
	j 255f
254:
	addi a2, s5, 0
255:
	j 253f
252:
253:
	addi a1, s1, 32
	add a1, a1, s6
	addi a0, s4, 0
	add s4, s4, a2
	sub s5, s5, a2
	add s6, s6, a2
256:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 256b
	addi a3, s6, -16
	beqz a3, 257f
	j 258f
257:
	addi a0, s2, 240
	addi a1, s1, 16
	addi a2, s1, 32
	addi a3, zero, 1
	addi a4, s0, 512
	call {vg_ghash}
258:
	j 251f
250:
251:
	addi a2, s4, 0
	srli a3, s5, 4
	andi a5, s5, 15
	sub a6, s5, a5
	add s4, s4, a6
	addi s5, a5, 0
	beqz a3, 259f
	addi a0, s2, 240
	addi a1, s1, 16
	addi a4, s0, 512
	call {vg_ghash}
	j 260f
259:
260:
	beqz s5, 261f
	addi a0, s4, 0
	addi a1, s1, 32
	addi a2, s5, 0
263:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 263b
	j 262f
261:
262:
	j 249f
248:
249:
	andi s6, s11, 15
	beqz s6, 264f
	addi t0, zero, 0
	sd t0, 96(s0)
	sd t0, 104(s0)
	addi a0, s1, 32
	addi a1, s0, 96
	addi a2, s6, 0
266:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 266b
	addi a0, s2, 240
	addi a1, s1, 16
	addi a2, s0, 96
	addi a3, zero, 1
	addi a4, s0, 512
	call {vg_ghash}
	j 265f
264:
265:
	addi s4, s10, 0
	addi s6, s11, 0
	slli a0, s4, 3
	slli a1, s6, 3
	srli t0, a0, 56
	sb t0, 96(s0)
	srli t0, a0, 48
	sb t0, 97(s0)
	srli t0, a0, 40
	sb t0, 98(s0)
	srli t0, a0, 32
	sb t0, 99(s0)
	srli t0, a0, 24
	sb t0, 100(s0)
	srli t0, a0, 16
	sb t0, 101(s0)
	srli t0, a0, 8
	sb t0, 102(s0)
	srli t0, a0, 0
	sb t0, 103(s0)
	srli t0, a1, 56
	sb t0, 104(s0)
	srli t0, a1, 48
	sb t0, 105(s0)
	srli t0, a1, 40
	sb t0, 106(s0)
	srli t0, a1, 32
	sb t0, 107(s0)
	srli t0, a1, 24
	sb t0, 108(s0)
	srli t0, a1, 16
	sb t0, 109(s0)
	srli t0, a1, 8
	sb t0, 110(s0)
	srli t0, a1, 0
	sb t0, 111(s0)
	addi a0, s2, 240
	addi a1, s1, 16
	addi a2, s0, 96
	addi a3, zero, 1
	addi a4, s0, 512
	call {vg_ghash}
	ld t0, 16(s1)
	sd t0, 112(s0)
	ld t0, 24(s1)
	sd t0, 120(s0)
	addi a0, s2, 0
	addi a1, s3, 0
	addi a2, s1, 0
	addi a3, s0, 112
	addi a4, zero, 1
	addi a5, s0, 512
	call {vg_aes_ctr32}
	addi t0, zero, 0
	sd t0, 256(s0)
	sd t0, 264(s0)
	addi a0, s9, 0
	addi a1, s0, 256
	addi a2, s8, 0
267:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 267b
	addi t0, zero, 0
	sd t0, 272(s0)
	sd t0, 280(s0)
	addi a0, s0, 112
	addi a1, s0, 272
	addi a2, s8, 0
268:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 268b
	ld a0, 272(s0)
	ld a1, 256(s0)
	xor a0, a0, a1
	ld a1, 280(s0)
	ld a2, 264(s0)
	xor a1, a1, a2
	or a0, a0, a1
	addi a1, zero, 0
	sub a1, a1, a0
	or a0, a0, a1
	srli a0, a0, 63
	addi a1, zero, 1
	sub a0, a1, a0
	addi s8, a0, 0
	beqz s8, 269f
	ld s4, 240(s0)
	addi s5, s11, 0
	addi s6, zero, 0
	beqz s5, 271f
	beqz s6, 273f
	addi a2, zero, 16
	sub a2, a2, s6
	srli a3, s5, 4
	bnez a3, 275f
	sub a3, s5, a2
	srli a3, a3, 63
	bnez a3, 277f
	j 278f
277:
	addi a2, s5, 0
278:
	j 276f
275:
276:
	addi a0, s1, 64
	add a0, a0, s6
	addi a1, s4, 0
	add s4, s4, a2
	sub s5, s5, a2
279:
	lbu t0, 0(a1)
	lbu a3, 0(a0)
	xor t0, t0, a3
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 279b
	j 274f
273:
274:
	addi a3, s4, 0
	srli a4, s5, 4
	andi a5, s5, 15
	sub a6, s5, a5
	add s4, s4, a6
	addi s5, a5, 0
	beqz a4, 280f
	addi a0, s2, 0
	addi a1, s3, 0
	addi a2, s1, 48
	addi a5, s0, 512
	call {vg_aes_ctr32}
	j 281f
280:
281:
	beqz s5, 282f
	addi t0, zero, 0
	sd t0, 64(s1)
	sd t0, 72(s1)
	addi a3, s1, 64
	addi a4, zero, 1
	addi a0, s2, 0
	addi a1, s3, 0
	addi a2, s1, 48
	addi a5, s0, 512
	call {vg_aes_ctr32}
	addi a0, s1, 64
	addi a1, s4, 0
	addi a2, s5, 0
284:
	lbu t0, 0(a1)
	lbu a3, 0(a0)
	xor t0, t0, a3
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 284b
	j 283f
282:
283:
	j 272f
271:
272:
	j 270f
269:
270:
	addi a0, s8, 0
	j 27f
26:
	addi a0, zero, 0
27:
	addi t1, s0, 0
	ld s0, 128(t1)
	ld s1, 136(t1)
	ld s2, 144(t1)
	ld s3, 152(t1)
	ld s4, 160(t1)
	ld s5, 168(t1)
	ld s6, 176(t1)
	ld s7, 184(t1)
	ld s8, 192(t1)
	ld s9, 200(t1)
	ld s10, 208(t1)
	ld s11, 216(t1)
	ld ra, 224(t1)
	addi sp, sp, 560
	addi sp, sp, 2032
	ret
	.option pop

vg_aes_gcm_seal_gather:
	.option push
	.option arch, +m, +c
	addi sp, sp, -16
	sd ra, 8(sp)
	addi t0, sp, 0
	ld t1, 32(t0)
	sd t1, 0(t0)
	addi t5, a4, 0
	addi t6, a5, 0
	addi a4, a6, 0
	addi a5, a7, 0
	ld a6, 16(t0)
	ld a7, 24(t0)
	beqz a5, 20f
22:
	lbu t0, 0(a4)
	lbu t3, 1(a4)
	slli t3, t3, 8
	or t0, t0, t3
	lbu t3, 2(a4)
	slli t3, t3, 16
	or t0, t0, t3
	lbu t3, 3(a4)
	slli t3, t3, 24
	or t0, t0, t3
	lbu t4, 4(a4)
	lbu t3, 5(a4)
	slli t3, t3, 8
	or t4, t4, t3
	lbu t3, 6(a4)
	slli t3, t3, 16
	or t4, t4, t3
	lbu t3, 7(a4)
	slli t3, t3, 24
	or t4, t4, t3
	slli t4, t4, 32
	or t0, t0, t4
	lbu t1, 8(a4)
	lbu t3, 9(a4)
	slli t3, t3, 8
	or t1, t1, t3
	lbu t3, 10(a4)
	slli t3, t3, 16
	or t1, t1, t3
	lbu t3, 11(a4)
	slli t3, t3, 24
	or t1, t1, t3
	lbu t4, 12(a4)
	lbu t3, 13(a4)
	slli t3, t3, 8
	or t4, t4, t3
	lbu t3, 14(a4)
	slli t3, t3, 16
	or t4, t4, t3
	lbu t3, 15(a4)
	slli t3, t3, 24
	or t4, t4, t3
	slli t4, t4, 32
	or t1, t1, t4
	addi a4, a4, 16
	beqz t1, 23f
25:
	lbu t2, 0(t0)
	sb t2, 0(a6)
	addi t0, t0, 1
	addi a6, a6, 1
	addi t1, t1, -1
	bnez t1, 25b
	j 24f
23:
24:
	addi a5, a5, -1
	bnez a5, 22b
	j 21f
20:
21:
	addi a4, t5, 0
	addi a5, t6, 0
	addi t0, sp, 0
	ld a6, 16(t0)
	call {vg_aes_gcm_seal}
	ld ra, 8(sp)
	addi sp, sp, 16
	ret
	.option pop

vg_ghash:
	.option push
	.option arch, +m, +c
	beqz a3, 20f
	addi sp, sp, -2032
	addi sp, sp, -16
	lbu a6, 0(a0)
	slli a6, a6, 8
	lbu t3, 1(a0)
	or a6, a6, t3
	slli a6, a6, 8
	lbu t3, 2(a0)
	or a6, a6, t3
	slli a6, a6, 8
	lbu t3, 3(a0)
	or a6, a6, t3
	slli a6, a6, 8
	lbu t3, 4(a0)
	or a6, a6, t3
	slli a6, a6, 8
	lbu t3, 5(a0)
	or a6, a6, t3
	slli a6, a6, 8
	lbu t3, 6(a0)
	or a6, a6, t3
	slli a6, a6, 8
	lbu t3, 7(a0)
	or a6, a6, t3
	lbu a7, 8(a0)
	slli a7, a7, 8
	lbu t3, 9(a0)
	or a7, a7, t3
	slli a7, a7, 8
	lbu t3, 10(a0)
	or a7, a7, t3
	slli a7, a7, 8
	lbu t3, 11(a0)
	or a7, a7, t3
	slli a7, a7, 8
	lbu t3, 12(a0)
	or a7, a7, t3
	slli a7, a7, 8
	lbu t3, 13(a0)
	or a7, a7, t3
	slli a7, a7, 8
	lbu t3, 14(a0)
	or a7, a7, t3
	slli a7, a7, 8
	lbu t3, 15(a0)
	or a7, a7, t3
	addi t6, zero, -31
	slli t6, t6, 56
	addi t4, sp, 0
	addi t5, t4, 1024
	addi t5, t5, 1024
22:
	sd a6, 0(t4)
	sd a7, 8(t4)
	slli t2, a7, 63
	srai t2, t2, 63
	and t2, t2, t6
	slli t3, a6, 63
	srli a7, a7, 1
	or a7, a7, t3
	srli a6, a6, 1
	xor a6, a6, t2
	sd a6, 16(t4)
	sd a7, 24(t4)
	slli t2, a7, 63
	srai t2, t2, 63
	and t2, t2, t6
	slli t3, a6, 63
	srli a7, a7, 1
	or a7, a7, t3
	srli a6, a6, 1
	xor a6, a6, t2
	sd a6, 32(t4)
	sd a7, 40(t4)
	slli t2, a7, 63
	srai t2, t2, 63
	and t2, t2, t6
	slli t3, a6, 63
	srli a7, a7, 1
	or a7, a7, t3
	srli a6, a6, 1
	xor a6, a6, t2
	sd a6, 48(t4)
	sd a7, 56(t4)
	slli t2, a7, 63
	srai t2, t2, 63
	and t2, t2, t6
	slli t3, a6, 63
	srli a7, a7, 1
	or a7, a7, t3
	srli a6, a6, 1
	xor a6, a6, t2
	sd a6, 64(t4)
	sd a7, 72(t4)
	slli t2, a7, 63
	srai t2, t2, 63
	and t2, t2, t6
	slli t3, a6, 63
	srli a7, a7, 1
	or a7, a7, t3
	srli a6, a6, 1
	xor a6, a6, t2
	sd a6, 80(t4)
	sd a7, 88(t4)
	slli t2, a7, 63
	srai t2, t2, 63
	and t2, t2, t6
	slli t3, a6, 63
	srli a7, a7, 1
	or a7, a7, t3
	srli a6, a6, 1
	xor a6, a6, t2
	sd a6, 96(t4)
	sd a7, 104(t4)
	slli t2, a7, 63
	srai t2, t2, 63
	and t2, t2, t6
	slli t3, a6, 63
	srli a7, a7, 1
	or a7, a7, t3
	srli a6, a6, 1
	xor a6, a6, t2
	sd a6, 112(t4)
	sd a7, 120(t4)
	slli t2, a7, 63
	srai t2, t2, 63
	and t2, t2, t6
	slli t3, a6, 63
	srli a7, a7, 1
	or a7, a7, t3
	srli a6, a6, 1
	xor a6, a6, t2
	addi t4, t4, 128
	bne t4, t5, 22b
	lbu a4, 0(a1)
	slli a4, a4, 8
	lbu t3, 1(a1)
	or a4, a4, t3
	slli a4, a4, 8
	lbu t3, 2(a1)
	or a4, a4, t3
	slli a4, a4, 8
	lbu t3, 3(a1)
	or a4, a4, t3
	slli a4, a4, 8
	lbu t3, 4(a1)
	or a4, a4, t3
	slli a4, a4, 8
	lbu t3, 5(a1)
	or a4, a4, t3
	slli a4, a4, 8
	lbu t3, 6(a1)
	or a4, a4, t3
	slli a4, a4, 8
	lbu t3, 7(a1)
	or a4, a4, t3
	lbu a5, 8(a1)
	slli a5, a5, 8
	lbu t3, 9(a1)
	or a5, a5, t3
	slli a5, a5, 8
	lbu t3, 10(a1)
	or a5, a5, t3
	slli a5, a5, 8
	lbu t3, 11(a1)
	or a5, a5, t3
	slli a5, a5, 8
	lbu t3, 12(a1)
	or a5, a5, t3
	slli a5, a5, 8
	lbu t3, 13(a1)
	or a5, a5, t3
	slli a5, a5, 8
	lbu t3, 14(a1)
	or a5, a5, t3
	slli a5, a5, 8
	lbu t3, 15(a1)
	or a5, a5, t3
23:
	lbu a6, 0(a2)
	slli a6, a6, 8
	lbu t3, 1(a2)
	or a6, a6, t3
	slli a6, a6, 8
	lbu t3, 2(a2)
	or a6, a6, t3
	slli a6, a6, 8
	lbu t3, 3(a2)
	or a6, a6, t3
	slli a6, a6, 8
	lbu t3, 4(a2)
	or a6, a6, t3
	slli a6, a6, 8
	lbu t3, 5(a2)
	or a6, a6, t3
	slli a6, a6, 8
	lbu t3, 6(a2)
	or a6, a6, t3
	slli a6, a6, 8
	lbu t3, 7(a2)
	or a6, a6, t3
	lbu a7, 8(a2)
	slli a7, a7, 8
	lbu t3, 9(a2)
	or a7, a7, t3
	slli a7, a7, 8
	lbu t3, 10(a2)
	or a7, a7, t3
	slli a7, a7, 8
	lbu t3, 11(a2)
	or a7, a7, t3
	slli a7, a7, 8
	lbu t3, 12(a2)
	or a7, a7, t3
	slli a7, a7, 8
	lbu t3, 13(a2)
	or a7, a7, t3
	slli a7, a7, 8
	lbu t3, 14(a2)
	or a7, a7, t3
	slli a7, a7, 8
	lbu t3, 15(a2)
	or a7, a7, t3
	xor a6, a6, a4
	xor a7, a7, a5
	addi a4, zero, 0
	addi a5, zero, 0
	addi t4, sp, 0
24:
	slli t2, a6, 0
	srai t2, t2, 63
	ld t0, 0(t4)
	ld t1, 8(t4)
	and t0, t0, t2
	and t1, t1, t2
	xor a4, a4, t0
	xor a5, a5, t1
	slli t2, a6, 1
	srai t2, t2, 63
	ld t0, 16(t4)
	ld t1, 24(t4)
	and t0, t0, t2
	and t1, t1, t2
	xor a4, a4, t0
	xor a5, a5, t1
	slli t2, a6, 2
	srai t2, t2, 63
	ld t0, 32(t4)
	ld t1, 40(t4)
	and t0, t0, t2
	and t1, t1, t2
	xor a4, a4, t0
	xor a5, a5, t1
	slli t2, a6, 3
	srai t2, t2, 63
	ld t0, 48(t4)
	ld t1, 56(t4)
	and t0, t0, t2
	and t1, t1, t2
	xor a4, a4, t0
	xor a5, a5, t1
	slli t2, a6, 4
	srai t2, t2, 63
	ld t0, 64(t4)
	ld t1, 72(t4)
	and t0, t0, t2
	and t1, t1, t2
	xor a4, a4, t0
	xor a5, a5, t1
	slli t2, a6, 5
	srai t2, t2, 63
	ld t0, 80(t4)
	ld t1, 88(t4)
	and t0, t0, t2
	and t1, t1, t2
	xor a4, a4, t0
	xor a5, a5, t1
	slli t2, a6, 6
	srai t2, t2, 63
	ld t0, 96(t4)
	ld t1, 104(t4)
	and t0, t0, t2
	and t1, t1, t2
	xor a4, a4, t0
	xor a5, a5, t1
	slli t2, a6, 7
	srai t2, t2, 63
	ld t0, 112(t4)
	ld t1, 120(t4)
	and t0, t0, t2
	and t1, t1, t2
	xor a4, a4, t0
	xor a5, a5, t1
	slli a6, a6, 8
	srli t3, a7, 56
	or a6, a6, t3
	slli a7, a7, 8
	addi t4, t4, 128
	bne t4, t5, 24b
	addi a2, a2, 16
	addi a3, a3, -1
	bnez a3, 23b
	srli t3, a4, 56
	sb t3, 0(a1)
	srli t3, a4, 48
	sb t3, 1(a1)
	srli t3, a4, 40
	sb t3, 2(a1)
	srli t3, a4, 32
	sb t3, 3(a1)
	srli t3, a4, 24
	sb t3, 4(a1)
	srli t3, a4, 16
	sb t3, 5(a1)
	srli t3, a4, 8
	sb t3, 6(a1)
	srli t3, a4, 0
	sb t3, 7(a1)
	srli t3, a5, 56
	sb t3, 8(a1)
	srli t3, a5, 48
	sb t3, 9(a1)
	srli t3, a5, 40
	sb t3, 10(a1)
	srli t3, a5, 32
	sb t3, 11(a1)
	srli t3, a5, 24
	sb t3, 12(a1)
	srli t3, a5, 16
	sb t3, 13(a1)
	srli t3, a5, 8
	sb t3, 14(a1)
	srli t3, a5, 0
	sb t3, 15(a1)
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
	sd t6, 224(t5)
	sd t6, 232(t5)
	sd t6, 240(t5)
	sd t6, 248(t5)
	sd t6, 256(t5)
	sd t6, 264(t5)
	sd t6, 272(t5)
	sd t6, 280(t5)
	sd t6, 288(t5)
	sd t6, 296(t5)
	sd t6, 304(t5)
	sd t6, 312(t5)
	sd t6, 320(t5)
	sd t6, 328(t5)
	sd t6, 336(t5)
	sd t6, 344(t5)
	sd t6, 352(t5)
	sd t6, 360(t5)
	sd t6, 368(t5)
	sd t6, 376(t5)
	sd t6, 384(t5)
	sd t6, 392(t5)
	sd t6, 400(t5)
	sd t6, 408(t5)
	sd t6, 416(t5)
	sd t6, 424(t5)
	sd t6, 432(t5)
	sd t6, 440(t5)
	sd t6, 448(t5)
	sd t6, 456(t5)
	sd t6, 464(t5)
	sd t6, 472(t5)
	sd t6, 480(t5)
	sd t6, 488(t5)
	sd t6, 496(t5)
	sd t6, 504(t5)
	sd t6, 512(t5)
	sd t6, 520(t5)
	sd t6, 528(t5)
	sd t6, 536(t5)
	sd t6, 544(t5)
	sd t6, 552(t5)
	sd t6, 560(t5)
	sd t6, 568(t5)
	sd t6, 576(t5)
	sd t6, 584(t5)
	sd t6, 592(t5)
	sd t6, 600(t5)
	sd t6, 608(t5)
	sd t6, 616(t5)
	sd t6, 624(t5)
	sd t6, 632(t5)
	sd t6, 640(t5)
	sd t6, 648(t5)
	sd t6, 656(t5)
	sd t6, 664(t5)
	sd t6, 672(t5)
	sd t6, 680(t5)
	sd t6, 688(t5)
	sd t6, 696(t5)
	sd t6, 704(t5)
	sd t6, 712(t5)
	sd t6, 720(t5)
	sd t6, 728(t5)
	sd t6, 736(t5)
	sd t6, 744(t5)
	sd t6, 752(t5)
	sd t6, 760(t5)
	sd t6, 768(t5)
	sd t6, 776(t5)
	sd t6, 784(t5)
	sd t6, 792(t5)
	sd t6, 800(t5)
	sd t6, 808(t5)
	sd t6, 816(t5)
	sd t6, 824(t5)
	sd t6, 832(t5)
	sd t6, 840(t5)
	sd t6, 848(t5)
	sd t6, 856(t5)
	sd t6, 864(t5)
	sd t6, 872(t5)
	sd t6, 880(t5)
	sd t6, 888(t5)
	sd t6, 896(t5)
	sd t6, 904(t5)
	sd t6, 912(t5)
	sd t6, 920(t5)
	sd t6, 928(t5)
	sd t6, 936(t5)
	sd t6, 944(t5)
	sd t6, 952(t5)
	sd t6, 960(t5)
	sd t6, 968(t5)
	sd t6, 976(t5)
	sd t6, 984(t5)
	sd t6, 992(t5)
	sd t6, 1000(t5)
	sd t6, 1008(t5)
	sd t6, 1016(t5)
	sd t6, 1024(t5)
	sd t6, 1032(t5)
	sd t6, 1040(t5)
	sd t6, 1048(t5)
	sd t6, 1056(t5)
	sd t6, 1064(t5)
	sd t6, 1072(t5)
	sd t6, 1080(t5)
	sd t6, 1088(t5)
	sd t6, 1096(t5)
	sd t6, 1104(t5)
	sd t6, 1112(t5)
	sd t6, 1120(t5)
	sd t6, 1128(t5)
	sd t6, 1136(t5)
	sd t6, 1144(t5)
	sd t6, 1152(t5)
	sd t6, 1160(t5)
	sd t6, 1168(t5)
	sd t6, 1176(t5)
	sd t6, 1184(t5)
	sd t6, 1192(t5)
	sd t6, 1200(t5)
	sd t6, 1208(t5)
	sd t6, 1216(t5)
	sd t6, 1224(t5)
	sd t6, 1232(t5)
	sd t6, 1240(t5)
	sd t6, 1248(t5)
	sd t6, 1256(t5)
	sd t6, 1264(t5)
	sd t6, 1272(t5)
	sd t6, 1280(t5)
	sd t6, 1288(t5)
	sd t6, 1296(t5)
	sd t6, 1304(t5)
	sd t6, 1312(t5)
	sd t6, 1320(t5)
	sd t6, 1328(t5)
	sd t6, 1336(t5)
	sd t6, 1344(t5)
	sd t6, 1352(t5)
	sd t6, 1360(t5)
	sd t6, 1368(t5)
	sd t6, 1376(t5)
	sd t6, 1384(t5)
	sd t6, 1392(t5)
	sd t6, 1400(t5)
	sd t6, 1408(t5)
	sd t6, 1416(t5)
	sd t6, 1424(t5)
	sd t6, 1432(t5)
	sd t6, 1440(t5)
	sd t6, 1448(t5)
	sd t6, 1456(t5)
	sd t6, 1464(t5)
	sd t6, 1472(t5)
	sd t6, 1480(t5)
	sd t6, 1488(t5)
	sd t6, 1496(t5)
	sd t6, 1504(t5)
	sd t6, 1512(t5)
	sd t6, 1520(t5)
	sd t6, 1528(t5)
	sd t6, 1536(t5)
	sd t6, 1544(t5)
	sd t6, 1552(t5)
	sd t6, 1560(t5)
	sd t6, 1568(t5)
	sd t6, 1576(t5)
	sd t6, 1584(t5)
	sd t6, 1592(t5)
	sd t6, 1600(t5)
	sd t6, 1608(t5)
	sd t6, 1616(t5)
	sd t6, 1624(t5)
	sd t6, 1632(t5)
	sd t6, 1640(t5)
	sd t6, 1648(t5)
	sd t6, 1656(t5)
	sd t6, 1664(t5)
	sd t6, 1672(t5)
	sd t6, 1680(t5)
	sd t6, 1688(t5)
	sd t6, 1696(t5)
	sd t6, 1704(t5)
	sd t6, 1712(t5)
	sd t6, 1720(t5)
	sd t6, 1728(t5)
	sd t6, 1736(t5)
	sd t6, 1744(t5)
	sd t6, 1752(t5)
	sd t6, 1760(t5)
	sd t6, 1768(t5)
	sd t6, 1776(t5)
	sd t6, 1784(t5)
	sd t6, 1792(t5)
	sd t6, 1800(t5)
	sd t6, 1808(t5)
	sd t6, 1816(t5)
	sd t6, 1824(t5)
	sd t6, 1832(t5)
	sd t6, 1840(t5)
	sd t6, 1848(t5)
	sd t6, 1856(t5)
	sd t6, 1864(t5)
	sd t6, 1872(t5)
	sd t6, 1880(t5)
	sd t6, 1888(t5)
	sd t6, 1896(t5)
	sd t6, 1904(t5)
	sd t6, 1912(t5)
	sd t6, 1920(t5)
	sd t6, 1928(t5)
	sd t6, 1936(t5)
	sd t6, 1944(t5)
	sd t6, 1952(t5)
	sd t6, 1960(t5)
	sd t6, 1968(t5)
	sd t6, 1976(t5)
	sd t6, 1984(t5)
	sd t6, 1992(t5)
	sd t6, 2000(t5)
	sd t6, 2008(t5)
	sd t6, 2016(t5)
	sd t6, 2024(t5)
	sd t6, 2032(t5)
	sd t6, 2040(t5)
	addi sp, sp, 16
	addi sp, sp, 2032
	j 21f
20:
21:
	ret
	.option pop
