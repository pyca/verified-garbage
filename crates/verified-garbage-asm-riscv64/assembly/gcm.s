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

vg_aes_gcm_open_to:
	.option push
	.option arch, +m, +c
	addi sp, sp, -2032
	addi sp, sp, -576
	addi t0, sp, 0
	addi t1, t0, 2032
	ld t1, 576(t1)
	sd t1, 0(t0)
	addi t1, t0, 2032
	ld t1, 584(t1)
	sd t1, 8(t0)
	addi t1, t0, 2032
	ld t1, 592(t1)
	sd t1, 16(t0)
	addi t1, t0, 2032
	ld t1, 600(t1)
	sd t1, 24(t0)
	addi t1, t0, 40
	sd t1, 32(t0)
	addi t1, sp, 0
	ld t1, 32(t1)
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
	ld s9, 16(t1)
	ld s8, 24(t1)
	ld t2, 0(t1)
	sub t2, t2, a6
	sd t2, 248(s0)
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
	ld s9, 248(s0)
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
	add a4, s9, s4
	add s4, s4, a2
	sub s5, s5, a2
279:
	lbu t0, 0(a1)
	lbu a3, 0(a0)
	xor t0, t0, a3
	sb t0, 0(a4)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a4, a4, 1
	addi a2, a2, -1
	bnez a2, 279b
	j 274f
273:
274:
	add a3, s9, s4
	addi a6, s4, 0
	srli a4, s5, 4
	andi a5, s5, 15
	sub a7, s5, a5
	add s4, s4, a7
	addi s5, a5, 0
	beqz a4, 280f
	addi a0, s2, 0
	addi a1, s3, 0
	addi a2, s1, 48
	addi a5, s0, 512
	call {vg_aes_ctr32_to}
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
	add a4, s9, s4
	addi a2, s5, 0
284:
	lbu t0, 0(a1)
	lbu a3, 0(a0)
	xor t0, t0, a3
	sb t0, 0(a4)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a4, a4, 1
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
	beqz a0, 285f
	j 286f
285:
	ld t2, 240(s0)
	ld t3, 248(s0)
	add t2, t2, t3
	addi t3, s11, 0
	addi t1, zero, 0
	beqz t3, 287f
289:
	sb t1, 0(t2)
	addi t2, t2, 1
	addi t3, t3, -1
	bnez t3, 289b
	j 288f
287:
288:
286:
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
	addi sp, sp, 576
	addi sp, sp, 2032
	ret
	.option pop

vg_aes_gcm_bitslice:
	.option push
	.option arch, +m, +c
	addi sp, sp, -2032
	addi sp, sp, -16
	addi a2, sp, 0
	addi a5, a2, 0
	addi a5, a5, 7
	andi a5, a5, -8
	sd s0, 320(a5)
	sd s1, 328(a5)
	sd s2, 336(a5)
	sd s3, 344(a5)
	sd s4, 352(a5)
	sd s5, 360(a5)
	sd s6, 368(a5)
	sd s7, 376(a5)
	sd s8, 384(a5)
	sd s9, 392(a5)
	sd s10, 400(a5)
	sd s11, 408(a5)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 416(a5)
	lui t0, 16
	addiw t0, t0, -256
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, -256
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 424(a5)
	lui t0, 4080
	addiw t0, t0, 255
	slli t0, t0, 32
	lui t1, 4080
	addiw t1, t1, 255
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 432(a5)
	lui t0, 349525
	addiw t0, t0, 1365
	slli t0, t0, 32
	lui t1, 349525
	addiw t1, t1, 1365
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 440(a5)
	lui t0, 209715
	addiw t0, t0, 819
	slli t0, t0, 32
	lui t1, 209715
	addiw t1, t1, 819
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 448(a5)
	lui t0, 61681
	addiw t0, t0, -241
	slli t0, t0, 32
	lui t1, 61681
	addiw t1, t1, -241
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 456(a5)
	lui t0, 16
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, -1
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 512(a5)
	lui t0, 65520
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 65520
	addiw t1, t1, 0
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 520(a5)
	lui t0, 983040
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 983040
	addiw t1, t1, 0
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 528(a5)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 536(a5)
	lui t0, 4080
	addiw t0, t0, 255
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 544(a5)
	lui t0, 1044496
	addiw t0, t0, -256
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 552(a5)
	lui t0, 16
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, -1
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 560(a5)
	lui t0, 1048320
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048320
	addiw t1, t1, 0
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 568(a5)
	lui t0, 240
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 240
	addiw t1, t1, 0
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 576(a5)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 584(a5)
	lui t0, 4080
	addiw t0, t0, 255
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 592(a5)
	lui t0, 1044496
	addiw t0, t0, -256
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 600(a5)
	addi a3, a0, 0
	addi a4, a1, 0
	addi a1, zero, 14
	slli t0, a1, 4
	add a0, a0, t0
	addi a2, a5, 1920
	addi a1, a1, 1
20:
	lbu s0, 0(a0)
	lbu t0, 1(a0)
	slli t0, t0, 8
	or s0, s0, t0
	lbu t0, 2(a0)
	slli t0, t0, 16
	or s0, s0, t0
	lbu t0, 3(a0)
	slli t0, t0, 24
	or s0, s0, t0
	lbu t1, 4(a0)
	lbu t0, 5(a0)
	slli t0, t0, 8
	or t1, t1, t0
	lbu t0, 6(a0)
	slli t0, t0, 16
	or t1, t1, t0
	lbu t0, 7(a0)
	slli t0, t0, 24
	or t1, t1, t0
	slli t1, t1, 32
	or s0, s0, t1
	lbu s4, 8(a0)
	lbu t0, 9(a0)
	slli t0, t0, 8
	or s4, s4, t0
	lbu t0, 10(a0)
	slli t0, t0, 16
	or s4, s4, t0
	lbu t0, 11(a0)
	slli t0, t0, 24
	or s4, s4, t0
	lbu t1, 12(a0)
	lbu t0, 13(a0)
	slli t0, t0, 8
	or t1, t1, t0
	lbu t0, 14(a0)
	slli t0, t0, 16
	or t1, t1, t0
	lbu t0, 15(a0)
	slli t0, t0, 24
	or t1, t1, t0
	slli t1, t1, 32
	or s4, s4, t1
	addi s1, s0, 0
	addi s2, s0, 0
	addi s3, s0, 0
	addi s5, s4, 0
	addi s6, s4, 0
	addi s7, s4, 0
	ld t3, 416(a5)
	ld t4, 424(a5)
	ld t5, 432(a5)
	ld t6, 440(a5)
	ld a6, 448(a5)
	ld a7, 456(a5)
	srli t0, s0, 16
	xor t0, t0, s0
	and t0, t0, t3
	xor s0, s0, t0
	slli t0, t0, 16
	xor s0, s0, t0
	srli t0, s1, 16
	xor t0, t0, s1
	and t0, t0, t3
	xor s1, s1, t0
	slli t0, t0, 16
	xor s1, s1, t0
	srli t0, s2, 16
	xor t0, t0, s2
	and t0, t0, t3
	xor s2, s2, t0
	slli t0, t0, 16
	xor s2, s2, t0
	srli t0, s3, 16
	xor t0, t0, s3
	and t0, t0, t3
	xor s3, s3, t0
	slli t0, t0, 16
	xor s3, s3, t0
	srli t0, s4, 16
	xor t0, t0, s4
	and t0, t0, t3
	xor s4, s4, t0
	slli t0, t0, 16
	xor s4, s4, t0
	srli t0, s5, 16
	xor t0, t0, s5
	and t0, t0, t3
	xor s5, s5, t0
	slli t0, t0, 16
	xor s5, s5, t0
	srli t0, s6, 16
	xor t0, t0, s6
	and t0, t0, t3
	xor s6, s6, t0
	slli t0, t0, 16
	xor s6, s6, t0
	srli t0, s7, 16
	xor t0, t0, s7
	and t0, t0, t3
	xor s7, s7, t0
	slli t0, t0, 16
	xor s7, s7, t0
	srli t0, s0, 8
	xor t0, t0, s0
	and t0, t0, t4
	xor s0, s0, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s1
	and t0, t0, t4
	xor s1, s1, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s2
	and t0, t0, t4
	xor s2, s2, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s3
	and t0, t0, t4
	xor s3, s3, t0
	slli t0, t0, 8
	xor s3, s3, t0
	srli t0, s4, 8
	xor t0, t0, s4
	and t0, t0, t4
	xor s4, s4, t0
	slli t0, t0, 8
	xor s4, s4, t0
	srli t0, s5, 8
	xor t0, t0, s5
	and t0, t0, t4
	xor s5, s5, t0
	slli t0, t0, 8
	xor s5, s5, t0
	srli t0, s6, 8
	xor t0, t0, s6
	and t0, t0, t4
	xor s6, s6, t0
	slli t0, t0, 8
	xor s6, s6, t0
	srli t0, s7, 8
	xor t0, t0, s7
	and t0, t0, t4
	xor s7, s7, t0
	slli t0, t0, 8
	xor s7, s7, t0
	srli t0, s0, 8
	xor t0, t0, s4
	and t0, t0, t5
	xor s4, s4, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s5
	and t0, t0, t5
	xor s5, s5, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s6
	and t0, t0, t5
	xor s6, s6, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s7
	and t0, t0, t5
	xor s7, s7, t0
	slli t0, t0, 8
	xor s3, s3, t0
	srli t0, s0, 1
	xor t0, t0, s1
	and t0, t0, t6
	xor s1, s1, t0
	slli t0, t0, 1
	xor s0, s0, t0
	srli t0, s2, 1
	xor t0, t0, s3
	and t0, t0, t6
	xor s3, s3, t0
	slli t0, t0, 1
	xor s2, s2, t0
	srli t0, s4, 1
	xor t0, t0, s5
	and t0, t0, t6
	xor s5, s5, t0
	slli t0, t0, 1
	xor s4, s4, t0
	srli t0, s6, 1
	xor t0, t0, s7
	and t0, t0, t6
	xor s7, s7, t0
	slli t0, t0, 1
	xor s6, s6, t0
	srli t0, s0, 2
	xor t0, t0, s2
	and t0, t0, a6
	xor s2, s2, t0
	slli t0, t0, 2
	xor s0, s0, t0
	srli t0, s1, 2
	xor t0, t0, s3
	and t0, t0, a6
	xor s3, s3, t0
	slli t0, t0, 2
	xor s1, s1, t0
	srli t0, s4, 2
	xor t0, t0, s6
	and t0, t0, a6
	xor s6, s6, t0
	slli t0, t0, 2
	xor s4, s4, t0
	srli t0, s5, 2
	xor t0, t0, s7
	and t0, t0, a6
	xor s7, s7, t0
	slli t0, t0, 2
	xor s5, s5, t0
	srli t0, s0, 4
	xor t0, t0, s4
	and t0, t0, a7
	xor s4, s4, t0
	slli t0, t0, 4
	xor s0, s0, t0
	srli t0, s1, 4
	xor t0, t0, s5
	and t0, t0, a7
	xor s5, s5, t0
	slli t0, t0, 4
	xor s1, s1, t0
	srli t0, s2, 4
	xor t0, t0, s6
	and t0, t0, a7
	xor s6, s6, t0
	slli t0, t0, 4
	xor s2, s2, t0
	srli t0, s3, 4
	xor t0, t0, s7
	and t0, t0, a7
	xor s7, s7, t0
	slli t0, t0, 4
	xor s3, s3, t0
	sd s0, 0(a2)
	sd s1, 8(a2)
	sd s2, 16(a2)
	sd s3, 24(a2)
	sd s4, 32(a2)
	sd s5, 40(a2)
	sd s6, 48(a2)
	sd s7, 56(a2)
	addi a0, a0, -16
	addi a2, a2, -64
	addi a1, a1, -1
	bnez a1, 20b
	addi a0, a5, 1024
	addi a1, a4, 0
	addi a2, zero, 120
21:
	ld t0, 0(a0)
	sd t0, 0(a1)
	addi a0, a0, 8
	addi a1, a1, 8
	addi a2, a2, -1
	bnez a2, 21b
	addi a0, a3, 240
	addi s9, a4, 960
	lbu t0, 0(a0)
	slli t0, t0, 8
	lbu t2, 1(a0)
	or t0, t0, t2
	slli t0, t0, 8
	lbu t2, 2(a0)
	or t0, t0, t2
	slli t0, t0, 8
	lbu t2, 3(a0)
	or t0, t0, t2
	slli t0, t0, 8
	lbu t2, 4(a0)
	or t0, t0, t2
	slli t0, t0, 8
	lbu t2, 5(a0)
	or t0, t0, t2
	slli t0, t0, 8
	lbu t2, 6(a0)
	or t0, t0, t2
	slli t0, t0, 8
	lbu t2, 7(a0)
	or t0, t0, t2
	lbu t1, 8(a0)
	slli t1, t1, 8
	lbu t2, 9(a0)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 10(a0)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 11(a0)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 12(a0)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 13(a0)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 14(a0)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 15(a0)
	or t1, t1, t2
	slli t3, t0, 1
	srli t4, t1, 63
	xor t3, t3, t4
	srli t4, t0, 63
	addi t2, zero, 0
	sub t4, t2, t4
	addi t5, zero, -62
	slli t5, t5, 56
	and t5, t4, t5
	xor t3, t3, t5
	slli t5, t1, 1
	andi t6, t4, 1
	xor t5, t5, t6
	lui s0, 69905
	addi s0, s0, 273
	slli a7, s0, 32
	or s0, s0, a7
	slli s1, s0, 1
	slli s2, s0, 2
	slli s3, s0, 3
	slli t6, t3, 32
	srli t6, t6, 32
	srli a6, t3, 32
	xor s4, t6, a6
	and a7, t6, s0
	sd a7, 0(s9)
	and a7, t6, s1
	sd a7, 8(s9)
	and a7, t6, s2
	sd a7, 16(s9)
	and a7, t6, s3
	sd a7, 24(s9)
	and a7, a6, s0
	sd a7, 32(s9)
	and a7, a6, s1
	sd a7, 40(s9)
	and a7, a6, s2
	sd a7, 48(s9)
	and a7, a6, s3
	sd a7, 56(s9)
	and a7, s4, s0
	sd a7, 64(s9)
	and a7, s4, s1
	sd a7, 72(s9)
	and a7, s4, s2
	sd a7, 80(s9)
	and a7, s4, s3
	sd a7, 88(s9)
	slli t6, t5, 32
	srli t6, t6, 32
	srli a6, t5, 32
	xor s4, t6, a6
	and a7, t6, s0
	sd a7, 96(s9)
	and a7, t6, s1
	sd a7, 104(s9)
	and a7, t6, s2
	sd a7, 112(s9)
	and a7, t6, s3
	sd a7, 120(s9)
	and a7, a6, s0
	sd a7, 128(s9)
	and a7, a6, s1
	sd a7, 136(s9)
	and a7, a6, s2
	sd a7, 144(s9)
	and a7, a6, s3
	sd a7, 152(s9)
	and a7, s4, s0
	sd a7, 160(s9)
	and a7, s4, s1
	sd a7, 168(s9)
	and a7, s4, s2
	sd a7, 176(s9)
	and a7, s4, s3
	sd a7, 184(s9)
	xor t4, t3, t5
	slli t6, t4, 32
	srli t6, t6, 32
	srli a6, t4, 32
	xor s4, t6, a6
	and a7, t6, s0
	sd a7, 192(s9)
	and a7, t6, s1
	sd a7, 200(s9)
	and a7, t6, s2
	sd a7, 208(s9)
	and a7, t6, s3
	sd a7, 216(s9)
	and a7, a6, s0
	sd a7, 224(s9)
	and a7, a6, s1
	sd a7, 232(s9)
	and a7, a6, s2
	sd a7, 240(s9)
	and a7, a6, s3
	sd a7, 248(s9)
	and a7, s4, s0
	sd a7, 256(s9)
	and a7, s4, s1
	sd a7, 264(s9)
	and a7, s4, s2
	sd a7, 272(s9)
	and a7, s4, s3
	sd a7, 280(s9)
	ld s0, 320(a5)
	ld s1, 328(a5)
	ld s2, 336(a5)
	ld s3, 344(a5)
	ld s4, 352(a5)
	ld s5, 360(a5)
	ld s6, 368(a5)
	ld s7, 376(a5)
	ld s8, 384(a5)
	ld s9, 392(a5)
	ld s10, 400(a5)
	ld s11, 408(a5)
	addi sp, sp, 16
	addi sp, sp, 2032
	addi t0, zero, 0
	addi sp, sp, -2032
	addi sp, sp, -16
	addi t1, sp, 0
	sd t0, 0(t1)
	sd t0, 8(t1)
	sd t0, 16(t1)
	sd t0, 24(t1)
	sd t0, 32(t1)
	sd t0, 40(t1)
	sd t0, 48(t1)
	sd t0, 56(t1)
	sd t0, 64(t1)
	sd t0, 72(t1)
	sd t0, 80(t1)
	sd t0, 88(t1)
	sd t0, 96(t1)
	sd t0, 104(t1)
	sd t0, 112(t1)
	sd t0, 120(t1)
	sd t0, 128(t1)
	sd t0, 136(t1)
	sd t0, 144(t1)
	sd t0, 152(t1)
	sd t0, 160(t1)
	sd t0, 168(t1)
	sd t0, 176(t1)
	sd t0, 184(t1)
	sd t0, 192(t1)
	sd t0, 200(t1)
	sd t0, 208(t1)
	sd t0, 216(t1)
	sd t0, 224(t1)
	sd t0, 232(t1)
	sd t0, 240(t1)
	sd t0, 248(t1)
	sd t0, 256(t1)
	sd t0, 264(t1)
	sd t0, 272(t1)
	sd t0, 280(t1)
	sd t0, 288(t1)
	sd t0, 296(t1)
	sd t0, 304(t1)
	sd t0, 312(t1)
	sd t0, 320(t1)
	sd t0, 328(t1)
	sd t0, 336(t1)
	sd t0, 344(t1)
	sd t0, 352(t1)
	sd t0, 360(t1)
	sd t0, 368(t1)
	sd t0, 376(t1)
	sd t0, 384(t1)
	sd t0, 392(t1)
	sd t0, 400(t1)
	sd t0, 408(t1)
	sd t0, 416(t1)
	sd t0, 424(t1)
	sd t0, 432(t1)
	sd t0, 440(t1)
	sd t0, 448(t1)
	sd t0, 456(t1)
	sd t0, 464(t1)
	sd t0, 472(t1)
	sd t0, 480(t1)
	sd t0, 488(t1)
	sd t0, 496(t1)
	sd t0, 504(t1)
	sd t0, 512(t1)
	sd t0, 520(t1)
	sd t0, 528(t1)
	sd t0, 536(t1)
	sd t0, 544(t1)
	sd t0, 552(t1)
	sd t0, 560(t1)
	sd t0, 568(t1)
	sd t0, 576(t1)
	sd t0, 584(t1)
	sd t0, 592(t1)
	sd t0, 600(t1)
	sd t0, 608(t1)
	sd t0, 616(t1)
	sd t0, 624(t1)
	sd t0, 632(t1)
	sd t0, 640(t1)
	sd t0, 648(t1)
	sd t0, 656(t1)
	sd t0, 664(t1)
	sd t0, 672(t1)
	sd t0, 680(t1)
	sd t0, 688(t1)
	sd t0, 696(t1)
	sd t0, 704(t1)
	sd t0, 712(t1)
	sd t0, 720(t1)
	sd t0, 728(t1)
	sd t0, 736(t1)
	sd t0, 744(t1)
	sd t0, 752(t1)
	sd t0, 760(t1)
	sd t0, 768(t1)
	sd t0, 776(t1)
	sd t0, 784(t1)
	sd t0, 792(t1)
	sd t0, 800(t1)
	sd t0, 808(t1)
	sd t0, 816(t1)
	sd t0, 824(t1)
	sd t0, 832(t1)
	sd t0, 840(t1)
	sd t0, 848(t1)
	sd t0, 856(t1)
	sd t0, 864(t1)
	sd t0, 872(t1)
	sd t0, 880(t1)
	sd t0, 888(t1)
	sd t0, 896(t1)
	sd t0, 904(t1)
	sd t0, 912(t1)
	sd t0, 920(t1)
	sd t0, 928(t1)
	sd t0, 936(t1)
	sd t0, 944(t1)
	sd t0, 952(t1)
	sd t0, 960(t1)
	sd t0, 968(t1)
	sd t0, 976(t1)
	sd t0, 984(t1)
	sd t0, 992(t1)
	sd t0, 1000(t1)
	sd t0, 1008(t1)
	sd t0, 1016(t1)
	sd t0, 1024(t1)
	sd t0, 1032(t1)
	sd t0, 1040(t1)
	sd t0, 1048(t1)
	sd t0, 1056(t1)
	sd t0, 1064(t1)
	sd t0, 1072(t1)
	sd t0, 1080(t1)
	sd t0, 1088(t1)
	sd t0, 1096(t1)
	sd t0, 1104(t1)
	sd t0, 1112(t1)
	sd t0, 1120(t1)
	sd t0, 1128(t1)
	sd t0, 1136(t1)
	sd t0, 1144(t1)
	sd t0, 1152(t1)
	sd t0, 1160(t1)
	sd t0, 1168(t1)
	sd t0, 1176(t1)
	sd t0, 1184(t1)
	sd t0, 1192(t1)
	sd t0, 1200(t1)
	sd t0, 1208(t1)
	sd t0, 1216(t1)
	sd t0, 1224(t1)
	sd t0, 1232(t1)
	sd t0, 1240(t1)
	sd t0, 1248(t1)
	sd t0, 1256(t1)
	sd t0, 1264(t1)
	sd t0, 1272(t1)
	sd t0, 1280(t1)
	sd t0, 1288(t1)
	sd t0, 1296(t1)
	sd t0, 1304(t1)
	sd t0, 1312(t1)
	sd t0, 1320(t1)
	sd t0, 1328(t1)
	sd t0, 1336(t1)
	sd t0, 1344(t1)
	sd t0, 1352(t1)
	sd t0, 1360(t1)
	sd t0, 1368(t1)
	sd t0, 1376(t1)
	sd t0, 1384(t1)
	sd t0, 1392(t1)
	sd t0, 1400(t1)
	sd t0, 1408(t1)
	sd t0, 1416(t1)
	sd t0, 1424(t1)
	sd t0, 1432(t1)
	sd t0, 1440(t1)
	sd t0, 1448(t1)
	sd t0, 1456(t1)
	sd t0, 1464(t1)
	sd t0, 1472(t1)
	sd t0, 1480(t1)
	sd t0, 1488(t1)
	sd t0, 1496(t1)
	sd t0, 1504(t1)
	sd t0, 1512(t1)
	sd t0, 1520(t1)
	sd t0, 1528(t1)
	sd t0, 1536(t1)
	sd t0, 1544(t1)
	sd t0, 1552(t1)
	sd t0, 1560(t1)
	sd t0, 1568(t1)
	sd t0, 1576(t1)
	sd t0, 1584(t1)
	sd t0, 1592(t1)
	sd t0, 1600(t1)
	sd t0, 1608(t1)
	sd t0, 1616(t1)
	sd t0, 1624(t1)
	sd t0, 1632(t1)
	sd t0, 1640(t1)
	sd t0, 1648(t1)
	sd t0, 1656(t1)
	sd t0, 1664(t1)
	sd t0, 1672(t1)
	sd t0, 1680(t1)
	sd t0, 1688(t1)
	sd t0, 1696(t1)
	sd t0, 1704(t1)
	sd t0, 1712(t1)
	sd t0, 1720(t1)
	sd t0, 1728(t1)
	sd t0, 1736(t1)
	sd t0, 1744(t1)
	sd t0, 1752(t1)
	sd t0, 1760(t1)
	sd t0, 1768(t1)
	sd t0, 1776(t1)
	sd t0, 1784(t1)
	sd t0, 1792(t1)
	sd t0, 1800(t1)
	sd t0, 1808(t1)
	sd t0, 1816(t1)
	sd t0, 1824(t1)
	sd t0, 1832(t1)
	sd t0, 1840(t1)
	sd t0, 1848(t1)
	sd t0, 1856(t1)
	sd t0, 1864(t1)
	sd t0, 1872(t1)
	sd t0, 1880(t1)
	sd t0, 1888(t1)
	sd t0, 1896(t1)
	sd t0, 1904(t1)
	sd t0, 1912(t1)
	sd t0, 1920(t1)
	sd t0, 1928(t1)
	sd t0, 1936(t1)
	sd t0, 1944(t1)
	sd t0, 1952(t1)
	sd t0, 1960(t1)
	sd t0, 1968(t1)
	sd t0, 1976(t1)
	sd t0, 1984(t1)
	sd t0, 1992(t1)
	sd t0, 2000(t1)
	sd t0, 2008(t1)
	sd t0, 2016(t1)
	sd t0, 2024(t1)
	sd t0, 2032(t1)
	sd t0, 2040(t1)
	addi sp, sp, 16
	addi sp, sp, 2032
	addi a0, zero, 0
	addi a1, zero, 0
	addi a2, zero, 0
	addi a3, zero, 0
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	addi a7, zero, 0
	addi t0, zero, 0
	addi t1, zero, 0
	addi t2, zero, 0
	addi t3, zero, 0
	addi t4, zero, 0
	addi t5, zero, 0
	addi t6, zero, 0
	ret
	.option pop

vg_aes_gcm_stream_encrypt_bitsliced:
	.option push
	.option arch, +m, +c
	addi sp, sp, -2032
	addi sp, sp, -544
	addi t0, sp, 0
	addi t1, t0, 8
	sd t1, 0(t0)
	addi t2, a7, 0
	addi a7, sp, 0
	ld a7, 0(a7)
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
	addi s7, t2, 0
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
	addi a0, s7, 0
	addi a1, s3, 0
	addi a2, s1, 48
	addi a5, s0, 512
	call {vg_aes_ctr32_bs}
	j 210f
29:
210:
	beqz s5, 211f
	addi t0, zero, 0
	sd t0, 64(s1)
	sd t0, 72(s1)
	addi a3, s1, 64
	addi a4, zero, 1
	addi a0, s7, 0
	addi a1, s3, 0
	addi a2, s1, 48
	addi a5, s0, 512
	call {vg_aes_ctr32_bs}
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
	addi sp, sp, 544
	addi sp, sp, 2032
	addi t0, zero, 0
	addi sp, sp, -2032
	addi sp, sp, -16
	addi t1, sp, 0
	sd t0, 0(t1)
	sd t0, 8(t1)
	sd t0, 16(t1)
	sd t0, 24(t1)
	sd t0, 32(t1)
	sd t0, 40(t1)
	sd t0, 48(t1)
	sd t0, 56(t1)
	sd t0, 64(t1)
	sd t0, 72(t1)
	sd t0, 80(t1)
	sd t0, 88(t1)
	sd t0, 96(t1)
	sd t0, 104(t1)
	sd t0, 112(t1)
	sd t0, 120(t1)
	sd t0, 128(t1)
	sd t0, 136(t1)
	sd t0, 144(t1)
	sd t0, 152(t1)
	sd t0, 160(t1)
	sd t0, 168(t1)
	sd t0, 176(t1)
	sd t0, 184(t1)
	sd t0, 192(t1)
	sd t0, 200(t1)
	sd t0, 208(t1)
	sd t0, 216(t1)
	sd t0, 224(t1)
	sd t0, 232(t1)
	sd t0, 240(t1)
	sd t0, 248(t1)
	sd t0, 256(t1)
	sd t0, 264(t1)
	sd t0, 272(t1)
	sd t0, 280(t1)
	sd t0, 288(t1)
	sd t0, 296(t1)
	sd t0, 304(t1)
	sd t0, 312(t1)
	sd t0, 320(t1)
	sd t0, 328(t1)
	sd t0, 336(t1)
	sd t0, 344(t1)
	sd t0, 352(t1)
	sd t0, 360(t1)
	sd t0, 368(t1)
	sd t0, 376(t1)
	sd t0, 384(t1)
	sd t0, 392(t1)
	sd t0, 400(t1)
	sd t0, 408(t1)
	sd t0, 416(t1)
	sd t0, 424(t1)
	sd t0, 432(t1)
	sd t0, 440(t1)
	sd t0, 448(t1)
	sd t0, 456(t1)
	sd t0, 464(t1)
	sd t0, 472(t1)
	sd t0, 480(t1)
	sd t0, 488(t1)
	sd t0, 496(t1)
	sd t0, 504(t1)
	sd t0, 512(t1)
	sd t0, 520(t1)
	sd t0, 528(t1)
	sd t0, 536(t1)
	sd t0, 544(t1)
	sd t0, 552(t1)
	sd t0, 560(t1)
	sd t0, 568(t1)
	sd t0, 576(t1)
	sd t0, 584(t1)
	sd t0, 592(t1)
	sd t0, 600(t1)
	sd t0, 608(t1)
	sd t0, 616(t1)
	sd t0, 624(t1)
	sd t0, 632(t1)
	sd t0, 640(t1)
	sd t0, 648(t1)
	sd t0, 656(t1)
	sd t0, 664(t1)
	sd t0, 672(t1)
	sd t0, 680(t1)
	sd t0, 688(t1)
	sd t0, 696(t1)
	sd t0, 704(t1)
	sd t0, 712(t1)
	sd t0, 720(t1)
	sd t0, 728(t1)
	sd t0, 736(t1)
	sd t0, 744(t1)
	sd t0, 752(t1)
	sd t0, 760(t1)
	sd t0, 768(t1)
	sd t0, 776(t1)
	sd t0, 784(t1)
	sd t0, 792(t1)
	sd t0, 800(t1)
	sd t0, 808(t1)
	sd t0, 816(t1)
	sd t0, 824(t1)
	sd t0, 832(t1)
	sd t0, 840(t1)
	sd t0, 848(t1)
	sd t0, 856(t1)
	sd t0, 864(t1)
	sd t0, 872(t1)
	sd t0, 880(t1)
	sd t0, 888(t1)
	sd t0, 896(t1)
	sd t0, 904(t1)
	sd t0, 912(t1)
	sd t0, 920(t1)
	sd t0, 928(t1)
	sd t0, 936(t1)
	sd t0, 944(t1)
	sd t0, 952(t1)
	sd t0, 960(t1)
	sd t0, 968(t1)
	sd t0, 976(t1)
	sd t0, 984(t1)
	sd t0, 992(t1)
	sd t0, 1000(t1)
	sd t0, 1008(t1)
	sd t0, 1016(t1)
	sd t0, 1024(t1)
	sd t0, 1032(t1)
	sd t0, 1040(t1)
	sd t0, 1048(t1)
	sd t0, 1056(t1)
	sd t0, 1064(t1)
	sd t0, 1072(t1)
	sd t0, 1080(t1)
	sd t0, 1088(t1)
	sd t0, 1096(t1)
	sd t0, 1104(t1)
	sd t0, 1112(t1)
	sd t0, 1120(t1)
	sd t0, 1128(t1)
	sd t0, 1136(t1)
	sd t0, 1144(t1)
	sd t0, 1152(t1)
	sd t0, 1160(t1)
	sd t0, 1168(t1)
	sd t0, 1176(t1)
	sd t0, 1184(t1)
	sd t0, 1192(t1)
	sd t0, 1200(t1)
	sd t0, 1208(t1)
	sd t0, 1216(t1)
	sd t0, 1224(t1)
	sd t0, 1232(t1)
	sd t0, 1240(t1)
	sd t0, 1248(t1)
	sd t0, 1256(t1)
	sd t0, 1264(t1)
	sd t0, 1272(t1)
	sd t0, 1280(t1)
	sd t0, 1288(t1)
	sd t0, 1296(t1)
	sd t0, 1304(t1)
	sd t0, 1312(t1)
	sd t0, 1320(t1)
	sd t0, 1328(t1)
	sd t0, 1336(t1)
	sd t0, 1344(t1)
	sd t0, 1352(t1)
	sd t0, 1360(t1)
	sd t0, 1368(t1)
	sd t0, 1376(t1)
	sd t0, 1384(t1)
	sd t0, 1392(t1)
	sd t0, 1400(t1)
	sd t0, 1408(t1)
	sd t0, 1416(t1)
	sd t0, 1424(t1)
	sd t0, 1432(t1)
	sd t0, 1440(t1)
	sd t0, 1448(t1)
	sd t0, 1456(t1)
	sd t0, 1464(t1)
	sd t0, 1472(t1)
	sd t0, 1480(t1)
	sd t0, 1488(t1)
	sd t0, 1496(t1)
	sd t0, 1504(t1)
	sd t0, 1512(t1)
	sd t0, 1520(t1)
	sd t0, 1528(t1)
	sd t0, 1536(t1)
	sd t0, 1544(t1)
	sd t0, 1552(t1)
	sd t0, 1560(t1)
	sd t0, 1568(t1)
	sd t0, 1576(t1)
	sd t0, 1584(t1)
	sd t0, 1592(t1)
	sd t0, 1600(t1)
	sd t0, 1608(t1)
	sd t0, 1616(t1)
	sd t0, 1624(t1)
	sd t0, 1632(t1)
	sd t0, 1640(t1)
	sd t0, 1648(t1)
	sd t0, 1656(t1)
	sd t0, 1664(t1)
	sd t0, 1672(t1)
	sd t0, 1680(t1)
	sd t0, 1688(t1)
	sd t0, 1696(t1)
	sd t0, 1704(t1)
	sd t0, 1712(t1)
	sd t0, 1720(t1)
	sd t0, 1728(t1)
	sd t0, 1736(t1)
	sd t0, 1744(t1)
	sd t0, 1752(t1)
	sd t0, 1760(t1)
	sd t0, 1768(t1)
	sd t0, 1776(t1)
	sd t0, 1784(t1)
	sd t0, 1792(t1)
	sd t0, 1800(t1)
	sd t0, 1808(t1)
	sd t0, 1816(t1)
	sd t0, 1824(t1)
	sd t0, 1832(t1)
	sd t0, 1840(t1)
	sd t0, 1848(t1)
	sd t0, 1856(t1)
	sd t0, 1864(t1)
	sd t0, 1872(t1)
	sd t0, 1880(t1)
	sd t0, 1888(t1)
	sd t0, 1896(t1)
	sd t0, 1904(t1)
	sd t0, 1912(t1)
	sd t0, 1920(t1)
	sd t0, 1928(t1)
	sd t0, 1936(t1)
	sd t0, 1944(t1)
	sd t0, 1952(t1)
	sd t0, 1960(t1)
	sd t0, 1968(t1)
	sd t0, 1976(t1)
	sd t0, 1984(t1)
	sd t0, 1992(t1)
	sd t0, 2000(t1)
	sd t0, 2008(t1)
	sd t0, 2016(t1)
	sd t0, 2024(t1)
	sd t0, 2032(t1)
	sd t0, 2040(t1)
	addi sp, sp, -2032
	addi sp, sp, -16
	addi t1, sp, 0
	sd t0, 0(t1)
	sd t0, 8(t1)
	sd t0, 16(t1)
	sd t0, 24(t1)
	sd t0, 32(t1)
	sd t0, 40(t1)
	sd t0, 48(t1)
	sd t0, 56(t1)
	sd t0, 64(t1)
	sd t0, 72(t1)
	sd t0, 80(t1)
	sd t0, 88(t1)
	sd t0, 96(t1)
	sd t0, 104(t1)
	sd t0, 112(t1)
	sd t0, 120(t1)
	sd t0, 128(t1)
	sd t0, 136(t1)
	sd t0, 144(t1)
	sd t0, 152(t1)
	sd t0, 160(t1)
	sd t0, 168(t1)
	sd t0, 176(t1)
	sd t0, 184(t1)
	sd t0, 192(t1)
	sd t0, 200(t1)
	sd t0, 208(t1)
	sd t0, 216(t1)
	sd t0, 224(t1)
	sd t0, 232(t1)
	sd t0, 240(t1)
	sd t0, 248(t1)
	sd t0, 256(t1)
	sd t0, 264(t1)
	sd t0, 272(t1)
	sd t0, 280(t1)
	sd t0, 288(t1)
	sd t0, 296(t1)
	sd t0, 304(t1)
	sd t0, 312(t1)
	sd t0, 320(t1)
	sd t0, 328(t1)
	sd t0, 336(t1)
	sd t0, 344(t1)
	sd t0, 352(t1)
	sd t0, 360(t1)
	sd t0, 368(t1)
	sd t0, 376(t1)
	sd t0, 384(t1)
	sd t0, 392(t1)
	sd t0, 400(t1)
	sd t0, 408(t1)
	sd t0, 416(t1)
	sd t0, 424(t1)
	sd t0, 432(t1)
	sd t0, 440(t1)
	sd t0, 448(t1)
	sd t0, 456(t1)
	sd t0, 464(t1)
	sd t0, 472(t1)
	sd t0, 480(t1)
	sd t0, 488(t1)
	sd t0, 496(t1)
	sd t0, 504(t1)
	sd t0, 512(t1)
	sd t0, 520(t1)
	sd t0, 528(t1)
	sd t0, 536(t1)
	sd t0, 544(t1)
	sd t0, 552(t1)
	sd t0, 560(t1)
	sd t0, 568(t1)
	sd t0, 576(t1)
	sd t0, 584(t1)
	sd t0, 592(t1)
	sd t0, 600(t1)
	sd t0, 608(t1)
	sd t0, 616(t1)
	sd t0, 624(t1)
	sd t0, 632(t1)
	sd t0, 640(t1)
	sd t0, 648(t1)
	sd t0, 656(t1)
	sd t0, 664(t1)
	sd t0, 672(t1)
	sd t0, 680(t1)
	sd t0, 688(t1)
	sd t0, 696(t1)
	sd t0, 704(t1)
	sd t0, 712(t1)
	sd t0, 720(t1)
	sd t0, 728(t1)
	sd t0, 736(t1)
	sd t0, 744(t1)
	sd t0, 752(t1)
	sd t0, 760(t1)
	sd t0, 768(t1)
	sd t0, 776(t1)
	sd t0, 784(t1)
	sd t0, 792(t1)
	sd t0, 800(t1)
	sd t0, 808(t1)
	sd t0, 816(t1)
	sd t0, 824(t1)
	sd t0, 832(t1)
	sd t0, 840(t1)
	sd t0, 848(t1)
	sd t0, 856(t1)
	sd t0, 864(t1)
	sd t0, 872(t1)
	sd t0, 880(t1)
	sd t0, 888(t1)
	sd t0, 896(t1)
	sd t0, 904(t1)
	sd t0, 912(t1)
	sd t0, 920(t1)
	sd t0, 928(t1)
	sd t0, 936(t1)
	sd t0, 944(t1)
	sd t0, 952(t1)
	sd t0, 960(t1)
	sd t0, 968(t1)
	sd t0, 976(t1)
	sd t0, 984(t1)
	sd t0, 992(t1)
	sd t0, 1000(t1)
	sd t0, 1008(t1)
	sd t0, 1016(t1)
	sd t0, 1024(t1)
	sd t0, 1032(t1)
	sd t0, 1040(t1)
	sd t0, 1048(t1)
	sd t0, 1056(t1)
	sd t0, 1064(t1)
	sd t0, 1072(t1)
	sd t0, 1080(t1)
	sd t0, 1088(t1)
	sd t0, 1096(t1)
	sd t0, 1104(t1)
	sd t0, 1112(t1)
	sd t0, 1120(t1)
	sd t0, 1128(t1)
	sd t0, 1136(t1)
	sd t0, 1144(t1)
	sd t0, 1152(t1)
	sd t0, 1160(t1)
	sd t0, 1168(t1)
	sd t0, 1176(t1)
	sd t0, 1184(t1)
	sd t0, 1192(t1)
	sd t0, 1200(t1)
	sd t0, 1208(t1)
	sd t0, 1216(t1)
	sd t0, 1224(t1)
	sd t0, 1232(t1)
	sd t0, 1240(t1)
	sd t0, 1248(t1)
	sd t0, 1256(t1)
	sd t0, 1264(t1)
	sd t0, 1272(t1)
	sd t0, 1280(t1)
	sd t0, 1288(t1)
	sd t0, 1296(t1)
	sd t0, 1304(t1)
	sd t0, 1312(t1)
	sd t0, 1320(t1)
	sd t0, 1328(t1)
	sd t0, 1336(t1)
	sd t0, 1344(t1)
	sd t0, 1352(t1)
	sd t0, 1360(t1)
	sd t0, 1368(t1)
	sd t0, 1376(t1)
	sd t0, 1384(t1)
	sd t0, 1392(t1)
	sd t0, 1400(t1)
	sd t0, 1408(t1)
	sd t0, 1416(t1)
	sd t0, 1424(t1)
	sd t0, 1432(t1)
	sd t0, 1440(t1)
	sd t0, 1448(t1)
	sd t0, 1456(t1)
	sd t0, 1464(t1)
	sd t0, 1472(t1)
	sd t0, 1480(t1)
	sd t0, 1488(t1)
	sd t0, 1496(t1)
	sd t0, 1504(t1)
	sd t0, 1512(t1)
	sd t0, 1520(t1)
	sd t0, 1528(t1)
	sd t0, 1536(t1)
	sd t0, 1544(t1)
	sd t0, 1552(t1)
	sd t0, 1560(t1)
	sd t0, 1568(t1)
	sd t0, 1576(t1)
	sd t0, 1584(t1)
	sd t0, 1592(t1)
	sd t0, 1600(t1)
	sd t0, 1608(t1)
	sd t0, 1616(t1)
	sd t0, 1624(t1)
	sd t0, 1632(t1)
	sd t0, 1640(t1)
	sd t0, 1648(t1)
	sd t0, 1656(t1)
	sd t0, 1664(t1)
	sd t0, 1672(t1)
	sd t0, 1680(t1)
	sd t0, 1688(t1)
	sd t0, 1696(t1)
	sd t0, 1704(t1)
	sd t0, 1712(t1)
	sd t0, 1720(t1)
	sd t0, 1728(t1)
	sd t0, 1736(t1)
	sd t0, 1744(t1)
	sd t0, 1752(t1)
	sd t0, 1760(t1)
	sd t0, 1768(t1)
	sd t0, 1776(t1)
	sd t0, 1784(t1)
	sd t0, 1792(t1)
	sd t0, 1800(t1)
	sd t0, 1808(t1)
	sd t0, 1816(t1)
	sd t0, 1824(t1)
	sd t0, 1832(t1)
	sd t0, 1840(t1)
	sd t0, 1848(t1)
	sd t0, 1856(t1)
	sd t0, 1864(t1)
	sd t0, 1872(t1)
	sd t0, 1880(t1)
	sd t0, 1888(t1)
	sd t0, 1896(t1)
	sd t0, 1904(t1)
	sd t0, 1912(t1)
	sd t0, 1920(t1)
	sd t0, 1928(t1)
	sd t0, 1936(t1)
	sd t0, 1944(t1)
	sd t0, 1952(t1)
	sd t0, 1960(t1)
	sd t0, 1968(t1)
	sd t0, 1976(t1)
	sd t0, 1984(t1)
	sd t0, 1992(t1)
	sd t0, 2000(t1)
	sd t0, 2008(t1)
	sd t0, 2016(t1)
	sd t0, 2024(t1)
	sd t0, 2032(t1)
	sd t0, 2040(t1)
	addi sp, sp, -128
	addi t1, sp, 0
	sd t0, 0(t1)
	sd t0, 8(t1)
	sd t0, 16(t1)
	sd t0, 24(t1)
	sd t0, 32(t1)
	sd t0, 40(t1)
	sd t0, 48(t1)
	sd t0, 56(t1)
	sd t0, 64(t1)
	sd t0, 72(t1)
	sd t0, 80(t1)
	sd t0, 88(t1)
	sd t0, 96(t1)
	sd t0, 104(t1)
	sd t0, 112(t1)
	sd t0, 120(t1)
	addi sp, sp, 128
	addi sp, sp, 16
	addi sp, sp, 2032
	addi sp, sp, 16
	addi sp, sp, 2032
	addi a0, zero, 0
	addi a1, zero, 0
	addi a2, zero, 0
	addi a3, zero, 0
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	addi a7, zero, 0
	addi t0, zero, 0
	addi t1, zero, 0
	addi t2, zero, 0
	addi t3, zero, 0
	addi t4, zero, 0
	addi t5, zero, 0
	addi t6, zero, 0
	ret
	.option pop

vg_aes_gcm_stream_decrypt_bitsliced:
	.option push
	.option arch, +m, +c
	addi sp, sp, -2032
	addi sp, sp, -544
	addi t0, sp, 0
	addi t1, t0, 8
	sd t1, 0(t0)
	addi t2, a7, 0
	addi a7, sp, 0
	ld a7, 0(a7)
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
	addi s7, t2, 0
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
	addi a0, s7, 0
	addi a1, s3, 0
	addi a2, s1, 48
	addi a5, s0, 512
	call {vg_aes_ctr32_bs}
	j 233f
232:
233:
	beqz s5, 234f
	addi t0, zero, 0
	sd t0, 64(s1)
	sd t0, 72(s1)
	addi a3, s1, 64
	addi a4, zero, 1
	addi a0, s7, 0
	addi a1, s3, 0
	addi a2, s1, 48
	addi a5, s0, 512
	call {vg_aes_ctr32_bs}
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
	addi sp, sp, 544
	addi sp, sp, 2032
	addi t0, zero, 0
	addi sp, sp, -2032
	addi sp, sp, -16
	addi t1, sp, 0
	sd t0, 0(t1)
	sd t0, 8(t1)
	sd t0, 16(t1)
	sd t0, 24(t1)
	sd t0, 32(t1)
	sd t0, 40(t1)
	sd t0, 48(t1)
	sd t0, 56(t1)
	sd t0, 64(t1)
	sd t0, 72(t1)
	sd t0, 80(t1)
	sd t0, 88(t1)
	sd t0, 96(t1)
	sd t0, 104(t1)
	sd t0, 112(t1)
	sd t0, 120(t1)
	sd t0, 128(t1)
	sd t0, 136(t1)
	sd t0, 144(t1)
	sd t0, 152(t1)
	sd t0, 160(t1)
	sd t0, 168(t1)
	sd t0, 176(t1)
	sd t0, 184(t1)
	sd t0, 192(t1)
	sd t0, 200(t1)
	sd t0, 208(t1)
	sd t0, 216(t1)
	sd t0, 224(t1)
	sd t0, 232(t1)
	sd t0, 240(t1)
	sd t0, 248(t1)
	sd t0, 256(t1)
	sd t0, 264(t1)
	sd t0, 272(t1)
	sd t0, 280(t1)
	sd t0, 288(t1)
	sd t0, 296(t1)
	sd t0, 304(t1)
	sd t0, 312(t1)
	sd t0, 320(t1)
	sd t0, 328(t1)
	sd t0, 336(t1)
	sd t0, 344(t1)
	sd t0, 352(t1)
	sd t0, 360(t1)
	sd t0, 368(t1)
	sd t0, 376(t1)
	sd t0, 384(t1)
	sd t0, 392(t1)
	sd t0, 400(t1)
	sd t0, 408(t1)
	sd t0, 416(t1)
	sd t0, 424(t1)
	sd t0, 432(t1)
	sd t0, 440(t1)
	sd t0, 448(t1)
	sd t0, 456(t1)
	sd t0, 464(t1)
	sd t0, 472(t1)
	sd t0, 480(t1)
	sd t0, 488(t1)
	sd t0, 496(t1)
	sd t0, 504(t1)
	sd t0, 512(t1)
	sd t0, 520(t1)
	sd t0, 528(t1)
	sd t0, 536(t1)
	sd t0, 544(t1)
	sd t0, 552(t1)
	sd t0, 560(t1)
	sd t0, 568(t1)
	sd t0, 576(t1)
	sd t0, 584(t1)
	sd t0, 592(t1)
	sd t0, 600(t1)
	sd t0, 608(t1)
	sd t0, 616(t1)
	sd t0, 624(t1)
	sd t0, 632(t1)
	sd t0, 640(t1)
	sd t0, 648(t1)
	sd t0, 656(t1)
	sd t0, 664(t1)
	sd t0, 672(t1)
	sd t0, 680(t1)
	sd t0, 688(t1)
	sd t0, 696(t1)
	sd t0, 704(t1)
	sd t0, 712(t1)
	sd t0, 720(t1)
	sd t0, 728(t1)
	sd t0, 736(t1)
	sd t0, 744(t1)
	sd t0, 752(t1)
	sd t0, 760(t1)
	sd t0, 768(t1)
	sd t0, 776(t1)
	sd t0, 784(t1)
	sd t0, 792(t1)
	sd t0, 800(t1)
	sd t0, 808(t1)
	sd t0, 816(t1)
	sd t0, 824(t1)
	sd t0, 832(t1)
	sd t0, 840(t1)
	sd t0, 848(t1)
	sd t0, 856(t1)
	sd t0, 864(t1)
	sd t0, 872(t1)
	sd t0, 880(t1)
	sd t0, 888(t1)
	sd t0, 896(t1)
	sd t0, 904(t1)
	sd t0, 912(t1)
	sd t0, 920(t1)
	sd t0, 928(t1)
	sd t0, 936(t1)
	sd t0, 944(t1)
	sd t0, 952(t1)
	sd t0, 960(t1)
	sd t0, 968(t1)
	sd t0, 976(t1)
	sd t0, 984(t1)
	sd t0, 992(t1)
	sd t0, 1000(t1)
	sd t0, 1008(t1)
	sd t0, 1016(t1)
	sd t0, 1024(t1)
	sd t0, 1032(t1)
	sd t0, 1040(t1)
	sd t0, 1048(t1)
	sd t0, 1056(t1)
	sd t0, 1064(t1)
	sd t0, 1072(t1)
	sd t0, 1080(t1)
	sd t0, 1088(t1)
	sd t0, 1096(t1)
	sd t0, 1104(t1)
	sd t0, 1112(t1)
	sd t0, 1120(t1)
	sd t0, 1128(t1)
	sd t0, 1136(t1)
	sd t0, 1144(t1)
	sd t0, 1152(t1)
	sd t0, 1160(t1)
	sd t0, 1168(t1)
	sd t0, 1176(t1)
	sd t0, 1184(t1)
	sd t0, 1192(t1)
	sd t0, 1200(t1)
	sd t0, 1208(t1)
	sd t0, 1216(t1)
	sd t0, 1224(t1)
	sd t0, 1232(t1)
	sd t0, 1240(t1)
	sd t0, 1248(t1)
	sd t0, 1256(t1)
	sd t0, 1264(t1)
	sd t0, 1272(t1)
	sd t0, 1280(t1)
	sd t0, 1288(t1)
	sd t0, 1296(t1)
	sd t0, 1304(t1)
	sd t0, 1312(t1)
	sd t0, 1320(t1)
	sd t0, 1328(t1)
	sd t0, 1336(t1)
	sd t0, 1344(t1)
	sd t0, 1352(t1)
	sd t0, 1360(t1)
	sd t0, 1368(t1)
	sd t0, 1376(t1)
	sd t0, 1384(t1)
	sd t0, 1392(t1)
	sd t0, 1400(t1)
	sd t0, 1408(t1)
	sd t0, 1416(t1)
	sd t0, 1424(t1)
	sd t0, 1432(t1)
	sd t0, 1440(t1)
	sd t0, 1448(t1)
	sd t0, 1456(t1)
	sd t0, 1464(t1)
	sd t0, 1472(t1)
	sd t0, 1480(t1)
	sd t0, 1488(t1)
	sd t0, 1496(t1)
	sd t0, 1504(t1)
	sd t0, 1512(t1)
	sd t0, 1520(t1)
	sd t0, 1528(t1)
	sd t0, 1536(t1)
	sd t0, 1544(t1)
	sd t0, 1552(t1)
	sd t0, 1560(t1)
	sd t0, 1568(t1)
	sd t0, 1576(t1)
	sd t0, 1584(t1)
	sd t0, 1592(t1)
	sd t0, 1600(t1)
	sd t0, 1608(t1)
	sd t0, 1616(t1)
	sd t0, 1624(t1)
	sd t0, 1632(t1)
	sd t0, 1640(t1)
	sd t0, 1648(t1)
	sd t0, 1656(t1)
	sd t0, 1664(t1)
	sd t0, 1672(t1)
	sd t0, 1680(t1)
	sd t0, 1688(t1)
	sd t0, 1696(t1)
	sd t0, 1704(t1)
	sd t0, 1712(t1)
	sd t0, 1720(t1)
	sd t0, 1728(t1)
	sd t0, 1736(t1)
	sd t0, 1744(t1)
	sd t0, 1752(t1)
	sd t0, 1760(t1)
	sd t0, 1768(t1)
	sd t0, 1776(t1)
	sd t0, 1784(t1)
	sd t0, 1792(t1)
	sd t0, 1800(t1)
	sd t0, 1808(t1)
	sd t0, 1816(t1)
	sd t0, 1824(t1)
	sd t0, 1832(t1)
	sd t0, 1840(t1)
	sd t0, 1848(t1)
	sd t0, 1856(t1)
	sd t0, 1864(t1)
	sd t0, 1872(t1)
	sd t0, 1880(t1)
	sd t0, 1888(t1)
	sd t0, 1896(t1)
	sd t0, 1904(t1)
	sd t0, 1912(t1)
	sd t0, 1920(t1)
	sd t0, 1928(t1)
	sd t0, 1936(t1)
	sd t0, 1944(t1)
	sd t0, 1952(t1)
	sd t0, 1960(t1)
	sd t0, 1968(t1)
	sd t0, 1976(t1)
	sd t0, 1984(t1)
	sd t0, 1992(t1)
	sd t0, 2000(t1)
	sd t0, 2008(t1)
	sd t0, 2016(t1)
	sd t0, 2024(t1)
	sd t0, 2032(t1)
	sd t0, 2040(t1)
	addi sp, sp, -2032
	addi sp, sp, -16
	addi t1, sp, 0
	sd t0, 0(t1)
	sd t0, 8(t1)
	sd t0, 16(t1)
	sd t0, 24(t1)
	sd t0, 32(t1)
	sd t0, 40(t1)
	sd t0, 48(t1)
	sd t0, 56(t1)
	sd t0, 64(t1)
	sd t0, 72(t1)
	sd t0, 80(t1)
	sd t0, 88(t1)
	sd t0, 96(t1)
	sd t0, 104(t1)
	sd t0, 112(t1)
	sd t0, 120(t1)
	sd t0, 128(t1)
	sd t0, 136(t1)
	sd t0, 144(t1)
	sd t0, 152(t1)
	sd t0, 160(t1)
	sd t0, 168(t1)
	sd t0, 176(t1)
	sd t0, 184(t1)
	sd t0, 192(t1)
	sd t0, 200(t1)
	sd t0, 208(t1)
	sd t0, 216(t1)
	sd t0, 224(t1)
	sd t0, 232(t1)
	sd t0, 240(t1)
	sd t0, 248(t1)
	sd t0, 256(t1)
	sd t0, 264(t1)
	sd t0, 272(t1)
	sd t0, 280(t1)
	sd t0, 288(t1)
	sd t0, 296(t1)
	sd t0, 304(t1)
	sd t0, 312(t1)
	sd t0, 320(t1)
	sd t0, 328(t1)
	sd t0, 336(t1)
	sd t0, 344(t1)
	sd t0, 352(t1)
	sd t0, 360(t1)
	sd t0, 368(t1)
	sd t0, 376(t1)
	sd t0, 384(t1)
	sd t0, 392(t1)
	sd t0, 400(t1)
	sd t0, 408(t1)
	sd t0, 416(t1)
	sd t0, 424(t1)
	sd t0, 432(t1)
	sd t0, 440(t1)
	sd t0, 448(t1)
	sd t0, 456(t1)
	sd t0, 464(t1)
	sd t0, 472(t1)
	sd t0, 480(t1)
	sd t0, 488(t1)
	sd t0, 496(t1)
	sd t0, 504(t1)
	sd t0, 512(t1)
	sd t0, 520(t1)
	sd t0, 528(t1)
	sd t0, 536(t1)
	sd t0, 544(t1)
	sd t0, 552(t1)
	sd t0, 560(t1)
	sd t0, 568(t1)
	sd t0, 576(t1)
	sd t0, 584(t1)
	sd t0, 592(t1)
	sd t0, 600(t1)
	sd t0, 608(t1)
	sd t0, 616(t1)
	sd t0, 624(t1)
	sd t0, 632(t1)
	sd t0, 640(t1)
	sd t0, 648(t1)
	sd t0, 656(t1)
	sd t0, 664(t1)
	sd t0, 672(t1)
	sd t0, 680(t1)
	sd t0, 688(t1)
	sd t0, 696(t1)
	sd t0, 704(t1)
	sd t0, 712(t1)
	sd t0, 720(t1)
	sd t0, 728(t1)
	sd t0, 736(t1)
	sd t0, 744(t1)
	sd t0, 752(t1)
	sd t0, 760(t1)
	sd t0, 768(t1)
	sd t0, 776(t1)
	sd t0, 784(t1)
	sd t0, 792(t1)
	sd t0, 800(t1)
	sd t0, 808(t1)
	sd t0, 816(t1)
	sd t0, 824(t1)
	sd t0, 832(t1)
	sd t0, 840(t1)
	sd t0, 848(t1)
	sd t0, 856(t1)
	sd t0, 864(t1)
	sd t0, 872(t1)
	sd t0, 880(t1)
	sd t0, 888(t1)
	sd t0, 896(t1)
	sd t0, 904(t1)
	sd t0, 912(t1)
	sd t0, 920(t1)
	sd t0, 928(t1)
	sd t0, 936(t1)
	sd t0, 944(t1)
	sd t0, 952(t1)
	sd t0, 960(t1)
	sd t0, 968(t1)
	sd t0, 976(t1)
	sd t0, 984(t1)
	sd t0, 992(t1)
	sd t0, 1000(t1)
	sd t0, 1008(t1)
	sd t0, 1016(t1)
	sd t0, 1024(t1)
	sd t0, 1032(t1)
	sd t0, 1040(t1)
	sd t0, 1048(t1)
	sd t0, 1056(t1)
	sd t0, 1064(t1)
	sd t0, 1072(t1)
	sd t0, 1080(t1)
	sd t0, 1088(t1)
	sd t0, 1096(t1)
	sd t0, 1104(t1)
	sd t0, 1112(t1)
	sd t0, 1120(t1)
	sd t0, 1128(t1)
	sd t0, 1136(t1)
	sd t0, 1144(t1)
	sd t0, 1152(t1)
	sd t0, 1160(t1)
	sd t0, 1168(t1)
	sd t0, 1176(t1)
	sd t0, 1184(t1)
	sd t0, 1192(t1)
	sd t0, 1200(t1)
	sd t0, 1208(t1)
	sd t0, 1216(t1)
	sd t0, 1224(t1)
	sd t0, 1232(t1)
	sd t0, 1240(t1)
	sd t0, 1248(t1)
	sd t0, 1256(t1)
	sd t0, 1264(t1)
	sd t0, 1272(t1)
	sd t0, 1280(t1)
	sd t0, 1288(t1)
	sd t0, 1296(t1)
	sd t0, 1304(t1)
	sd t0, 1312(t1)
	sd t0, 1320(t1)
	sd t0, 1328(t1)
	sd t0, 1336(t1)
	sd t0, 1344(t1)
	sd t0, 1352(t1)
	sd t0, 1360(t1)
	sd t0, 1368(t1)
	sd t0, 1376(t1)
	sd t0, 1384(t1)
	sd t0, 1392(t1)
	sd t0, 1400(t1)
	sd t0, 1408(t1)
	sd t0, 1416(t1)
	sd t0, 1424(t1)
	sd t0, 1432(t1)
	sd t0, 1440(t1)
	sd t0, 1448(t1)
	sd t0, 1456(t1)
	sd t0, 1464(t1)
	sd t0, 1472(t1)
	sd t0, 1480(t1)
	sd t0, 1488(t1)
	sd t0, 1496(t1)
	sd t0, 1504(t1)
	sd t0, 1512(t1)
	sd t0, 1520(t1)
	sd t0, 1528(t1)
	sd t0, 1536(t1)
	sd t0, 1544(t1)
	sd t0, 1552(t1)
	sd t0, 1560(t1)
	sd t0, 1568(t1)
	sd t0, 1576(t1)
	sd t0, 1584(t1)
	sd t0, 1592(t1)
	sd t0, 1600(t1)
	sd t0, 1608(t1)
	sd t0, 1616(t1)
	sd t0, 1624(t1)
	sd t0, 1632(t1)
	sd t0, 1640(t1)
	sd t0, 1648(t1)
	sd t0, 1656(t1)
	sd t0, 1664(t1)
	sd t0, 1672(t1)
	sd t0, 1680(t1)
	sd t0, 1688(t1)
	sd t0, 1696(t1)
	sd t0, 1704(t1)
	sd t0, 1712(t1)
	sd t0, 1720(t1)
	sd t0, 1728(t1)
	sd t0, 1736(t1)
	sd t0, 1744(t1)
	sd t0, 1752(t1)
	sd t0, 1760(t1)
	sd t0, 1768(t1)
	sd t0, 1776(t1)
	sd t0, 1784(t1)
	sd t0, 1792(t1)
	sd t0, 1800(t1)
	sd t0, 1808(t1)
	sd t0, 1816(t1)
	sd t0, 1824(t1)
	sd t0, 1832(t1)
	sd t0, 1840(t1)
	sd t0, 1848(t1)
	sd t0, 1856(t1)
	sd t0, 1864(t1)
	sd t0, 1872(t1)
	sd t0, 1880(t1)
	sd t0, 1888(t1)
	sd t0, 1896(t1)
	sd t0, 1904(t1)
	sd t0, 1912(t1)
	sd t0, 1920(t1)
	sd t0, 1928(t1)
	sd t0, 1936(t1)
	sd t0, 1944(t1)
	sd t0, 1952(t1)
	sd t0, 1960(t1)
	sd t0, 1968(t1)
	sd t0, 1976(t1)
	sd t0, 1984(t1)
	sd t0, 1992(t1)
	sd t0, 2000(t1)
	sd t0, 2008(t1)
	sd t0, 2016(t1)
	sd t0, 2024(t1)
	sd t0, 2032(t1)
	sd t0, 2040(t1)
	addi sp, sp, -128
	addi t1, sp, 0
	sd t0, 0(t1)
	sd t0, 8(t1)
	sd t0, 16(t1)
	sd t0, 24(t1)
	sd t0, 32(t1)
	sd t0, 40(t1)
	sd t0, 48(t1)
	sd t0, 56(t1)
	sd t0, 64(t1)
	sd t0, 72(t1)
	sd t0, 80(t1)
	sd t0, 88(t1)
	sd t0, 96(t1)
	sd t0, 104(t1)
	sd t0, 112(t1)
	sd t0, 120(t1)
	addi sp, sp, 128
	addi sp, sp, 16
	addi sp, sp, 2032
	addi sp, sp, 16
	addi sp, sp, 2032
	addi a0, zero, 0
	addi a1, zero, 0
	addi a2, zero, 0
	addi a3, zero, 0
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	addi a7, zero, 0
	addi t0, zero, 0
	addi t1, zero, 0
	addi t2, zero, 0
	addi t3, zero, 0
	addi t4, zero, 0
	addi t5, zero, 0
	addi t6, zero, 0
	ret
	.option pop

vg_aes_gcm_stream_finish_bitsliced:
	.option push
	.option arch, +m, +c
	addi sp, sp, -2032
	addi sp, sp, -528
	addi a7, sp, 0
	addi t2, a6, 0
	addi a6, a7, 0
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
	addi s7, t2, 0
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
	addi a0, s7, 0
	addi a1, s3, 0
	addi a2, s1, 0
	addi a3, s0, 0
	addi a4, zero, 1
	addi a5, s0, 512
	call {vg_aes_ctr32_bs}
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
	addi t0, zero, 0
	addi sp, sp, -2032
	addi sp, sp, -16
	addi t1, sp, 0
	sd t0, 0(t1)
	sd t0, 8(t1)
	sd t0, 16(t1)
	sd t0, 24(t1)
	sd t0, 32(t1)
	sd t0, 40(t1)
	sd t0, 48(t1)
	sd t0, 56(t1)
	sd t0, 64(t1)
	sd t0, 72(t1)
	sd t0, 80(t1)
	sd t0, 88(t1)
	sd t0, 96(t1)
	sd t0, 104(t1)
	sd t0, 112(t1)
	sd t0, 120(t1)
	sd t0, 128(t1)
	sd t0, 136(t1)
	sd t0, 144(t1)
	sd t0, 152(t1)
	sd t0, 160(t1)
	sd t0, 168(t1)
	sd t0, 176(t1)
	sd t0, 184(t1)
	sd t0, 192(t1)
	sd t0, 200(t1)
	sd t0, 208(t1)
	sd t0, 216(t1)
	sd t0, 224(t1)
	sd t0, 232(t1)
	sd t0, 240(t1)
	sd t0, 248(t1)
	sd t0, 256(t1)
	sd t0, 264(t1)
	sd t0, 272(t1)
	sd t0, 280(t1)
	sd t0, 288(t1)
	sd t0, 296(t1)
	sd t0, 304(t1)
	sd t0, 312(t1)
	sd t0, 320(t1)
	sd t0, 328(t1)
	sd t0, 336(t1)
	sd t0, 344(t1)
	sd t0, 352(t1)
	sd t0, 360(t1)
	sd t0, 368(t1)
	sd t0, 376(t1)
	sd t0, 384(t1)
	sd t0, 392(t1)
	sd t0, 400(t1)
	sd t0, 408(t1)
	sd t0, 416(t1)
	sd t0, 424(t1)
	sd t0, 432(t1)
	sd t0, 440(t1)
	sd t0, 448(t1)
	sd t0, 456(t1)
	sd t0, 464(t1)
	sd t0, 472(t1)
	sd t0, 480(t1)
	sd t0, 488(t1)
	sd t0, 496(t1)
	sd t0, 504(t1)
	sd t0, 512(t1)
	sd t0, 520(t1)
	sd t0, 528(t1)
	sd t0, 536(t1)
	sd t0, 544(t1)
	sd t0, 552(t1)
	sd t0, 560(t1)
	sd t0, 568(t1)
	sd t0, 576(t1)
	sd t0, 584(t1)
	sd t0, 592(t1)
	sd t0, 600(t1)
	sd t0, 608(t1)
	sd t0, 616(t1)
	sd t0, 624(t1)
	sd t0, 632(t1)
	sd t0, 640(t1)
	sd t0, 648(t1)
	sd t0, 656(t1)
	sd t0, 664(t1)
	sd t0, 672(t1)
	sd t0, 680(t1)
	sd t0, 688(t1)
	sd t0, 696(t1)
	sd t0, 704(t1)
	sd t0, 712(t1)
	sd t0, 720(t1)
	sd t0, 728(t1)
	sd t0, 736(t1)
	sd t0, 744(t1)
	sd t0, 752(t1)
	sd t0, 760(t1)
	sd t0, 768(t1)
	sd t0, 776(t1)
	sd t0, 784(t1)
	sd t0, 792(t1)
	sd t0, 800(t1)
	sd t0, 808(t1)
	sd t0, 816(t1)
	sd t0, 824(t1)
	sd t0, 832(t1)
	sd t0, 840(t1)
	sd t0, 848(t1)
	sd t0, 856(t1)
	sd t0, 864(t1)
	sd t0, 872(t1)
	sd t0, 880(t1)
	sd t0, 888(t1)
	sd t0, 896(t1)
	sd t0, 904(t1)
	sd t0, 912(t1)
	sd t0, 920(t1)
	sd t0, 928(t1)
	sd t0, 936(t1)
	sd t0, 944(t1)
	sd t0, 952(t1)
	sd t0, 960(t1)
	sd t0, 968(t1)
	sd t0, 976(t1)
	sd t0, 984(t1)
	sd t0, 992(t1)
	sd t0, 1000(t1)
	sd t0, 1008(t1)
	sd t0, 1016(t1)
	sd t0, 1024(t1)
	sd t0, 1032(t1)
	sd t0, 1040(t1)
	sd t0, 1048(t1)
	sd t0, 1056(t1)
	sd t0, 1064(t1)
	sd t0, 1072(t1)
	sd t0, 1080(t1)
	sd t0, 1088(t1)
	sd t0, 1096(t1)
	sd t0, 1104(t1)
	sd t0, 1112(t1)
	sd t0, 1120(t1)
	sd t0, 1128(t1)
	sd t0, 1136(t1)
	sd t0, 1144(t1)
	sd t0, 1152(t1)
	sd t0, 1160(t1)
	sd t0, 1168(t1)
	sd t0, 1176(t1)
	sd t0, 1184(t1)
	sd t0, 1192(t1)
	sd t0, 1200(t1)
	sd t0, 1208(t1)
	sd t0, 1216(t1)
	sd t0, 1224(t1)
	sd t0, 1232(t1)
	sd t0, 1240(t1)
	sd t0, 1248(t1)
	sd t0, 1256(t1)
	sd t0, 1264(t1)
	sd t0, 1272(t1)
	sd t0, 1280(t1)
	sd t0, 1288(t1)
	sd t0, 1296(t1)
	sd t0, 1304(t1)
	sd t0, 1312(t1)
	sd t0, 1320(t1)
	sd t0, 1328(t1)
	sd t0, 1336(t1)
	sd t0, 1344(t1)
	sd t0, 1352(t1)
	sd t0, 1360(t1)
	sd t0, 1368(t1)
	sd t0, 1376(t1)
	sd t0, 1384(t1)
	sd t0, 1392(t1)
	sd t0, 1400(t1)
	sd t0, 1408(t1)
	sd t0, 1416(t1)
	sd t0, 1424(t1)
	sd t0, 1432(t1)
	sd t0, 1440(t1)
	sd t0, 1448(t1)
	sd t0, 1456(t1)
	sd t0, 1464(t1)
	sd t0, 1472(t1)
	sd t0, 1480(t1)
	sd t0, 1488(t1)
	sd t0, 1496(t1)
	sd t0, 1504(t1)
	sd t0, 1512(t1)
	sd t0, 1520(t1)
	sd t0, 1528(t1)
	sd t0, 1536(t1)
	sd t0, 1544(t1)
	sd t0, 1552(t1)
	sd t0, 1560(t1)
	sd t0, 1568(t1)
	sd t0, 1576(t1)
	sd t0, 1584(t1)
	sd t0, 1592(t1)
	sd t0, 1600(t1)
	sd t0, 1608(t1)
	sd t0, 1616(t1)
	sd t0, 1624(t1)
	sd t0, 1632(t1)
	sd t0, 1640(t1)
	sd t0, 1648(t1)
	sd t0, 1656(t1)
	sd t0, 1664(t1)
	sd t0, 1672(t1)
	sd t0, 1680(t1)
	sd t0, 1688(t1)
	sd t0, 1696(t1)
	sd t0, 1704(t1)
	sd t0, 1712(t1)
	sd t0, 1720(t1)
	sd t0, 1728(t1)
	sd t0, 1736(t1)
	sd t0, 1744(t1)
	sd t0, 1752(t1)
	sd t0, 1760(t1)
	sd t0, 1768(t1)
	sd t0, 1776(t1)
	sd t0, 1784(t1)
	sd t0, 1792(t1)
	sd t0, 1800(t1)
	sd t0, 1808(t1)
	sd t0, 1816(t1)
	sd t0, 1824(t1)
	sd t0, 1832(t1)
	sd t0, 1840(t1)
	sd t0, 1848(t1)
	sd t0, 1856(t1)
	sd t0, 1864(t1)
	sd t0, 1872(t1)
	sd t0, 1880(t1)
	sd t0, 1888(t1)
	sd t0, 1896(t1)
	sd t0, 1904(t1)
	sd t0, 1912(t1)
	sd t0, 1920(t1)
	sd t0, 1928(t1)
	sd t0, 1936(t1)
	sd t0, 1944(t1)
	sd t0, 1952(t1)
	sd t0, 1960(t1)
	sd t0, 1968(t1)
	sd t0, 1976(t1)
	sd t0, 1984(t1)
	sd t0, 1992(t1)
	sd t0, 2000(t1)
	sd t0, 2008(t1)
	sd t0, 2016(t1)
	sd t0, 2024(t1)
	sd t0, 2032(t1)
	sd t0, 2040(t1)
	addi sp, sp, -2032
	addi sp, sp, -16
	addi t1, sp, 0
	sd t0, 0(t1)
	sd t0, 8(t1)
	sd t0, 16(t1)
	sd t0, 24(t1)
	sd t0, 32(t1)
	sd t0, 40(t1)
	sd t0, 48(t1)
	sd t0, 56(t1)
	sd t0, 64(t1)
	sd t0, 72(t1)
	sd t0, 80(t1)
	sd t0, 88(t1)
	sd t0, 96(t1)
	sd t0, 104(t1)
	sd t0, 112(t1)
	sd t0, 120(t1)
	sd t0, 128(t1)
	sd t0, 136(t1)
	sd t0, 144(t1)
	sd t0, 152(t1)
	sd t0, 160(t1)
	sd t0, 168(t1)
	sd t0, 176(t1)
	sd t0, 184(t1)
	sd t0, 192(t1)
	sd t0, 200(t1)
	sd t0, 208(t1)
	sd t0, 216(t1)
	sd t0, 224(t1)
	sd t0, 232(t1)
	sd t0, 240(t1)
	sd t0, 248(t1)
	sd t0, 256(t1)
	sd t0, 264(t1)
	sd t0, 272(t1)
	sd t0, 280(t1)
	sd t0, 288(t1)
	sd t0, 296(t1)
	sd t0, 304(t1)
	sd t0, 312(t1)
	sd t0, 320(t1)
	sd t0, 328(t1)
	sd t0, 336(t1)
	sd t0, 344(t1)
	sd t0, 352(t1)
	sd t0, 360(t1)
	sd t0, 368(t1)
	sd t0, 376(t1)
	sd t0, 384(t1)
	sd t0, 392(t1)
	sd t0, 400(t1)
	sd t0, 408(t1)
	sd t0, 416(t1)
	sd t0, 424(t1)
	sd t0, 432(t1)
	sd t0, 440(t1)
	sd t0, 448(t1)
	sd t0, 456(t1)
	sd t0, 464(t1)
	sd t0, 472(t1)
	sd t0, 480(t1)
	sd t0, 488(t1)
	sd t0, 496(t1)
	sd t0, 504(t1)
	sd t0, 512(t1)
	sd t0, 520(t1)
	sd t0, 528(t1)
	sd t0, 536(t1)
	sd t0, 544(t1)
	sd t0, 552(t1)
	sd t0, 560(t1)
	sd t0, 568(t1)
	sd t0, 576(t1)
	sd t0, 584(t1)
	sd t0, 592(t1)
	sd t0, 600(t1)
	sd t0, 608(t1)
	sd t0, 616(t1)
	sd t0, 624(t1)
	sd t0, 632(t1)
	sd t0, 640(t1)
	sd t0, 648(t1)
	sd t0, 656(t1)
	sd t0, 664(t1)
	sd t0, 672(t1)
	sd t0, 680(t1)
	sd t0, 688(t1)
	sd t0, 696(t1)
	sd t0, 704(t1)
	sd t0, 712(t1)
	sd t0, 720(t1)
	sd t0, 728(t1)
	sd t0, 736(t1)
	sd t0, 744(t1)
	sd t0, 752(t1)
	sd t0, 760(t1)
	sd t0, 768(t1)
	sd t0, 776(t1)
	sd t0, 784(t1)
	sd t0, 792(t1)
	sd t0, 800(t1)
	sd t0, 808(t1)
	sd t0, 816(t1)
	sd t0, 824(t1)
	sd t0, 832(t1)
	sd t0, 840(t1)
	sd t0, 848(t1)
	sd t0, 856(t1)
	sd t0, 864(t1)
	sd t0, 872(t1)
	sd t0, 880(t1)
	sd t0, 888(t1)
	sd t0, 896(t1)
	sd t0, 904(t1)
	sd t0, 912(t1)
	sd t0, 920(t1)
	sd t0, 928(t1)
	sd t0, 936(t1)
	sd t0, 944(t1)
	sd t0, 952(t1)
	sd t0, 960(t1)
	sd t0, 968(t1)
	sd t0, 976(t1)
	sd t0, 984(t1)
	sd t0, 992(t1)
	sd t0, 1000(t1)
	sd t0, 1008(t1)
	sd t0, 1016(t1)
	sd t0, 1024(t1)
	sd t0, 1032(t1)
	sd t0, 1040(t1)
	sd t0, 1048(t1)
	sd t0, 1056(t1)
	sd t0, 1064(t1)
	sd t0, 1072(t1)
	sd t0, 1080(t1)
	sd t0, 1088(t1)
	sd t0, 1096(t1)
	sd t0, 1104(t1)
	sd t0, 1112(t1)
	sd t0, 1120(t1)
	sd t0, 1128(t1)
	sd t0, 1136(t1)
	sd t0, 1144(t1)
	sd t0, 1152(t1)
	sd t0, 1160(t1)
	sd t0, 1168(t1)
	sd t0, 1176(t1)
	sd t0, 1184(t1)
	sd t0, 1192(t1)
	sd t0, 1200(t1)
	sd t0, 1208(t1)
	sd t0, 1216(t1)
	sd t0, 1224(t1)
	sd t0, 1232(t1)
	sd t0, 1240(t1)
	sd t0, 1248(t1)
	sd t0, 1256(t1)
	sd t0, 1264(t1)
	sd t0, 1272(t1)
	sd t0, 1280(t1)
	sd t0, 1288(t1)
	sd t0, 1296(t1)
	sd t0, 1304(t1)
	sd t0, 1312(t1)
	sd t0, 1320(t1)
	sd t0, 1328(t1)
	sd t0, 1336(t1)
	sd t0, 1344(t1)
	sd t0, 1352(t1)
	sd t0, 1360(t1)
	sd t0, 1368(t1)
	sd t0, 1376(t1)
	sd t0, 1384(t1)
	sd t0, 1392(t1)
	sd t0, 1400(t1)
	sd t0, 1408(t1)
	sd t0, 1416(t1)
	sd t0, 1424(t1)
	sd t0, 1432(t1)
	sd t0, 1440(t1)
	sd t0, 1448(t1)
	sd t0, 1456(t1)
	sd t0, 1464(t1)
	sd t0, 1472(t1)
	sd t0, 1480(t1)
	sd t0, 1488(t1)
	sd t0, 1496(t1)
	sd t0, 1504(t1)
	sd t0, 1512(t1)
	sd t0, 1520(t1)
	sd t0, 1528(t1)
	sd t0, 1536(t1)
	sd t0, 1544(t1)
	sd t0, 1552(t1)
	sd t0, 1560(t1)
	sd t0, 1568(t1)
	sd t0, 1576(t1)
	sd t0, 1584(t1)
	sd t0, 1592(t1)
	sd t0, 1600(t1)
	sd t0, 1608(t1)
	sd t0, 1616(t1)
	sd t0, 1624(t1)
	sd t0, 1632(t1)
	sd t0, 1640(t1)
	sd t0, 1648(t1)
	sd t0, 1656(t1)
	sd t0, 1664(t1)
	sd t0, 1672(t1)
	sd t0, 1680(t1)
	sd t0, 1688(t1)
	sd t0, 1696(t1)
	sd t0, 1704(t1)
	sd t0, 1712(t1)
	sd t0, 1720(t1)
	sd t0, 1728(t1)
	sd t0, 1736(t1)
	sd t0, 1744(t1)
	sd t0, 1752(t1)
	sd t0, 1760(t1)
	sd t0, 1768(t1)
	sd t0, 1776(t1)
	sd t0, 1784(t1)
	sd t0, 1792(t1)
	sd t0, 1800(t1)
	sd t0, 1808(t1)
	sd t0, 1816(t1)
	sd t0, 1824(t1)
	sd t0, 1832(t1)
	sd t0, 1840(t1)
	sd t0, 1848(t1)
	sd t0, 1856(t1)
	sd t0, 1864(t1)
	sd t0, 1872(t1)
	sd t0, 1880(t1)
	sd t0, 1888(t1)
	sd t0, 1896(t1)
	sd t0, 1904(t1)
	sd t0, 1912(t1)
	sd t0, 1920(t1)
	sd t0, 1928(t1)
	sd t0, 1936(t1)
	sd t0, 1944(t1)
	sd t0, 1952(t1)
	sd t0, 1960(t1)
	sd t0, 1968(t1)
	sd t0, 1976(t1)
	sd t0, 1984(t1)
	sd t0, 1992(t1)
	sd t0, 2000(t1)
	sd t0, 2008(t1)
	sd t0, 2016(t1)
	sd t0, 2024(t1)
	sd t0, 2032(t1)
	sd t0, 2040(t1)
	addi sp, sp, -112
	addi t1, sp, 0
	sd t0, 0(t1)
	sd t0, 8(t1)
	sd t0, 16(t1)
	sd t0, 24(t1)
	sd t0, 32(t1)
	sd t0, 40(t1)
	sd t0, 48(t1)
	sd t0, 56(t1)
	sd t0, 64(t1)
	sd t0, 72(t1)
	sd t0, 80(t1)
	sd t0, 88(t1)
	sd t0, 96(t1)
	sd t0, 104(t1)
	addi sp, sp, 112
	addi sp, sp, 16
	addi sp, sp, 2032
	addi sp, sp, 16
	addi sp, sp, 2032
	addi a0, zero, 0
	addi a1, zero, 0
	addi a2, zero, 0
	addi a3, zero, 0
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	addi a7, zero, 0
	addi t0, zero, 0
	addi t1, zero, 0
	addi t2, zero, 0
	addi t3, zero, 0
	addi t4, zero, 0
	addi t5, zero, 0
	addi t6, zero, 0
	ret
	.option pop

vg_aes_gcm_stream_verify_bitsliced:
	.option push
	.option arch, +m, +c
	addi sp, sp, -2032
	addi sp, sp, -544
	addi t0, sp, 0
	addi t1, t0, 8
	sd t1, 0(t0)
	addi t2, a7, 0
	addi a7, sp, 0
	ld a7, 0(a7)
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
	addi s7, t2, 0
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
	addi a0, s7, 0
	addi a1, s3, 0
	addi a2, s1, 0
	addi a3, s0, 0
	addi a4, zero, 1
	addi a5, s0, 512
	call {vg_aes_ctr32_bs}
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
	addi sp, sp, 544
	addi sp, sp, 2032
	addi t0, zero, 0
	addi sp, sp, -2032
	addi sp, sp, -16
	addi t1, sp, 0
	sd t0, 0(t1)
	sd t0, 8(t1)
	sd t0, 16(t1)
	sd t0, 24(t1)
	sd t0, 32(t1)
	sd t0, 40(t1)
	sd t0, 48(t1)
	sd t0, 56(t1)
	sd t0, 64(t1)
	sd t0, 72(t1)
	sd t0, 80(t1)
	sd t0, 88(t1)
	sd t0, 96(t1)
	sd t0, 104(t1)
	sd t0, 112(t1)
	sd t0, 120(t1)
	sd t0, 128(t1)
	sd t0, 136(t1)
	sd t0, 144(t1)
	sd t0, 152(t1)
	sd t0, 160(t1)
	sd t0, 168(t1)
	sd t0, 176(t1)
	sd t0, 184(t1)
	sd t0, 192(t1)
	sd t0, 200(t1)
	sd t0, 208(t1)
	sd t0, 216(t1)
	sd t0, 224(t1)
	sd t0, 232(t1)
	sd t0, 240(t1)
	sd t0, 248(t1)
	sd t0, 256(t1)
	sd t0, 264(t1)
	sd t0, 272(t1)
	sd t0, 280(t1)
	sd t0, 288(t1)
	sd t0, 296(t1)
	sd t0, 304(t1)
	sd t0, 312(t1)
	sd t0, 320(t1)
	sd t0, 328(t1)
	sd t0, 336(t1)
	sd t0, 344(t1)
	sd t0, 352(t1)
	sd t0, 360(t1)
	sd t0, 368(t1)
	sd t0, 376(t1)
	sd t0, 384(t1)
	sd t0, 392(t1)
	sd t0, 400(t1)
	sd t0, 408(t1)
	sd t0, 416(t1)
	sd t0, 424(t1)
	sd t0, 432(t1)
	sd t0, 440(t1)
	sd t0, 448(t1)
	sd t0, 456(t1)
	sd t0, 464(t1)
	sd t0, 472(t1)
	sd t0, 480(t1)
	sd t0, 488(t1)
	sd t0, 496(t1)
	sd t0, 504(t1)
	sd t0, 512(t1)
	sd t0, 520(t1)
	sd t0, 528(t1)
	sd t0, 536(t1)
	sd t0, 544(t1)
	sd t0, 552(t1)
	sd t0, 560(t1)
	sd t0, 568(t1)
	sd t0, 576(t1)
	sd t0, 584(t1)
	sd t0, 592(t1)
	sd t0, 600(t1)
	sd t0, 608(t1)
	sd t0, 616(t1)
	sd t0, 624(t1)
	sd t0, 632(t1)
	sd t0, 640(t1)
	sd t0, 648(t1)
	sd t0, 656(t1)
	sd t0, 664(t1)
	sd t0, 672(t1)
	sd t0, 680(t1)
	sd t0, 688(t1)
	sd t0, 696(t1)
	sd t0, 704(t1)
	sd t0, 712(t1)
	sd t0, 720(t1)
	sd t0, 728(t1)
	sd t0, 736(t1)
	sd t0, 744(t1)
	sd t0, 752(t1)
	sd t0, 760(t1)
	sd t0, 768(t1)
	sd t0, 776(t1)
	sd t0, 784(t1)
	sd t0, 792(t1)
	sd t0, 800(t1)
	sd t0, 808(t1)
	sd t0, 816(t1)
	sd t0, 824(t1)
	sd t0, 832(t1)
	sd t0, 840(t1)
	sd t0, 848(t1)
	sd t0, 856(t1)
	sd t0, 864(t1)
	sd t0, 872(t1)
	sd t0, 880(t1)
	sd t0, 888(t1)
	sd t0, 896(t1)
	sd t0, 904(t1)
	sd t0, 912(t1)
	sd t0, 920(t1)
	sd t0, 928(t1)
	sd t0, 936(t1)
	sd t0, 944(t1)
	sd t0, 952(t1)
	sd t0, 960(t1)
	sd t0, 968(t1)
	sd t0, 976(t1)
	sd t0, 984(t1)
	sd t0, 992(t1)
	sd t0, 1000(t1)
	sd t0, 1008(t1)
	sd t0, 1016(t1)
	sd t0, 1024(t1)
	sd t0, 1032(t1)
	sd t0, 1040(t1)
	sd t0, 1048(t1)
	sd t0, 1056(t1)
	sd t0, 1064(t1)
	sd t0, 1072(t1)
	sd t0, 1080(t1)
	sd t0, 1088(t1)
	sd t0, 1096(t1)
	sd t0, 1104(t1)
	sd t0, 1112(t1)
	sd t0, 1120(t1)
	sd t0, 1128(t1)
	sd t0, 1136(t1)
	sd t0, 1144(t1)
	sd t0, 1152(t1)
	sd t0, 1160(t1)
	sd t0, 1168(t1)
	sd t0, 1176(t1)
	sd t0, 1184(t1)
	sd t0, 1192(t1)
	sd t0, 1200(t1)
	sd t0, 1208(t1)
	sd t0, 1216(t1)
	sd t0, 1224(t1)
	sd t0, 1232(t1)
	sd t0, 1240(t1)
	sd t0, 1248(t1)
	sd t0, 1256(t1)
	sd t0, 1264(t1)
	sd t0, 1272(t1)
	sd t0, 1280(t1)
	sd t0, 1288(t1)
	sd t0, 1296(t1)
	sd t0, 1304(t1)
	sd t0, 1312(t1)
	sd t0, 1320(t1)
	sd t0, 1328(t1)
	sd t0, 1336(t1)
	sd t0, 1344(t1)
	sd t0, 1352(t1)
	sd t0, 1360(t1)
	sd t0, 1368(t1)
	sd t0, 1376(t1)
	sd t0, 1384(t1)
	sd t0, 1392(t1)
	sd t0, 1400(t1)
	sd t0, 1408(t1)
	sd t0, 1416(t1)
	sd t0, 1424(t1)
	sd t0, 1432(t1)
	sd t0, 1440(t1)
	sd t0, 1448(t1)
	sd t0, 1456(t1)
	sd t0, 1464(t1)
	sd t0, 1472(t1)
	sd t0, 1480(t1)
	sd t0, 1488(t1)
	sd t0, 1496(t1)
	sd t0, 1504(t1)
	sd t0, 1512(t1)
	sd t0, 1520(t1)
	sd t0, 1528(t1)
	sd t0, 1536(t1)
	sd t0, 1544(t1)
	sd t0, 1552(t1)
	sd t0, 1560(t1)
	sd t0, 1568(t1)
	sd t0, 1576(t1)
	sd t0, 1584(t1)
	sd t0, 1592(t1)
	sd t0, 1600(t1)
	sd t0, 1608(t1)
	sd t0, 1616(t1)
	sd t0, 1624(t1)
	sd t0, 1632(t1)
	sd t0, 1640(t1)
	sd t0, 1648(t1)
	sd t0, 1656(t1)
	sd t0, 1664(t1)
	sd t0, 1672(t1)
	sd t0, 1680(t1)
	sd t0, 1688(t1)
	sd t0, 1696(t1)
	sd t0, 1704(t1)
	sd t0, 1712(t1)
	sd t0, 1720(t1)
	sd t0, 1728(t1)
	sd t0, 1736(t1)
	sd t0, 1744(t1)
	sd t0, 1752(t1)
	sd t0, 1760(t1)
	sd t0, 1768(t1)
	sd t0, 1776(t1)
	sd t0, 1784(t1)
	sd t0, 1792(t1)
	sd t0, 1800(t1)
	sd t0, 1808(t1)
	sd t0, 1816(t1)
	sd t0, 1824(t1)
	sd t0, 1832(t1)
	sd t0, 1840(t1)
	sd t0, 1848(t1)
	sd t0, 1856(t1)
	sd t0, 1864(t1)
	sd t0, 1872(t1)
	sd t0, 1880(t1)
	sd t0, 1888(t1)
	sd t0, 1896(t1)
	sd t0, 1904(t1)
	sd t0, 1912(t1)
	sd t0, 1920(t1)
	sd t0, 1928(t1)
	sd t0, 1936(t1)
	sd t0, 1944(t1)
	sd t0, 1952(t1)
	sd t0, 1960(t1)
	sd t0, 1968(t1)
	sd t0, 1976(t1)
	sd t0, 1984(t1)
	sd t0, 1992(t1)
	sd t0, 2000(t1)
	sd t0, 2008(t1)
	sd t0, 2016(t1)
	sd t0, 2024(t1)
	sd t0, 2032(t1)
	sd t0, 2040(t1)
	addi sp, sp, -2032
	addi sp, sp, -16
	addi t1, sp, 0
	sd t0, 0(t1)
	sd t0, 8(t1)
	sd t0, 16(t1)
	sd t0, 24(t1)
	sd t0, 32(t1)
	sd t0, 40(t1)
	sd t0, 48(t1)
	sd t0, 56(t1)
	sd t0, 64(t1)
	sd t0, 72(t1)
	sd t0, 80(t1)
	sd t0, 88(t1)
	sd t0, 96(t1)
	sd t0, 104(t1)
	sd t0, 112(t1)
	sd t0, 120(t1)
	sd t0, 128(t1)
	sd t0, 136(t1)
	sd t0, 144(t1)
	sd t0, 152(t1)
	sd t0, 160(t1)
	sd t0, 168(t1)
	sd t0, 176(t1)
	sd t0, 184(t1)
	sd t0, 192(t1)
	sd t0, 200(t1)
	sd t0, 208(t1)
	sd t0, 216(t1)
	sd t0, 224(t1)
	sd t0, 232(t1)
	sd t0, 240(t1)
	sd t0, 248(t1)
	sd t0, 256(t1)
	sd t0, 264(t1)
	sd t0, 272(t1)
	sd t0, 280(t1)
	sd t0, 288(t1)
	sd t0, 296(t1)
	sd t0, 304(t1)
	sd t0, 312(t1)
	sd t0, 320(t1)
	sd t0, 328(t1)
	sd t0, 336(t1)
	sd t0, 344(t1)
	sd t0, 352(t1)
	sd t0, 360(t1)
	sd t0, 368(t1)
	sd t0, 376(t1)
	sd t0, 384(t1)
	sd t0, 392(t1)
	sd t0, 400(t1)
	sd t0, 408(t1)
	sd t0, 416(t1)
	sd t0, 424(t1)
	sd t0, 432(t1)
	sd t0, 440(t1)
	sd t0, 448(t1)
	sd t0, 456(t1)
	sd t0, 464(t1)
	sd t0, 472(t1)
	sd t0, 480(t1)
	sd t0, 488(t1)
	sd t0, 496(t1)
	sd t0, 504(t1)
	sd t0, 512(t1)
	sd t0, 520(t1)
	sd t0, 528(t1)
	sd t0, 536(t1)
	sd t0, 544(t1)
	sd t0, 552(t1)
	sd t0, 560(t1)
	sd t0, 568(t1)
	sd t0, 576(t1)
	sd t0, 584(t1)
	sd t0, 592(t1)
	sd t0, 600(t1)
	sd t0, 608(t1)
	sd t0, 616(t1)
	sd t0, 624(t1)
	sd t0, 632(t1)
	sd t0, 640(t1)
	sd t0, 648(t1)
	sd t0, 656(t1)
	sd t0, 664(t1)
	sd t0, 672(t1)
	sd t0, 680(t1)
	sd t0, 688(t1)
	sd t0, 696(t1)
	sd t0, 704(t1)
	sd t0, 712(t1)
	sd t0, 720(t1)
	sd t0, 728(t1)
	sd t0, 736(t1)
	sd t0, 744(t1)
	sd t0, 752(t1)
	sd t0, 760(t1)
	sd t0, 768(t1)
	sd t0, 776(t1)
	sd t0, 784(t1)
	sd t0, 792(t1)
	sd t0, 800(t1)
	sd t0, 808(t1)
	sd t0, 816(t1)
	sd t0, 824(t1)
	sd t0, 832(t1)
	sd t0, 840(t1)
	sd t0, 848(t1)
	sd t0, 856(t1)
	sd t0, 864(t1)
	sd t0, 872(t1)
	sd t0, 880(t1)
	sd t0, 888(t1)
	sd t0, 896(t1)
	sd t0, 904(t1)
	sd t0, 912(t1)
	sd t0, 920(t1)
	sd t0, 928(t1)
	sd t0, 936(t1)
	sd t0, 944(t1)
	sd t0, 952(t1)
	sd t0, 960(t1)
	sd t0, 968(t1)
	sd t0, 976(t1)
	sd t0, 984(t1)
	sd t0, 992(t1)
	sd t0, 1000(t1)
	sd t0, 1008(t1)
	sd t0, 1016(t1)
	sd t0, 1024(t1)
	sd t0, 1032(t1)
	sd t0, 1040(t1)
	sd t0, 1048(t1)
	sd t0, 1056(t1)
	sd t0, 1064(t1)
	sd t0, 1072(t1)
	sd t0, 1080(t1)
	sd t0, 1088(t1)
	sd t0, 1096(t1)
	sd t0, 1104(t1)
	sd t0, 1112(t1)
	sd t0, 1120(t1)
	sd t0, 1128(t1)
	sd t0, 1136(t1)
	sd t0, 1144(t1)
	sd t0, 1152(t1)
	sd t0, 1160(t1)
	sd t0, 1168(t1)
	sd t0, 1176(t1)
	sd t0, 1184(t1)
	sd t0, 1192(t1)
	sd t0, 1200(t1)
	sd t0, 1208(t1)
	sd t0, 1216(t1)
	sd t0, 1224(t1)
	sd t0, 1232(t1)
	sd t0, 1240(t1)
	sd t0, 1248(t1)
	sd t0, 1256(t1)
	sd t0, 1264(t1)
	sd t0, 1272(t1)
	sd t0, 1280(t1)
	sd t0, 1288(t1)
	sd t0, 1296(t1)
	sd t0, 1304(t1)
	sd t0, 1312(t1)
	sd t0, 1320(t1)
	sd t0, 1328(t1)
	sd t0, 1336(t1)
	sd t0, 1344(t1)
	sd t0, 1352(t1)
	sd t0, 1360(t1)
	sd t0, 1368(t1)
	sd t0, 1376(t1)
	sd t0, 1384(t1)
	sd t0, 1392(t1)
	sd t0, 1400(t1)
	sd t0, 1408(t1)
	sd t0, 1416(t1)
	sd t0, 1424(t1)
	sd t0, 1432(t1)
	sd t0, 1440(t1)
	sd t0, 1448(t1)
	sd t0, 1456(t1)
	sd t0, 1464(t1)
	sd t0, 1472(t1)
	sd t0, 1480(t1)
	sd t0, 1488(t1)
	sd t0, 1496(t1)
	sd t0, 1504(t1)
	sd t0, 1512(t1)
	sd t0, 1520(t1)
	sd t0, 1528(t1)
	sd t0, 1536(t1)
	sd t0, 1544(t1)
	sd t0, 1552(t1)
	sd t0, 1560(t1)
	sd t0, 1568(t1)
	sd t0, 1576(t1)
	sd t0, 1584(t1)
	sd t0, 1592(t1)
	sd t0, 1600(t1)
	sd t0, 1608(t1)
	sd t0, 1616(t1)
	sd t0, 1624(t1)
	sd t0, 1632(t1)
	sd t0, 1640(t1)
	sd t0, 1648(t1)
	sd t0, 1656(t1)
	sd t0, 1664(t1)
	sd t0, 1672(t1)
	sd t0, 1680(t1)
	sd t0, 1688(t1)
	sd t0, 1696(t1)
	sd t0, 1704(t1)
	sd t0, 1712(t1)
	sd t0, 1720(t1)
	sd t0, 1728(t1)
	sd t0, 1736(t1)
	sd t0, 1744(t1)
	sd t0, 1752(t1)
	sd t0, 1760(t1)
	sd t0, 1768(t1)
	sd t0, 1776(t1)
	sd t0, 1784(t1)
	sd t0, 1792(t1)
	sd t0, 1800(t1)
	sd t0, 1808(t1)
	sd t0, 1816(t1)
	sd t0, 1824(t1)
	sd t0, 1832(t1)
	sd t0, 1840(t1)
	sd t0, 1848(t1)
	sd t0, 1856(t1)
	sd t0, 1864(t1)
	sd t0, 1872(t1)
	sd t0, 1880(t1)
	sd t0, 1888(t1)
	sd t0, 1896(t1)
	sd t0, 1904(t1)
	sd t0, 1912(t1)
	sd t0, 1920(t1)
	sd t0, 1928(t1)
	sd t0, 1936(t1)
	sd t0, 1944(t1)
	sd t0, 1952(t1)
	sd t0, 1960(t1)
	sd t0, 1968(t1)
	sd t0, 1976(t1)
	sd t0, 1984(t1)
	sd t0, 1992(t1)
	sd t0, 2000(t1)
	sd t0, 2008(t1)
	sd t0, 2016(t1)
	sd t0, 2024(t1)
	sd t0, 2032(t1)
	sd t0, 2040(t1)
	addi sp, sp, -128
	addi t1, sp, 0
	sd t0, 0(t1)
	sd t0, 8(t1)
	sd t0, 16(t1)
	sd t0, 24(t1)
	sd t0, 32(t1)
	sd t0, 40(t1)
	sd t0, 48(t1)
	sd t0, 56(t1)
	sd t0, 64(t1)
	sd t0, 72(t1)
	sd t0, 80(t1)
	sd t0, 88(t1)
	sd t0, 96(t1)
	sd t0, 104(t1)
	sd t0, 112(t1)
	sd t0, 120(t1)
	addi sp, sp, 128
	addi sp, sp, 16
	addi sp, sp, 2032
	addi sp, sp, 16
	addi sp, sp, 2032
	slli a0, a0, 32
	srli a0, a0, 32
	addi a1, zero, 0
	addi a2, zero, 0
	addi a3, zero, 0
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	addi a7, zero, 0
	addi t0, zero, 0
	addi t1, zero, 0
	addi t2, zero, 0
	addi t3, zero, 0
	addi t4, zero, 0
	addi t5, zero, 0
	addi t6, zero, 0
	ret
	.option pop

vg_aes_gcm_seal_bitsliced:
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
	addi t2, sp, 0
	ld s7, 8(t2)
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
	addi a0, s7, 0
	addi a1, s3, 0
	addi a2, s1, 48
	addi a5, s0, 512
	call {vg_aes_ctr32_bs}
	j 250f
249:
250:
	beqz s5, 251f
	addi t0, zero, 0
	sd t0, 64(s1)
	sd t0, 72(s1)
	addi a3, s1, 64
	addi a4, zero, 1
	addi a0, s7, 0
	addi a1, s3, 0
	addi a2, s1, 48
	addi a5, s0, 512
	call {vg_aes_ctr32_bs}
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
	addi a0, s7, 0
	addi a1, s3, 0
	addi a2, s1, 0
	addi a3, s0, 0
	addi a4, zero, 1
	addi a5, s0, 512
	call {vg_aes_ctr32_bs}
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
	addi sp, sp, 560
	addi sp, sp, 2032
	addi t0, zero, 0
	addi sp, sp, -2032
	addi sp, sp, -16
	addi t1, sp, 0
	sd t0, 0(t1)
	sd t0, 8(t1)
	sd t0, 16(t1)
	sd t0, 24(t1)
	sd t0, 32(t1)
	sd t0, 40(t1)
	sd t0, 48(t1)
	sd t0, 56(t1)
	sd t0, 64(t1)
	sd t0, 72(t1)
	sd t0, 80(t1)
	sd t0, 88(t1)
	sd t0, 96(t1)
	sd t0, 104(t1)
	sd t0, 112(t1)
	sd t0, 120(t1)
	sd t0, 128(t1)
	sd t0, 136(t1)
	sd t0, 144(t1)
	sd t0, 152(t1)
	sd t0, 160(t1)
	sd t0, 168(t1)
	sd t0, 176(t1)
	sd t0, 184(t1)
	sd t0, 192(t1)
	sd t0, 200(t1)
	sd t0, 208(t1)
	sd t0, 216(t1)
	sd t0, 224(t1)
	sd t0, 232(t1)
	sd t0, 240(t1)
	sd t0, 248(t1)
	sd t0, 256(t1)
	sd t0, 264(t1)
	sd t0, 272(t1)
	sd t0, 280(t1)
	sd t0, 288(t1)
	sd t0, 296(t1)
	sd t0, 304(t1)
	sd t0, 312(t1)
	sd t0, 320(t1)
	sd t0, 328(t1)
	sd t0, 336(t1)
	sd t0, 344(t1)
	sd t0, 352(t1)
	sd t0, 360(t1)
	sd t0, 368(t1)
	sd t0, 376(t1)
	sd t0, 384(t1)
	sd t0, 392(t1)
	sd t0, 400(t1)
	sd t0, 408(t1)
	sd t0, 416(t1)
	sd t0, 424(t1)
	sd t0, 432(t1)
	sd t0, 440(t1)
	sd t0, 448(t1)
	sd t0, 456(t1)
	sd t0, 464(t1)
	sd t0, 472(t1)
	sd t0, 480(t1)
	sd t0, 488(t1)
	sd t0, 496(t1)
	sd t0, 504(t1)
	sd t0, 512(t1)
	sd t0, 520(t1)
	sd t0, 528(t1)
	sd t0, 536(t1)
	sd t0, 544(t1)
	sd t0, 552(t1)
	sd t0, 560(t1)
	sd t0, 568(t1)
	sd t0, 576(t1)
	sd t0, 584(t1)
	sd t0, 592(t1)
	sd t0, 600(t1)
	sd t0, 608(t1)
	sd t0, 616(t1)
	sd t0, 624(t1)
	sd t0, 632(t1)
	sd t0, 640(t1)
	sd t0, 648(t1)
	sd t0, 656(t1)
	sd t0, 664(t1)
	sd t0, 672(t1)
	sd t0, 680(t1)
	sd t0, 688(t1)
	sd t0, 696(t1)
	sd t0, 704(t1)
	sd t0, 712(t1)
	sd t0, 720(t1)
	sd t0, 728(t1)
	sd t0, 736(t1)
	sd t0, 744(t1)
	sd t0, 752(t1)
	sd t0, 760(t1)
	sd t0, 768(t1)
	sd t0, 776(t1)
	sd t0, 784(t1)
	sd t0, 792(t1)
	sd t0, 800(t1)
	sd t0, 808(t1)
	sd t0, 816(t1)
	sd t0, 824(t1)
	sd t0, 832(t1)
	sd t0, 840(t1)
	sd t0, 848(t1)
	sd t0, 856(t1)
	sd t0, 864(t1)
	sd t0, 872(t1)
	sd t0, 880(t1)
	sd t0, 888(t1)
	sd t0, 896(t1)
	sd t0, 904(t1)
	sd t0, 912(t1)
	sd t0, 920(t1)
	sd t0, 928(t1)
	sd t0, 936(t1)
	sd t0, 944(t1)
	sd t0, 952(t1)
	sd t0, 960(t1)
	sd t0, 968(t1)
	sd t0, 976(t1)
	sd t0, 984(t1)
	sd t0, 992(t1)
	sd t0, 1000(t1)
	sd t0, 1008(t1)
	sd t0, 1016(t1)
	sd t0, 1024(t1)
	sd t0, 1032(t1)
	sd t0, 1040(t1)
	sd t0, 1048(t1)
	sd t0, 1056(t1)
	sd t0, 1064(t1)
	sd t0, 1072(t1)
	sd t0, 1080(t1)
	sd t0, 1088(t1)
	sd t0, 1096(t1)
	sd t0, 1104(t1)
	sd t0, 1112(t1)
	sd t0, 1120(t1)
	sd t0, 1128(t1)
	sd t0, 1136(t1)
	sd t0, 1144(t1)
	sd t0, 1152(t1)
	sd t0, 1160(t1)
	sd t0, 1168(t1)
	sd t0, 1176(t1)
	sd t0, 1184(t1)
	sd t0, 1192(t1)
	sd t0, 1200(t1)
	sd t0, 1208(t1)
	sd t0, 1216(t1)
	sd t0, 1224(t1)
	sd t0, 1232(t1)
	sd t0, 1240(t1)
	sd t0, 1248(t1)
	sd t0, 1256(t1)
	sd t0, 1264(t1)
	sd t0, 1272(t1)
	sd t0, 1280(t1)
	sd t0, 1288(t1)
	sd t0, 1296(t1)
	sd t0, 1304(t1)
	sd t0, 1312(t1)
	sd t0, 1320(t1)
	sd t0, 1328(t1)
	sd t0, 1336(t1)
	sd t0, 1344(t1)
	sd t0, 1352(t1)
	sd t0, 1360(t1)
	sd t0, 1368(t1)
	sd t0, 1376(t1)
	sd t0, 1384(t1)
	sd t0, 1392(t1)
	sd t0, 1400(t1)
	sd t0, 1408(t1)
	sd t0, 1416(t1)
	sd t0, 1424(t1)
	sd t0, 1432(t1)
	sd t0, 1440(t1)
	sd t0, 1448(t1)
	sd t0, 1456(t1)
	sd t0, 1464(t1)
	sd t0, 1472(t1)
	sd t0, 1480(t1)
	sd t0, 1488(t1)
	sd t0, 1496(t1)
	sd t0, 1504(t1)
	sd t0, 1512(t1)
	sd t0, 1520(t1)
	sd t0, 1528(t1)
	sd t0, 1536(t1)
	sd t0, 1544(t1)
	sd t0, 1552(t1)
	sd t0, 1560(t1)
	sd t0, 1568(t1)
	sd t0, 1576(t1)
	sd t0, 1584(t1)
	sd t0, 1592(t1)
	sd t0, 1600(t1)
	sd t0, 1608(t1)
	sd t0, 1616(t1)
	sd t0, 1624(t1)
	sd t0, 1632(t1)
	sd t0, 1640(t1)
	sd t0, 1648(t1)
	sd t0, 1656(t1)
	sd t0, 1664(t1)
	sd t0, 1672(t1)
	sd t0, 1680(t1)
	sd t0, 1688(t1)
	sd t0, 1696(t1)
	sd t0, 1704(t1)
	sd t0, 1712(t1)
	sd t0, 1720(t1)
	sd t0, 1728(t1)
	sd t0, 1736(t1)
	sd t0, 1744(t1)
	sd t0, 1752(t1)
	sd t0, 1760(t1)
	sd t0, 1768(t1)
	sd t0, 1776(t1)
	sd t0, 1784(t1)
	sd t0, 1792(t1)
	sd t0, 1800(t1)
	sd t0, 1808(t1)
	sd t0, 1816(t1)
	sd t0, 1824(t1)
	sd t0, 1832(t1)
	sd t0, 1840(t1)
	sd t0, 1848(t1)
	sd t0, 1856(t1)
	sd t0, 1864(t1)
	sd t0, 1872(t1)
	sd t0, 1880(t1)
	sd t0, 1888(t1)
	sd t0, 1896(t1)
	sd t0, 1904(t1)
	sd t0, 1912(t1)
	sd t0, 1920(t1)
	sd t0, 1928(t1)
	sd t0, 1936(t1)
	sd t0, 1944(t1)
	sd t0, 1952(t1)
	sd t0, 1960(t1)
	sd t0, 1968(t1)
	sd t0, 1976(t1)
	sd t0, 1984(t1)
	sd t0, 1992(t1)
	sd t0, 2000(t1)
	sd t0, 2008(t1)
	sd t0, 2016(t1)
	sd t0, 2024(t1)
	sd t0, 2032(t1)
	sd t0, 2040(t1)
	addi sp, sp, -2032
	addi sp, sp, -16
	addi t1, sp, 0
	sd t0, 0(t1)
	sd t0, 8(t1)
	sd t0, 16(t1)
	sd t0, 24(t1)
	sd t0, 32(t1)
	sd t0, 40(t1)
	sd t0, 48(t1)
	sd t0, 56(t1)
	sd t0, 64(t1)
	sd t0, 72(t1)
	sd t0, 80(t1)
	sd t0, 88(t1)
	sd t0, 96(t1)
	sd t0, 104(t1)
	sd t0, 112(t1)
	sd t0, 120(t1)
	sd t0, 128(t1)
	sd t0, 136(t1)
	sd t0, 144(t1)
	sd t0, 152(t1)
	sd t0, 160(t1)
	sd t0, 168(t1)
	sd t0, 176(t1)
	sd t0, 184(t1)
	sd t0, 192(t1)
	sd t0, 200(t1)
	sd t0, 208(t1)
	sd t0, 216(t1)
	sd t0, 224(t1)
	sd t0, 232(t1)
	sd t0, 240(t1)
	sd t0, 248(t1)
	sd t0, 256(t1)
	sd t0, 264(t1)
	sd t0, 272(t1)
	sd t0, 280(t1)
	sd t0, 288(t1)
	sd t0, 296(t1)
	sd t0, 304(t1)
	sd t0, 312(t1)
	sd t0, 320(t1)
	sd t0, 328(t1)
	sd t0, 336(t1)
	sd t0, 344(t1)
	sd t0, 352(t1)
	sd t0, 360(t1)
	sd t0, 368(t1)
	sd t0, 376(t1)
	sd t0, 384(t1)
	sd t0, 392(t1)
	sd t0, 400(t1)
	sd t0, 408(t1)
	sd t0, 416(t1)
	sd t0, 424(t1)
	sd t0, 432(t1)
	sd t0, 440(t1)
	sd t0, 448(t1)
	sd t0, 456(t1)
	sd t0, 464(t1)
	sd t0, 472(t1)
	sd t0, 480(t1)
	sd t0, 488(t1)
	sd t0, 496(t1)
	sd t0, 504(t1)
	sd t0, 512(t1)
	sd t0, 520(t1)
	sd t0, 528(t1)
	sd t0, 536(t1)
	sd t0, 544(t1)
	sd t0, 552(t1)
	sd t0, 560(t1)
	sd t0, 568(t1)
	sd t0, 576(t1)
	sd t0, 584(t1)
	sd t0, 592(t1)
	sd t0, 600(t1)
	sd t0, 608(t1)
	sd t0, 616(t1)
	sd t0, 624(t1)
	sd t0, 632(t1)
	sd t0, 640(t1)
	sd t0, 648(t1)
	sd t0, 656(t1)
	sd t0, 664(t1)
	sd t0, 672(t1)
	sd t0, 680(t1)
	sd t0, 688(t1)
	sd t0, 696(t1)
	sd t0, 704(t1)
	sd t0, 712(t1)
	sd t0, 720(t1)
	sd t0, 728(t1)
	sd t0, 736(t1)
	sd t0, 744(t1)
	sd t0, 752(t1)
	sd t0, 760(t1)
	sd t0, 768(t1)
	sd t0, 776(t1)
	sd t0, 784(t1)
	sd t0, 792(t1)
	sd t0, 800(t1)
	sd t0, 808(t1)
	sd t0, 816(t1)
	sd t0, 824(t1)
	sd t0, 832(t1)
	sd t0, 840(t1)
	sd t0, 848(t1)
	sd t0, 856(t1)
	sd t0, 864(t1)
	sd t0, 872(t1)
	sd t0, 880(t1)
	sd t0, 888(t1)
	sd t0, 896(t1)
	sd t0, 904(t1)
	sd t0, 912(t1)
	sd t0, 920(t1)
	sd t0, 928(t1)
	sd t0, 936(t1)
	sd t0, 944(t1)
	sd t0, 952(t1)
	sd t0, 960(t1)
	sd t0, 968(t1)
	sd t0, 976(t1)
	sd t0, 984(t1)
	sd t0, 992(t1)
	sd t0, 1000(t1)
	sd t0, 1008(t1)
	sd t0, 1016(t1)
	sd t0, 1024(t1)
	sd t0, 1032(t1)
	sd t0, 1040(t1)
	sd t0, 1048(t1)
	sd t0, 1056(t1)
	sd t0, 1064(t1)
	sd t0, 1072(t1)
	sd t0, 1080(t1)
	sd t0, 1088(t1)
	sd t0, 1096(t1)
	sd t0, 1104(t1)
	sd t0, 1112(t1)
	sd t0, 1120(t1)
	sd t0, 1128(t1)
	sd t0, 1136(t1)
	sd t0, 1144(t1)
	sd t0, 1152(t1)
	sd t0, 1160(t1)
	sd t0, 1168(t1)
	sd t0, 1176(t1)
	sd t0, 1184(t1)
	sd t0, 1192(t1)
	sd t0, 1200(t1)
	sd t0, 1208(t1)
	sd t0, 1216(t1)
	sd t0, 1224(t1)
	sd t0, 1232(t1)
	sd t0, 1240(t1)
	sd t0, 1248(t1)
	sd t0, 1256(t1)
	sd t0, 1264(t1)
	sd t0, 1272(t1)
	sd t0, 1280(t1)
	sd t0, 1288(t1)
	sd t0, 1296(t1)
	sd t0, 1304(t1)
	sd t0, 1312(t1)
	sd t0, 1320(t1)
	sd t0, 1328(t1)
	sd t0, 1336(t1)
	sd t0, 1344(t1)
	sd t0, 1352(t1)
	sd t0, 1360(t1)
	sd t0, 1368(t1)
	sd t0, 1376(t1)
	sd t0, 1384(t1)
	sd t0, 1392(t1)
	sd t0, 1400(t1)
	sd t0, 1408(t1)
	sd t0, 1416(t1)
	sd t0, 1424(t1)
	sd t0, 1432(t1)
	sd t0, 1440(t1)
	sd t0, 1448(t1)
	sd t0, 1456(t1)
	sd t0, 1464(t1)
	sd t0, 1472(t1)
	sd t0, 1480(t1)
	sd t0, 1488(t1)
	sd t0, 1496(t1)
	sd t0, 1504(t1)
	sd t0, 1512(t1)
	sd t0, 1520(t1)
	sd t0, 1528(t1)
	sd t0, 1536(t1)
	sd t0, 1544(t1)
	sd t0, 1552(t1)
	sd t0, 1560(t1)
	sd t0, 1568(t1)
	sd t0, 1576(t1)
	sd t0, 1584(t1)
	sd t0, 1592(t1)
	sd t0, 1600(t1)
	sd t0, 1608(t1)
	sd t0, 1616(t1)
	sd t0, 1624(t1)
	sd t0, 1632(t1)
	sd t0, 1640(t1)
	sd t0, 1648(t1)
	sd t0, 1656(t1)
	sd t0, 1664(t1)
	sd t0, 1672(t1)
	sd t0, 1680(t1)
	sd t0, 1688(t1)
	sd t0, 1696(t1)
	sd t0, 1704(t1)
	sd t0, 1712(t1)
	sd t0, 1720(t1)
	sd t0, 1728(t1)
	sd t0, 1736(t1)
	sd t0, 1744(t1)
	sd t0, 1752(t1)
	sd t0, 1760(t1)
	sd t0, 1768(t1)
	sd t0, 1776(t1)
	sd t0, 1784(t1)
	sd t0, 1792(t1)
	sd t0, 1800(t1)
	sd t0, 1808(t1)
	sd t0, 1816(t1)
	sd t0, 1824(t1)
	sd t0, 1832(t1)
	sd t0, 1840(t1)
	sd t0, 1848(t1)
	sd t0, 1856(t1)
	sd t0, 1864(t1)
	sd t0, 1872(t1)
	sd t0, 1880(t1)
	sd t0, 1888(t1)
	sd t0, 1896(t1)
	sd t0, 1904(t1)
	sd t0, 1912(t1)
	sd t0, 1920(t1)
	sd t0, 1928(t1)
	sd t0, 1936(t1)
	sd t0, 1944(t1)
	sd t0, 1952(t1)
	sd t0, 1960(t1)
	sd t0, 1968(t1)
	sd t0, 1976(t1)
	sd t0, 1984(t1)
	sd t0, 1992(t1)
	sd t0, 2000(t1)
	sd t0, 2008(t1)
	sd t0, 2016(t1)
	sd t0, 2024(t1)
	sd t0, 2032(t1)
	sd t0, 2040(t1)
	addi sp, sp, -144
	addi t1, sp, 0
	sd t0, 0(t1)
	sd t0, 8(t1)
	sd t0, 16(t1)
	sd t0, 24(t1)
	sd t0, 32(t1)
	sd t0, 40(t1)
	sd t0, 48(t1)
	sd t0, 56(t1)
	sd t0, 64(t1)
	sd t0, 72(t1)
	sd t0, 80(t1)
	sd t0, 88(t1)
	sd t0, 96(t1)
	sd t0, 104(t1)
	sd t0, 112(t1)
	sd t0, 120(t1)
	sd t0, 128(t1)
	sd t0, 136(t1)
	addi sp, sp, 144
	addi sp, sp, 16
	addi sp, sp, 2032
	addi sp, sp, 16
	addi sp, sp, 2032
	addi a0, zero, 0
	addi a1, zero, 0
	addi a2, zero, 0
	addi a3, zero, 0
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	addi a7, zero, 0
	addi t0, zero, 0
	addi t1, zero, 0
	addi t2, zero, 0
	addi t3, zero, 0
	addi t4, zero, 0
	addi t5, zero, 0
	addi t6, zero, 0
	ret
	.option pop

vg_aes_gcm_open_bitsliced:
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
	addi t1, t0, 2032
	ld t1, 576(t1)
	sd t1, 16(t0)
	addi t1, t0, 32
	sd t1, 24(t0)
	addi t1, sp, 0
	ld t1, 24(t1)
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
	addi t2, sp, 0
	ld s7, 16(t2)
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
	addi a0, s7, 0
	addi a1, s3, 0
	addi a2, s1, 0
	addi a3, s0, 112
	addi a4, zero, 1
	addi a5, s0, 512
	call {vg_aes_ctr32_bs}
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
	addi a0, s7, 0
	addi a1, s3, 0
	addi a2, s1, 48
	addi a5, s0, 512
	call {vg_aes_ctr32_bs}
	j 281f
280:
281:
	beqz s5, 282f
	addi t0, zero, 0
	sd t0, 64(s1)
	sd t0, 72(s1)
	addi a3, s1, 64
	addi a4, zero, 1
	addi a0, s7, 0
	addi a1, s3, 0
	addi a2, s1, 48
	addi a5, s0, 512
	call {vg_aes_ctr32_bs}
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
	addi t0, zero, 0
	addi sp, sp, -2032
	addi sp, sp, -16
	addi t1, sp, 0
	sd t0, 0(t1)
	sd t0, 8(t1)
	sd t0, 16(t1)
	sd t0, 24(t1)
	sd t0, 32(t1)
	sd t0, 40(t1)
	sd t0, 48(t1)
	sd t0, 56(t1)
	sd t0, 64(t1)
	sd t0, 72(t1)
	sd t0, 80(t1)
	sd t0, 88(t1)
	sd t0, 96(t1)
	sd t0, 104(t1)
	sd t0, 112(t1)
	sd t0, 120(t1)
	sd t0, 128(t1)
	sd t0, 136(t1)
	sd t0, 144(t1)
	sd t0, 152(t1)
	sd t0, 160(t1)
	sd t0, 168(t1)
	sd t0, 176(t1)
	sd t0, 184(t1)
	sd t0, 192(t1)
	sd t0, 200(t1)
	sd t0, 208(t1)
	sd t0, 216(t1)
	sd t0, 224(t1)
	sd t0, 232(t1)
	sd t0, 240(t1)
	sd t0, 248(t1)
	sd t0, 256(t1)
	sd t0, 264(t1)
	sd t0, 272(t1)
	sd t0, 280(t1)
	sd t0, 288(t1)
	sd t0, 296(t1)
	sd t0, 304(t1)
	sd t0, 312(t1)
	sd t0, 320(t1)
	sd t0, 328(t1)
	sd t0, 336(t1)
	sd t0, 344(t1)
	sd t0, 352(t1)
	sd t0, 360(t1)
	sd t0, 368(t1)
	sd t0, 376(t1)
	sd t0, 384(t1)
	sd t0, 392(t1)
	sd t0, 400(t1)
	sd t0, 408(t1)
	sd t0, 416(t1)
	sd t0, 424(t1)
	sd t0, 432(t1)
	sd t0, 440(t1)
	sd t0, 448(t1)
	sd t0, 456(t1)
	sd t0, 464(t1)
	sd t0, 472(t1)
	sd t0, 480(t1)
	sd t0, 488(t1)
	sd t0, 496(t1)
	sd t0, 504(t1)
	sd t0, 512(t1)
	sd t0, 520(t1)
	sd t0, 528(t1)
	sd t0, 536(t1)
	sd t0, 544(t1)
	sd t0, 552(t1)
	sd t0, 560(t1)
	sd t0, 568(t1)
	sd t0, 576(t1)
	sd t0, 584(t1)
	sd t0, 592(t1)
	sd t0, 600(t1)
	sd t0, 608(t1)
	sd t0, 616(t1)
	sd t0, 624(t1)
	sd t0, 632(t1)
	sd t0, 640(t1)
	sd t0, 648(t1)
	sd t0, 656(t1)
	sd t0, 664(t1)
	sd t0, 672(t1)
	sd t0, 680(t1)
	sd t0, 688(t1)
	sd t0, 696(t1)
	sd t0, 704(t1)
	sd t0, 712(t1)
	sd t0, 720(t1)
	sd t0, 728(t1)
	sd t0, 736(t1)
	sd t0, 744(t1)
	sd t0, 752(t1)
	sd t0, 760(t1)
	sd t0, 768(t1)
	sd t0, 776(t1)
	sd t0, 784(t1)
	sd t0, 792(t1)
	sd t0, 800(t1)
	sd t0, 808(t1)
	sd t0, 816(t1)
	sd t0, 824(t1)
	sd t0, 832(t1)
	sd t0, 840(t1)
	sd t0, 848(t1)
	sd t0, 856(t1)
	sd t0, 864(t1)
	sd t0, 872(t1)
	sd t0, 880(t1)
	sd t0, 888(t1)
	sd t0, 896(t1)
	sd t0, 904(t1)
	sd t0, 912(t1)
	sd t0, 920(t1)
	sd t0, 928(t1)
	sd t0, 936(t1)
	sd t0, 944(t1)
	sd t0, 952(t1)
	sd t0, 960(t1)
	sd t0, 968(t1)
	sd t0, 976(t1)
	sd t0, 984(t1)
	sd t0, 992(t1)
	sd t0, 1000(t1)
	sd t0, 1008(t1)
	sd t0, 1016(t1)
	sd t0, 1024(t1)
	sd t0, 1032(t1)
	sd t0, 1040(t1)
	sd t0, 1048(t1)
	sd t0, 1056(t1)
	sd t0, 1064(t1)
	sd t0, 1072(t1)
	sd t0, 1080(t1)
	sd t0, 1088(t1)
	sd t0, 1096(t1)
	sd t0, 1104(t1)
	sd t0, 1112(t1)
	sd t0, 1120(t1)
	sd t0, 1128(t1)
	sd t0, 1136(t1)
	sd t0, 1144(t1)
	sd t0, 1152(t1)
	sd t0, 1160(t1)
	sd t0, 1168(t1)
	sd t0, 1176(t1)
	sd t0, 1184(t1)
	sd t0, 1192(t1)
	sd t0, 1200(t1)
	sd t0, 1208(t1)
	sd t0, 1216(t1)
	sd t0, 1224(t1)
	sd t0, 1232(t1)
	sd t0, 1240(t1)
	sd t0, 1248(t1)
	sd t0, 1256(t1)
	sd t0, 1264(t1)
	sd t0, 1272(t1)
	sd t0, 1280(t1)
	sd t0, 1288(t1)
	sd t0, 1296(t1)
	sd t0, 1304(t1)
	sd t0, 1312(t1)
	sd t0, 1320(t1)
	sd t0, 1328(t1)
	sd t0, 1336(t1)
	sd t0, 1344(t1)
	sd t0, 1352(t1)
	sd t0, 1360(t1)
	sd t0, 1368(t1)
	sd t0, 1376(t1)
	sd t0, 1384(t1)
	sd t0, 1392(t1)
	sd t0, 1400(t1)
	sd t0, 1408(t1)
	sd t0, 1416(t1)
	sd t0, 1424(t1)
	sd t0, 1432(t1)
	sd t0, 1440(t1)
	sd t0, 1448(t1)
	sd t0, 1456(t1)
	sd t0, 1464(t1)
	sd t0, 1472(t1)
	sd t0, 1480(t1)
	sd t0, 1488(t1)
	sd t0, 1496(t1)
	sd t0, 1504(t1)
	sd t0, 1512(t1)
	sd t0, 1520(t1)
	sd t0, 1528(t1)
	sd t0, 1536(t1)
	sd t0, 1544(t1)
	sd t0, 1552(t1)
	sd t0, 1560(t1)
	sd t0, 1568(t1)
	sd t0, 1576(t1)
	sd t0, 1584(t1)
	sd t0, 1592(t1)
	sd t0, 1600(t1)
	sd t0, 1608(t1)
	sd t0, 1616(t1)
	sd t0, 1624(t1)
	sd t0, 1632(t1)
	sd t0, 1640(t1)
	sd t0, 1648(t1)
	sd t0, 1656(t1)
	sd t0, 1664(t1)
	sd t0, 1672(t1)
	sd t0, 1680(t1)
	sd t0, 1688(t1)
	sd t0, 1696(t1)
	sd t0, 1704(t1)
	sd t0, 1712(t1)
	sd t0, 1720(t1)
	sd t0, 1728(t1)
	sd t0, 1736(t1)
	sd t0, 1744(t1)
	sd t0, 1752(t1)
	sd t0, 1760(t1)
	sd t0, 1768(t1)
	sd t0, 1776(t1)
	sd t0, 1784(t1)
	sd t0, 1792(t1)
	sd t0, 1800(t1)
	sd t0, 1808(t1)
	sd t0, 1816(t1)
	sd t0, 1824(t1)
	sd t0, 1832(t1)
	sd t0, 1840(t1)
	sd t0, 1848(t1)
	sd t0, 1856(t1)
	sd t0, 1864(t1)
	sd t0, 1872(t1)
	sd t0, 1880(t1)
	sd t0, 1888(t1)
	sd t0, 1896(t1)
	sd t0, 1904(t1)
	sd t0, 1912(t1)
	sd t0, 1920(t1)
	sd t0, 1928(t1)
	sd t0, 1936(t1)
	sd t0, 1944(t1)
	sd t0, 1952(t1)
	sd t0, 1960(t1)
	sd t0, 1968(t1)
	sd t0, 1976(t1)
	sd t0, 1984(t1)
	sd t0, 1992(t1)
	sd t0, 2000(t1)
	sd t0, 2008(t1)
	sd t0, 2016(t1)
	sd t0, 2024(t1)
	sd t0, 2032(t1)
	sd t0, 2040(t1)
	addi sp, sp, -2032
	addi sp, sp, -16
	addi t1, sp, 0
	sd t0, 0(t1)
	sd t0, 8(t1)
	sd t0, 16(t1)
	sd t0, 24(t1)
	sd t0, 32(t1)
	sd t0, 40(t1)
	sd t0, 48(t1)
	sd t0, 56(t1)
	sd t0, 64(t1)
	sd t0, 72(t1)
	sd t0, 80(t1)
	sd t0, 88(t1)
	sd t0, 96(t1)
	sd t0, 104(t1)
	sd t0, 112(t1)
	sd t0, 120(t1)
	sd t0, 128(t1)
	sd t0, 136(t1)
	sd t0, 144(t1)
	sd t0, 152(t1)
	sd t0, 160(t1)
	sd t0, 168(t1)
	sd t0, 176(t1)
	sd t0, 184(t1)
	sd t0, 192(t1)
	sd t0, 200(t1)
	sd t0, 208(t1)
	sd t0, 216(t1)
	sd t0, 224(t1)
	sd t0, 232(t1)
	sd t0, 240(t1)
	sd t0, 248(t1)
	sd t0, 256(t1)
	sd t0, 264(t1)
	sd t0, 272(t1)
	sd t0, 280(t1)
	sd t0, 288(t1)
	sd t0, 296(t1)
	sd t0, 304(t1)
	sd t0, 312(t1)
	sd t0, 320(t1)
	sd t0, 328(t1)
	sd t0, 336(t1)
	sd t0, 344(t1)
	sd t0, 352(t1)
	sd t0, 360(t1)
	sd t0, 368(t1)
	sd t0, 376(t1)
	sd t0, 384(t1)
	sd t0, 392(t1)
	sd t0, 400(t1)
	sd t0, 408(t1)
	sd t0, 416(t1)
	sd t0, 424(t1)
	sd t0, 432(t1)
	sd t0, 440(t1)
	sd t0, 448(t1)
	sd t0, 456(t1)
	sd t0, 464(t1)
	sd t0, 472(t1)
	sd t0, 480(t1)
	sd t0, 488(t1)
	sd t0, 496(t1)
	sd t0, 504(t1)
	sd t0, 512(t1)
	sd t0, 520(t1)
	sd t0, 528(t1)
	sd t0, 536(t1)
	sd t0, 544(t1)
	sd t0, 552(t1)
	sd t0, 560(t1)
	sd t0, 568(t1)
	sd t0, 576(t1)
	sd t0, 584(t1)
	sd t0, 592(t1)
	sd t0, 600(t1)
	sd t0, 608(t1)
	sd t0, 616(t1)
	sd t0, 624(t1)
	sd t0, 632(t1)
	sd t0, 640(t1)
	sd t0, 648(t1)
	sd t0, 656(t1)
	sd t0, 664(t1)
	sd t0, 672(t1)
	sd t0, 680(t1)
	sd t0, 688(t1)
	sd t0, 696(t1)
	sd t0, 704(t1)
	sd t0, 712(t1)
	sd t0, 720(t1)
	sd t0, 728(t1)
	sd t0, 736(t1)
	sd t0, 744(t1)
	sd t0, 752(t1)
	sd t0, 760(t1)
	sd t0, 768(t1)
	sd t0, 776(t1)
	sd t0, 784(t1)
	sd t0, 792(t1)
	sd t0, 800(t1)
	sd t0, 808(t1)
	sd t0, 816(t1)
	sd t0, 824(t1)
	sd t0, 832(t1)
	sd t0, 840(t1)
	sd t0, 848(t1)
	sd t0, 856(t1)
	sd t0, 864(t1)
	sd t0, 872(t1)
	sd t0, 880(t1)
	sd t0, 888(t1)
	sd t0, 896(t1)
	sd t0, 904(t1)
	sd t0, 912(t1)
	sd t0, 920(t1)
	sd t0, 928(t1)
	sd t0, 936(t1)
	sd t0, 944(t1)
	sd t0, 952(t1)
	sd t0, 960(t1)
	sd t0, 968(t1)
	sd t0, 976(t1)
	sd t0, 984(t1)
	sd t0, 992(t1)
	sd t0, 1000(t1)
	sd t0, 1008(t1)
	sd t0, 1016(t1)
	sd t0, 1024(t1)
	sd t0, 1032(t1)
	sd t0, 1040(t1)
	sd t0, 1048(t1)
	sd t0, 1056(t1)
	sd t0, 1064(t1)
	sd t0, 1072(t1)
	sd t0, 1080(t1)
	sd t0, 1088(t1)
	sd t0, 1096(t1)
	sd t0, 1104(t1)
	sd t0, 1112(t1)
	sd t0, 1120(t1)
	sd t0, 1128(t1)
	sd t0, 1136(t1)
	sd t0, 1144(t1)
	sd t0, 1152(t1)
	sd t0, 1160(t1)
	sd t0, 1168(t1)
	sd t0, 1176(t1)
	sd t0, 1184(t1)
	sd t0, 1192(t1)
	sd t0, 1200(t1)
	sd t0, 1208(t1)
	sd t0, 1216(t1)
	sd t0, 1224(t1)
	sd t0, 1232(t1)
	sd t0, 1240(t1)
	sd t0, 1248(t1)
	sd t0, 1256(t1)
	sd t0, 1264(t1)
	sd t0, 1272(t1)
	sd t0, 1280(t1)
	sd t0, 1288(t1)
	sd t0, 1296(t1)
	sd t0, 1304(t1)
	sd t0, 1312(t1)
	sd t0, 1320(t1)
	sd t0, 1328(t1)
	sd t0, 1336(t1)
	sd t0, 1344(t1)
	sd t0, 1352(t1)
	sd t0, 1360(t1)
	sd t0, 1368(t1)
	sd t0, 1376(t1)
	sd t0, 1384(t1)
	sd t0, 1392(t1)
	sd t0, 1400(t1)
	sd t0, 1408(t1)
	sd t0, 1416(t1)
	sd t0, 1424(t1)
	sd t0, 1432(t1)
	sd t0, 1440(t1)
	sd t0, 1448(t1)
	sd t0, 1456(t1)
	sd t0, 1464(t1)
	sd t0, 1472(t1)
	sd t0, 1480(t1)
	sd t0, 1488(t1)
	sd t0, 1496(t1)
	sd t0, 1504(t1)
	sd t0, 1512(t1)
	sd t0, 1520(t1)
	sd t0, 1528(t1)
	sd t0, 1536(t1)
	sd t0, 1544(t1)
	sd t0, 1552(t1)
	sd t0, 1560(t1)
	sd t0, 1568(t1)
	sd t0, 1576(t1)
	sd t0, 1584(t1)
	sd t0, 1592(t1)
	sd t0, 1600(t1)
	sd t0, 1608(t1)
	sd t0, 1616(t1)
	sd t0, 1624(t1)
	sd t0, 1632(t1)
	sd t0, 1640(t1)
	sd t0, 1648(t1)
	sd t0, 1656(t1)
	sd t0, 1664(t1)
	sd t0, 1672(t1)
	sd t0, 1680(t1)
	sd t0, 1688(t1)
	sd t0, 1696(t1)
	sd t0, 1704(t1)
	sd t0, 1712(t1)
	sd t0, 1720(t1)
	sd t0, 1728(t1)
	sd t0, 1736(t1)
	sd t0, 1744(t1)
	sd t0, 1752(t1)
	sd t0, 1760(t1)
	sd t0, 1768(t1)
	sd t0, 1776(t1)
	sd t0, 1784(t1)
	sd t0, 1792(t1)
	sd t0, 1800(t1)
	sd t0, 1808(t1)
	sd t0, 1816(t1)
	sd t0, 1824(t1)
	sd t0, 1832(t1)
	sd t0, 1840(t1)
	sd t0, 1848(t1)
	sd t0, 1856(t1)
	sd t0, 1864(t1)
	sd t0, 1872(t1)
	sd t0, 1880(t1)
	sd t0, 1888(t1)
	sd t0, 1896(t1)
	sd t0, 1904(t1)
	sd t0, 1912(t1)
	sd t0, 1920(t1)
	sd t0, 1928(t1)
	sd t0, 1936(t1)
	sd t0, 1944(t1)
	sd t0, 1952(t1)
	sd t0, 1960(t1)
	sd t0, 1968(t1)
	sd t0, 1976(t1)
	sd t0, 1984(t1)
	sd t0, 1992(t1)
	sd t0, 2000(t1)
	sd t0, 2008(t1)
	sd t0, 2016(t1)
	sd t0, 2024(t1)
	sd t0, 2032(t1)
	sd t0, 2040(t1)
	addi sp, sp, -144
	addi t1, sp, 0
	sd t0, 0(t1)
	sd t0, 8(t1)
	sd t0, 16(t1)
	sd t0, 24(t1)
	sd t0, 32(t1)
	sd t0, 40(t1)
	sd t0, 48(t1)
	sd t0, 56(t1)
	sd t0, 64(t1)
	sd t0, 72(t1)
	sd t0, 80(t1)
	sd t0, 88(t1)
	sd t0, 96(t1)
	sd t0, 104(t1)
	sd t0, 112(t1)
	sd t0, 120(t1)
	sd t0, 128(t1)
	sd t0, 136(t1)
	addi sp, sp, 144
	addi sp, sp, 16
	addi sp, sp, 2032
	addi sp, sp, 16
	addi sp, sp, 2032
	slli a0, a0, 32
	srli a0, a0, 32
	addi a1, zero, 0
	addi a2, zero, 0
	addi a3, zero, 0
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	addi a7, zero, 0
	addi t0, zero, 0
	addi t1, zero, 0
	addi t2, zero, 0
	addi t3, zero, 0
	addi t4, zero, 0
	addi t5, zero, 0
	addi t6, zero, 0
	ret
	.option pop
