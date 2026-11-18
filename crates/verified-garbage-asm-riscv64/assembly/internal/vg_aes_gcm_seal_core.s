// The functions of `src/internal/vg_aes_gcm_seal_core.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_gcm_seal_core:
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
