// The functions of `src/internal/vg_dsa_sign.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_dsa_sign:
	.option push
	.option arch, +m, +c
	addi t2, sp, 8
	ld t2, 0(t2)
	sd s0, 128(t2)
	sd s1, 136(t2)
	sd s2, 144(t2)
	sd s3, 152(t2)
	sd s4, 160(t2)
	sd s5, 168(t2)
	sd s7, 176(t2)
	sd s8, 184(t2)
	sd s9, 192(t2)
	sd s10, 200(t2)
	sd s11, 208(t2)
	sd ra, 216(t2)
	sd s6, 224(t2)
	addi s6, t2, 0
	addi s11, a2, 0
	addi ra, a5, 0
	sd a7, 8(s6)
	sd a0, 24(s6)
	addi t3, sp, 0
	ld a7, 0(t3)
	srli a1, a7, 6
	addi t3, zero, 0
	sub a1, t3, a1
	srli a1, a1, 63
	sub a1, t3, a1
	addi t3, zero, 64
	xor t3, a7, t3
	and t3, t3, a1
	xor a1, a7, t3
	slli a1, a1, 48
	slli t3, a6, 16
	add t3, a4, t3
	add t3, t3, a1
	sd t3, 16(s6)
	addi s7, s11, 0
	ld s8, 16(s6)
	slli s8, s8, 48
	srli s8, s8, 48
	addi t3, s7, 0
	addi t5, s8, 0
	addi t4, zero, 0
	addi a1, zero, 0
20:
	lbu s0, 0(t3)
	or t4, t4, s0
	addi a0, zero, 0
	sub a0, a0, t4
	srli a0, a0, 63
	add a1, a1, a0
	addi t3, t3, 1
	addi t5, t5, -1
	bnez t5, 20b
	beqz a1, 21f
	add t3, s7, s8
	sub t3, t3, a1
	lbu a0, 0(t3)
	srli a0, a0, 7
	addi t4, zero, 1
	xor a0, a0, t4
	j 22f
21:
	addi a0, zero, 1
22:
	beqz a0, 23f
	ld t4, 24(s6)
	ld t5, 16(s6)
	slli t5, t5, 32
	srli t5, t5, 48
	add t5, t5, t5
	addi s0, zero, 0
25:
	sb s0, 0(t4)
	addi t4, t4, 1
	addi t5, t5, -1
	bnez t5, 25b
	addi a0, zero, 0
	j 24f
23:
	addi a2, a1, 0
	ld t3, 16(s6)
	slli t3, t3, 48
	srli t3, t3, 48
	add s7, s11, t3
	ld s8, 16(s6)
	slli s8, s8, 32
	srli s8, s8, 48
	addi t3, s7, 0
	addi t5, s8, 0
	addi t4, zero, 0
	addi a1, zero, 0
26:
	lbu s0, 0(t3)
	or t4, t4, s0
	addi a0, zero, 0
	sub a0, a0, t4
	srli a0, a0, 63
	add a1, a1, a0
	addi t3, t3, 1
	addi t5, t5, -1
	bnez t5, 26b
	beqz a1, 27f
	add t3, s7, s8
	sub t3, t3, a1
	lbu a0, 0(t3)
	srli a0, a0, 7
	addi t4, zero, 1
	xor a0, a0, t4
	j 28f
27:
	addi a0, zero, 1
28:
	beqz a0, 29f
	ld t4, 24(s6)
	ld t5, 16(s6)
	slli t5, t5, 32
	srli t5, t5, 48
	add t5, t5, t5
	addi s0, zero, 0
211:
	sb s0, 0(t4)
	addi t4, t4, 1
	addi t5, t5, -1
	bnez t5, 211b
	addi a0, zero, 0
	j 210f
29:
	addi a3, a1, 0
	slli t3, a1, 32
	ld t4, 16(s6)
	add t4, t4, t3
	sd t4, 16(s6)
	addi a0, zero, 1
	addi t3, a2, -128
	addi t4, a3, -20
	or t3, t3, t4
	beqz t3, 212f
	j 213f
212:
	addi a0, zero, 0
213:
	addi t3, a2, -256
	addi t4, a3, -20
	or t3, t3, t4
	beqz t3, 214f
	j 215f
214:
	addi a0, zero, 0
215:
	addi t3, a2, -256
	addi t4, a3, -28
	or t3, t3, t4
	beqz t3, 216f
	j 217f
216:
	addi a0, zero, 0
217:
	addi t3, a2, -256
	addi t4, a3, -32
	or t3, t3, t4
	beqz t3, 218f
	j 219f
218:
	addi a0, zero, 0
219:
	addi t3, a2, -384
	addi t4, a3, -32
	or t3, t3, t4
	beqz t3, 220f
	j 221f
220:
	addi a0, zero, 0
221:
	beqz a0, 222f
	ld t4, 24(s6)
	ld t5, 16(s6)
	slli t5, t5, 32
	srli t5, t5, 48
	add t5, t5, t5
	addi s0, zero, 0
224:
	sb s0, 0(t4)
	addi t4, t4, 1
	addi t5, t5, -1
	bnez t5, 224b
	addi a0, zero, 0
	j 223f
222:
	addi s7, s11, 0
	ld s8, 16(s6)
	slli s8, s8, 48
	srli s8, s8, 48
	add t3, s7, s8
	addi t3, t3, -1
	lbu a0, 0(t3)
	andi a0, a0, 1
	xori a0, a0, 1
	beqz a0, 225f
	ld t4, 24(s6)
	ld t5, 16(s6)
	slli t5, t5, 32
	srli t5, t5, 48
	add t5, t5, t5
	addi s0, zero, 0
227:
	sb s0, 0(t4)
	addi t4, t4, 1
	addi t5, t5, -1
	bnez t5, 227b
	addi a0, zero, 0
	j 226f
225:
	ld t3, 16(s6)
	slli t3, t3, 48
	srli t3, t3, 48
	add s7, s11, t3
	ld s8, 16(s6)
	slli s8, s8, 32
	srli s8, s8, 48
	add t3, s7, s8
	addi t3, t3, -1
	lbu a0, 0(t3)
	andi a0, a0, 1
	xori a0, a0, 1
	beqz a0, 228f
	ld t4, 24(s6)
	ld t5, 16(s6)
	slli t5, t5, 32
	srli t5, t5, 48
	add t5, t5, t5
	addi s0, zero, 0
230:
	sb s0, 0(t4)
	addi t4, t4, 1
	addi t5, t5, -1
	bnez t5, 230b
	addi a0, zero, 0
	j 229f
228:
	ld a7, 16(s6)
	slli a7, a7, 48
	srli a7, a7, 48
	addi t2, zero, 28
	mul a7, a7, t2
	addi a7, a7, 704
	add a7, a7, s6
	addi a7, a7, 256
	ld t0, 16(s6)
	slli t0, t0, 32
	srli t0, t0, 48
	addi t0, t0, 7
	srli t0, t0, 3
	slli s5, t0, 3
	addi s5, s5, 16
	ld t3, 16(s6)
	slli t3, t3, 48
	srli t3, t3, 48
	add s7, s11, t3
	ld s8, 16(s6)
	slli s8, s8, 32
	srli s8, s8, 48
	add t3, a7, s5
	addi t3, t3, -16
	addi s0, zero, 0
	sd s0, 0(t3)
	addi t3, a7, 0
	addi t5, t0, 0
	addi s0, zero, 0
231:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 231b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
232:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 232b
	addi s9, s11, 0
	ld s10, 16(s6)
	slli s10, s10, 48
	srli s10, s10, 48
	addi t3, a7, 0
	add t3, t3, s5
	addi t5, t0, 0
	addi s0, zero, 0
233:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 233b
	addi a2, a7, 0
	add a2, a2, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
234:
	lbu s7, 0(s9)
	slli s7, s7, 56
	addi s9, s9, 1
	addi s8, zero, 8
235:
	srli s4, s7, 63
	slli s7, s7, 1
	addi t3, a5, 0
	addi t4, a2, 0
	addi t5, t0, 0
236:
	ld s2, 0(t4)
	slli s3, s2, 1
	add s3, s3, s4
	srli s4, s2, 63
	sd s3, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 236b
	sd s4, 0(t3)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
237:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 237b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
238:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 238b
	addi s8, s8, -1
	bnez s8, 235b
	addi s10, s10, -1
	bnez s10, 234b
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t5, t0, 0
	addi s0, zero, 0
239:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 239b
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi s0, zero, 1
	sd s0, 0(t3)
	addi t3, a7, 0
	add t3, t3, s5
	addi t4, a7, 0
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	addi t5, t0, 0
	addi t2, zero, 0
240:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 240b
	addi s0, zero, 0
	sltu s1, s0, t2
	addi a0, s1, -1
	andi a0, a0, 1
	xori a0, a0, 1
	beqz a0, 241f
	ld t4, 24(s6)
	ld t5, 16(s6)
	slli t5, t5, 32
	srli t5, t5, 48
	add t5, t5, t5
	addi s0, zero, 0
243:
	sb s0, 0(t4)
	addi t4, t4, 1
	addi t5, t5, -1
	bnez t5, 243b
	addi a0, zero, 0
	j 242f
241:
	addi a7, s6, 256
	ld t0, 16(s6)
	slli t0, t0, 48
	srli t0, t0, 48
	srli t0, t0, 3
	slli s5, t0, 3
	addi s5, s5, 16
	addi s7, s11, 0
	ld s8, 16(s6)
	slli s8, s8, 48
	srli s8, s8, 48
	add t3, a7, s5
	addi t3, t3, -16
	addi s0, zero, 0
	sd s0, 0(t3)
	addi t3, a7, 0
	addi t5, t0, 0
	addi s0, zero, 0
244:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 244b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
245:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 245b
	ld s3, 0(a7)
	addi s0, s3, 0
	mul s1, s3, s0
	addi s2, zero, 2
	sub s1, s2, s1
	mul s0, s0, s1
	mul s1, s3, s0
	addi s2, zero, 2
	sub s1, s2, s1
	mul s0, s0, s1
	mul s1, s3, s0
	addi s2, zero, 2
	sub s1, s2, s1
	mul s0, s0, s1
	mul s1, s3, s0
	addi s2, zero, 2
	sub s1, s2, s1
	mul s0, s0, s1
	mul s1, s3, s0
	addi s2, zero, 2
	sub s1, s2, s1
	mul s0, s0, s1
	addi s1, zero, 0
	sub t1, s1, s0
	addi a2, a7, 0
	add a2, a2, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a2, 0
	addi t5, t0, 0
	addi s0, zero, 0
246:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 246b
	addi s0, zero, 1
	sd s0, 0(a2)
	slli a1, t0, 7
247:
	addi t3, a5, 0
	addi t4, a2, 0
	addi t5, t0, 0
	addi s4, zero, 0
248:
	ld s2, 0(t4)
	slli s3, s2, 1
	add s3, s3, s4
	srli s4, s2, 63
	sd s3, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 248b
	sd s4, 0(t3)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
249:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 249b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
250:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 250b
	addi a1, a1, -1
	bnez a1, 247b
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t4, a7, 0
	add t4, t4, s5
	addi t5, t0, 2
251:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 251b
	ld s8, 16(s6)
	slli s8, s8, 48
	srli s8, s8, 48
	ld t3, 16(s6)
	slli t3, t3, 32
	srli t3, t3, 48
	add s7, s11, s8
	add s7, s7, t3
	add a7, a7, s5
	add a7, a7, s5
	add a7, a7, s5
	add a7, a7, s5
	add t3, a7, s5
	addi t3, t3, -16
	addi s0, zero, 0
	sd s0, 0(t3)
	addi t3, a7, 0
	addi t5, t0, 0
	addi s0, zero, 0
252:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 252b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
253:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 253b
	sub a7, a7, s5
	sub a7, a7, s5
	sub a7, a7, s5
	sub a7, a7, s5
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t5, t0, 0
	addi s0, zero, 0
254:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 254b
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi s0, zero, 1
	sd s0, 0(t3)
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t5, t0, 0
	addi s0, zero, 0
255:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 255b
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
256:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 256b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi a1, s4, 0
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t4, a7, 0
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	addi t5, t0, 0
	addi t2, zero, 0
257:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 257b
	addi s0, zero, 0
	sltu s1, s0, t2
	addi a2, s1, -1
	or a1, a1, a2
	xor a1, a1, a2
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t4, a7, 0
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	addi t5, t0, 0
	addi t2, zero, 0
258:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 258b
	addi s0, zero, 0
	sltu s1, s0, t2
	addi a2, s1, -1
	or a1, a1, a2
	xor a1, a1, a2
	addi a0, a1, 0
	andi a0, a0, 1
	xori a0, a0, 1
	beqz a0, 259f
	j 260f
259:
	addi t3, a7, 0
	add t3, t3, s5
	addi t4, a7, 0
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	addi t5, t0, 2
261:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 261b
	ld t3, 16(s6)
	slli t3, t3, 48
	srli t3, t3, 48
	add s7, s11, t3
	ld s8, 16(s6)
	slli s8, s8, 32
	srli s8, s8, 48
	addi s9, s7, 0
	addi s10, s8, 0
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t5, t0, 0
	addi s0, zero, 0
262:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 262b
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi s0, zero, 1
	sd s0, 0(t3)
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	addi a4, a7, 0
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
263:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 263b
264:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a7)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi a0, a7, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 265f
267:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 267b
	j 266f
265:
266:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 268f
270:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 16(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 16(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 24(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 24(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 32(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 32(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 270b
	j 269f
268:
269:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	addi a1, a1, -1
	bnez a1, 264b
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
271:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 271b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
272:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 272b
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a4, a7, 0
	add a4, a4, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
273:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 273b
274:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a7)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi a0, a7, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 275f
277:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 277b
	j 276f
275:
276:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 278f
280:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 16(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 16(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 24(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 24(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 32(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 32(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 280b
	j 279f
278:
279:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	addi a1, a1, -1
	bnez a1, 274b
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
281:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 281b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
282:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 282b
	addi s4, zero, -1
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
283:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 283b
	addi s7, zero, 2
284:
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a4, a7, 0
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
285:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 285b
286:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a7)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi a0, a7, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 287f
289:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 289b
	j 288f
287:
288:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 290f
292:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 16(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 16(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 24(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 24(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 32(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 32(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 292b
	j 291f
290:
291:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	addi a1, a1, -1
	bnez a1, 286b
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
293:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 293b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
294:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 294b
	addi s4, zero, -1
	addi t2, s7, 8
	mul t2, t2, s5
	add a2, t2, a7
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
295:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 295b
	addi s7, s7, 1
	addi t2, s7, -16
	bnez t2, 284b
	addi s4, zero, -1
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
296:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 296b
297:
	lbu s7, 0(s9)
	slli s7, s7, 56
	addi s9, s9, 1
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a5, 0
	add t5, t0, t0
	addi t5, t5, 2
	addi s0, zero, 0
298:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 298b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
299:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2100f
2102:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2102b
	j 2101f
2100:
2101:
	beqz t6, 2103f
2105:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2105b
	j 2104f
2103:
2104:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 299b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2106:
	ld s2, 0(t3)
	ld s3, 8(t3)
	srli s4, s2, 63
	slli s2, s2, 1
	add s2, s2, t2
	srli t2, s3, 63
	slli s3, s3, 1
	add s3, s3, s4
	ld s4, 0(a0)
	add s1, s1, s2
	sltu s2, s1, s2
	mul s0, s4, s4
	mulhu s4, s4, s4
	add s4, s4, s2
	add s0, s0, s1
	sltu s2, s0, s1
	add s4, s4, s2
	add s3, s3, s4
	sltu s1, s3, s4
	sd s0, 0(t3)
	sd s3, 8(t3)
	addi t3, t3, 16
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2106b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
2107:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi a0, a7, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2108f
2110:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2110b
	j 2109f
2108:
2109:
	beqz t6, 2111f
2113:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2113b
	j 2112f
2111:
2112:
	ld s2, 0(t4)
	add s1, s1, s2
	sltu s3, s1, s2
	add s1, s1, a1
	sltu s2, s1, a1
	add a1, s3, s2
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, -1
	bnez t2, 2107b
	slli t3, t0, 3
	add a5, a5, t3
	add t4, a5, t3
	sd a1, 0(t4)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2114:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2114b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2115:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2115b
	slli t3, t0, 3
	sub a5, a5, t3
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a5, 0
	add t5, t0, t0
	addi t5, t5, 2
	addi s0, zero, 0
2116:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2116b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2117:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2118f
2120:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2120b
	j 2119f
2118:
2119:
	beqz t6, 2121f
2123:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2123b
	j 2122f
2121:
2122:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2117b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2124:
	ld s2, 0(t3)
	ld s3, 8(t3)
	srli s4, s2, 63
	slli s2, s2, 1
	add s2, s2, t2
	srli t2, s3, 63
	slli s3, s3, 1
	add s3, s3, s4
	ld s4, 0(a0)
	add s1, s1, s2
	sltu s2, s1, s2
	mul s0, s4, s4
	mulhu s4, s4, s4
	add s4, s4, s2
	add s0, s0, s1
	sltu s2, s0, s1
	add s4, s4, s2
	add s3, s3, s4
	sltu s1, s3, s4
	sd s0, 0(t3)
	sd s3, 8(t3)
	addi t3, t3, 16
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2124b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
2125:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi a0, a7, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2126f
2128:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2128b
	j 2127f
2126:
2127:
	beqz t6, 2129f
2131:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2131b
	j 2130f
2129:
2130:
	ld s2, 0(t4)
	add s1, s1, s2
	sltu s3, s1, s2
	add s1, s1, a1
	sltu s2, s1, a1
	add a1, s3, s2
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, -1
	bnez t2, 2125b
	slli t3, t0, 3
	add a5, a5, t3
	add t4, a5, t3
	sd a1, 0(t4)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2132:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2132b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2133:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2133b
	slli t3, t0, 3
	sub a5, a5, t3
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a5, 0
	add t5, t0, t0
	addi t5, t5, 2
	addi s0, zero, 0
2134:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2134b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2135:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2136f
2138:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2138b
	j 2137f
2136:
2137:
	beqz t6, 2139f
2141:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2141b
	j 2140f
2139:
2140:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2135b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2142:
	ld s2, 0(t3)
	ld s3, 8(t3)
	srli s4, s2, 63
	slli s2, s2, 1
	add s2, s2, t2
	srli t2, s3, 63
	slli s3, s3, 1
	add s3, s3, s4
	ld s4, 0(a0)
	add s1, s1, s2
	sltu s2, s1, s2
	mul s0, s4, s4
	mulhu s4, s4, s4
	add s4, s4, s2
	add s0, s0, s1
	sltu s2, s0, s1
	add s4, s4, s2
	add s3, s3, s4
	sltu s1, s3, s4
	sd s0, 0(t3)
	sd s3, 8(t3)
	addi t3, t3, 16
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2142b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
2143:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi a0, a7, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2144f
2146:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2146b
	j 2145f
2144:
2145:
	beqz t6, 2147f
2149:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2149b
	j 2148f
2147:
2148:
	ld s2, 0(t4)
	add s1, s1, s2
	sltu s3, s1, s2
	add s1, s1, a1
	sltu s2, s1, a1
	add a1, s3, s2
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, -1
	bnez t2, 2143b
	slli t3, t0, 3
	add a5, a5, t3
	add t4, a5, t3
	sd a1, 0(t4)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2150:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2150b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2151:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2151b
	slli t3, t0, 3
	sub a5, a5, t3
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a5, 0
	add t5, t0, t0
	addi t5, t5, 2
	addi s0, zero, 0
2152:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2152b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2153:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2154f
2156:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2156b
	j 2155f
2154:
2155:
	beqz t6, 2157f
2159:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2159b
	j 2158f
2157:
2158:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2153b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2160:
	ld s2, 0(t3)
	ld s3, 8(t3)
	srli s4, s2, 63
	slli s2, s2, 1
	add s2, s2, t2
	srli t2, s3, 63
	slli s3, s3, 1
	add s3, s3, s4
	ld s4, 0(a0)
	add s1, s1, s2
	sltu s2, s1, s2
	mul s0, s4, s4
	mulhu s4, s4, s4
	add s4, s4, s2
	add s0, s0, s1
	sltu s2, s0, s1
	add s4, s4, s2
	add s3, s3, s4
	sltu s1, s3, s4
	sd s0, 0(t3)
	sd s3, 8(t3)
	addi t3, t3, 16
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2160b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
2161:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi a0, a7, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2162f
2164:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2164b
	j 2163f
2162:
2163:
	beqz t6, 2165f
2167:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2167b
	j 2166f
2165:
2166:
	ld s2, 0(t4)
	add s1, s1, s2
	sltu s3, s1, s2
	add s1, s1, a1
	sltu s2, s1, a1
	add a1, s3, s2
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, -1
	bnez t2, 2161b
	slli t3, t0, 3
	add a5, a5, t3
	add t4, a5, t3
	sd a1, 0(t4)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2168:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2168b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2169:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2169b
	slli t3, t0, 3
	sub a5, a5, t3
	srli a1, s7, 60
	addi s8, zero, 0
2170:
	xor t2, s8, a1
	addi t2, t2, -1
	srli t2, t2, 63
	addi t3, zero, 0
	sub s4, t3, t2
	addi t2, s8, 8
	mul t2, t2, s5
	add a5, t2, a7
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2171:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2171b
	addi s8, s8, 1
	xor t2, s8, a1
	addi t2, t2, -1
	srli t2, t2, 63
	addi t3, zero, 0
	sub s4, t3, t2
	addi t2, s8, 8
	mul t2, t2, s5
	add a5, t2, a7
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2172:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2172b
	addi s8, s8, 1
	addi t2, s8, -16
	bnez t2, 2170b
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a4, a7, 0
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
2173:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2173b
2174:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a7)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi a0, a7, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 2175f
2177:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2177b
	j 2176f
2175:
2176:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2178f
2180:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 16(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 16(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 24(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 24(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 32(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 32(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2180b
	j 2179f
2178:
2179:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	addi a1, a1, -1
	bnez a1, 2174b
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2181:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2181b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2182:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2182b
	slli s7, s7, 4
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a5, 0
	add t5, t0, t0
	addi t5, t5, 2
	addi s0, zero, 0
2183:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2183b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2184:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2185f
2187:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2187b
	j 2186f
2185:
2186:
	beqz t6, 2188f
2190:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2190b
	j 2189f
2188:
2189:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2184b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2191:
	ld s2, 0(t3)
	ld s3, 8(t3)
	srli s4, s2, 63
	slli s2, s2, 1
	add s2, s2, t2
	srli t2, s3, 63
	slli s3, s3, 1
	add s3, s3, s4
	ld s4, 0(a0)
	add s1, s1, s2
	sltu s2, s1, s2
	mul s0, s4, s4
	mulhu s4, s4, s4
	add s4, s4, s2
	add s0, s0, s1
	sltu s2, s0, s1
	add s4, s4, s2
	add s3, s3, s4
	sltu s1, s3, s4
	sd s0, 0(t3)
	sd s3, 8(t3)
	addi t3, t3, 16
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2191b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
2192:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi a0, a7, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2193f
2195:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2195b
	j 2194f
2193:
2194:
	beqz t6, 2196f
2198:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2198b
	j 2197f
2196:
2197:
	ld s2, 0(t4)
	add s1, s1, s2
	sltu s3, s1, s2
	add s1, s1, a1
	sltu s2, s1, a1
	add a1, s3, s2
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, -1
	bnez t2, 2192b
	slli t3, t0, 3
	add a5, a5, t3
	add t4, a5, t3
	sd a1, 0(t4)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2199:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2199b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2200:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2200b
	slli t3, t0, 3
	sub a5, a5, t3
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a5, 0
	add t5, t0, t0
	addi t5, t5, 2
	addi s0, zero, 0
2201:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2201b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2202:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2203f
2205:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2205b
	j 2204f
2203:
2204:
	beqz t6, 2206f
2208:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2208b
	j 2207f
2206:
2207:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2202b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2209:
	ld s2, 0(t3)
	ld s3, 8(t3)
	srli s4, s2, 63
	slli s2, s2, 1
	add s2, s2, t2
	srli t2, s3, 63
	slli s3, s3, 1
	add s3, s3, s4
	ld s4, 0(a0)
	add s1, s1, s2
	sltu s2, s1, s2
	mul s0, s4, s4
	mulhu s4, s4, s4
	add s4, s4, s2
	add s0, s0, s1
	sltu s2, s0, s1
	add s4, s4, s2
	add s3, s3, s4
	sltu s1, s3, s4
	sd s0, 0(t3)
	sd s3, 8(t3)
	addi t3, t3, 16
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2209b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
2210:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi a0, a7, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2211f
2213:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2213b
	j 2212f
2211:
2212:
	beqz t6, 2214f
2216:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2216b
	j 2215f
2214:
2215:
	ld s2, 0(t4)
	add s1, s1, s2
	sltu s3, s1, s2
	add s1, s1, a1
	sltu s2, s1, a1
	add a1, s3, s2
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, -1
	bnez t2, 2210b
	slli t3, t0, 3
	add a5, a5, t3
	add t4, a5, t3
	sd a1, 0(t4)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2217:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2217b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2218:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2218b
	slli t3, t0, 3
	sub a5, a5, t3
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a5, 0
	add t5, t0, t0
	addi t5, t5, 2
	addi s0, zero, 0
2219:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2219b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2220:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2221f
2223:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2223b
	j 2222f
2221:
2222:
	beqz t6, 2224f
2226:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2226b
	j 2225f
2224:
2225:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2220b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2227:
	ld s2, 0(t3)
	ld s3, 8(t3)
	srli s4, s2, 63
	slli s2, s2, 1
	add s2, s2, t2
	srli t2, s3, 63
	slli s3, s3, 1
	add s3, s3, s4
	ld s4, 0(a0)
	add s1, s1, s2
	sltu s2, s1, s2
	mul s0, s4, s4
	mulhu s4, s4, s4
	add s4, s4, s2
	add s0, s0, s1
	sltu s2, s0, s1
	add s4, s4, s2
	add s3, s3, s4
	sltu s1, s3, s4
	sd s0, 0(t3)
	sd s3, 8(t3)
	addi t3, t3, 16
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2227b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
2228:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi a0, a7, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2229f
2231:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2231b
	j 2230f
2229:
2230:
	beqz t6, 2232f
2234:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2234b
	j 2233f
2232:
2233:
	ld s2, 0(t4)
	add s1, s1, s2
	sltu s3, s1, s2
	add s1, s1, a1
	sltu s2, s1, a1
	add a1, s3, s2
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, -1
	bnez t2, 2228b
	slli t3, t0, 3
	add a5, a5, t3
	add t4, a5, t3
	sd a1, 0(t4)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2235:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2235b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2236:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2236b
	slli t3, t0, 3
	sub a5, a5, t3
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a5, 0
	add t5, t0, t0
	addi t5, t5, 2
	addi s0, zero, 0
2237:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2237b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2238:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2239f
2241:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2241b
	j 2240f
2239:
2240:
	beqz t6, 2242f
2244:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2244b
	j 2243f
2242:
2243:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2238b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2245:
	ld s2, 0(t3)
	ld s3, 8(t3)
	srli s4, s2, 63
	slli s2, s2, 1
	add s2, s2, t2
	srli t2, s3, 63
	slli s3, s3, 1
	add s3, s3, s4
	ld s4, 0(a0)
	add s1, s1, s2
	sltu s2, s1, s2
	mul s0, s4, s4
	mulhu s4, s4, s4
	add s4, s4, s2
	add s0, s0, s1
	sltu s2, s0, s1
	add s4, s4, s2
	add s3, s3, s4
	sltu s1, s3, s4
	sd s0, 0(t3)
	sd s3, 8(t3)
	addi t3, t3, 16
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2245b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
2246:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi a0, a7, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2247f
2249:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2249b
	j 2248f
2247:
2248:
	beqz t6, 2250f
2252:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2252b
	j 2251f
2250:
2251:
	ld s2, 0(t4)
	add s1, s1, s2
	sltu s3, s1, s2
	add s1, s1, a1
	sltu s2, s1, a1
	add a1, s3, s2
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, -1
	bnez t2, 2246b
	slli t3, t0, 3
	add a5, a5, t3
	add t4, a5, t3
	sd a1, 0(t4)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2253:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2253b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2254:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2254b
	slli t3, t0, 3
	sub a5, a5, t3
	srli a1, s7, 60
	addi s8, zero, 0
2255:
	xor t2, s8, a1
	addi t2, t2, -1
	srli t2, t2, 63
	addi t3, zero, 0
	sub s4, t3, t2
	addi t2, s8, 8
	mul t2, t2, s5
	add a5, t2, a7
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2256:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2256b
	addi s8, s8, 1
	xor t2, s8, a1
	addi t2, t2, -1
	srli t2, t2, 63
	addi t3, zero, 0
	sub s4, t3, t2
	addi t2, s8, 8
	mul t2, t2, s5
	add a5, t2, a7
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2257:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2257b
	addi s8, s8, 1
	addi t2, s8, -16
	bnez t2, 2255b
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a4, a7, 0
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
2258:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2258b
2259:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a7)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi a0, a7, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 2260f
2262:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2262b
	j 2261f
2260:
2261:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2263f
2265:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 16(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 16(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 24(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 24(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 32(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 32(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2265b
	j 2264f
2263:
2264:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	addi a1, a1, -1
	bnez a1, 2259b
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2266:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2266b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2267:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2267b
	slli s7, s7, 4
	addi s10, s10, -1
	bnez s10, 297b
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a4, a7, 0
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
2268:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2268b
2269:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a7)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi a0, a7, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 2270f
2272:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2272b
	j 2271f
2270:
2271:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2273f
2275:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 16(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 16(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 24(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 24(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 32(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 32(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2275b
	j 2274f
2273:
2274:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	addi a1, a1, -1
	bnez a1, 2269b
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2276:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2276b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2277:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2277b
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t5, t0, 0
	addi s0, zero, 0
2278:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2278b
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi s0, zero, 1
	sd s0, 0(t3)
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t4, a7, 0
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	addi t5, t0, 0
	addi t2, zero, 0
2279:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2279b
	addi s0, zero, 0
	sltu s1, s0, t2
	addi a0, s1, -1
	andi a0, a0, 1
	xori a0, a0, 1
260:
	beqz a0, 2280f
	ld t4, 24(s6)
	ld t5, 16(s6)
	slli t5, t5, 32
	srli t5, t5, 48
	add t5, t5, t5
	addi s0, zero, 0
2282:
	sb s0, 0(t4)
	addi t4, t4, 1
	addi t5, t5, -1
	bnez t5, 2282b
	addi a0, zero, 0
	j 2281f
2280:
	ld s8, 16(s6)
	slli s8, s8, 48
	srli s8, s8, 48
	ld t3, 16(s6)
	slli t3, t3, 32
	srli t3, t3, 48
	add s7, s11, s8
	add s7, s7, t3
	add s7, s7, s8
	add a7, a7, s5
	add a7, a7, s5
	add a7, a7, s5
	add a7, a7, s5
	add t3, a7, s5
	addi t3, t3, -16
	addi s0, zero, 0
	sd s0, 0(t3)
	addi t3, a7, 0
	addi t5, t0, 0
	addi s0, zero, 0
2283:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2283b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
2284:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 2284b
	sub a7, a7, s5
	sub a7, a7, s5
	sub a7, a7, s5
	sub a7, a7, s5
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t5, t0, 0
	addi s0, zero, 0
2285:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2285b
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi s0, zero, 1
	sd s0, 0(t3)
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t5, t0, 0
	addi s0, zero, 0
2286:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2286b
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2287:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2287b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi a1, s4, 0
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t4, a7, 0
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	addi t5, t0, 0
	addi t2, zero, 0
2288:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2288b
	addi s0, zero, 0
	sltu s1, s0, t2
	addi a2, s1, -1
	or a1, a1, a2
	xor a1, a1, a2
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t4, a7, 0
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	addi t5, t0, 0
	addi t2, zero, 0
2289:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2289b
	addi s0, zero, 0
	sltu s1, s0, t2
	addi a2, s1, -1
	or a1, a1, a2
	xor a1, a1, a2
	addi a0, a1, 0
	andi a0, a0, 1
	xori a0, a0, 1
	beqz a0, 2290f
	j 2291f
2290:
	addi t3, a7, 0
	add t3, t3, s5
	addi t4, a7, 0
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	addi t5, t0, 2
2292:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2292b
	ld t3, 16(s6)
	slli t3, t3, 48
	srli t3, t3, 48
	add s7, s11, t3
	ld s8, 16(s6)
	slli s8, s8, 32
	srli s8, s8, 48
	addi s9, s7, 0
	addi s10, s8, 0
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t5, t0, 0
	addi s0, zero, 0
2293:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2293b
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi s0, zero, 1
	sd s0, 0(t3)
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	addi a4, a7, 0
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
2294:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2294b
2295:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a7)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi a0, a7, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 2296f
2298:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2298b
	j 2297f
2296:
2297:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2299f
2301:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 16(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 16(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 24(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 24(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 32(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 32(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2301b
	j 2300f
2299:
2300:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	addi a1, a1, -1
	bnez a1, 2295b
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2302:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2302b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2303:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2303b
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a4, a7, 0
	add a4, a4, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
2304:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2304b
2305:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a7)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi a0, a7, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 2306f
2308:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2308b
	j 2307f
2306:
2307:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2309f
2311:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 16(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 16(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 24(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 24(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 32(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 32(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2311b
	j 2310f
2309:
2310:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	addi a1, a1, -1
	bnez a1, 2305b
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2312:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2312b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2313:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2313b
	addi s4, zero, -1
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2314:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2314b
	addi s7, zero, 2
2315:
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a4, a7, 0
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
2316:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2316b
2317:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a7)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi a0, a7, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 2318f
2320:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2320b
	j 2319f
2318:
2319:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2321f
2323:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 16(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 16(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 24(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 24(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 32(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 32(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2323b
	j 2322f
2321:
2322:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	addi a1, a1, -1
	bnez a1, 2317b
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2324:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2324b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2325:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2325b
	addi s4, zero, -1
	addi t2, s7, 8
	mul t2, t2, s5
	add a2, t2, a7
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2326:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2326b
	addi s7, s7, 1
	addi t2, s7, -16
	bnez t2, 2315b
	addi s4, zero, -1
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2327:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2327b
2328:
	lbu s7, 0(s9)
	slli s7, s7, 56
	addi s9, s9, 1
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a5, 0
	add t5, t0, t0
	addi t5, t5, 2
	addi s0, zero, 0
2329:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2329b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2330:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2331f
2333:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2333b
	j 2332f
2331:
2332:
	beqz t6, 2334f
2336:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2336b
	j 2335f
2334:
2335:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2330b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2337:
	ld s2, 0(t3)
	ld s3, 8(t3)
	srli s4, s2, 63
	slli s2, s2, 1
	add s2, s2, t2
	srli t2, s3, 63
	slli s3, s3, 1
	add s3, s3, s4
	ld s4, 0(a0)
	add s1, s1, s2
	sltu s2, s1, s2
	mul s0, s4, s4
	mulhu s4, s4, s4
	add s4, s4, s2
	add s0, s0, s1
	sltu s2, s0, s1
	add s4, s4, s2
	add s3, s3, s4
	sltu s1, s3, s4
	sd s0, 0(t3)
	sd s3, 8(t3)
	addi t3, t3, 16
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2337b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
2338:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi a0, a7, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2339f
2341:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2341b
	j 2340f
2339:
2340:
	beqz t6, 2342f
2344:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2344b
	j 2343f
2342:
2343:
	ld s2, 0(t4)
	add s1, s1, s2
	sltu s3, s1, s2
	add s1, s1, a1
	sltu s2, s1, a1
	add a1, s3, s2
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, -1
	bnez t2, 2338b
	slli t3, t0, 3
	add a5, a5, t3
	add t4, a5, t3
	sd a1, 0(t4)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2345:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2345b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2346:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2346b
	slli t3, t0, 3
	sub a5, a5, t3
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a5, 0
	add t5, t0, t0
	addi t5, t5, 2
	addi s0, zero, 0
2347:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2347b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2348:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2349f
2351:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2351b
	j 2350f
2349:
2350:
	beqz t6, 2352f
2354:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2354b
	j 2353f
2352:
2353:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2348b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2355:
	ld s2, 0(t3)
	ld s3, 8(t3)
	srli s4, s2, 63
	slli s2, s2, 1
	add s2, s2, t2
	srli t2, s3, 63
	slli s3, s3, 1
	add s3, s3, s4
	ld s4, 0(a0)
	add s1, s1, s2
	sltu s2, s1, s2
	mul s0, s4, s4
	mulhu s4, s4, s4
	add s4, s4, s2
	add s0, s0, s1
	sltu s2, s0, s1
	add s4, s4, s2
	add s3, s3, s4
	sltu s1, s3, s4
	sd s0, 0(t3)
	sd s3, 8(t3)
	addi t3, t3, 16
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2355b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
2356:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi a0, a7, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2357f
2359:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2359b
	j 2358f
2357:
2358:
	beqz t6, 2360f
2362:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2362b
	j 2361f
2360:
2361:
	ld s2, 0(t4)
	add s1, s1, s2
	sltu s3, s1, s2
	add s1, s1, a1
	sltu s2, s1, a1
	add a1, s3, s2
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, -1
	bnez t2, 2356b
	slli t3, t0, 3
	add a5, a5, t3
	add t4, a5, t3
	sd a1, 0(t4)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2363:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2363b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2364:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2364b
	slli t3, t0, 3
	sub a5, a5, t3
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a5, 0
	add t5, t0, t0
	addi t5, t5, 2
	addi s0, zero, 0
2365:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2365b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2366:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2367f
2369:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2369b
	j 2368f
2367:
2368:
	beqz t6, 2370f
2372:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2372b
	j 2371f
2370:
2371:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2366b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2373:
	ld s2, 0(t3)
	ld s3, 8(t3)
	srli s4, s2, 63
	slli s2, s2, 1
	add s2, s2, t2
	srli t2, s3, 63
	slli s3, s3, 1
	add s3, s3, s4
	ld s4, 0(a0)
	add s1, s1, s2
	sltu s2, s1, s2
	mul s0, s4, s4
	mulhu s4, s4, s4
	add s4, s4, s2
	add s0, s0, s1
	sltu s2, s0, s1
	add s4, s4, s2
	add s3, s3, s4
	sltu s1, s3, s4
	sd s0, 0(t3)
	sd s3, 8(t3)
	addi t3, t3, 16
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2373b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
2374:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi a0, a7, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2375f
2377:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2377b
	j 2376f
2375:
2376:
	beqz t6, 2378f
2380:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2380b
	j 2379f
2378:
2379:
	ld s2, 0(t4)
	add s1, s1, s2
	sltu s3, s1, s2
	add s1, s1, a1
	sltu s2, s1, a1
	add a1, s3, s2
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, -1
	bnez t2, 2374b
	slli t3, t0, 3
	add a5, a5, t3
	add t4, a5, t3
	sd a1, 0(t4)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2381:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2381b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2382:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2382b
	slli t3, t0, 3
	sub a5, a5, t3
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a5, 0
	add t5, t0, t0
	addi t5, t5, 2
	addi s0, zero, 0
2383:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2383b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2384:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2385f
2387:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2387b
	j 2386f
2385:
2386:
	beqz t6, 2388f
2390:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2390b
	j 2389f
2388:
2389:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2384b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2391:
	ld s2, 0(t3)
	ld s3, 8(t3)
	srli s4, s2, 63
	slli s2, s2, 1
	add s2, s2, t2
	srli t2, s3, 63
	slli s3, s3, 1
	add s3, s3, s4
	ld s4, 0(a0)
	add s1, s1, s2
	sltu s2, s1, s2
	mul s0, s4, s4
	mulhu s4, s4, s4
	add s4, s4, s2
	add s0, s0, s1
	sltu s2, s0, s1
	add s4, s4, s2
	add s3, s3, s4
	sltu s1, s3, s4
	sd s0, 0(t3)
	sd s3, 8(t3)
	addi t3, t3, 16
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2391b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
2392:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi a0, a7, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2393f
2395:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2395b
	j 2394f
2393:
2394:
	beqz t6, 2396f
2398:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2398b
	j 2397f
2396:
2397:
	ld s2, 0(t4)
	add s1, s1, s2
	sltu s3, s1, s2
	add s1, s1, a1
	sltu s2, s1, a1
	add a1, s3, s2
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, -1
	bnez t2, 2392b
	slli t3, t0, 3
	add a5, a5, t3
	add t4, a5, t3
	sd a1, 0(t4)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2399:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2399b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2400:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2400b
	slli t3, t0, 3
	sub a5, a5, t3
	srli a1, s7, 60
	addi s8, zero, 0
2401:
	xor t2, s8, a1
	addi t2, t2, -1
	srli t2, t2, 63
	addi t3, zero, 0
	sub s4, t3, t2
	addi t2, s8, 8
	mul t2, t2, s5
	add a5, t2, a7
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2402:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2402b
	addi s8, s8, 1
	xor t2, s8, a1
	addi t2, t2, -1
	srli t2, t2, 63
	addi t3, zero, 0
	sub s4, t3, t2
	addi t2, s8, 8
	mul t2, t2, s5
	add a5, t2, a7
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2403:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2403b
	addi s8, s8, 1
	addi t2, s8, -16
	bnez t2, 2401b
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a4, a7, 0
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
2404:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2404b
2405:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a7)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi a0, a7, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 2406f
2408:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2408b
	j 2407f
2406:
2407:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2409f
2411:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 16(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 16(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 24(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 24(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 32(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 32(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2411b
	j 2410f
2409:
2410:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	addi a1, a1, -1
	bnez a1, 2405b
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2412:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2412b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2413:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2413b
	slli s7, s7, 4
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a5, 0
	add t5, t0, t0
	addi t5, t5, 2
	addi s0, zero, 0
2414:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2414b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2415:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2416f
2418:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2418b
	j 2417f
2416:
2417:
	beqz t6, 2419f
2421:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2421b
	j 2420f
2419:
2420:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2415b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2422:
	ld s2, 0(t3)
	ld s3, 8(t3)
	srli s4, s2, 63
	slli s2, s2, 1
	add s2, s2, t2
	srli t2, s3, 63
	slli s3, s3, 1
	add s3, s3, s4
	ld s4, 0(a0)
	add s1, s1, s2
	sltu s2, s1, s2
	mul s0, s4, s4
	mulhu s4, s4, s4
	add s4, s4, s2
	add s0, s0, s1
	sltu s2, s0, s1
	add s4, s4, s2
	add s3, s3, s4
	sltu s1, s3, s4
	sd s0, 0(t3)
	sd s3, 8(t3)
	addi t3, t3, 16
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2422b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
2423:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi a0, a7, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2424f
2426:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2426b
	j 2425f
2424:
2425:
	beqz t6, 2427f
2429:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2429b
	j 2428f
2427:
2428:
	ld s2, 0(t4)
	add s1, s1, s2
	sltu s3, s1, s2
	add s1, s1, a1
	sltu s2, s1, a1
	add a1, s3, s2
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, -1
	bnez t2, 2423b
	slli t3, t0, 3
	add a5, a5, t3
	add t4, a5, t3
	sd a1, 0(t4)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2430:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2430b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2431:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2431b
	slli t3, t0, 3
	sub a5, a5, t3
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a5, 0
	add t5, t0, t0
	addi t5, t5, 2
	addi s0, zero, 0
2432:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2432b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2433:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2434f
2436:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2436b
	j 2435f
2434:
2435:
	beqz t6, 2437f
2439:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2439b
	j 2438f
2437:
2438:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2433b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2440:
	ld s2, 0(t3)
	ld s3, 8(t3)
	srli s4, s2, 63
	slli s2, s2, 1
	add s2, s2, t2
	srli t2, s3, 63
	slli s3, s3, 1
	add s3, s3, s4
	ld s4, 0(a0)
	add s1, s1, s2
	sltu s2, s1, s2
	mul s0, s4, s4
	mulhu s4, s4, s4
	add s4, s4, s2
	add s0, s0, s1
	sltu s2, s0, s1
	add s4, s4, s2
	add s3, s3, s4
	sltu s1, s3, s4
	sd s0, 0(t3)
	sd s3, 8(t3)
	addi t3, t3, 16
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2440b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
2441:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi a0, a7, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2442f
2444:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2444b
	j 2443f
2442:
2443:
	beqz t6, 2445f
2447:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2447b
	j 2446f
2445:
2446:
	ld s2, 0(t4)
	add s1, s1, s2
	sltu s3, s1, s2
	add s1, s1, a1
	sltu s2, s1, a1
	add a1, s3, s2
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, -1
	bnez t2, 2441b
	slli t3, t0, 3
	add a5, a5, t3
	add t4, a5, t3
	sd a1, 0(t4)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2448:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2448b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2449:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2449b
	slli t3, t0, 3
	sub a5, a5, t3
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a5, 0
	add t5, t0, t0
	addi t5, t5, 2
	addi s0, zero, 0
2450:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2450b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2451:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2452f
2454:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2454b
	j 2453f
2452:
2453:
	beqz t6, 2455f
2457:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2457b
	j 2456f
2455:
2456:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2451b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2458:
	ld s2, 0(t3)
	ld s3, 8(t3)
	srli s4, s2, 63
	slli s2, s2, 1
	add s2, s2, t2
	srli t2, s3, 63
	slli s3, s3, 1
	add s3, s3, s4
	ld s4, 0(a0)
	add s1, s1, s2
	sltu s2, s1, s2
	mul s0, s4, s4
	mulhu s4, s4, s4
	add s4, s4, s2
	add s0, s0, s1
	sltu s2, s0, s1
	add s4, s4, s2
	add s3, s3, s4
	sltu s1, s3, s4
	sd s0, 0(t3)
	sd s3, 8(t3)
	addi t3, t3, 16
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2458b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
2459:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi a0, a7, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2460f
2462:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2462b
	j 2461f
2460:
2461:
	beqz t6, 2463f
2465:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2465b
	j 2464f
2463:
2464:
	ld s2, 0(t4)
	add s1, s1, s2
	sltu s3, s1, s2
	add s1, s1, a1
	sltu s2, s1, a1
	add a1, s3, s2
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, -1
	bnez t2, 2459b
	slli t3, t0, 3
	add a5, a5, t3
	add t4, a5, t3
	sd a1, 0(t4)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2466:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2466b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2467:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2467b
	slli t3, t0, 3
	sub a5, a5, t3
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a5, 0
	add t5, t0, t0
	addi t5, t5, 2
	addi s0, zero, 0
2468:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2468b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2469:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2470f
2472:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2472b
	j 2471f
2470:
2471:
	beqz t6, 2473f
2475:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2475b
	j 2474f
2473:
2474:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2469b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2476:
	ld s2, 0(t3)
	ld s3, 8(t3)
	srli s4, s2, 63
	slli s2, s2, 1
	add s2, s2, t2
	srli t2, s3, 63
	slli s3, s3, 1
	add s3, s3, s4
	ld s4, 0(a0)
	add s1, s1, s2
	sltu s2, s1, s2
	mul s0, s4, s4
	mulhu s4, s4, s4
	add s4, s4, s2
	add s0, s0, s1
	sltu s2, s0, s1
	add s4, s4, s2
	add s3, s3, s4
	sltu s1, s3, s4
	sd s0, 0(t3)
	sd s3, 8(t3)
	addi t3, t3, 16
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2476b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
2477:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi a0, a7, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2478f
2480:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2480b
	j 2479f
2478:
2479:
	beqz t6, 2481f
2483:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2483b
	j 2482f
2481:
2482:
	ld s2, 0(t4)
	add s1, s1, s2
	sltu s3, s1, s2
	add s1, s1, a1
	sltu s2, s1, a1
	add a1, s3, s2
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, -1
	bnez t2, 2477b
	slli t3, t0, 3
	add a5, a5, t3
	add t4, a5, t3
	sd a1, 0(t4)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2484:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2484b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2485:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2485b
	slli t3, t0, 3
	sub a5, a5, t3
	srli a1, s7, 60
	addi s8, zero, 0
2486:
	xor t2, s8, a1
	addi t2, t2, -1
	srli t2, t2, 63
	addi t3, zero, 0
	sub s4, t3, t2
	addi t2, s8, 8
	mul t2, t2, s5
	add a5, t2, a7
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2487:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2487b
	addi s8, s8, 1
	xor t2, s8, a1
	addi t2, t2, -1
	srli t2, t2, 63
	addi t3, zero, 0
	sub s4, t3, t2
	addi t2, s8, 8
	mul t2, t2, s5
	add a5, t2, a7
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2488:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2488b
	addi s8, s8, 1
	addi t2, s8, -16
	bnez t2, 2486b
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a4, a7, 0
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
2489:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2489b
2490:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a7)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi a0, a7, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 2491f
2493:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2493b
	j 2492f
2491:
2492:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2494f
2496:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 16(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 16(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 24(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 24(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 32(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 32(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2496b
	j 2495f
2494:
2495:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	addi a1, a1, -1
	bnez a1, 2490b
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2497:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2497b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2498:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2498b
	slli s7, s7, 4
	addi s10, s10, -1
	bnez s10, 2328b
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a4, a7, 0
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
2499:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2499b
2500:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a7)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi a0, a7, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 2501f
2503:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2503b
	j 2502f
2501:
2502:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2504f
2506:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 16(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 16(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 24(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 24(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 32(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 32(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2506b
	j 2505f
2504:
2505:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	addi a1, a1, -1
	bnez a1, 2500b
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2507:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2507b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2508:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2508b
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t5, t0, 0
	addi s0, zero, 0
2509:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2509b
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi s0, zero, 1
	sd s0, 0(t3)
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t4, a7, 0
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	addi t5, t0, 0
	addi t2, zero, 0
2510:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2510b
	addi s0, zero, 0
	sltu s1, s0, t2
	addi a0, s1, -1
	andi a0, a0, 1
	xori a0, a0, 1
2291:
	beqz a0, 2511f
	ld t4, 24(s6)
	ld t5, 16(s6)
	slli t5, t5, 32
	srli t5, t5, 48
	add t5, t5, t5
	addi s0, zero, 0
2513:
	sb s0, 0(t4)
	addi t4, t4, 1
	addi t5, t5, -1
	bnez t5, 2513b
	addi a0, zero, 0
	j 2512f
2511:
	ld s8, 16(s6)
	slli s8, s8, 48
	srli s8, s8, 48
	ld t3, 16(s6)
	slli t3, t3, 32
	srli t3, t3, 48
	add s7, s11, s8
	add s7, s7, t3
	add s7, s7, s8
	add s7, s7, s8
	ld s8, 16(s6)
	slli s8, s8, 32
	srli s8, s8, 48
	addi s9, s7, 0
	ld s8, 16(s6)
	slli s8, s8, 48
	srli s8, s8, 48
	ld t3, 16(s6)
	slli t3, t3, 32
	srli t3, t3, 48
	add s7, s11, s8
	add s7, s7, t3
	ld s8, 16(s6)
	slli s8, s8, 48
	srli s8, s8, 48
	add a7, a7, s5
	add a7, a7, s5
	add a7, a7, s5
	add a7, a7, s5
	add t3, a7, s5
	addi t3, t3, -16
	addi s0, zero, 0
	sd s0, 0(t3)
	addi t3, a7, 0
	addi t5, t0, 0
	addi s0, zero, 0
2514:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2514b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
2515:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 2515b
	sub a7, a7, s5
	sub a7, a7, s5
	sub a7, a7, s5
	sub a7, a7, s5
	addi t3, a7, 0
	add t3, t3, s5
	addi t4, a7, 0
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	addi t5, t0, 2
2516:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2516b
	ld s10, 16(s6)
	slli s10, s10, 32
	srli s10, s10, 48
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t5, t0, 0
	addi s0, zero, 0
2517:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2517b
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi s0, zero, 1
	sd s0, 0(t3)
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	addi a4, a7, 0
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
2518:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2518b
2519:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a7)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi a0, a7, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 2520f
2522:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2522b
	j 2521f
2520:
2521:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2523f
2525:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 16(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 16(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 24(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 24(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 32(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 32(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2525b
	j 2524f
2523:
2524:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	addi a1, a1, -1
	bnez a1, 2519b
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2526:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2526b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2527:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2527b
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a4, a7, 0
	add a4, a4, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
2528:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2528b
2529:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a7)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi a0, a7, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 2530f
2532:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2532b
	j 2531f
2530:
2531:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2533f
2535:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 16(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 16(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 24(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 24(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 32(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 32(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2535b
	j 2534f
2533:
2534:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	addi a1, a1, -1
	bnez a1, 2529b
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2536:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2536b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2537:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2537b
	addi s4, zero, -1
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2538:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2538b
	addi s7, zero, 2
2539:
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a4, a7, 0
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
2540:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2540b
2541:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a7)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi a0, a7, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 2542f
2544:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2544b
	j 2543f
2542:
2543:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2545f
2547:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 16(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 16(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 24(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 24(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 32(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 32(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2547b
	j 2546f
2545:
2546:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	addi a1, a1, -1
	bnez a1, 2541b
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2548:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2548b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2549:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2549b
	addi s4, zero, -1
	addi t2, s7, 8
	mul t2, t2, s5
	add a2, t2, a7
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2550:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2550b
	addi s7, s7, 1
	addi t2, s7, -16
	bnez t2, 2539b
	addi s4, zero, -1
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2551:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2551b
2552:
	lbu s7, 0(s9)
	slli s7, s7, 56
	addi s9, s9, 1
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a5, 0
	add t5, t0, t0
	addi t5, t5, 2
	addi s0, zero, 0
2553:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2553b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2554:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2555f
2557:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2557b
	j 2556f
2555:
2556:
	beqz t6, 2558f
2560:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2560b
	j 2559f
2558:
2559:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2554b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2561:
	ld s2, 0(t3)
	ld s3, 8(t3)
	srli s4, s2, 63
	slli s2, s2, 1
	add s2, s2, t2
	srli t2, s3, 63
	slli s3, s3, 1
	add s3, s3, s4
	ld s4, 0(a0)
	add s1, s1, s2
	sltu s2, s1, s2
	mul s0, s4, s4
	mulhu s4, s4, s4
	add s4, s4, s2
	add s0, s0, s1
	sltu s2, s0, s1
	add s4, s4, s2
	add s3, s3, s4
	sltu s1, s3, s4
	sd s0, 0(t3)
	sd s3, 8(t3)
	addi t3, t3, 16
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2561b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
2562:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi a0, a7, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2563f
2565:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2565b
	j 2564f
2563:
2564:
	beqz t6, 2566f
2568:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2568b
	j 2567f
2566:
2567:
	ld s2, 0(t4)
	add s1, s1, s2
	sltu s3, s1, s2
	add s1, s1, a1
	sltu s2, s1, a1
	add a1, s3, s2
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, -1
	bnez t2, 2562b
	slli t3, t0, 3
	add a5, a5, t3
	add t4, a5, t3
	sd a1, 0(t4)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2569:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2569b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2570:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2570b
	slli t3, t0, 3
	sub a5, a5, t3
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a5, 0
	add t5, t0, t0
	addi t5, t5, 2
	addi s0, zero, 0
2571:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2571b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2572:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2573f
2575:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2575b
	j 2574f
2573:
2574:
	beqz t6, 2576f
2578:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2578b
	j 2577f
2576:
2577:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2572b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2579:
	ld s2, 0(t3)
	ld s3, 8(t3)
	srli s4, s2, 63
	slli s2, s2, 1
	add s2, s2, t2
	srli t2, s3, 63
	slli s3, s3, 1
	add s3, s3, s4
	ld s4, 0(a0)
	add s1, s1, s2
	sltu s2, s1, s2
	mul s0, s4, s4
	mulhu s4, s4, s4
	add s4, s4, s2
	add s0, s0, s1
	sltu s2, s0, s1
	add s4, s4, s2
	add s3, s3, s4
	sltu s1, s3, s4
	sd s0, 0(t3)
	sd s3, 8(t3)
	addi t3, t3, 16
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2579b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
2580:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi a0, a7, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2581f
2583:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2583b
	j 2582f
2581:
2582:
	beqz t6, 2584f
2586:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2586b
	j 2585f
2584:
2585:
	ld s2, 0(t4)
	add s1, s1, s2
	sltu s3, s1, s2
	add s1, s1, a1
	sltu s2, s1, a1
	add a1, s3, s2
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, -1
	bnez t2, 2580b
	slli t3, t0, 3
	add a5, a5, t3
	add t4, a5, t3
	sd a1, 0(t4)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2587:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2587b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2588:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2588b
	slli t3, t0, 3
	sub a5, a5, t3
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a5, 0
	add t5, t0, t0
	addi t5, t5, 2
	addi s0, zero, 0
2589:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2589b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2590:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2591f
2593:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2593b
	j 2592f
2591:
2592:
	beqz t6, 2594f
2596:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2596b
	j 2595f
2594:
2595:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2590b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2597:
	ld s2, 0(t3)
	ld s3, 8(t3)
	srli s4, s2, 63
	slli s2, s2, 1
	add s2, s2, t2
	srli t2, s3, 63
	slli s3, s3, 1
	add s3, s3, s4
	ld s4, 0(a0)
	add s1, s1, s2
	sltu s2, s1, s2
	mul s0, s4, s4
	mulhu s4, s4, s4
	add s4, s4, s2
	add s0, s0, s1
	sltu s2, s0, s1
	add s4, s4, s2
	add s3, s3, s4
	sltu s1, s3, s4
	sd s0, 0(t3)
	sd s3, 8(t3)
	addi t3, t3, 16
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2597b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
2598:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi a0, a7, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2599f
2601:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2601b
	j 2600f
2599:
2600:
	beqz t6, 2602f
2604:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2604b
	j 2603f
2602:
2603:
	ld s2, 0(t4)
	add s1, s1, s2
	sltu s3, s1, s2
	add s1, s1, a1
	sltu s2, s1, a1
	add a1, s3, s2
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, -1
	bnez t2, 2598b
	slli t3, t0, 3
	add a5, a5, t3
	add t4, a5, t3
	sd a1, 0(t4)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2605:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2605b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2606:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2606b
	slli t3, t0, 3
	sub a5, a5, t3
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a5, 0
	add t5, t0, t0
	addi t5, t5, 2
	addi s0, zero, 0
2607:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2607b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2608:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2609f
2611:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2611b
	j 2610f
2609:
2610:
	beqz t6, 2612f
2614:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2614b
	j 2613f
2612:
2613:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2608b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2615:
	ld s2, 0(t3)
	ld s3, 8(t3)
	srli s4, s2, 63
	slli s2, s2, 1
	add s2, s2, t2
	srli t2, s3, 63
	slli s3, s3, 1
	add s3, s3, s4
	ld s4, 0(a0)
	add s1, s1, s2
	sltu s2, s1, s2
	mul s0, s4, s4
	mulhu s4, s4, s4
	add s4, s4, s2
	add s0, s0, s1
	sltu s2, s0, s1
	add s4, s4, s2
	add s3, s3, s4
	sltu s1, s3, s4
	sd s0, 0(t3)
	sd s3, 8(t3)
	addi t3, t3, 16
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2615b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
2616:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi a0, a7, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2617f
2619:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2619b
	j 2618f
2617:
2618:
	beqz t6, 2620f
2622:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2622b
	j 2621f
2620:
2621:
	ld s2, 0(t4)
	add s1, s1, s2
	sltu s3, s1, s2
	add s1, s1, a1
	sltu s2, s1, a1
	add a1, s3, s2
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, -1
	bnez t2, 2616b
	slli t3, t0, 3
	add a5, a5, t3
	add t4, a5, t3
	sd a1, 0(t4)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2623:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2623b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2624:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2624b
	slli t3, t0, 3
	sub a5, a5, t3
	srli a1, s7, 60
	addi s8, zero, 0
2625:
	xor t2, s8, a1
	addi t2, t2, -1
	srli t2, t2, 63
	addi t3, zero, 0
	sub s4, t3, t2
	addi t2, s8, 8
	mul t2, t2, s5
	add a5, t2, a7
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2626:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2626b
	addi s8, s8, 1
	xor t2, s8, a1
	addi t2, t2, -1
	srli t2, t2, 63
	addi t3, zero, 0
	sub s4, t3, t2
	addi t2, s8, 8
	mul t2, t2, s5
	add a5, t2, a7
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2627:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2627b
	addi s8, s8, 1
	addi t2, s8, -16
	bnez t2, 2625b
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a4, a7, 0
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
2628:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2628b
2629:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a7)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi a0, a7, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 2630f
2632:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2632b
	j 2631f
2630:
2631:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2633f
2635:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 16(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 16(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 24(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 24(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 32(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 32(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2635b
	j 2634f
2633:
2634:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	addi a1, a1, -1
	bnez a1, 2629b
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2636:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2636b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2637:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2637b
	slli s7, s7, 4
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a5, 0
	add t5, t0, t0
	addi t5, t5, 2
	addi s0, zero, 0
2638:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2638b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2639:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2640f
2642:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2642b
	j 2641f
2640:
2641:
	beqz t6, 2643f
2645:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2645b
	j 2644f
2643:
2644:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2639b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2646:
	ld s2, 0(t3)
	ld s3, 8(t3)
	srli s4, s2, 63
	slli s2, s2, 1
	add s2, s2, t2
	srli t2, s3, 63
	slli s3, s3, 1
	add s3, s3, s4
	ld s4, 0(a0)
	add s1, s1, s2
	sltu s2, s1, s2
	mul s0, s4, s4
	mulhu s4, s4, s4
	add s4, s4, s2
	add s0, s0, s1
	sltu s2, s0, s1
	add s4, s4, s2
	add s3, s3, s4
	sltu s1, s3, s4
	sd s0, 0(t3)
	sd s3, 8(t3)
	addi t3, t3, 16
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2646b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
2647:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi a0, a7, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2648f
2650:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2650b
	j 2649f
2648:
2649:
	beqz t6, 2651f
2653:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2653b
	j 2652f
2651:
2652:
	ld s2, 0(t4)
	add s1, s1, s2
	sltu s3, s1, s2
	add s1, s1, a1
	sltu s2, s1, a1
	add a1, s3, s2
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, -1
	bnez t2, 2647b
	slli t3, t0, 3
	add a5, a5, t3
	add t4, a5, t3
	sd a1, 0(t4)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2654:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2654b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2655:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2655b
	slli t3, t0, 3
	sub a5, a5, t3
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a5, 0
	add t5, t0, t0
	addi t5, t5, 2
	addi s0, zero, 0
2656:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2656b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2657:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2658f
2660:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2660b
	j 2659f
2658:
2659:
	beqz t6, 2661f
2663:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2663b
	j 2662f
2661:
2662:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2657b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2664:
	ld s2, 0(t3)
	ld s3, 8(t3)
	srli s4, s2, 63
	slli s2, s2, 1
	add s2, s2, t2
	srli t2, s3, 63
	slli s3, s3, 1
	add s3, s3, s4
	ld s4, 0(a0)
	add s1, s1, s2
	sltu s2, s1, s2
	mul s0, s4, s4
	mulhu s4, s4, s4
	add s4, s4, s2
	add s0, s0, s1
	sltu s2, s0, s1
	add s4, s4, s2
	add s3, s3, s4
	sltu s1, s3, s4
	sd s0, 0(t3)
	sd s3, 8(t3)
	addi t3, t3, 16
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2664b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
2665:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi a0, a7, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2666f
2668:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2668b
	j 2667f
2666:
2667:
	beqz t6, 2669f
2671:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2671b
	j 2670f
2669:
2670:
	ld s2, 0(t4)
	add s1, s1, s2
	sltu s3, s1, s2
	add s1, s1, a1
	sltu s2, s1, a1
	add a1, s3, s2
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, -1
	bnez t2, 2665b
	slli t3, t0, 3
	add a5, a5, t3
	add t4, a5, t3
	sd a1, 0(t4)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2672:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2672b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2673:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2673b
	slli t3, t0, 3
	sub a5, a5, t3
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a5, 0
	add t5, t0, t0
	addi t5, t5, 2
	addi s0, zero, 0
2674:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2674b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2675:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2676f
2678:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2678b
	j 2677f
2676:
2677:
	beqz t6, 2679f
2681:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2681b
	j 2680f
2679:
2680:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2675b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2682:
	ld s2, 0(t3)
	ld s3, 8(t3)
	srli s4, s2, 63
	slli s2, s2, 1
	add s2, s2, t2
	srli t2, s3, 63
	slli s3, s3, 1
	add s3, s3, s4
	ld s4, 0(a0)
	add s1, s1, s2
	sltu s2, s1, s2
	mul s0, s4, s4
	mulhu s4, s4, s4
	add s4, s4, s2
	add s0, s0, s1
	sltu s2, s0, s1
	add s4, s4, s2
	add s3, s3, s4
	sltu s1, s3, s4
	sd s0, 0(t3)
	sd s3, 8(t3)
	addi t3, t3, 16
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2682b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
2683:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi a0, a7, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2684f
2686:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2686b
	j 2685f
2684:
2685:
	beqz t6, 2687f
2689:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2689b
	j 2688f
2687:
2688:
	ld s2, 0(t4)
	add s1, s1, s2
	sltu s3, s1, s2
	add s1, s1, a1
	sltu s2, s1, a1
	add a1, s3, s2
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, -1
	bnez t2, 2683b
	slli t3, t0, 3
	add a5, a5, t3
	add t4, a5, t3
	sd a1, 0(t4)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2690:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2690b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2691:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2691b
	slli t3, t0, 3
	sub a5, a5, t3
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a5, 0
	add t5, t0, t0
	addi t5, t5, 2
	addi s0, zero, 0
2692:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2692b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2693:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2694f
2696:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2696b
	j 2695f
2694:
2695:
	beqz t6, 2697f
2699:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2699b
	j 2698f
2697:
2698:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2693b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2700:
	ld s2, 0(t3)
	ld s3, 8(t3)
	srli s4, s2, 63
	slli s2, s2, 1
	add s2, s2, t2
	srli t2, s3, 63
	slli s3, s3, 1
	add s3, s3, s4
	ld s4, 0(a0)
	add s1, s1, s2
	sltu s2, s1, s2
	mul s0, s4, s4
	mulhu s4, s4, s4
	add s4, s4, s2
	add s0, s0, s1
	sltu s2, s0, s1
	add s4, s4, s2
	add s3, s3, s4
	sltu s1, s3, s4
	sd s0, 0(t3)
	sd s3, 8(t3)
	addi t3, t3, 16
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2700b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
2701:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi a0, a7, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2702f
2704:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2704b
	j 2703f
2702:
2703:
	beqz t6, 2705f
2707:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2707b
	j 2706f
2705:
2706:
	ld s2, 0(t4)
	add s1, s1, s2
	sltu s3, s1, s2
	add s1, s1, a1
	sltu s2, s1, a1
	add a1, s3, s2
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, -1
	bnez t2, 2701b
	slli t3, t0, 3
	add a5, a5, t3
	add t4, a5, t3
	sd a1, 0(t4)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2708:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2708b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2709:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2709b
	slli t3, t0, 3
	sub a5, a5, t3
	srli a1, s7, 60
	addi s8, zero, 0
2710:
	xor t2, s8, a1
	addi t2, t2, -1
	srli t2, t2, 63
	addi t3, zero, 0
	sub s4, t3, t2
	addi t2, s8, 8
	mul t2, t2, s5
	add a5, t2, a7
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2711:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2711b
	addi s8, s8, 1
	xor t2, s8, a1
	addi t2, t2, -1
	srli t2, t2, 63
	addi t3, zero, 0
	sub s4, t3, t2
	addi t2, s8, 8
	mul t2, t2, s5
	add a5, t2, a7
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2712:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2712b
	addi s8, s8, 1
	addi t2, s8, -16
	bnez t2, 2710b
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a4, a7, 0
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
2713:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2713b
2714:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a7)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi a0, a7, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 2715f
2717:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2717b
	j 2716f
2715:
2716:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2718f
2720:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 16(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 16(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 24(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 24(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 32(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 32(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2720b
	j 2719f
2718:
2719:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	addi a1, a1, -1
	bnez a1, 2714b
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2721:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2721b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2722:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2722b
	slli s7, s7, 4
	addi s10, s10, -1
	bnez s10, 2552b
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a4, a7, 0
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
2723:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2723b
2724:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a7)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi a0, a7, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 2725f
2727:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2727b
	j 2726f
2725:
2726:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2728f
2730:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 16(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 16(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 24(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 24(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 32(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 32(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2730b
	j 2729f
2728:
2729:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	addi a1, a1, -1
	bnez a1, 2724b
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2731:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2731b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2732:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2732b
	ld s8, 16(s6)
	slli s8, s8, 48
	srli s8, s8, 48
	ld t3, 16(s6)
	slli t3, t3, 32
	srli t3, t3, 48
	add s7, s11, s8
	add s7, s7, t3
	add s7, s7, s8
	add a7, a7, s5
	add a7, a7, s5
	add a7, a7, s5
	add a7, a7, s5
	add a7, a7, s5
	add t3, a7, s5
	addi t3, t3, -16
	addi s0, zero, 0
	sd s0, 0(t3)
	addi t3, a7, 0
	addi t5, t0, 0
	addi s0, zero, 0
2733:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2733b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
2734:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 2734b
	sub a7, a7, s5
	sub a7, a7, s5
	sub a7, a7, s5
	sub a7, a7, s5
	sub a7, a7, s5
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t4, a7, 0
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	addi t5, t0, 0
	addi t2, zero, 0
2735:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2735b
	addi s0, zero, 0
	sltu s1, s0, t2
	addi a0, s1, -1
	sd a0, 0(s6)
	addi s9, ra, 0
	ld s8, 16(s6)
	slli s8, s8, 48
	srli s8, s8, 48
	ld t3, 16(s6)
	slli t3, t3, 32
	srli t3, t3, 48
	add s7, s11, s8
	add s7, s7, t3
	ld s8, 16(s6)
	slli s8, s8, 48
	srli s8, s8, 48
	add a7, a7, s5
	add a7, a7, s5
	add a7, a7, s5
	add a7, a7, s5
	add t3, a7, s5
	addi t3, t3, -16
	addi s0, zero, 0
	sd s0, 0(t3)
	addi t3, a7, 0
	addi t5, t0, 0
	addi s0, zero, 0
2736:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2736b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
2737:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 2737b
	sub a7, a7, s5
	sub a7, a7, s5
	sub a7, a7, s5
	sub a7, a7, s5
	addi t3, a7, 0
	add t3, t3, s5
	addi t4, a7, 0
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	addi t5, t0, 2
2738:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2738b
	ld s10, 16(s6)
	slli s10, s10, 32
	srli s10, s10, 48
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t5, t0, 0
	addi s0, zero, 0
2739:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2739b
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi s0, zero, 1
	sd s0, 0(t3)
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	addi a4, a7, 0
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
2740:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2740b
2741:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a7)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi a0, a7, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 2742f
2744:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2744b
	j 2743f
2742:
2743:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2745f
2747:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 16(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 16(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 24(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 24(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 32(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 32(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2747b
	j 2746f
2745:
2746:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	addi a1, a1, -1
	bnez a1, 2741b
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2748:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2748b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2749:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2749b
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a4, a7, 0
	add a4, a4, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
2750:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2750b
2751:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a7)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi a0, a7, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 2752f
2754:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2754b
	j 2753f
2752:
2753:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2755f
2757:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 16(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 16(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 24(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 24(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 32(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 32(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2757b
	j 2756f
2755:
2756:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	addi a1, a1, -1
	bnez a1, 2751b
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2758:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2758b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2759:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2759b
	addi s4, zero, -1
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2760:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2760b
	addi s7, zero, 2
2761:
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a4, a7, 0
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
2762:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2762b
2763:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a7)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi a0, a7, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 2764f
2766:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2766b
	j 2765f
2764:
2765:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2767f
2769:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 16(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 16(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 24(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 24(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 32(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 32(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2769b
	j 2768f
2767:
2768:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	addi a1, a1, -1
	bnez a1, 2763b
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2770:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2770b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2771:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2771b
	addi s4, zero, -1
	addi t2, s7, 8
	mul t2, t2, s5
	add a2, t2, a7
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2772:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2772b
	addi s7, s7, 1
	addi t2, s7, -16
	bnez t2, 2761b
	addi s4, zero, -1
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2773:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2773b
2774:
	lbu s7, 0(s9)
	slli s7, s7, 56
	addi s9, s9, 1
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a5, 0
	add t5, t0, t0
	addi t5, t5, 2
	addi s0, zero, 0
2775:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2775b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2776:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2777f
2779:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2779b
	j 2778f
2777:
2778:
	beqz t6, 2780f
2782:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2782b
	j 2781f
2780:
2781:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2776b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2783:
	ld s2, 0(t3)
	ld s3, 8(t3)
	srli s4, s2, 63
	slli s2, s2, 1
	add s2, s2, t2
	srli t2, s3, 63
	slli s3, s3, 1
	add s3, s3, s4
	ld s4, 0(a0)
	add s1, s1, s2
	sltu s2, s1, s2
	mul s0, s4, s4
	mulhu s4, s4, s4
	add s4, s4, s2
	add s0, s0, s1
	sltu s2, s0, s1
	add s4, s4, s2
	add s3, s3, s4
	sltu s1, s3, s4
	sd s0, 0(t3)
	sd s3, 8(t3)
	addi t3, t3, 16
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2783b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
2784:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi a0, a7, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2785f
2787:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2787b
	j 2786f
2785:
2786:
	beqz t6, 2788f
2790:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2790b
	j 2789f
2788:
2789:
	ld s2, 0(t4)
	add s1, s1, s2
	sltu s3, s1, s2
	add s1, s1, a1
	sltu s2, s1, a1
	add a1, s3, s2
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, -1
	bnez t2, 2784b
	slli t3, t0, 3
	add a5, a5, t3
	add t4, a5, t3
	sd a1, 0(t4)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2791:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2791b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2792:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2792b
	slli t3, t0, 3
	sub a5, a5, t3
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a5, 0
	add t5, t0, t0
	addi t5, t5, 2
	addi s0, zero, 0
2793:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2793b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2794:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2795f
2797:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2797b
	j 2796f
2795:
2796:
	beqz t6, 2798f
2800:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2800b
	j 2799f
2798:
2799:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2794b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2801:
	ld s2, 0(t3)
	ld s3, 8(t3)
	srli s4, s2, 63
	slli s2, s2, 1
	add s2, s2, t2
	srli t2, s3, 63
	slli s3, s3, 1
	add s3, s3, s4
	ld s4, 0(a0)
	add s1, s1, s2
	sltu s2, s1, s2
	mul s0, s4, s4
	mulhu s4, s4, s4
	add s4, s4, s2
	add s0, s0, s1
	sltu s2, s0, s1
	add s4, s4, s2
	add s3, s3, s4
	sltu s1, s3, s4
	sd s0, 0(t3)
	sd s3, 8(t3)
	addi t3, t3, 16
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2801b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
2802:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi a0, a7, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2803f
2805:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2805b
	j 2804f
2803:
2804:
	beqz t6, 2806f
2808:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2808b
	j 2807f
2806:
2807:
	ld s2, 0(t4)
	add s1, s1, s2
	sltu s3, s1, s2
	add s1, s1, a1
	sltu s2, s1, a1
	add a1, s3, s2
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, -1
	bnez t2, 2802b
	slli t3, t0, 3
	add a5, a5, t3
	add t4, a5, t3
	sd a1, 0(t4)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2809:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2809b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2810:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2810b
	slli t3, t0, 3
	sub a5, a5, t3
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a5, 0
	add t5, t0, t0
	addi t5, t5, 2
	addi s0, zero, 0
2811:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2811b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2812:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2813f
2815:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2815b
	j 2814f
2813:
2814:
	beqz t6, 2816f
2818:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2818b
	j 2817f
2816:
2817:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2812b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2819:
	ld s2, 0(t3)
	ld s3, 8(t3)
	srli s4, s2, 63
	slli s2, s2, 1
	add s2, s2, t2
	srli t2, s3, 63
	slli s3, s3, 1
	add s3, s3, s4
	ld s4, 0(a0)
	add s1, s1, s2
	sltu s2, s1, s2
	mul s0, s4, s4
	mulhu s4, s4, s4
	add s4, s4, s2
	add s0, s0, s1
	sltu s2, s0, s1
	add s4, s4, s2
	add s3, s3, s4
	sltu s1, s3, s4
	sd s0, 0(t3)
	sd s3, 8(t3)
	addi t3, t3, 16
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2819b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
2820:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi a0, a7, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2821f
2823:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2823b
	j 2822f
2821:
2822:
	beqz t6, 2824f
2826:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2826b
	j 2825f
2824:
2825:
	ld s2, 0(t4)
	add s1, s1, s2
	sltu s3, s1, s2
	add s1, s1, a1
	sltu s2, s1, a1
	add a1, s3, s2
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, -1
	bnez t2, 2820b
	slli t3, t0, 3
	add a5, a5, t3
	add t4, a5, t3
	sd a1, 0(t4)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2827:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2827b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2828:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2828b
	slli t3, t0, 3
	sub a5, a5, t3
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a5, 0
	add t5, t0, t0
	addi t5, t5, 2
	addi s0, zero, 0
2829:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2829b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2830:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2831f
2833:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2833b
	j 2832f
2831:
2832:
	beqz t6, 2834f
2836:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2836b
	j 2835f
2834:
2835:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2830b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2837:
	ld s2, 0(t3)
	ld s3, 8(t3)
	srli s4, s2, 63
	slli s2, s2, 1
	add s2, s2, t2
	srli t2, s3, 63
	slli s3, s3, 1
	add s3, s3, s4
	ld s4, 0(a0)
	add s1, s1, s2
	sltu s2, s1, s2
	mul s0, s4, s4
	mulhu s4, s4, s4
	add s4, s4, s2
	add s0, s0, s1
	sltu s2, s0, s1
	add s4, s4, s2
	add s3, s3, s4
	sltu s1, s3, s4
	sd s0, 0(t3)
	sd s3, 8(t3)
	addi t3, t3, 16
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2837b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
2838:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi a0, a7, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2839f
2841:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2841b
	j 2840f
2839:
2840:
	beqz t6, 2842f
2844:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2844b
	j 2843f
2842:
2843:
	ld s2, 0(t4)
	add s1, s1, s2
	sltu s3, s1, s2
	add s1, s1, a1
	sltu s2, s1, a1
	add a1, s3, s2
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, -1
	bnez t2, 2838b
	slli t3, t0, 3
	add a5, a5, t3
	add t4, a5, t3
	sd a1, 0(t4)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2845:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2845b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2846:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2846b
	slli t3, t0, 3
	sub a5, a5, t3
	srli a1, s7, 60
	addi s8, zero, 0
2847:
	xor t2, s8, a1
	addi t2, t2, -1
	srli t2, t2, 63
	addi t3, zero, 0
	sub s4, t3, t2
	addi t2, s8, 8
	mul t2, t2, s5
	add a5, t2, a7
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2848:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2848b
	addi s8, s8, 1
	xor t2, s8, a1
	addi t2, t2, -1
	srli t2, t2, 63
	addi t3, zero, 0
	sub s4, t3, t2
	addi t2, s8, 8
	mul t2, t2, s5
	add a5, t2, a7
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2849:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2849b
	addi s8, s8, 1
	addi t2, s8, -16
	bnez t2, 2847b
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a4, a7, 0
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
2850:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2850b
2851:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a7)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi a0, a7, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 2852f
2854:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2854b
	j 2853f
2852:
2853:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2855f
2857:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 16(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 16(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 24(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 24(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 32(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 32(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2857b
	j 2856f
2855:
2856:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	addi a1, a1, -1
	bnez a1, 2851b
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2858:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2858b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2859:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2859b
	slli s7, s7, 4
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a5, 0
	add t5, t0, t0
	addi t5, t5, 2
	addi s0, zero, 0
2860:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2860b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2861:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2862f
2864:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2864b
	j 2863f
2862:
2863:
	beqz t6, 2865f
2867:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2867b
	j 2866f
2865:
2866:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2861b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2868:
	ld s2, 0(t3)
	ld s3, 8(t3)
	srli s4, s2, 63
	slli s2, s2, 1
	add s2, s2, t2
	srli t2, s3, 63
	slli s3, s3, 1
	add s3, s3, s4
	ld s4, 0(a0)
	add s1, s1, s2
	sltu s2, s1, s2
	mul s0, s4, s4
	mulhu s4, s4, s4
	add s4, s4, s2
	add s0, s0, s1
	sltu s2, s0, s1
	add s4, s4, s2
	add s3, s3, s4
	sltu s1, s3, s4
	sd s0, 0(t3)
	sd s3, 8(t3)
	addi t3, t3, 16
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2868b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
2869:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi a0, a7, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2870f
2872:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2872b
	j 2871f
2870:
2871:
	beqz t6, 2873f
2875:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2875b
	j 2874f
2873:
2874:
	ld s2, 0(t4)
	add s1, s1, s2
	sltu s3, s1, s2
	add s1, s1, a1
	sltu s2, s1, a1
	add a1, s3, s2
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, -1
	bnez t2, 2869b
	slli t3, t0, 3
	add a5, a5, t3
	add t4, a5, t3
	sd a1, 0(t4)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2876:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2876b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2877:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2877b
	slli t3, t0, 3
	sub a5, a5, t3
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a5, 0
	add t5, t0, t0
	addi t5, t5, 2
	addi s0, zero, 0
2878:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2878b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2879:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2880f
2882:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2882b
	j 2881f
2880:
2881:
	beqz t6, 2883f
2885:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2885b
	j 2884f
2883:
2884:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2879b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2886:
	ld s2, 0(t3)
	ld s3, 8(t3)
	srli s4, s2, 63
	slli s2, s2, 1
	add s2, s2, t2
	srli t2, s3, 63
	slli s3, s3, 1
	add s3, s3, s4
	ld s4, 0(a0)
	add s1, s1, s2
	sltu s2, s1, s2
	mul s0, s4, s4
	mulhu s4, s4, s4
	add s4, s4, s2
	add s0, s0, s1
	sltu s2, s0, s1
	add s4, s4, s2
	add s3, s3, s4
	sltu s1, s3, s4
	sd s0, 0(t3)
	sd s3, 8(t3)
	addi t3, t3, 16
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2886b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
2887:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi a0, a7, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2888f
2890:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2890b
	j 2889f
2888:
2889:
	beqz t6, 2891f
2893:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2893b
	j 2892f
2891:
2892:
	ld s2, 0(t4)
	add s1, s1, s2
	sltu s3, s1, s2
	add s1, s1, a1
	sltu s2, s1, a1
	add a1, s3, s2
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, -1
	bnez t2, 2887b
	slli t3, t0, 3
	add a5, a5, t3
	add t4, a5, t3
	sd a1, 0(t4)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2894:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2894b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2895:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2895b
	slli t3, t0, 3
	sub a5, a5, t3
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a5, 0
	add t5, t0, t0
	addi t5, t5, 2
	addi s0, zero, 0
2896:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2896b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2897:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2898f
2900:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2900b
	j 2899f
2898:
2899:
	beqz t6, 2901f
2903:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2903b
	j 2902f
2901:
2902:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2897b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2904:
	ld s2, 0(t3)
	ld s3, 8(t3)
	srli s4, s2, 63
	slli s2, s2, 1
	add s2, s2, t2
	srli t2, s3, 63
	slli s3, s3, 1
	add s3, s3, s4
	ld s4, 0(a0)
	add s1, s1, s2
	sltu s2, s1, s2
	mul s0, s4, s4
	mulhu s4, s4, s4
	add s4, s4, s2
	add s0, s0, s1
	sltu s2, s0, s1
	add s4, s4, s2
	add s3, s3, s4
	sltu s1, s3, s4
	sd s0, 0(t3)
	sd s3, 8(t3)
	addi t3, t3, 16
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2904b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
2905:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi a0, a7, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2906f
2908:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2908b
	j 2907f
2906:
2907:
	beqz t6, 2909f
2911:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2911b
	j 2910f
2909:
2910:
	ld s2, 0(t4)
	add s1, s1, s2
	sltu s3, s1, s2
	add s1, s1, a1
	sltu s2, s1, a1
	add a1, s3, s2
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, -1
	bnez t2, 2905b
	slli t3, t0, 3
	add a5, a5, t3
	add t4, a5, t3
	sd a1, 0(t4)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2912:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2912b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2913:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2913b
	slli t3, t0, 3
	sub a5, a5, t3
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a5, 0
	add t5, t0, t0
	addi t5, t5, 2
	addi s0, zero, 0
2914:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2914b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2915:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2916f
2918:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2918b
	j 2917f
2916:
2917:
	beqz t6, 2919f
2921:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2921b
	j 2920f
2919:
2920:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2915b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2922:
	ld s2, 0(t3)
	ld s3, 8(t3)
	srli s4, s2, 63
	slli s2, s2, 1
	add s2, s2, t2
	srli t2, s3, 63
	slli s3, s3, 1
	add s3, s3, s4
	ld s4, 0(a0)
	add s1, s1, s2
	sltu s2, s1, s2
	mul s0, s4, s4
	mulhu s4, s4, s4
	add s4, s4, s2
	add s0, s0, s1
	sltu s2, s0, s1
	add s4, s4, s2
	add s3, s3, s4
	sltu s1, s3, s4
	sd s0, 0(t3)
	sd s3, 8(t3)
	addi t3, t3, 16
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2922b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
2923:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi a0, a7, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 2924f
2926:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2926b
	j 2925f
2924:
2925:
	beqz t6, 2927f
2929:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2929b
	j 2928f
2927:
2928:
	ld s2, 0(t4)
	add s1, s1, s2
	sltu s3, s1, s2
	add s1, s1, a1
	sltu s2, s1, a1
	add a1, s3, s2
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, -1
	bnez t2, 2923b
	slli t3, t0, 3
	add a5, a5, t3
	add t4, a5, t3
	sd a1, 0(t4)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2930:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2930b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2931:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2931b
	slli t3, t0, 3
	sub a5, a5, t3
	srli a1, s7, 60
	addi s8, zero, 0
2932:
	xor t2, s8, a1
	addi t2, t2, -1
	srli t2, t2, 63
	addi t3, zero, 0
	sub s4, t3, t2
	addi t2, s8, 8
	mul t2, t2, s5
	add a5, t2, a7
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2933:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2933b
	addi s8, s8, 1
	xor t2, s8, a1
	addi t2, t2, -1
	srli t2, t2, 63
	addi t3, zero, 0
	sub s4, t3, t2
	addi t2, s8, 8
	mul t2, t2, s5
	add a5, t2, a7
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2934:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2934b
	addi s8, s8, 1
	addi t2, s8, -16
	bnez t2, 2932b
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a4, a7, 0
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
2935:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2935b
2936:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a7)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi a0, a7, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 2937f
2939:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2939b
	j 2938f
2937:
2938:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2940f
2942:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 16(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 16(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 24(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 24(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 32(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 32(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2942b
	j 2941f
2940:
2941:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	addi a1, a1, -1
	bnez a1, 2936b
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2943:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2943b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2944:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2944b
	slli s7, s7, 4
	addi s10, s10, -1
	bnez s10, 2774b
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a4, a7, 0
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
2945:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2945b
2946:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a7)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi a0, a7, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 2947f
2949:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2949b
	j 2948f
2947:
2948:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2950f
2952:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 16(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 16(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 24(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 24(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 32(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 32(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2952b
	j 2951f
2950:
2951:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	addi a1, a1, -1
	bnez a1, 2946b
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2953:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2953b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2954:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2954b
	ld s7, 16(s6)
	slli s7, s7, 48
	srli s7, s7, 48
	addi t2, zero, 28
	mul s7, s7, t2
	addi s7, s7, 704
	add s7, s7, s6
	addi s7, s7, 1600
	ld s8, 16(s6)
	slli s8, s8, 48
	srli s8, s8, 48
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s8
	addi t3, t3, -1
	addi t4, s7, 0
	addi t5, s8, 0
2955:
	lbu s0, 0(t3)
	sb s0, 0(t4)
	addi t4, t4, 1
	addi t3, t3, -1
	addi t5, t5, -1
	bnez t5, 2955b
	ld a7, 16(s6)
	slli a7, a7, 48
	srli a7, a7, 48
	addi t2, zero, 28
	mul a7, a7, t2
	addi a7, a7, 704
	add a7, a7, s6
	addi a7, a7, 256
	ld t0, 16(s6)
	slli t0, t0, 32
	srli t0, t0, 48
	addi t0, t0, 7
	srli t0, t0, 3
	slli s5, t0, 3
	addi s5, s5, 16
	ld s9, 16(s6)
	slli s9, s9, 48
	srli s9, s9, 48
	addi t2, zero, 28
	mul s9, s9, t2
	addi s9, s9, 704
	add s9, s9, s6
	addi s9, s9, 1600
	ld s10, 16(s6)
	slli s10, s10, 48
	srli s10, s10, 48
	addi t3, a7, 0
	add t3, t3, s5
	addi t5, t0, 0
	addi s0, zero, 0
2956:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2956b
	addi a2, a7, 0
	add a2, a2, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
2957:
	lbu s7, 0(s9)
	slli s7, s7, 56
	addi s9, s9, 1
	addi s8, zero, 8
2958:
	srli s4, s7, 63
	slli s7, s7, 1
	addi t3, a5, 0
	addi t4, a2, 0
	addi t5, t0, 0
2959:
	ld s2, 0(t4)
	slli s3, s2, 1
	add s3, s3, s4
	srli s4, s2, 63
	sd s3, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2959b
	sd s4, 0(t3)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2960:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2960b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2961:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2961b
	addi s8, s8, -1
	bnez s8, 2958b
	addi s10, s10, -1
	bnez s10, 2957b
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t4, a7, 0
	add t4, t4, s5
	addi t5, t0, 2
2962:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2962b
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t5, t0, 0
	addi s0, zero, 0
2963:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2963b
	addi s7, ra, 0
	ld s8, 16(s6)
	slli s8, s8, 32
	srli s8, s8, 48
	add a7, a7, s5
	add a7, a7, s5
	add a7, a7, s5
	add a7, a7, s5
	add a7, a7, s5
	add a7, a7, s5
	add t3, a7, s5
	addi t3, t3, -16
	addi s0, zero, 0
	sd s0, 0(t3)
	addi t3, a7, 0
	addi t5, t0, 0
	addi s0, zero, 0
2964:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2964b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
2965:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 2965b
	sub a7, a7, s5
	sub a7, a7, s5
	sub a7, a7, s5
	sub a7, a7, s5
	sub a7, a7, s5
	sub a7, a7, s5
	ld s8, 16(s6)
	slli s8, s8, 48
	srli s8, s8, 48
	ld t3, 16(s6)
	slli t3, t3, 32
	srli t3, t3, 48
	add s7, s11, s8
	add s7, s7, t3
	add s7, s7, s8
	add s7, s7, s8
	ld s8, 16(s6)
	slli s8, s8, 32
	srli s8, s8, 48
	add a7, a7, s5
	add a7, a7, s5
	add a7, a7, s5
	add a7, a7, s5
	add a7, a7, s5
	add t3, a7, s5
	addi t3, t3, -16
	addi s0, zero, 0
	sd s0, 0(t3)
	addi t3, a7, 0
	addi t5, t0, 0
	addi s0, zero, 0
2966:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2966b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
2967:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 2967b
	sub a7, a7, s5
	sub a7, a7, s5
	sub a7, a7, s5
	sub a7, a7, s5
	sub a7, a7, s5
	ld a4, 0(s6)
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2968:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2968b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi a1, s4, 0
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t4, a7, 0
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	addi t5, t0, 0
	addi t2, zero, 0
2969:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2969b
	addi s0, zero, 0
	sltu s1, s0, t2
	addi a2, s1, -1
	or a1, a1, a2
	xor a1, a1, a2
	and a4, a4, a1
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2970:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2970b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi a1, s4, 0
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t4, a7, 0
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	addi t5, t0, 0
	addi t2, zero, 0
2971:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2971b
	addi s0, zero, 0
	sltu s1, s0, t2
	addi a2, s1, -1
	or a1, a1, a2
	xor a1, a1, a2
	and a4, a4, a1
	addi a1, zero, -1
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t4, a7, 0
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	addi t5, t0, 0
	addi t2, zero, 0
2972:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2972b
	addi s0, zero, 0
	sltu s1, s0, t2
	addi a2, s1, -1
	or a1, a1, a2
	xor a1, a1, a2
	and a4, a4, a1
	sd a4, 0(s6)
	ld s3, 0(a7)
	addi s0, s3, 0
	mul s1, s3, s0
	addi s2, zero, 2
	sub s1, s2, s1
	mul s0, s0, s1
	mul s1, s3, s0
	addi s2, zero, 2
	sub s1, s2, s1
	mul s0, s0, s1
	mul s1, s3, s0
	addi s2, zero, 2
	sub s1, s2, s1
	mul s0, s0, s1
	mul s1, s3, s0
	addi s2, zero, 2
	sub s1, s2, s1
	mul s0, s0, s1
	mul s1, s3, s0
	addi s2, zero, 2
	sub s1, s2, s1
	mul s0, s0, s1
	addi s1, zero, 0
	sub t1, s1, s0
	addi a2, a7, 0
	add a2, a2, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a2, 0
	addi t5, t0, 0
	addi s0, zero, 0
2973:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2973b
	addi s0, zero, 1
	sd s0, 0(a2)
	slli a1, t0, 7
2974:
	addi t3, a5, 0
	addi t4, a2, 0
	addi t5, t0, 0
	addi s4, zero, 0
2975:
	ld s2, 0(t4)
	slli s3, s2, 1
	add s3, s3, s4
	srli s4, s2, 63
	sd s3, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2975b
	sd s4, 0(t3)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2976:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2976b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2977:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2977b
	addi a1, a1, -1
	bnez a1, 2974b
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t4, a7, 0
	add t4, t4, s5
	addi t5, t0, 2
2978:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2978b
	addi t3, a7, 0
	addi t4, a7, 0
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	addi t5, t0, 0
	addi s4, zero, 2
2979:
	ld s2, 0(t3)
	sltu s0, s2, s4
	sub s2, s2, s4
	addi s4, s0, 0
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2979b
	ld s7, 16(s6)
	slli s7, s7, 48
	srli s7, s7, 48
	addi t2, zero, 28
	mul s7, s7, t2
	addi s7, s7, 704
	add s7, s7, s6
	addi s7, s7, 1600
	ld s8, 16(s6)
	slli s8, s8, 32
	srli s8, s8, 48
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s8
	addi t3, t3, -1
	addi t4, s7, 0
	addi t5, s8, 0
2980:
	lbu s0, 0(t3)
	sb s0, 0(t4)
	addi t4, t4, 1
	addi t3, t3, -1
	addi t5, t5, -1
	bnez t5, 2980b
	addi s7, ra, 0
	ld s8, 16(s6)
	slli s8, s8, 32
	srli s8, s8, 48
	add a7, a7, s5
	add a7, a7, s5
	add a7, a7, s5
	add a7, a7, s5
	add t3, a7, s5
	addi t3, t3, -16
	addi s0, zero, 0
	sd s0, 0(t3)
	addi t3, a7, 0
	addi t5, t0, 0
	addi s0, zero, 0
2981:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2981b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
2982:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 2982b
	sub a7, a7, s5
	sub a7, a7, s5
	sub a7, a7, s5
	sub a7, a7, s5
	addi t3, a7, 0
	add t3, t3, s5
	addi t4, a7, 0
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	addi t5, t0, 2
2983:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2983b
	ld s7, 16(s6)
	slli s7, s7, 48
	srli s7, s7, 48
	addi t2, zero, 28
	mul s7, s7, t2
	addi s7, s7, 704
	add s7, s7, s6
	addi s7, s7, 1600
	ld s8, 16(s6)
	slli s8, s8, 32
	srli s8, s8, 48
	addi s9, s7, 0
	addi s10, s8, 0
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t5, t0, 0
	addi s0, zero, 0
2984:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2984b
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi s0, zero, 1
	sd s0, 0(t3)
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	addi a4, a7, 0
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
2985:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2985b
2986:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a7)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi a0, a7, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 2987f
2989:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2989b
	j 2988f
2987:
2988:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2990f
2992:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 16(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 16(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 24(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 24(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 32(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 32(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2992b
	j 2991f
2990:
2991:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	addi a1, a1, -1
	bnez a1, 2986b
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2993:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2993b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2994:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2994b
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a4, a7, 0
	add a4, a4, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
2995:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2995b
2996:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a7)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi a0, a7, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 2997f
2999:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2999b
	j 2998f
2997:
2998:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 21000f
21002:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 16(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 16(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 24(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 24(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 32(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 32(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 21002b
	j 21001f
21000:
21001:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	addi a1, a1, -1
	bnez a1, 2996b
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
21003:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21003b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
21004:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21004b
	addi s4, zero, -1
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
21005:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21005b
	addi s7, zero, 2
21006:
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a4, a7, 0
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
21007:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 21007b
21008:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a7)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi a0, a7, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 21009f
21011:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21011b
	j 21010f
21009:
21010:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 21012f
21014:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 16(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 16(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 24(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 24(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 32(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 32(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 21014b
	j 21013f
21012:
21013:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	addi a1, a1, -1
	bnez a1, 21008b
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
21015:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21015b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
21016:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21016b
	addi s4, zero, -1
	addi t2, s7, 8
	mul t2, t2, s5
	add a2, t2, a7
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
21017:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21017b
	addi s7, s7, 1
	addi t2, s7, -16
	bnez t2, 21006b
	addi s4, zero, -1
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
21018:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21018b
21019:
	lbu s7, 0(s9)
	slli s7, s7, 56
	addi s9, s9, 1
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a5, 0
	add t5, t0, t0
	addi t5, t5, 2
	addi s0, zero, 0
21020:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 21020b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
21021:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 21022f
21024:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 21024b
	j 21023f
21022:
21023:
	beqz t6, 21025f
21027:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 21027b
	j 21026f
21025:
21026:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 21021b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
21028:
	ld s2, 0(t3)
	ld s3, 8(t3)
	srli s4, s2, 63
	slli s2, s2, 1
	add s2, s2, t2
	srli t2, s3, 63
	slli s3, s3, 1
	add s3, s3, s4
	ld s4, 0(a0)
	add s1, s1, s2
	sltu s2, s1, s2
	mul s0, s4, s4
	mulhu s4, s4, s4
	add s4, s4, s2
	add s0, s0, s1
	sltu s2, s0, s1
	add s4, s4, s2
	add s3, s3, s4
	sltu s1, s3, s4
	sd s0, 0(t3)
	sd s3, 8(t3)
	addi t3, t3, 16
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21028b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
21029:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi a0, a7, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 21030f
21032:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 21032b
	j 21031f
21030:
21031:
	beqz t6, 21033f
21035:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 21035b
	j 21034f
21033:
21034:
	ld s2, 0(t4)
	add s1, s1, s2
	sltu s3, s1, s2
	add s1, s1, a1
	sltu s2, s1, a1
	add a1, s3, s2
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, -1
	bnez t2, 21029b
	slli t3, t0, 3
	add a5, a5, t3
	add t4, a5, t3
	sd a1, 0(t4)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
21036:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21036b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
21037:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21037b
	slli t3, t0, 3
	sub a5, a5, t3
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a5, 0
	add t5, t0, t0
	addi t5, t5, 2
	addi s0, zero, 0
21038:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 21038b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
21039:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 21040f
21042:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 21042b
	j 21041f
21040:
21041:
	beqz t6, 21043f
21045:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 21045b
	j 21044f
21043:
21044:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 21039b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
21046:
	ld s2, 0(t3)
	ld s3, 8(t3)
	srli s4, s2, 63
	slli s2, s2, 1
	add s2, s2, t2
	srli t2, s3, 63
	slli s3, s3, 1
	add s3, s3, s4
	ld s4, 0(a0)
	add s1, s1, s2
	sltu s2, s1, s2
	mul s0, s4, s4
	mulhu s4, s4, s4
	add s4, s4, s2
	add s0, s0, s1
	sltu s2, s0, s1
	add s4, s4, s2
	add s3, s3, s4
	sltu s1, s3, s4
	sd s0, 0(t3)
	sd s3, 8(t3)
	addi t3, t3, 16
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21046b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
21047:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi a0, a7, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 21048f
21050:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 21050b
	j 21049f
21048:
21049:
	beqz t6, 21051f
21053:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 21053b
	j 21052f
21051:
21052:
	ld s2, 0(t4)
	add s1, s1, s2
	sltu s3, s1, s2
	add s1, s1, a1
	sltu s2, s1, a1
	add a1, s3, s2
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, -1
	bnez t2, 21047b
	slli t3, t0, 3
	add a5, a5, t3
	add t4, a5, t3
	sd a1, 0(t4)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
21054:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21054b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
21055:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21055b
	slli t3, t0, 3
	sub a5, a5, t3
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a5, 0
	add t5, t0, t0
	addi t5, t5, 2
	addi s0, zero, 0
21056:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 21056b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
21057:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 21058f
21060:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 21060b
	j 21059f
21058:
21059:
	beqz t6, 21061f
21063:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 21063b
	j 21062f
21061:
21062:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 21057b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
21064:
	ld s2, 0(t3)
	ld s3, 8(t3)
	srli s4, s2, 63
	slli s2, s2, 1
	add s2, s2, t2
	srli t2, s3, 63
	slli s3, s3, 1
	add s3, s3, s4
	ld s4, 0(a0)
	add s1, s1, s2
	sltu s2, s1, s2
	mul s0, s4, s4
	mulhu s4, s4, s4
	add s4, s4, s2
	add s0, s0, s1
	sltu s2, s0, s1
	add s4, s4, s2
	add s3, s3, s4
	sltu s1, s3, s4
	sd s0, 0(t3)
	sd s3, 8(t3)
	addi t3, t3, 16
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21064b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
21065:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi a0, a7, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 21066f
21068:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 21068b
	j 21067f
21066:
21067:
	beqz t6, 21069f
21071:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 21071b
	j 21070f
21069:
21070:
	ld s2, 0(t4)
	add s1, s1, s2
	sltu s3, s1, s2
	add s1, s1, a1
	sltu s2, s1, a1
	add a1, s3, s2
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, -1
	bnez t2, 21065b
	slli t3, t0, 3
	add a5, a5, t3
	add t4, a5, t3
	sd a1, 0(t4)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
21072:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21072b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
21073:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21073b
	slli t3, t0, 3
	sub a5, a5, t3
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a5, 0
	add t5, t0, t0
	addi t5, t5, 2
	addi s0, zero, 0
21074:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 21074b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
21075:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 21076f
21078:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 21078b
	j 21077f
21076:
21077:
	beqz t6, 21079f
21081:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 21081b
	j 21080f
21079:
21080:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 21075b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
21082:
	ld s2, 0(t3)
	ld s3, 8(t3)
	srli s4, s2, 63
	slli s2, s2, 1
	add s2, s2, t2
	srli t2, s3, 63
	slli s3, s3, 1
	add s3, s3, s4
	ld s4, 0(a0)
	add s1, s1, s2
	sltu s2, s1, s2
	mul s0, s4, s4
	mulhu s4, s4, s4
	add s4, s4, s2
	add s0, s0, s1
	sltu s2, s0, s1
	add s4, s4, s2
	add s3, s3, s4
	sltu s1, s3, s4
	sd s0, 0(t3)
	sd s3, 8(t3)
	addi t3, t3, 16
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21082b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
21083:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi a0, a7, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 21084f
21086:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 21086b
	j 21085f
21084:
21085:
	beqz t6, 21087f
21089:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 21089b
	j 21088f
21087:
21088:
	ld s2, 0(t4)
	add s1, s1, s2
	sltu s3, s1, s2
	add s1, s1, a1
	sltu s2, s1, a1
	add a1, s3, s2
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, -1
	bnez t2, 21083b
	slli t3, t0, 3
	add a5, a5, t3
	add t4, a5, t3
	sd a1, 0(t4)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
21090:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21090b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
21091:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21091b
	slli t3, t0, 3
	sub a5, a5, t3
	srli a1, s7, 60
	addi s8, zero, 0
21092:
	xor t2, s8, a1
	addi t2, t2, -1
	srli t2, t2, 63
	addi t3, zero, 0
	sub s4, t3, t2
	addi t2, s8, 8
	mul t2, t2, s5
	add a5, t2, a7
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
21093:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21093b
	addi s8, s8, 1
	xor t2, s8, a1
	addi t2, t2, -1
	srli t2, t2, 63
	addi t3, zero, 0
	sub s4, t3, t2
	addi t2, s8, 8
	mul t2, t2, s5
	add a5, t2, a7
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
21094:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21094b
	addi s8, s8, 1
	addi t2, s8, -16
	bnez t2, 21092b
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a4, a7, 0
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
21095:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 21095b
21096:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a7)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi a0, a7, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 21097f
21099:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21099b
	j 21098f
21097:
21098:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 21100f
21102:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 16(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 16(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 24(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 24(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 32(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 32(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 21102b
	j 21101f
21100:
21101:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	addi a1, a1, -1
	bnez a1, 21096b
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
21103:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21103b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
21104:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21104b
	slli s7, s7, 4
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a5, 0
	add t5, t0, t0
	addi t5, t5, 2
	addi s0, zero, 0
21105:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 21105b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
21106:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 21107f
21109:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 21109b
	j 21108f
21107:
21108:
	beqz t6, 21110f
21112:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 21112b
	j 21111f
21110:
21111:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 21106b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
21113:
	ld s2, 0(t3)
	ld s3, 8(t3)
	srli s4, s2, 63
	slli s2, s2, 1
	add s2, s2, t2
	srli t2, s3, 63
	slli s3, s3, 1
	add s3, s3, s4
	ld s4, 0(a0)
	add s1, s1, s2
	sltu s2, s1, s2
	mul s0, s4, s4
	mulhu s4, s4, s4
	add s4, s4, s2
	add s0, s0, s1
	sltu s2, s0, s1
	add s4, s4, s2
	add s3, s3, s4
	sltu s1, s3, s4
	sd s0, 0(t3)
	sd s3, 8(t3)
	addi t3, t3, 16
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21113b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
21114:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi a0, a7, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 21115f
21117:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 21117b
	j 21116f
21115:
21116:
	beqz t6, 21118f
21120:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 21120b
	j 21119f
21118:
21119:
	ld s2, 0(t4)
	add s1, s1, s2
	sltu s3, s1, s2
	add s1, s1, a1
	sltu s2, s1, a1
	add a1, s3, s2
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, -1
	bnez t2, 21114b
	slli t3, t0, 3
	add a5, a5, t3
	add t4, a5, t3
	sd a1, 0(t4)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
21121:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21121b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
21122:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21122b
	slli t3, t0, 3
	sub a5, a5, t3
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a5, 0
	add t5, t0, t0
	addi t5, t5, 2
	addi s0, zero, 0
21123:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 21123b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
21124:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 21125f
21127:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 21127b
	j 21126f
21125:
21126:
	beqz t6, 21128f
21130:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 21130b
	j 21129f
21128:
21129:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 21124b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
21131:
	ld s2, 0(t3)
	ld s3, 8(t3)
	srli s4, s2, 63
	slli s2, s2, 1
	add s2, s2, t2
	srli t2, s3, 63
	slli s3, s3, 1
	add s3, s3, s4
	ld s4, 0(a0)
	add s1, s1, s2
	sltu s2, s1, s2
	mul s0, s4, s4
	mulhu s4, s4, s4
	add s4, s4, s2
	add s0, s0, s1
	sltu s2, s0, s1
	add s4, s4, s2
	add s3, s3, s4
	sltu s1, s3, s4
	sd s0, 0(t3)
	sd s3, 8(t3)
	addi t3, t3, 16
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21131b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
21132:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi a0, a7, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 21133f
21135:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 21135b
	j 21134f
21133:
21134:
	beqz t6, 21136f
21138:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 21138b
	j 21137f
21136:
21137:
	ld s2, 0(t4)
	add s1, s1, s2
	sltu s3, s1, s2
	add s1, s1, a1
	sltu s2, s1, a1
	add a1, s3, s2
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, -1
	bnez t2, 21132b
	slli t3, t0, 3
	add a5, a5, t3
	add t4, a5, t3
	sd a1, 0(t4)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
21139:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21139b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
21140:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21140b
	slli t3, t0, 3
	sub a5, a5, t3
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a5, 0
	add t5, t0, t0
	addi t5, t5, 2
	addi s0, zero, 0
21141:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 21141b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
21142:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 21143f
21145:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 21145b
	j 21144f
21143:
21144:
	beqz t6, 21146f
21148:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 21148b
	j 21147f
21146:
21147:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 21142b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
21149:
	ld s2, 0(t3)
	ld s3, 8(t3)
	srli s4, s2, 63
	slli s2, s2, 1
	add s2, s2, t2
	srli t2, s3, 63
	slli s3, s3, 1
	add s3, s3, s4
	ld s4, 0(a0)
	add s1, s1, s2
	sltu s2, s1, s2
	mul s0, s4, s4
	mulhu s4, s4, s4
	add s4, s4, s2
	add s0, s0, s1
	sltu s2, s0, s1
	add s4, s4, s2
	add s3, s3, s4
	sltu s1, s3, s4
	sd s0, 0(t3)
	sd s3, 8(t3)
	addi t3, t3, 16
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21149b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
21150:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi a0, a7, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 21151f
21153:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 21153b
	j 21152f
21151:
21152:
	beqz t6, 21154f
21156:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 21156b
	j 21155f
21154:
21155:
	ld s2, 0(t4)
	add s1, s1, s2
	sltu s3, s1, s2
	add s1, s1, a1
	sltu s2, s1, a1
	add a1, s3, s2
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, -1
	bnez t2, 21150b
	slli t3, t0, 3
	add a5, a5, t3
	add t4, a5, t3
	sd a1, 0(t4)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
21157:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21157b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
21158:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21158b
	slli t3, t0, 3
	sub a5, a5, t3
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a5, 0
	add t5, t0, t0
	addi t5, t5, 2
	addi s0, zero, 0
21159:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 21159b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
21160:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 21161f
21163:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 21163b
	j 21162f
21161:
21162:
	beqz t6, 21164f
21166:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 21166b
	j 21165f
21164:
21165:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 21160b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
21167:
	ld s2, 0(t3)
	ld s3, 8(t3)
	srli s4, s2, 63
	slli s2, s2, 1
	add s2, s2, t2
	srli t2, s3, 63
	slli s3, s3, 1
	add s3, s3, s4
	ld s4, 0(a0)
	add s1, s1, s2
	sltu s2, s1, s2
	mul s0, s4, s4
	mulhu s4, s4, s4
	add s4, s4, s2
	add s0, s0, s1
	sltu s2, s0, s1
	add s4, s4, s2
	add s3, s3, s4
	sltu s1, s3, s4
	sd s0, 0(t3)
	sd s3, 8(t3)
	addi t3, t3, 16
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21167b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
21168:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi a0, a7, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 3
	srli t5, t5, 2
	beqz t5, 21169f
21171:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	ld s4, 8(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 8(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 16(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 24(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 21171b
	j 21170f
21169:
21170:
	beqz t6, 21172f
21174:
	ld s4, 0(t4)
	add s1, s1, s4
	sltu s4, s1, s4
	ld s2, 0(a0)
	mul s3, s0, s2
	mulhu s2, s0, s2
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 21174b
	j 21173f
21172:
21173:
	ld s2, 0(t4)
	add s1, s1, s2
	sltu s3, s1, s2
	add s1, s1, a1
	sltu s2, s1, a1
	add a1, s3, s2
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, -1
	bnez t2, 21168b
	slli t3, t0, 3
	add a5, a5, t3
	add t4, a5, t3
	sd a1, 0(t4)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
21175:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21175b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
21176:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21176b
	slli t3, t0, 3
	sub a5, a5, t3
	srli a1, s7, 60
	addi s8, zero, 0
21177:
	xor t2, s8, a1
	addi t2, t2, -1
	srli t2, t2, 63
	addi t3, zero, 0
	sub s4, t3, t2
	addi t2, s8, 8
	mul t2, t2, s5
	add a5, t2, a7
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
21178:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21178b
	addi s8, s8, 1
	xor t2, s8, a1
	addi t2, t2, -1
	srli t2, t2, 63
	addi t3, zero, 0
	sub s4, t3, t2
	addi t2, s8, 8
	mul t2, t2, s5
	add a5, t2, a7
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
21179:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21179b
	addi s8, s8, 1
	addi t2, s8, -16
	bnez t2, 21177b
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a4, a7, 0
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
21180:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 21180b
21181:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a7)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi a0, a7, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 21182f
21184:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21184b
	j 21183f
21182:
21183:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 21185f
21187:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 16(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 16(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 24(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 24(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 32(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 32(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 21187b
	j 21186f
21185:
21186:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	addi a1, a1, -1
	bnez a1, 21181b
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
21188:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21188b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
21189:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21189b
	slli s7, s7, 4
	addi s10, s10, -1
	bnez s10, 21019b
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a4, a7, 0
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
21190:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 21190b
21191:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a7)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi a0, a7, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 21192f
21194:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21194b
	j 21193f
21192:
21193:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 21195f
21197:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 16(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 16(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 24(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 24(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 32(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 32(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 21197b
	j 21196f
21195:
21196:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	addi a1, a1, -1
	bnez a1, 21191b
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
21198:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21198b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
21199:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21199b
	ld s8, 16(s6)
	slli s8, s8, 16
	srli s8, s8, 48
	ld t3, 16(s6)
	srli t3, t3, 48
	sub a0, s8, t3
	srli a0, a0, 63
	beqz a0, 21200f
	j 21201f
21200:
	addi s8, t3, 0
21201:
	ld s7, 8(s6)
	beqz s8, 21202f
	add a7, a7, s5
	add a7, a7, s5
	add a7, a7, s5
	add a7, a7, s5
	add a7, a7, s5
	add a7, a7, s5
	add t3, a7, s5
	addi t3, t3, -16
	addi s0, zero, 0
	sd s0, 0(t3)
	addi t3, a7, 0
	addi t5, t0, 0
	addi s0, zero, 0
21204:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 21204b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
21205:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 21205b
	sub a7, a7, s5
	sub a7, a7, s5
	sub a7, a7, s5
	sub a7, a7, s5
	sub a7, a7, s5
	sub a7, a7, s5
	j 21203f
21202:
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t5, t0, 0
	addi s0, zero, 0
21206:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 21206b
21203:
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t5, t0, 0
	addi s0, zero, 0
21207:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 21207b
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a4, a7, 0
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi t3, a5, 0
	addi t4, a3, 0
	addi t2, a4, 0
	addi t5, t0, 0
	addi s4, zero, 0
21208:
	ld s2, 0(t4)
	ld s3, 0(t2)
	add s2, s2, s3
	sltu s0, s2, s3
	add s2, s2, s4
	sltu s1, s2, s4
	or s4, s0, s1
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t2, t2, 8
	addi t5, t5, -1
	bnez t5, 21208b
	sd s4, 0(t3)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
21209:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21209b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
21210:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21210b
	ld s8, 16(s6)
	slli s8, s8, 48
	srli s8, s8, 48
	ld t3, 16(s6)
	slli t3, t3, 32
	srli t3, t3, 48
	add s7, s11, s8
	add s7, s7, t3
	add s7, s7, s8
	add s7, s7, s8
	ld s8, 16(s6)
	slli s8, s8, 32
	srli s8, s8, 48
	addi s9, s7, 0
	addi s10, s8, 0
	addi t3, a7, 0
	add t3, t3, s5
	addi t5, t0, 0
	addi s0, zero, 0
21211:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 21211b
	addi a2, a7, 0
	add a2, a2, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
21212:
	lbu s7, 0(s9)
	slli s7, s7, 56
	addi s9, s9, 1
	addi s8, zero, 8
21213:
	srli s4, s7, 63
	slli s7, s7, 1
	addi t3, a5, 0
	addi t4, a2, 0
	addi t5, t0, 0
21214:
	ld s2, 0(t4)
	slli s3, s2, 1
	add s3, s3, s4
	srli s4, s2, 63
	sd s3, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 21214b
	sd s4, 0(t3)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
21215:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21215b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
21216:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21216b
	addi s8, s8, -1
	bnez s8, 21213b
	addi s10, s10, -1
	bnez s10, 21212b
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t4, a7, 0
	add t4, t4, s5
	addi t5, t0, 2
21217:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 21217b
	addi t3, a7, 0
	add t3, t3, s5
	addi t4, a7, 0
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	addi t5, t0, 2
21218:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 21218b
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a4, a7, 0
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
21219:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 21219b
21220:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a7)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi a0, a7, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 21221f
21223:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21223b
	j 21222f
21221:
21222:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 21224f
21226:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 16(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 16(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 24(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 24(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 32(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 32(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 21226b
	j 21225f
21224:
21225:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	addi a1, a1, -1
	bnez a1, 21220b
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
21227:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21227b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
21228:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21228b
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a4, a7, 0
	add a4, a4, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
21229:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 21229b
21230:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a7)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi a0, a7, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 21231f
21233:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21233b
	j 21232f
21231:
21232:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 21234f
21236:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 16(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 16(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 24(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 24(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 32(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 32(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 21236b
	j 21235f
21234:
21235:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	addi a1, a1, -1
	bnez a1, 21230b
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
21237:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21237b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
21238:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21238b
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a4, a7, 0
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi t3, a5, 0
	addi t4, a3, 0
	addi t2, a4, 0
	addi t5, t0, 0
	addi s4, zero, 0
21239:
	ld s2, 0(t4)
	ld s3, 0(t2)
	add s2, s2, s3
	sltu s0, s2, s3
	add s2, s2, s4
	sltu s1, s2, s4
	or s4, s0, s1
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t2, t2, 8
	addi t5, t5, -1
	bnez t5, 21239b
	sd s4, 0(t3)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
21240:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21240b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
21241:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21241b
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a4, a7, 0
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
21242:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 21242b
21243:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a7)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi a0, a7, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 21244f
21246:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21246b
	j 21245f
21244:
21245:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 21247f
21249:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 16(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 16(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 24(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 24(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 32(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 32(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 21249b
	j 21248f
21247:
21248:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	addi a1, a1, -1
	bnez a1, 21243b
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
21250:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21250b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
21251:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21251b
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a4, a7, 0
	add a4, a4, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
21252:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 21252b
21253:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a7)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi a0, a7, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 21254f
21256:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21256b
	j 21255f
21254:
21255:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 21257f
21259:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 8(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 8(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 16(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 16(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 24(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 24(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	ld s3, 32(t4)
	mul s2, t6, s3
	mulhu s3, t6, s3
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	ld s3, 32(a0)
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, s3
	mulhu s3, t2, s3
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 21259b
	j 21258f
21257:
21258:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	addi a1, a1, -1
	bnez a1, 21253b
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
21260:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21260b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
21261:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21261b
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t5, t0, 0
	addi s0, zero, 0
21262:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 21262b
	ld a4, 0(s6)
	addi a1, zero, -1
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t4, a7, 0
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	addi t5, t0, 0
	addi t2, zero, 0
21263:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 21263b
	addi s0, zero, 0
	sltu s1, s0, t2
	addi a2, s1, -1
	or a1, a1, a2
	xor a1, a1, a2
	and a4, a4, a1
	addi s4, a4, 0
	addi a2, a7, 0
	add a2, a2, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
21264:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21264b
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
21265:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 21265b
	ld s7, 24(s6)
	ld s8, 16(s6)
	slli s8, s8, 32
	srli s8, s8, 48
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s8
	addi t3, t3, -1
	addi t4, s7, 0
	addi t5, s8, 0
21266:
	lbu s0, 0(t3)
	sb s0, 0(t4)
	addi t4, t4, 1
	addi t3, t3, -1
	addi t5, t5, -1
	bnez t5, 21266b
	add s7, s7, s8
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s8
	addi t3, t3, -1
	addi t4, s7, 0
	addi t5, s8, 0
21267:
	lbu s0, 0(t3)
	sb s0, 0(t4)
	addi t4, t4, 1
	addi t3, t3, -1
	addi t5, t5, -1
	bnez t5, 21267b
	andi a0, a4, 1
2512:
2281:
242:
229:
226:
223:
210:
24:
	ld s0, 128(s6)
	ld s1, 136(s6)
	ld s2, 144(s6)
	ld s3, 152(s6)
	ld s4, 160(s6)
	ld s5, 168(s6)
	ld s7, 176(s6)
	ld s8, 184(s6)
	ld s9, 192(s6)
	ld s10, 200(s6)
	ld s11, 208(s6)
	ld ra, 216(s6)
	ld s6, 224(s6)
	ret
	.option pop
