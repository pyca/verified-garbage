// The functions of `src/dsa.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_dsa_derive_key:
	.option push
	.option arch, +m, +c
	addi t2, a7, 0
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
	sd a0, 24(s6)
	slli t3, a6, 16
	add t3, a4, t3
	sd t3, 16(s6)
	sd ra, 32(s6)
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
	slli t5, t5, 48
	srli t5, t5, 48
	ld t2, 16(s6)
	slli t2, t2, 32
	srli t2, t2, 48
	add t2, t2, t5
	add t5, t5, t2
	add t5, t5, t2
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
	slli t5, t5, 48
	srli t5, t5, 48
	ld t2, 16(s6)
	slli t2, t2, 32
	srli t2, t2, 48
	add t2, t2, t5
	add t5, t5, t2
	add t5, t5, t2
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
	slli t5, t5, 48
	srli t5, t5, 48
	ld t2, 16(s6)
	slli t2, t2, 32
	srli t2, t2, 48
	add t2, t2, t5
	add t5, t5, t2
	add t5, t5, t2
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
	slli t5, t5, 48
	srli t5, t5, 48
	ld t2, 16(s6)
	slli t2, t2, 32
	srli t2, t2, 48
	add t2, t2, t5
	add t5, t5, t2
	add t5, t5, t2
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
	slli t5, t5, 48
	srli t5, t5, 48
	ld t2, 16(s6)
	slli t2, t2, 32
	srli t2, t2, 48
	add t2, t2, t5
	add t5, t5, t2
	add t5, t5, t2
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
	slli t5, t5, 48
	srli t5, t5, 48
	ld t2, 16(s6)
	slli t2, t2, 32
	srli t2, t2, 48
	add t2, t2, t5
	add t5, t5, t2
	add t5, t5, t2
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
	call {vg_bignum_pow_win}
	ld ra, 32(s6)
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
263:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 263b
	addi s0, zero, 0
	sltu s1, s0, t2
	addi a0, s1, -1
	andi a0, a0, 1
	xori a0, a0, 1
260:
	beqz a0, 264f
	ld t4, 24(s6)
	ld t5, 16(s6)
	slli t5, t5, 48
	srli t5, t5, 48
	ld t2, 16(s6)
	slli t2, t2, 32
	srli t2, t2, 48
	add t2, t2, t5
	add t5, t5, t2
	add t5, t5, t2
	addi s0, zero, 0
266:
	sb s0, 0(t4)
	addi t4, t4, 1
	addi t5, t5, -1
	bnez t5, 266b
	addi a0, zero, 0
	j 265f
264:
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
267:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 267b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
268:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 268b
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
269:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 269b
	ld s10, 16(s6)
	slli s10, s10, 32
	srli s10, s10, 48
	call {vg_bignum_pow_win}
	ld ra, 32(s6)
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
270:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 270b
	addi a4, zero, -1
	addi a1, zero, -1
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
271:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 271b
	addi s0, zero, 0
	sltu s1, s0, t2
	addi a2, s1, -1
	or a1, a1, a2
	xor a1, a1, a2
	and a4, a4, a1
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
272:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 272b
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
	addi a1, zero, -1
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
273:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 273b
	addi s0, zero, 0
	sltu s1, s0, t2
	addi a2, s1, -1
	or a1, a1, a2
	xor a1, a1, a2
	and a4, a4, a1
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
274:
	lbu s0, 0(t3)
	sb s0, 0(t4)
	addi t4, t4, 1
	addi t3, t3, -1
	addi t5, t5, -1
	bnez t5, 274b
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
	addi s7, ra, 0
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
275:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 275b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
276:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 276b
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
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t5, t0, 0
	addi s0, zero, 0
277:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 277b
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
278:
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
	bnez t5, 278b
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
279:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 279b
	addi s0, zero, 0
	sltu s1, s0, t2
	addi a2, s1, -1
	or a1, a1, a2
	xor a1, a1, a2
	and a4, a4, a1
	ld t4, 24(s6)
	addi t3, s11, 0
	ld t5, 16(s6)
	slli t5, t5, 48
	srli t5, t5, 48
	ld t2, 16(s6)
	slli t2, t2, 32
	srli t2, t2, 48
	add t5, t5, t5
	add t5, t5, t2
280:
	lbu s0, 0(t3)
	and s0, s0, a4
	sb s0, 0(t4)
	addi t3, t3, 1
	addi t4, t4, 1
	addi t5, t5, -1
	bnez t5, 280b
	ld t3, 16(s6)
	slli t3, t3, 48
	srli t3, t3, 48
	addi t2, zero, 28
	mul t3, t3, t2
	addi t3, t3, 704
	add t3, t3, s6
	addi t3, t3, 1600
	ld t5, 16(s6)
	slli t5, t5, 48
	srli t5, t5, 48
281:
	lbu s0, 0(t3)
	and s0, s0, a4
	sb s0, 0(t4)
	addi t3, t3, 1
	addi t4, t4, 1
	addi t5, t5, -1
	bnez t5, 281b
	addi t3, ra, 0
	ld t5, 16(s6)
	slli t5, t5, 32
	srli t5, t5, 48
282:
	lbu s0, 0(t3)
	and s0, s0, a4
	sb s0, 0(t4)
	addi t3, t3, 1
	addi t4, t4, 1
	addi t5, t5, -1
	bnez t5, 282b
	andi a0, a4, 1
265:
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
	addi t0, zero, 0
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

vg_dsa_validate_private_key:
	.option push
	.option arch, +m, +c
	addi t2, a4, 0
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
	addi s11, a0, 0
	addi ra, zero, 0
	slli t3, a3, 16
	add t3, a2, t3
	sd t3, 16(s6)
	sd ra, 32(s6)
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
25:
	lbu s0, 0(t3)
	or t4, t4, s0
	addi a0, zero, 0
	sub a0, a0, t4
	srli a0, a0, 63
	add a1, a1, a0
	addi t3, t3, 1
	addi t5, t5, -1
	bnez t5, 25b
	beqz a1, 26f
	add t3, s7, s8
	sub t3, t3, a1
	lbu a0, 0(t3)
	srli a0, a0, 7
	addi t4, zero, 1
	xor a0, a0, t4
	j 27f
26:
	addi a0, zero, 1
27:
	beqz a0, 28f
	addi a0, zero, 0
	j 29f
28:
	addi a3, a1, 0
	slli t3, a1, 32
	ld t4, 16(s6)
	add t4, t4, t3
	sd t4, 16(s6)
	addi a0, zero, 1
	addi t3, a2, -128
	addi t4, a3, -20
	or t3, t3, t4
	beqz t3, 210f
	j 211f
210:
	addi a0, zero, 0
211:
	addi t3, a2, -256
	addi t4, a3, -20
	or t3, t3, t4
	beqz t3, 212f
	j 213f
212:
	addi a0, zero, 0
213:
	addi t3, a2, -256
	addi t4, a3, -28
	or t3, t3, t4
	beqz t3, 214f
	j 215f
214:
	addi a0, zero, 0
215:
	addi t3, a2, -256
	addi t4, a3, -32
	or t3, t3, t4
	beqz t3, 216f
	j 217f
216:
	addi a0, zero, 0
217:
	addi t3, a2, -384
	addi t4, a3, -32
	or t3, t3, t4
	beqz t3, 218f
	j 219f
218:
	addi a0, zero, 0
219:
	beqz a0, 220f
	addi a0, zero, 0
	j 221f
220:
	addi s7, s11, 0
	ld s8, 16(s6)
	slli s8, s8, 48
	srli s8, s8, 48
	add t3, s7, s8
	addi t3, t3, -1
	lbu a0, 0(t3)
	andi a0, a0, 1
	xori a0, a0, 1
	beqz a0, 222f
	addi a0, zero, 0
	j 223f
222:
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
	beqz a0, 224f
	addi a0, zero, 0
	j 225f
224:
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
226:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 226b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
227:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 227b
	addi s9, s11, 0
	ld s10, 16(s6)
	slli s10, s10, 48
	srli s10, s10, 48
	addi t3, a7, 0
	add t3, t3, s5
	addi t5, t0, 0
	addi s0, zero, 0
228:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 228b
	addi a2, a7, 0
	add a2, a2, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
229:
	lbu s7, 0(s9)
	slli s7, s7, 56
	addi s9, s9, 1
	addi s8, zero, 8
230:
	srli s4, s7, 63
	slli s7, s7, 1
	addi t3, a5, 0
	addi t4, a2, 0
	addi t5, t0, 0
231:
	ld s2, 0(t4)
	slli s3, s2, 1
	add s3, s3, s4
	srli s4, s2, 63
	sd s3, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 231b
	sd s4, 0(t3)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
232:
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
	bnez t5, 232b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
233:
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
	bnez t5, 233b
	addi s8, s8, -1
	bnez s8, 230b
	addi s10, s10, -1
	bnez s10, 229b
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
234:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 234b
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
235:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 235b
	addi s0, zero, 0
	sltu s1, s0, t2
	addi a0, s1, -1
	andi a0, a0, 1
	xori a0, a0, 1
	beqz a0, 236f
	addi a0, zero, 0
	j 237f
236:
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
238:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 238b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
239:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 239b
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
240:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 240b
	addi s0, zero, 1
	sd s0, 0(a2)
	slli a1, t0, 7
241:
	addi t3, a5, 0
	addi t4, a2, 0
	addi t5, t0, 0
	addi s4, zero, 0
242:
	ld s2, 0(t4)
	slli s3, s2, 1
	add s3, s3, s4
	srli s4, s2, 63
	sd s3, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 242b
	sd s4, 0(t3)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
243:
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
	bnez t5, 243b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
244:
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
	bnez t5, 244b
	addi a1, a1, -1
	bnez a1, 241b
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
245:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 245b
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
246:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 246b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
247:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 247b
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
248:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 248b
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
249:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 249b
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
250:
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
	bnez t5, 250b
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
251:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 251b
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
252:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 252b
	addi s0, zero, 0
	sltu s1, s0, t2
	addi a2, s1, -1
	or a1, a1, a2
	xor a1, a1, a2
	addi a0, a1, 0
	andi a0, a0, 1
	xori a0, a0, 1
	beqz a0, 253f
	j 254f
253:
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
255:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 255b
	ld t3, 16(s6)
	slli t3, t3, 48
	srli t3, t3, 48
	add s7, s11, t3
	ld s8, 16(s6)
	slli s8, s8, 32
	srli s8, s8, 48
	addi s9, s7, 0
	addi s10, s8, 0
	call {vg_bignum_pow_win}
	ld ra, 32(s6)
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
256:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 256b
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
	addi a0, s1, -1
	andi a0, a0, 1
	xori a0, a0, 1
254:
	beqz a0, 258f
	addi a0, zero, 0
	j 259f
258:
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
260:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 260b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
261:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 261b
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
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t5, t0, 0
	addi s0, zero, 0
263:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 263b
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
264:
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
	bnez t5, 264b
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
265:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 265b
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
266:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 266b
	addi s0, zero, 0
	sltu s1, s0, t2
	addi a2, s1, -1
	or a1, a1, a2
	xor a1, a1, a2
	addi a0, a1, 0
	andi a0, a0, 1
	xori a0, a0, 1
	beqz a0, 267f
	addi a0, zero, 0
	j 268f
267:
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
269:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 269b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
270:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 270b
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
271:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 271b
	ld s10, 16(s6)
	slli s10, s10, 32
	srli s10, s10, 48
	call {vg_bignum_pow_win}
	ld ra, 32(s6)
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
272:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 272b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
273:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 273b
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
274:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 274b
	addi s0, zero, 0
	sltu s1, s0, t2
	addi a0, s1, -1
	sd a0, 0(s6)
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
275:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 275b
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
276:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 276b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
277:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 277b
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
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
278:
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
	bnez t5, 278b
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
279:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 279b
	addi s0, zero, 0
	sltu s1, s0, t2
	addi a2, s1, -1
	or a1, a1, a2
	xor a1, a1, a2
	and a4, a4, a1
	andi a0, a4, 1
268:
259:
237:
225:
223:
221:
29:
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
	addi t0, zero, 0
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

vg_dsa_sign_random_prevalidated:
	.option push
	.option arch, +m, +c
	addi sp, sp, -192
	addi t0, sp, 0
	sd s0, 88(t0)
	sd s1, 96(t0)
	sd s2, 104(t0)
	sd s3, 112(t0)
	sd s4, 120(t0)
	sd s5, 128(t0)
	sd s6, 136(t0)
	sd s7, 144(t0)
	sd s8, 152(t0)
	sd s9, 160(t0)
	sd s10, 168(t0)
	sd s11, 176(t0)
	sd ra, 184(t0)
	sd a0, 64(t0)
	sd a2, 72(t0)
	sd a7, 80(t0)
	addi s1, a3, 0
	slli s2, a6, 16
	add s2, s2, a5
	addi t6, sp, 192
	ld s3, 8(t6)
	ld s4, 16(t6)
	ld t1, 0(t6)
	ld t2, 24(t6)
	ld t3, 32(t6)
	sd t1, 0(t0)
	sd t2, 8(t0)
	sd t3, 16(t0)
	addi s5, zero, 0
	addi s6, zero, 8
	addi t0, sp, 0
	addi t1, zero, 0
	sd t1, 32(t0)
	sd t1, 40(t0)
	sd t1, 48(t0)
	sd t1, 56(t0)
	slli t3, s2, 48
	srli t3, t3, 48
	add s7, s1, t3
	srli s8, s2, 16
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
	add t3, s7, s8
	sub s7, t3, a1
	addi s8, a1, 0
	lbu t4, 0(s7)
	srli t5, t4, 1
	or s9, t4, t5
	srli t5, s9, 2
	or s9, s9, t5
	srli t5, s9, 4
	or s9, s9, t5
	srli t5, a1, 1
	srli a2, t4, 1
	or t5, t5, a2
	addi a2, zero, 0
	sub t5, a2, t5
	srli t5, t5, 63
	sub a2, a2, a1
	srli a2, a2, 63
	and a0, t5, a2
	beqz a0, 21f
23:
	addi s11, zero, 128
	addi s10, zero, 4
24:
	sub a0, s4, s5
	sub a1, a0, s8
	srli a1, a1, 63
	srli a0, a0, 63
	xori a0, a0, 1
	and a0, a0, a1
	bnez a0, 25f
	add t3, s3, s5
	addi t4, sp, 32
	srli a2, s2, 16
	add t4, t4, a2
	sub t4, t4, s8
	addi t5, s8, 0
	addi t2, s9, 0
27:
	lbu a0, 0(t3)
	and a0, a0, t2
	sb a0, 0(t4)
	addi t2, zero, 255
	addi t3, t3, 1
	addi t4, t4, 1
	addi t5, t5, -1
	bnez t5, 27b
	add s5, s5, s8
	addi t3, sp, 32
	srli a2, s2, 16
	add t3, t3, a2
	add t4, s7, s8
	addi t5, s8, 0
	addi a3, zero, 0
	addi a4, zero, 0
28:
	addi t3, t3, -1
	addi t4, t4, -1
	lbu a0, 0(t3)
	or a4, a4, a0
	lbu a5, 0(t4)
	add a5, a5, a3
	sub a0, a0, a5
	srli a3, a0, 63
	addi t5, t5, -1
	bnez t5, 28b
	addi a0, zero, 0
	sub a0, a0, a4
	srli a0, a0, 63
	and a3, a3, a0
	bnez a3, 29f
	addi s11, s11, -1
	beqz s11, 211f
	j 212f
211:
	addi s10, zero, 0
212:
	j 210f
29:
	addi s10, zero, 1
210:
	j 26f
25:
	addi s10, zero, 2
26:
	addi a0, s10, -4
	beqz a0, 24b
	addi a0, s10, -1
	beqz a0, 213f
	j 214f
213:
	addi t3, sp, 0
	ld a0, 64(t3)
	srli a6, s2, 16
	add a1, a6, a6
	addi a2, s1, 0
	slli a4, s2, 48
	srli a4, a4, 48
	add a3, a4, a4
	add a3, a3, a4
	add a3, a3, a1
	addi a5, sp, 32
	ld a7, 80(t3)
	call {vg_dsa_sign_prevalidated}
	slli a0, a0, 32
	srli a0, a0, 32
	beqz a0, 215f
	addi s10, zero, 1
	j 216f
215:
	addi s6, s6, -1
	bnez s6, 217f
	addi s10, zero, 0
	j 218f
217:
	addi s10, zero, 4
218:
216:
214:
	addi a0, s10, -4
	beqz a0, 23b
	j 22f
21:
	addi s10, zero, 0
22:
	addi a0, s10, -1
	beqz a0, 219f
	addi t3, sp, 0
	ld t4, 64(t3)
	srli t5, s2, 16
	add t5, t5, t5
	addi a0, zero, 0
221:
	sb a0, 0(t4)
	addi t4, t4, 1
	addi t5, t5, -1
	bnez t5, 221b
	j 220f
219:
220:
	addi t0, sp, 0
	addi t1, zero, 0
	sd t1, 32(t0)
	sd t1, 40(t0)
	sd t1, 48(t0)
	sd t1, 56(t0)
	ld t4, 72(t0)
	sd s5, 0(t4)
	addi a0, s10, 0
	addi t0, sp, 0
	ld ra, 184(t0)
	ld s0, 88(t0)
	ld s1, 96(t0)
	ld s2, 104(t0)
	ld s3, 112(t0)
	ld s4, 120(t0)
	ld s5, 128(t0)
	ld s6, 136(t0)
	ld s7, 144(t0)
	ld s8, 152(t0)
	ld s9, 160(t0)
	ld s10, 168(t0)
	ld s11, 176(t0)
	addi sp, sp, 192
	addi t0, zero, 0
	addi sp, sp, -192
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
	addi sp, sp, 192
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

vg_dsa_generate_key:
	.option push
	.option arch, +m, +c
	addi sp, sp, -192
	addi t0, sp, 0
	sd s0, 88(t0)
	sd s1, 96(t0)
	sd s2, 104(t0)
	sd s3, 112(t0)
	sd s4, 120(t0)
	sd s5, 128(t0)
	sd s6, 136(t0)
	sd s7, 144(t0)
	sd s8, 152(t0)
	sd s9, 160(t0)
	sd s10, 168(t0)
	sd s11, 176(t0)
	sd ra, 184(t0)
	sd a0, 64(t0)
	sd a2, 72(t0)
	addi s1, a3, 0
	slli s2, a6, 16
	add s2, s2, a5
	addi s3, a7, 0
	addi t6, sp, 192
	ld s4, 0(t6)
	ld s6, 8(t6)
	ld t1, 16(t6)
	sd t1, 0(t0)
	addi s5, zero, 0
	addi t0, sp, 0
	addi t1, zero, 0
	sd t1, 32(t0)
	sd t1, 40(t0)
	sd t1, 48(t0)
	sd t1, 56(t0)
	addi a0, s1, 0
	slli a2, s2, 48
	srli a2, a2, 48
	srli a3, s2, 16
	add a1, a2, a2
	add a1, a1, a3
	addi a4, s6, 0
	addi t3, sp, 0
	ld a5, 0(t3)
	call {vg_dsa_check_parameters}
	slli a0, a0, 32
	srli a0, a0, 32
	beqz a0, 20f
	slli t3, s2, 48
	srli t3, t3, 48
	add s7, s1, t3
	srli s8, s2, 16
	addi t3, s7, 0
	addi t5, s8, 0
	addi t4, zero, 0
	addi a1, zero, 0
22:
	lbu s0, 0(t3)
	or t4, t4, s0
	addi a0, zero, 0
	sub a0, a0, t4
	srli a0, a0, 63
	add a1, a1, a0
	addi t3, t3, 1
	addi t5, t5, -1
	bnez t5, 22b
	add t3, s7, s8
	sub s7, t3, a1
	addi s8, a1, 0
	lbu t4, 0(s7)
	srli t5, t4, 1
	or s9, t4, t5
	srli t5, s9, 2
	or s9, s9, t5
	srli t5, s9, 4
	or s9, s9, t5
	srli t5, a1, 1
	srli a2, t4, 1
	or t5, t5, a2
	addi a2, zero, 0
	sub t5, a2, t5
	srli t5, t5, 63
	sub a2, a2, a1
	srli a2, a2, 63
	and a0, t5, a2
	beqz a0, 23f
	addi s11, zero, 128
	addi s10, zero, 4
25:
	sub a0, s4, s5
	sub a1, a0, s8
	srli a1, a1, 63
	srli a0, a0, 63
	xori a0, a0, 1
	and a0, a0, a1
	bnez a0, 26f
	add t3, s3, s5
	addi t4, sp, 32
	srli a2, s2, 16
	add t4, t4, a2
	sub t4, t4, s8
	addi t5, s8, 0
	addi t2, s9, 0
28:
	lbu a0, 0(t3)
	and a0, a0, t2
	sb a0, 0(t4)
	addi t2, zero, 255
	addi t3, t3, 1
	addi t4, t4, 1
	addi t5, t5, -1
	bnez t5, 28b
	add s5, s5, s8
	addi t3, sp, 32
	srli a2, s2, 16
	add t3, t3, a2
	add t4, s7, s8
	addi t5, s8, 0
	addi a3, zero, 0
	addi a4, zero, 0
29:
	addi t3, t3, -1
	addi t4, t4, -1
	lbu a0, 0(t3)
	or a4, a4, a0
	lbu a5, 0(t4)
	add a5, a5, a3
	sub a0, a0, a5
	srli a3, a0, 63
	addi t5, t5, -1
	bnez t5, 29b
	addi a0, zero, 0
	sub a0, a0, a4
	srli a0, a0, 63
	and a3, a3, a0
	bnez a3, 210f
	addi s11, s11, -1
	beqz s11, 212f
	j 213f
212:
	addi s10, zero, 0
213:
	j 211f
210:
	addi s10, zero, 1
211:
	j 27f
26:
	addi s10, zero, 2
27:
	addi a0, s10, -4
	beqz a0, 25b
	addi a0, s10, -1
	beqz a0, 214f
	j 215f
214:
	addi t3, sp, 0
	ld a0, 64(t3)
	slli a4, s2, 48
	srli a4, a4, 48
	srli a6, s2, 16
	add a3, a4, a4
	add a3, a3, a6
	add a1, a3, a4
	add a1, a1, a6
	addi a2, s1, 0
	addi a5, sp, 32
	addi a7, s6, 0
	call {vg_dsa_derive_key_checked}
	slli a0, a0, 32
	srli a0, a0, 32
	beqz a0, 216f
	addi s10, zero, 1
	j 217f
216:
	addi s10, zero, 0
217:
215:
	j 24f
23:
	addi s10, zero, 0
24:
	j 21f
20:
	addi s10, zero, 0
21:
	addi a0, s10, -1
	beqz a0, 218f
	addi t3, sp, 0
	ld t4, 64(t3)
	slli t5, s2, 48
	srli t5, t5, 48
	srli t2, s2, 16
	add t1, t5, t5
	add t5, t5, t1
	add t5, t5, t2
	add t5, t5, t2
	addi a0, zero, 0
220:
	sb a0, 0(t4)
	addi t4, t4, 1
	addi t5, t5, -1
	bnez t5, 220b
	j 219f
218:
219:
	addi t0, sp, 0
	addi t1, zero, 0
	sd t1, 32(t0)
	sd t1, 40(t0)
	sd t1, 48(t0)
	sd t1, 56(t0)
	ld t4, 72(t0)
	sd s5, 0(t4)
	addi a0, s10, 0
	addi t0, sp, 0
	ld ra, 184(t0)
	ld s0, 88(t0)
	ld s1, 96(t0)
	ld s2, 104(t0)
	ld s3, 112(t0)
	ld s4, 120(t0)
	ld s5, 128(t0)
	ld s6, 136(t0)
	ld s7, 144(t0)
	ld s8, 152(t0)
	ld s9, 160(t0)
	ld s10, 168(t0)
	ld s11, 176(t0)
	addi sp, sp, 192
	addi t0, zero, 0
	addi sp, sp, -192
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
	addi sp, sp, 192
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

vg_dsa_validate_public_key:
	.option push
	.option arch, +m, +c
	addi t2, a4, 0
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
	addi s11, a0, 0
	addi ra, zero, 0
	slli t3, a3, 16
	add t3, a2, t3
	sd t3, 16(s6)
	sd ra, 32(s6)
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
25:
	lbu s0, 0(t3)
	or t4, t4, s0
	addi a0, zero, 0
	sub a0, a0, t4
	srli a0, a0, 63
	add a1, a1, a0
	addi t3, t3, 1
	addi t5, t5, -1
	bnez t5, 25b
	beqz a1, 26f
	add t3, s7, s8
	sub t3, t3, a1
	lbu a0, 0(t3)
	srli a0, a0, 7
	addi t4, zero, 1
	xor a0, a0, t4
	j 27f
26:
	addi a0, zero, 1
27:
	beqz a0, 28f
	addi a0, zero, 0
	j 29f
28:
	addi a3, a1, 0
	slli t3, a1, 32
	ld t4, 16(s6)
	add t4, t4, t3
	sd t4, 16(s6)
	addi a0, zero, 1
	addi t3, a2, -128
	addi t4, a3, -20
	or t3, t3, t4
	beqz t3, 210f
	j 211f
210:
	addi a0, zero, 0
211:
	addi t3, a2, -256
	addi t4, a3, -20
	or t3, t3, t4
	beqz t3, 212f
	j 213f
212:
	addi a0, zero, 0
213:
	addi t3, a2, -256
	addi t4, a3, -28
	or t3, t3, t4
	beqz t3, 214f
	j 215f
214:
	addi a0, zero, 0
215:
	addi t3, a2, -256
	addi t4, a3, -32
	or t3, t3, t4
	beqz t3, 216f
	j 217f
216:
	addi a0, zero, 0
217:
	addi t3, a2, -384
	addi t4, a3, -32
	or t3, t3, t4
	beqz t3, 218f
	j 219f
218:
	addi a0, zero, 0
219:
	beqz a0, 220f
	addi a0, zero, 0
	j 221f
220:
	addi s7, s11, 0
	ld s8, 16(s6)
	slli s8, s8, 48
	srli s8, s8, 48
	add t3, s7, s8
	addi t3, t3, -1
	lbu a0, 0(t3)
	andi a0, a0, 1
	xori a0, a0, 1
	beqz a0, 222f
	addi a0, zero, 0
	j 223f
222:
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
	beqz a0, 224f
	addi a0, zero, 0
	j 225f
224:
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
226:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 226b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
227:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 227b
	addi s9, s11, 0
	ld s10, 16(s6)
	slli s10, s10, 48
	srli s10, s10, 48
	addi t3, a7, 0
	add t3, t3, s5
	addi t5, t0, 0
	addi s0, zero, 0
228:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 228b
	addi a2, a7, 0
	add a2, a2, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
229:
	lbu s7, 0(s9)
	slli s7, s7, 56
	addi s9, s9, 1
	addi s8, zero, 8
230:
	srli s4, s7, 63
	slli s7, s7, 1
	addi t3, a5, 0
	addi t4, a2, 0
	addi t5, t0, 0
231:
	ld s2, 0(t4)
	slli s3, s2, 1
	add s3, s3, s4
	srli s4, s2, 63
	sd s3, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 231b
	sd s4, 0(t3)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
232:
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
	bnez t5, 232b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
233:
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
	bnez t5, 233b
	addi s8, s8, -1
	bnez s8, 230b
	addi s10, s10, -1
	bnez s10, 229b
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
234:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 234b
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
235:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 235b
	addi s0, zero, 0
	sltu s1, s0, t2
	addi a0, s1, -1
	andi a0, a0, 1
	xori a0, a0, 1
	beqz a0, 236f
	addi a0, zero, 0
	j 237f
236:
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
238:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 238b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
239:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 239b
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
240:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 240b
	addi s0, zero, 1
	sd s0, 0(a2)
	slli a1, t0, 7
241:
	addi t3, a5, 0
	addi t4, a2, 0
	addi t5, t0, 0
	addi s4, zero, 0
242:
	ld s2, 0(t4)
	slli s3, s2, 1
	add s3, s3, s4
	srli s4, s2, 63
	sd s3, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 242b
	sd s4, 0(t3)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
243:
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
	bnez t5, 243b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
244:
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
	bnez t5, 244b
	addi a1, a1, -1
	bnez a1, 241b
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
245:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 245b
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
246:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 246b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
247:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 247b
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
248:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 248b
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
249:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 249b
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
250:
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
	bnez t5, 250b
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
251:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 251b
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
252:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 252b
	addi s0, zero, 0
	sltu s1, s0, t2
	addi a2, s1, -1
	or a1, a1, a2
	xor a1, a1, a2
	addi a0, a1, 0
	andi a0, a0, 1
	xori a0, a0, 1
	beqz a0, 253f
	j 254f
253:
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
255:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 255b
	ld t3, 16(s6)
	slli t3, t3, 48
	srli t3, t3, 48
	add s7, s11, t3
	ld s8, 16(s6)
	slli s8, s8, 32
	srli s8, s8, 48
	addi s9, s7, 0
	addi s10, s8, 0
	call {vg_bignum_pow_win}
	ld ra, 32(s6)
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
256:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 256b
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
	addi a0, s1, -1
	andi a0, a0, 1
	xori a0, a0, 1
254:
	beqz a0, 258f
	addi a0, zero, 0
	j 259f
258:
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
260:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 260b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
261:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 261b
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
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t5, t0, 0
	addi s0, zero, 0
263:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 263b
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
264:
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
	bnez t5, 264b
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
265:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 265b
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
266:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 266b
	addi s0, zero, 0
	sltu s1, s0, t2
	addi a2, s1, -1
	or a1, a1, a2
	xor a1, a1, a2
	addi a0, a1, 0
	andi a0, a0, 1
	xori a0, a0, 1
	beqz a0, 267f
	j 268f
267:
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
269:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 269b
	ld t3, 16(s6)
	slli t3, t3, 48
	srli t3, t3, 48
	add s7, s11, t3
	ld s8, 16(s6)
	slli s8, s8, 32
	srli s8, s8, 48
	addi s9, s7, 0
	addi s10, s8, 0
	call {vg_bignum_pow_win}
	ld ra, 32(s6)
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
270:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 270b
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
271:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 271b
	addi s0, zero, 0
	sltu s1, s0, t2
	addi a0, s1, -1
	andi a0, a0, 1
	xori a0, a0, 1
268:
	beqz a0, 272f
	addi a0, zero, 0
	j 273f
272:
	addi a0, zero, 1
273:
259:
237:
225:
223:
221:
29:
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
	addi t0, zero, 0
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

vg_dsa_verify_prevalidated:
	.option push
	.option arch, +m, +c
	addi t2, sp, 0
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
	addi s11, a0, 0
	addi ra, a4, 0
	sd a6, 8(s6)
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
	slli t3, a3, 16
	add t3, a2, t3
	add t3, t3, a1
	sd t3, 16(s6)
	sd a4, 32(s6)
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
25:
	lbu s0, 0(t3)
	or t4, t4, s0
	addi a0, zero, 0
	sub a0, a0, t4
	srli a0, a0, 63
	add a1, a1, a0
	addi t3, t3, 1
	addi t5, t5, -1
	bnez t5, 25b
	beqz a1, 26f
	add t3, s7, s8
	sub t3, t3, a1
	lbu a0, 0(t3)
	srli a0, a0, 7
	addi t4, zero, 1
	xor a0, a0, t4
	j 27f
26:
	addi a0, zero, 1
27:
	beqz a0, 28f
	addi a0, zero, 0
	j 29f
28:
	addi a3, a1, 0
	slli t3, a1, 32
	ld t4, 16(s6)
	add t4, t4, t3
	sd t4, 16(s6)
	addi a0, zero, 1
	addi t3, a2, -128
	addi t4, a3, -20
	or t3, t3, t4
	beqz t3, 210f
	j 211f
210:
	addi a0, zero, 0
211:
	addi t3, a2, -256
	addi t4, a3, -20
	or t3, t3, t4
	beqz t3, 212f
	j 213f
212:
	addi a0, zero, 0
213:
	addi t3, a2, -256
	addi t4, a3, -28
	or t3, t3, t4
	beqz t3, 214f
	j 215f
214:
	addi a0, zero, 0
215:
	addi t3, a2, -256
	addi t4, a3, -32
	or t3, t3, t4
	beqz t3, 216f
	j 217f
216:
	addi a0, zero, 0
217:
	addi t3, a2, -384
	addi t4, a3, -32
	or t3, t3, t4
	beqz t3, 218f
	j 219f
218:
	addi a0, zero, 0
219:
	beqz a0, 220f
	addi a0, zero, 0
	j 221f
220:
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
222:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 222b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
223:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 223b
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
224:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 224b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
225:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 225b
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
226:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 226b
	addi s0, zero, 1
	sd s0, 0(a2)
	slli a1, t0, 7
227:
	addi t3, a5, 0
	addi t4, a2, 0
	addi t5, t0, 0
	addi s4, zero, 0
228:
	ld s2, 0(t4)
	slli s3, s2, 1
	add s3, s3, s4
	srli s4, s2, 63
	sd s3, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 228b
	sd s4, 0(t3)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
229:
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
	bnez t5, 229b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
230:
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
	bnez t5, 230b
	addi a1, a1, -1
	bnez a1, 227b
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
231:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 231b
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
	addi s7, ra, 0
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
232:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 232b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
233:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 233b
	sub a7, a7, s5
	sub a7, a7, s5
	sub a7, a7, s5
	sub a7, a7, s5
	sub a7, a7, s5
	addi s7, ra, 0
	ld s8, 16(s6)
	slli s8, s8, 32
	srli s8, s8, 48
	add s7, s7, s8
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
234:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 234b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
235:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 235b
	sub a7, a7, s5
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
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t5, t0, 0
	addi s0, zero, 0
236:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 236b
	addi a4, zero, -1
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
238:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 238b
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
239:
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
	bnez t5, 239b
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
241:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 241b
	addi s0, zero, 1
	sd s0, 0(a2)
	slli a1, t0, 7
242:
	addi t3, a5, 0
	addi t4, a2, 0
	addi t5, t0, 0
	addi s4, zero, 0
243:
	ld s2, 0(t4)
	slli s3, s2, 1
	add s3, s3, s4
	srli s4, s2, 63
	sd s3, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 243b
	sd s4, 0(t3)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
244:
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
	bnez t5, 244b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
245:
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
	bnez t5, 245b
	addi a1, a1, -1
	bnez a1, 242b
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
246:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 246b
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
247:
	ld s2, 0(t3)
	sltu s0, s2, s4
	sub s2, s2, s4
	addi s4, s0, 0
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 247b
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
248:
	lbu s0, 0(t3)
	sb s0, 0(t4)
	addi t4, t4, 1
	addi t3, t3, -1
	addi t5, t5, -1
	bnez t5, 248b
	addi s7, ra, 0
	ld s8, 16(s6)
	slli s8, s8, 32
	srli s8, s8, 48
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
249:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 249b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
250:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 250b
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
251:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 251b
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
	call {vg_bignum_pow_win}
	ld ra, 32(s6)
	ld s8, 16(s6)
	slli s8, s8, 16
	srli s8, s8, 48
	ld t3, 16(s6)
	srli t3, t3, 48
	sub a0, s8, t3
	srli a0, a0, 63
	beqz a0, 252f
	j 253f
252:
	addi s8, t3, 0
253:
	ld s7, 8(s6)
	beqz s8, 254f
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
256:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 256b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
257:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 257b
	sub a7, a7, s5
	sub a7, a7, s5
	sub a7, a7, s5
	sub a7, a7, s5
	sub a7, a7, s5
	sub a7, a7, s5
	j 255f
254:
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t5, t0, 0
	addi s0, zero, 0
258:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 258b
255:
	addi s7, ra, 0
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
259:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 259b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
260:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 260b
	sub a7, a7, s5
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
261:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 261b
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
	addi a0, a7, 0
262:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 262b
263:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	ld a6, 8(a4)
	ld a7, 8(a0)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a0)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 264f
266:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 266b
	j 265f
264:
265:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 267f
269:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 24(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 24(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 32(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 32(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 40(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 40(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 269b
	j 268f
267:
268:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	slli s2, t0, 3
	sub a0, a0, s2
	addi a0, a0, 8
	addi a1, a1, -1
	bnez a1, 263b
	slli s2, t0, 3
	addi s2, s2, 16
	add a6, a5, s2
	slli s3, s2, 1
	sub a7, a5, s3
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
270:
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
	bnez t5, 270b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
271:
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
	bnez t5, 271b
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
	addi a0, a7, 0
272:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 272b
273:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	ld a6, 8(a4)
	ld a7, 8(a0)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a0)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 274f
276:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 276b
	j 275f
274:
275:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 277f
279:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 24(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 24(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 32(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 32(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 40(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 40(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 279b
	j 278f
277:
278:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	slli s2, t0, 3
	sub a0, a0, s2
	addi a0, a0, 8
	addi a1, a1, -1
	bnez a1, 273b
	slli s2, t0, 3
	addi s2, s2, 16
	add a6, a5, s2
	slli s3, s2, 1
	sub a7, a5, s3
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
280:
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
	bnez t5, 280b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
281:
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
	bnez t5, 281b
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
	addi a0, a7, 0
282:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 282b
283:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	ld a6, 8(a4)
	ld a7, 8(a0)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a0)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 284f
286:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 286b
	j 285f
284:
285:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 287f
289:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 24(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 24(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 32(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 32(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 40(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 40(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 289b
	j 288f
287:
288:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	slli s2, t0, 3
	sub a0, a0, s2
	addi a0, a0, 8
	addi a1, a1, -1
	bnez a1, 283b
	slli s2, t0, 3
	addi s2, s2, 16
	add a6, a5, s2
	slli s3, s2, 1
	sub a7, a5, s3
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
290:
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
	bnez t5, 290b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
291:
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
	bnez t5, 291b
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
	addi a0, a7, 0
292:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 292b
293:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	ld a6, 8(a4)
	ld a7, 8(a0)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a0)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 294f
296:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 296b
	j 295f
294:
295:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 297f
299:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 24(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 24(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 32(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 32(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 40(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 40(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 299b
	j 298f
297:
298:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	slli s2, t0, 3
	sub a0, a0, s2
	addi a0, a0, 8
	addi a1, a1, -1
	bnez a1, 293b
	slli s2, t0, 3
	addi s2, s2, 16
	add a6, a5, s2
	slli s3, s2, 1
	sub a7, a5, s3
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2100:
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
	bnez t5, 2100b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2101:
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
	bnez t5, 2101b
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
2102:
	lbu s0, 0(t3)
	sb s0, 0(t4)
	addi t4, t4, 1
	addi t3, t3, -1
	addi t5, t5, -1
	bnez t5, 2102b
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
	addi s7, s7, 32
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s8
	addi t3, t3, -1
	addi t4, s7, 0
	addi t5, s8, 0
2103:
	lbu s0, 0(t3)
	sb s0, 0(t4)
	addi t4, t4, 1
	addi t3, t3, -1
	addi t5, t5, -1
	bnez t5, 2103b
	addi a7, s6, 256
	ld t0, 16(s6)
	slli t0, t0, 48
	srli t0, t0, 48
	srli t0, t0, 3
	slli s5, t0, 3
	addi s5, s5, 16
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
2104:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2104b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
2105:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 2105b
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
2106:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2106b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
2107:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 2107b
	sub a7, a7, s5
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
2108:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2108b
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
2109:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2109b
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
	addi a0, a7, 0
2110:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2110b
2111:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	ld a6, 8(a4)
	ld a7, 8(a0)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a0)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 2112f
2114:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2114b
	j 2113f
2112:
2113:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2115f
2117:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 24(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 24(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 32(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 32(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 40(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 40(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2117b
	j 2116f
2115:
2116:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	slli s2, t0, 3
	sub a0, a0, s2
	addi a0, a0, 8
	addi a1, a1, -1
	bnez a1, 2111b
	slli s2, t0, 3
	addi s2, s2, 16
	add a6, a5, s2
	slli s3, s2, 1
	sub a7, a5, s3
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2118:
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
	bnez t5, 2118b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2119:
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
	bnez t5, 2119b
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
	addi a0, a7, 0
2120:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2120b
2121:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	ld a6, 8(a4)
	ld a7, 8(a0)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a0)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 2122f
2124:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2124b
	j 2123f
2122:
2123:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2125f
2127:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 24(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 24(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 32(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 32(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 40(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 40(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2127b
	j 2126f
2125:
2126:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	slli s2, t0, 3
	sub a0, a0, s2
	addi a0, a0, 8
	addi a1, a1, -1
	bnez a1, 2121b
	slli s2, t0, 3
	addi s2, s2, 16
	add a6, a5, s2
	slli s3, s2, 1
	sub a7, a5, s3
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2128:
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
	bnez t5, 2128b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2129:
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
	bnez t5, 2129b
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
	addi a0, a7, 0
2130:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2130b
2131:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	ld a6, 8(a4)
	ld a7, 8(a0)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a0)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 2132f
2134:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2134b
	j 2133f
2132:
2133:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2135f
2137:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 24(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 24(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 32(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 32(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 40(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 40(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2137b
	j 2136f
2135:
2136:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	slli s2, t0, 3
	sub a0, a0, s2
	addi a0, a0, 8
	addi a1, a1, -1
	bnez a1, 2131b
	slli s2, t0, 3
	addi s2, s2, 16
	add a6, a5, s2
	slli s3, s2, 1
	sub a7, a5, s3
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2138:
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
	bnez t5, 2138b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2139:
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
	bnez t5, 2139b
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
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
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
	addi a0, a7, 0
2140:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2140b
2141:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	ld a6, 8(a4)
	ld a7, 8(a0)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a0)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 2142f
2144:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2144b
	j 2143f
2142:
2143:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2145f
2147:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 24(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 24(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 32(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 32(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 40(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 40(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2147b
	j 2146f
2145:
2146:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	slli s2, t0, 3
	sub a0, a0, s2
	addi a0, a0, 8
	addi a1, a1, -1
	bnez a1, 2141b
	slli s2, t0, 3
	addi s2, s2, 16
	add a6, a5, s2
	slli s3, s2, 1
	sub a7, a5, s3
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2148:
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
	bnez t5, 2148b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2149:
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
	bnez t5, 2149b
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
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
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
	addi a0, a7, 0
2150:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2150b
2151:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	ld a6, 8(a4)
	ld a7, 8(a0)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a0)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 2152f
2154:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2154b
	j 2153f
2152:
2153:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2155f
2157:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 24(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 24(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 32(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 32(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 40(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 40(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2157b
	j 2156f
2155:
2156:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	slli s2, t0, 3
	sub a0, a0, s2
	addi a0, a0, 8
	addi a1, a1, -1
	bnez a1, 2151b
	slli s2, t0, 3
	addi s2, s2, 16
	add a6, a5, s2
	slli s3, s2, 1
	sub a7, a5, s3
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2158:
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
	bnez t5, 2158b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2159:
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
	bnez t5, 2159b
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
	addi a0, a7, 0
2160:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2160b
2161:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	ld a6, 8(a4)
	ld a7, 8(a0)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a0)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 2162f
2164:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2164b
	j 2163f
2162:
2163:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2165f
2167:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 24(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 24(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 32(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 32(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 40(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 40(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2167b
	j 2166f
2165:
2166:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	slli s2, t0, 3
	sub a0, a0, s2
	addi a0, a0, 8
	addi a1, a1, -1
	bnez a1, 2161b
	slli s2, t0, 3
	addi s2, s2, 16
	add a6, a5, s2
	slli s3, s2, 1
	sub a7, a5, s3
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
	addi a0, a7, 0
2170:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2170b
2171:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	ld a6, 8(a4)
	ld a7, 8(a0)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a0)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 2172f
2174:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2174b
	j 2173f
2172:
2173:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2175f
2177:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 24(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 24(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 32(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 32(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 40(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 40(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2177b
	j 2176f
2175:
2176:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	slli s2, t0, 3
	sub a0, a0, s2
	addi a0, a0, 8
	addi a1, a1, -1
	bnez a1, 2171b
	slli s2, t0, 3
	addi s2, s2, 16
	add a6, a5, s2
	slli s3, s2, 1
	sub a7, a5, s3
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2178:
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
	bnez t5, 2178b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2179:
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
	bnez t5, 2179b
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
	addi a0, a7, 0
2180:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2180b
2181:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	ld a6, 8(a4)
	ld a7, 8(a0)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a0)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 2182f
2184:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2184b
	j 2183f
2182:
2183:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2185f
2187:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 24(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 24(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 32(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 32(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 40(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 40(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2187b
	j 2186f
2185:
2186:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	slli s2, t0, 3
	sub a0, a0, s2
	addi a0, a0, 8
	addi a1, a1, -1
	bnez a1, 2181b
	slli s2, t0, 3
	addi s2, s2, 16
	add a6, a5, s2
	slli s3, s2, 1
	sub a7, a5, s3
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2188:
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
	bnez t5, 2188b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2189:
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
	bnez t5, 2189b
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
	add a3, a3, s5
	add a3, a3, s5
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
	addi a0, a7, 0
2190:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2190b
2191:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	ld a6, 8(a4)
	ld a7, 8(a0)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a0)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 2192f
2194:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2194b
	j 2193f
2192:
2193:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2195f
2197:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 24(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 24(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 32(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 32(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 40(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 40(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2197b
	j 2196f
2195:
2196:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	slli s2, t0, 3
	sub a0, a0, s2
	addi a0, a0, 8
	addi a1, a1, -1
	bnez a1, 2191b
	slli s2, t0, 3
	addi s2, s2, 16
	add a6, a5, s2
	slli s3, s2, 1
	sub a7, a5, s3
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2198:
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
	bnez t5, 2198b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2199:
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
	bnez t5, 2199b
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
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
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
	addi a0, a7, 0
2200:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2200b
2201:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	ld a6, 8(a4)
	ld a7, 8(a0)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a0)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 2202f
2204:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2204b
	j 2203f
2202:
2203:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2205f
2207:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 24(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 24(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 32(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 32(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 40(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 40(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2207b
	j 2206f
2205:
2206:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	slli s2, t0, 3
	sub a0, a0, s2
	addi a0, a0, 8
	addi a1, a1, -1
	bnez a1, 2201b
	slli s2, t0, 3
	addi s2, s2, 16
	add a6, a5, s2
	slli s3, s2, 1
	sub a7, a5, s3
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2208:
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
	bnez t5, 2208b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2209:
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
	bnez t5, 2209b
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
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
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
	addi a0, a7, 0
2210:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2210b
2211:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	ld a6, 8(a4)
	ld a7, 8(a0)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a0)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 2212f
2214:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2214b
	j 2213f
2212:
2213:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2215f
2217:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 24(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 24(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 32(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 32(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 40(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 40(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2217b
	j 2216f
2215:
2216:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	slli s2, t0, 3
	sub a0, a0, s2
	addi a0, a0, 8
	addi a1, a1, -1
	bnez a1, 2211b
	slli s2, t0, 3
	addi s2, s2, 16
	add a6, a5, s2
	slli s3, s2, 1
	sub a7, a5, s3
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2218:
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
	bnez t5, 2218b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2219:
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
	bnez t5, 2219b
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
	add a2, a2, s5
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
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
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
	addi a0, a7, 0
2220:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2220b
2221:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	ld a6, 8(a4)
	ld a7, 8(a0)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a0)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 2222f
2224:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2224b
	j 2223f
2222:
2223:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2225f
2227:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 24(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 24(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 32(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 32(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 40(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 40(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2227b
	j 2226f
2225:
2226:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	slli s2, t0, 3
	sub a0, a0, s2
	addi a0, a0, 8
	addi a1, a1, -1
	bnez a1, 2221b
	slli s2, t0, 3
	addi s2, s2, 16
	add a6, a5, s2
	slli s3, s2, 1
	sub a7, a5, s3
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2228:
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
	bnez t5, 2228b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2229:
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
	bnez t5, 2229b
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
	add a2, a2, s5
	add a2, a2, s5
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
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
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
	addi a0, a7, 0
2230:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2230b
2231:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	ld a6, 8(a4)
	ld a7, 8(a0)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a0)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 2232f
2234:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2234b
	j 2233f
2232:
2233:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2235f
2237:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 24(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 24(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 32(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 32(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 40(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 40(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2237b
	j 2236f
2235:
2236:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	slli s2, t0, 3
	sub a0, a0, s2
	addi a0, a0, 8
	addi a1, a1, -1
	bnez a1, 2231b
	slli s2, t0, 3
	addi s2, s2, 16
	add a6, a5, s2
	slli s3, s2, 1
	sub a7, a5, s3
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2238:
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
	bnez t5, 2238b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2239:
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
	bnez t5, 2239b
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
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
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
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
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
	addi a0, a7, 0
2240:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2240b
2241:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	ld a6, 8(a4)
	ld a7, 8(a0)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a0)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 2242f
2244:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2244b
	j 2243f
2242:
2243:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2245f
2247:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 24(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 24(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 32(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 32(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 40(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 40(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2247b
	j 2246f
2245:
2246:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	slli s2, t0, 3
	sub a0, a0, s2
	addi a0, a0, 8
	addi a1, a1, -1
	bnez a1, 2241b
	slli s2, t0, 3
	addi s2, s2, 16
	add a6, a5, s2
	slli s3, s2, 1
	sub a7, a5, s3
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2248:
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
	bnez t5, 2248b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2249:
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
	bnez t5, 2249b
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
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
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
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
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
	addi a0, a7, 0
2250:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2250b
2251:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	ld a6, 8(a4)
	ld a7, 8(a0)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a0)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 2252f
2254:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2254b
	j 2253f
2252:
2253:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2255f
2257:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 24(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 24(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 32(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 32(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 40(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 40(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2257b
	j 2256f
2255:
2256:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	slli s2, t0, 3
	sub a0, a0, s2
	addi a0, a0, 8
	addi a1, a1, -1
	bnez a1, 2251b
	slli s2, t0, 3
	addi s2, s2, 16
	add a6, a5, s2
	slli s3, s2, 1
	sub a7, a5, s3
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2258:
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
	bnez t5, 2258b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2259:
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
	bnez t5, 2259b
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
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
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
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
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
	addi a0, a7, 0
2260:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2260b
2261:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	ld a6, 8(a4)
	ld a7, 8(a0)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a0)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 2262f
2264:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2264b
	j 2263f
2262:
2263:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2265f
2267:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 24(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 24(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 32(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 32(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 40(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 40(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2267b
	j 2266f
2265:
2266:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	slli s2, t0, 3
	sub a0, a0, s2
	addi a0, a0, 8
	addi a1, a1, -1
	bnez a1, 2261b
	slli s2, t0, 3
	addi s2, s2, 16
	add a6, a5, s2
	slli s3, s2, 1
	sub a7, a5, s3
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2268:
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
	bnez t5, 2268b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2269:
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
	bnez t5, 2269b
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
2270:
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
	bnez t5, 2270b
	ld s10, 16(s6)
	slli s10, s10, 32
	srli s10, s10, 48
2271:
	lbu s7, 0(s9)
	slli s7, s7, 56
	lbu t3, 32(s9)
	slli t3, t3, 56
	srli t3, t3, 8
	add s7, s7, t3
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
2272:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2272b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2273:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2274f
2276:
	ld s4, 0(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 8(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 16(a0)
	ld s4, 8(t4)
	sd s3, 0(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 8(t4)
	ld s4, 16(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 24(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 32(a0)
	ld s4, 24(t4)
	sd s3, 16(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 24(t4)
	ld s4, 32(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 40(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 48(a0)
	ld s4, 40(t4)
	sd s3, 32(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 40(t4)
	ld s4, 48(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 56(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 64(a0)
	ld s4, 56(t4)
	sd s3, 48(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 56(t4)
	addi t4, t4, 64
	addi a0, a0, 64
	addi t5, t5, -1
	bnez t5, 2276b
	j 2275f
2274:
2275:
	beqz t6, 2277f
2279:
	ld s4, 0(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 8(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2279b
	j 2278f
2277:
2278:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2273b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2280:
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
	bnez t5, 2280b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2281:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2282f
2284:
	ld s4, 0(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 8(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 16(a0)
	ld s4, 8(t4)
	sd s3, 0(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 8(t4)
	ld s4, 16(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 24(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 32(a0)
	ld s4, 24(t4)
	sd s3, 16(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 24(t4)
	ld s4, 32(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 40(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 48(a0)
	ld s4, 40(t4)
	sd s3, 32(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 40(t4)
	ld s4, 48(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 56(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 64(a0)
	ld s4, 56(t4)
	sd s3, 48(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 56(t4)
	addi t4, t4, 64
	addi a0, a0, 64
	addi t5, t5, -1
	bnez t5, 2284b
	j 2283f
2282:
2283:
	beqz t6, 2285f
2287:
	ld s4, 0(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 8(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2287b
	j 2286f
2285:
2286:
	ld s2, 0(t4)
	add s1, s1, s2
	sltu s3, s1, s2
	add s1, s1, a1
	sltu s2, s1, a1
	add a1, s3, s2
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, -1
	slli s2, t0, 3
	sub a0, a0, s2
	bnez t2, 2281b
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a7, a5, s2
	slli t3, t0, 3
	add a5, a5, t3
	add t4, a5, t3
	sd a1, 0(t4)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2288:
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
	bnez t5, 2288b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2289:
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
	bnez t5, 2289b
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
2290:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2290b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2291:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2292f
2294:
	ld s4, 0(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 8(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 16(a0)
	ld s4, 8(t4)
	sd s3, 0(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 8(t4)
	ld s4, 16(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 24(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 32(a0)
	ld s4, 24(t4)
	sd s3, 16(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 24(t4)
	ld s4, 32(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 40(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 48(a0)
	ld s4, 40(t4)
	sd s3, 32(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 40(t4)
	ld s4, 48(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 56(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 64(a0)
	ld s4, 56(t4)
	sd s3, 48(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 56(t4)
	addi t4, t4, 64
	addi a0, a0, 64
	addi t5, t5, -1
	bnez t5, 2294b
	j 2293f
2292:
2293:
	beqz t6, 2295f
2297:
	ld s4, 0(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 8(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2297b
	j 2296f
2295:
2296:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2291b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2298:
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
	bnez t5, 2298b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2299:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2300f
2302:
	ld s4, 0(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 8(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 16(a0)
	ld s4, 8(t4)
	sd s3, 0(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 8(t4)
	ld s4, 16(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 24(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 32(a0)
	ld s4, 24(t4)
	sd s3, 16(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 24(t4)
	ld s4, 32(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 40(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 48(a0)
	ld s4, 40(t4)
	sd s3, 32(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 40(t4)
	ld s4, 48(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 56(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 64(a0)
	ld s4, 56(t4)
	sd s3, 48(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 56(t4)
	addi t4, t4, 64
	addi a0, a0, 64
	addi t5, t5, -1
	bnez t5, 2302b
	j 2301f
2300:
2301:
	beqz t6, 2303f
2305:
	ld s4, 0(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 8(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2305b
	j 2304f
2303:
2304:
	ld s2, 0(t4)
	add s1, s1, s2
	sltu s3, s1, s2
	add s1, s1, a1
	sltu s2, s1, a1
	add a1, s3, s2
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, -1
	slli s2, t0, 3
	sub a0, a0, s2
	bnez t2, 2299b
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a7, a5, s2
	slli t3, t0, 3
	add a5, a5, t3
	add t4, a5, t3
	sd a1, 0(t4)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2306:
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
	bnez t5, 2306b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2307:
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
	bnez t5, 2307b
	slli t3, t0, 3
	sub a5, a5, t3
	srli a1, s7, 62
	srli t3, s7, 54
	andi t3, t3, 3
	slli t3, t3, 2
	add a1, a1, t3
	slli t3, s5, 3
	add t3, a7, t3
	slli s4, s5, 2
	add s4, s4, s5
	add s4, a7, s4
	addi t5, t0, 0
2308:
	addi s1, t3, 0
	addi s0, zero, 0
	addi s3, zero, 0
	addi t6, zero, 1
	sll t6, t6, a1
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	sd s0, 0(s4)
	addi s4, s4, 8
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2308b
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
	addi a0, a7, 0
2309:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2309b
2310:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	ld a6, 8(a4)
	ld a7, 8(a0)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a0)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 2311f
2313:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2313b
	j 2312f
2311:
2312:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2314f
2316:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 24(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 24(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 32(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 32(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 40(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 40(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2316b
	j 2315f
2314:
2315:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	slli s2, t0, 3
	sub a0, a0, s2
	addi a0, a0, 8
	addi a1, a1, -1
	bnez a1, 2310b
	slli s2, t0, 3
	addi s2, s2, 16
	add a6, a5, s2
	slli s3, s2, 1
	sub a7, a5, s3
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2317:
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
	bnez t5, 2317b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2318:
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
	bnez t5, 2318b
	slli s7, s7, 2
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
2319:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2319b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2320:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2321f
2323:
	ld s4, 0(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 8(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 16(a0)
	ld s4, 8(t4)
	sd s3, 0(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 8(t4)
	ld s4, 16(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 24(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 32(a0)
	ld s4, 24(t4)
	sd s3, 16(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 24(t4)
	ld s4, 32(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 40(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 48(a0)
	ld s4, 40(t4)
	sd s3, 32(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 40(t4)
	ld s4, 48(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 56(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 64(a0)
	ld s4, 56(t4)
	sd s3, 48(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 56(t4)
	addi t4, t4, 64
	addi a0, a0, 64
	addi t5, t5, -1
	bnez t5, 2323b
	j 2322f
2321:
2322:
	beqz t6, 2324f
2326:
	ld s4, 0(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 8(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2326b
	j 2325f
2324:
2325:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2320b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2327:
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
	bnez t5, 2327b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2328:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2329f
2331:
	ld s4, 0(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 8(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 16(a0)
	ld s4, 8(t4)
	sd s3, 0(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 8(t4)
	ld s4, 16(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 24(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 32(a0)
	ld s4, 24(t4)
	sd s3, 16(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 24(t4)
	ld s4, 32(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 40(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 48(a0)
	ld s4, 40(t4)
	sd s3, 32(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 40(t4)
	ld s4, 48(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 56(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 64(a0)
	ld s4, 56(t4)
	sd s3, 48(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 56(t4)
	addi t4, t4, 64
	addi a0, a0, 64
	addi t5, t5, -1
	bnez t5, 2331b
	j 2330f
2329:
2330:
	beqz t6, 2332f
2334:
	ld s4, 0(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 8(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2334b
	j 2333f
2332:
2333:
	ld s2, 0(t4)
	add s1, s1, s2
	sltu s3, s1, s2
	add s1, s1, a1
	sltu s2, s1, a1
	add a1, s3, s2
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, -1
	slli s2, t0, 3
	sub a0, a0, s2
	bnez t2, 2328b
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a7, a5, s2
	slli t3, t0, 3
	add a5, a5, t3
	add t4, a5, t3
	sd a1, 0(t4)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2335:
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
	bnez t5, 2335b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2336:
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
	bnez t5, 2336b
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
2337:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2337b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2338:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2339f
2341:
	ld s4, 0(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 8(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 16(a0)
	ld s4, 8(t4)
	sd s3, 0(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 8(t4)
	ld s4, 16(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 24(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 32(a0)
	ld s4, 24(t4)
	sd s3, 16(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 24(t4)
	ld s4, 32(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 40(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 48(a0)
	ld s4, 40(t4)
	sd s3, 32(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 40(t4)
	ld s4, 48(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 56(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 64(a0)
	ld s4, 56(t4)
	sd s3, 48(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 56(t4)
	addi t4, t4, 64
	addi a0, a0, 64
	addi t5, t5, -1
	bnez t5, 2341b
	j 2340f
2339:
2340:
	beqz t6, 2342f
2344:
	ld s4, 0(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 8(a0)
	add s3, s3, s4
	sltu s4, s3, s4
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
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2338b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2345:
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
	bnez t5, 2345b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2346:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2347f
2349:
	ld s4, 0(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 8(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 16(a0)
	ld s4, 8(t4)
	sd s3, 0(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 8(t4)
	ld s4, 16(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 24(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 32(a0)
	ld s4, 24(t4)
	sd s3, 16(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 24(t4)
	ld s4, 32(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 40(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 48(a0)
	ld s4, 40(t4)
	sd s3, 32(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 40(t4)
	ld s4, 48(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 56(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 64(a0)
	ld s4, 56(t4)
	sd s3, 48(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 56(t4)
	addi t4, t4, 64
	addi a0, a0, 64
	addi t5, t5, -1
	bnez t5, 2349b
	j 2348f
2347:
2348:
	beqz t6, 2350f
2352:
	ld s4, 0(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 8(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2352b
	j 2351f
2350:
2351:
	ld s2, 0(t4)
	add s1, s1, s2
	sltu s3, s1, s2
	add s1, s1, a1
	sltu s2, s1, a1
	add a1, s3, s2
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, -1
	slli s2, t0, 3
	sub a0, a0, s2
	bnez t2, 2346b
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a7, a5, s2
	slli t3, t0, 3
	add a5, a5, t3
	add t4, a5, t3
	sd a1, 0(t4)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2353:
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
	bnez t5, 2353b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2354:
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
	bnez t5, 2354b
	slli t3, t0, 3
	sub a5, a5, t3
	srli a1, s7, 62
	srli t3, s7, 54
	andi t3, t3, 3
	slli t3, t3, 2
	add a1, a1, t3
	slli t3, s5, 3
	add t3, a7, t3
	slli s4, s5, 2
	add s4, s4, s5
	add s4, a7, s4
	addi t5, t0, 0
2355:
	addi s1, t3, 0
	addi s0, zero, 0
	addi s3, zero, 0
	addi t6, zero, 1
	sll t6, t6, a1
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	sd s0, 0(s4)
	addi s4, s4, 8
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2355b
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
	addi a0, a7, 0
2356:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2356b
2357:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	ld a6, 8(a4)
	ld a7, 8(a0)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a0)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 2358f
2360:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2360b
	j 2359f
2358:
2359:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2361f
2363:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 24(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 24(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 32(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 32(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 40(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 40(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2363b
	j 2362f
2361:
2362:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	slli s2, t0, 3
	sub a0, a0, s2
	addi a0, a0, 8
	addi a1, a1, -1
	bnez a1, 2357b
	slli s2, t0, 3
	addi s2, s2, 16
	add a6, a5, s2
	slli s3, s2, 1
	sub a7, a5, s3
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2364:
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
	bnez t5, 2364b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2365:
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
	bnez t5, 2365b
	slli s7, s7, 2
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
2366:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2366b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2367:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2368f
2370:
	ld s4, 0(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 8(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 16(a0)
	ld s4, 8(t4)
	sd s3, 0(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 8(t4)
	ld s4, 16(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 24(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 32(a0)
	ld s4, 24(t4)
	sd s3, 16(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 24(t4)
	ld s4, 32(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 40(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 48(a0)
	ld s4, 40(t4)
	sd s3, 32(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 40(t4)
	ld s4, 48(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 56(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 64(a0)
	ld s4, 56(t4)
	sd s3, 48(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 56(t4)
	addi t4, t4, 64
	addi a0, a0, 64
	addi t5, t5, -1
	bnez t5, 2370b
	j 2369f
2368:
2369:
	beqz t6, 2371f
2373:
	ld s4, 0(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 8(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2373b
	j 2372f
2371:
2372:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2367b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2374:
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
	bnez t5, 2374b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2375:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2376f
2378:
	ld s4, 0(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 8(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 16(a0)
	ld s4, 8(t4)
	sd s3, 0(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 8(t4)
	ld s4, 16(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 24(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 32(a0)
	ld s4, 24(t4)
	sd s3, 16(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 24(t4)
	ld s4, 32(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 40(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 48(a0)
	ld s4, 40(t4)
	sd s3, 32(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 40(t4)
	ld s4, 48(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 56(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 64(a0)
	ld s4, 56(t4)
	sd s3, 48(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 56(t4)
	addi t4, t4, 64
	addi a0, a0, 64
	addi t5, t5, -1
	bnez t5, 2378b
	j 2377f
2376:
2377:
	beqz t6, 2379f
2381:
	ld s4, 0(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 8(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2381b
	j 2380f
2379:
2380:
	ld s2, 0(t4)
	add s1, s1, s2
	sltu s3, s1, s2
	add s1, s1, a1
	sltu s2, s1, a1
	add a1, s3, s2
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, -1
	slli s2, t0, 3
	sub a0, a0, s2
	bnez t2, 2375b
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a7, a5, s2
	slli t3, t0, 3
	add a5, a5, t3
	add t4, a5, t3
	sd a1, 0(t4)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2382:
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
	bnez t5, 2382b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2383:
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
	bnez t5, 2383b
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
2384:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2384b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2385:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2386f
2388:
	ld s4, 0(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 8(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 16(a0)
	ld s4, 8(t4)
	sd s3, 0(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 8(t4)
	ld s4, 16(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 24(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 32(a0)
	ld s4, 24(t4)
	sd s3, 16(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 24(t4)
	ld s4, 32(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 40(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 48(a0)
	ld s4, 40(t4)
	sd s3, 32(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 40(t4)
	ld s4, 48(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 56(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 64(a0)
	ld s4, 56(t4)
	sd s3, 48(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 56(t4)
	addi t4, t4, 64
	addi a0, a0, 64
	addi t5, t5, -1
	bnez t5, 2388b
	j 2387f
2386:
2387:
	beqz t6, 2389f
2391:
	ld s4, 0(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 8(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2391b
	j 2390f
2389:
2390:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2385b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2392:
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
	bnez t5, 2392b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2393:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2394f
2396:
	ld s4, 0(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 8(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 16(a0)
	ld s4, 8(t4)
	sd s3, 0(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 8(t4)
	ld s4, 16(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 24(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 32(a0)
	ld s4, 24(t4)
	sd s3, 16(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 24(t4)
	ld s4, 32(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 40(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 48(a0)
	ld s4, 40(t4)
	sd s3, 32(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 40(t4)
	ld s4, 48(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 56(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 64(a0)
	ld s4, 56(t4)
	sd s3, 48(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 56(t4)
	addi t4, t4, 64
	addi a0, a0, 64
	addi t5, t5, -1
	bnez t5, 2396b
	j 2395f
2394:
2395:
	beqz t6, 2397f
2399:
	ld s4, 0(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 8(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2399b
	j 2398f
2397:
2398:
	ld s2, 0(t4)
	add s1, s1, s2
	sltu s3, s1, s2
	add s1, s1, a1
	sltu s2, s1, a1
	add a1, s3, s2
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, -1
	slli s2, t0, 3
	sub a0, a0, s2
	bnez t2, 2393b
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a7, a5, s2
	slli t3, t0, 3
	add a5, a5, t3
	add t4, a5, t3
	sd a1, 0(t4)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2400:
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
	bnez t5, 2400b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2401:
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
	bnez t5, 2401b
	slli t3, t0, 3
	sub a5, a5, t3
	srli a1, s7, 62
	srli t3, s7, 54
	andi t3, t3, 3
	slli t3, t3, 2
	add a1, a1, t3
	slli t3, s5, 3
	add t3, a7, t3
	slli s4, s5, 2
	add s4, s4, s5
	add s4, a7, s4
	addi t5, t0, 0
2402:
	addi s1, t3, 0
	addi s0, zero, 0
	addi s3, zero, 0
	addi t6, zero, 1
	sll t6, t6, a1
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	sd s0, 0(s4)
	addi s4, s4, 8
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2402b
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
	addi a0, a7, 0
2403:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2403b
2404:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	ld a6, 8(a4)
	ld a7, 8(a0)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a0)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 2405f
2407:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2407b
	j 2406f
2405:
2406:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2408f
2410:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 24(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 24(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 32(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 32(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 40(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 40(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2410b
	j 2409f
2408:
2409:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	slli s2, t0, 3
	sub a0, a0, s2
	addi a0, a0, 8
	addi a1, a1, -1
	bnez a1, 2404b
	slli s2, t0, 3
	addi s2, s2, 16
	add a6, a5, s2
	slli s3, s2, 1
	sub a7, a5, s3
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2411:
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
	bnez t5, 2411b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2412:
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
	bnez t5, 2412b
	slli s7, s7, 2
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
2413:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2413b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2414:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2415f
2417:
	ld s4, 0(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 8(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 16(a0)
	ld s4, 8(t4)
	sd s3, 0(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 8(t4)
	ld s4, 16(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 24(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 32(a0)
	ld s4, 24(t4)
	sd s3, 16(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 24(t4)
	ld s4, 32(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 40(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 48(a0)
	ld s4, 40(t4)
	sd s3, 32(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 40(t4)
	ld s4, 48(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 56(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 64(a0)
	ld s4, 56(t4)
	sd s3, 48(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 56(t4)
	addi t4, t4, 64
	addi a0, a0, 64
	addi t5, t5, -1
	bnez t5, 2417b
	j 2416f
2415:
2416:
	beqz t6, 2418f
2420:
	ld s4, 0(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 8(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2420b
	j 2419f
2418:
2419:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2414b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2421:
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
	bnez t5, 2421b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2422:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2423f
2425:
	ld s4, 0(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 8(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 16(a0)
	ld s4, 8(t4)
	sd s3, 0(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 8(t4)
	ld s4, 16(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 24(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 32(a0)
	ld s4, 24(t4)
	sd s3, 16(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 24(t4)
	ld s4, 32(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 40(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 48(a0)
	ld s4, 40(t4)
	sd s3, 32(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 40(t4)
	ld s4, 48(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 56(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 64(a0)
	ld s4, 56(t4)
	sd s3, 48(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 56(t4)
	addi t4, t4, 64
	addi a0, a0, 64
	addi t5, t5, -1
	bnez t5, 2425b
	j 2424f
2423:
2424:
	beqz t6, 2426f
2428:
	ld s4, 0(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 8(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2428b
	j 2427f
2426:
2427:
	ld s2, 0(t4)
	add s1, s1, s2
	sltu s3, s1, s2
	add s1, s1, a1
	sltu s2, s1, a1
	add a1, s3, s2
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, -1
	slli s2, t0, 3
	sub a0, a0, s2
	bnez t2, 2422b
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a7, a5, s2
	slli t3, t0, 3
	add a5, a5, t3
	add t4, a5, t3
	sd a1, 0(t4)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2429:
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
	bnez t5, 2429b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2430:
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
	bnez t5, 2430b
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
2431:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2431b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2432:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2433f
2435:
	ld s4, 0(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 8(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 16(a0)
	ld s4, 8(t4)
	sd s3, 0(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 8(t4)
	ld s4, 16(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 24(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 32(a0)
	ld s4, 24(t4)
	sd s3, 16(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 24(t4)
	ld s4, 32(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 40(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 48(a0)
	ld s4, 40(t4)
	sd s3, 32(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 40(t4)
	ld s4, 48(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 56(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 64(a0)
	ld s4, 56(t4)
	sd s3, 48(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 56(t4)
	addi t4, t4, 64
	addi a0, a0, 64
	addi t5, t5, -1
	bnez t5, 2435b
	j 2434f
2433:
2434:
	beqz t6, 2436f
2438:
	ld s4, 0(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 8(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2438b
	j 2437f
2436:
2437:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2432b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2439:
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
	bnez t5, 2439b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2440:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2441f
2443:
	ld s4, 0(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 8(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 16(a0)
	ld s4, 8(t4)
	sd s3, 0(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 8(t4)
	ld s4, 16(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 24(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 32(a0)
	ld s4, 24(t4)
	sd s3, 16(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 24(t4)
	ld s4, 32(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 40(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 48(a0)
	ld s4, 40(t4)
	sd s3, 32(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 40(t4)
	ld s4, 48(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 56(a0)
	mul a4, s0, a7
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	mulhu s2, s0, a7
	ld a7, 64(a0)
	ld s4, 56(t4)
	sd s3, 48(t4)
	add a4, a4, s4
	sltu s4, a4, s4
	add s2, s2, s4
	add a4, a4, s1
	sltu s4, a4, s1
	add s1, s2, s4
	sd a4, 56(t4)
	addi t4, t4, 64
	addi a0, a0, 64
	addi t5, t5, -1
	bnez t5, 2443b
	j 2442f
2441:
2442:
	beqz t6, 2444f
2446:
	ld s4, 0(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 8(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2446b
	j 2445f
2444:
2445:
	ld s2, 0(t4)
	add s1, s1, s2
	sltu s3, s1, s2
	add s1, s1, a1
	sltu s2, s1, a1
	add a1, s3, s2
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, -1
	slli s2, t0, 3
	sub a0, a0, s2
	bnez t2, 2440b
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a7, a5, s2
	slli t3, t0, 3
	add a5, a5, t3
	add t4, a5, t3
	sd a1, 0(t4)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2447:
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
	bnez t5, 2447b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2448:
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
	bnez t5, 2448b
	slli t3, t0, 3
	sub a5, a5, t3
	srli a1, s7, 62
	srli t3, s7, 54
	andi t3, t3, 3
	slli t3, t3, 2
	add a1, a1, t3
	slli t3, s5, 3
	add t3, a7, t3
	slli s4, s5, 2
	add s4, s4, s5
	add s4, a7, s4
	addi t5, t0, 0
2449:
	addi s1, t3, 0
	addi s0, zero, 0
	addi s3, zero, 0
	addi t6, zero, 1
	sll t6, t6, a1
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	sd s0, 0(s4)
	addi s4, s4, 8
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2449b
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
	addi a0, a7, 0
2450:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2450b
2451:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	ld a6, 8(a4)
	ld a7, 8(a0)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a0)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 2452f
2454:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2454b
	j 2453f
2452:
2453:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2455f
2457:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 24(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 24(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 32(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 32(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 40(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 40(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2457b
	j 2456f
2455:
2456:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	slli s2, t0, 3
	sub a0, a0, s2
	addi a0, a0, 8
	addi a1, a1, -1
	bnez a1, 2451b
	slli s2, t0, 3
	addi s2, s2, 16
	add a6, a5, s2
	slli s3, s2, 1
	sub a7, a5, s3
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2458:
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
	bnez t5, 2458b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2459:
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
	bnez t5, 2459b
	slli s7, s7, 2
	addi s10, s10, -1
	bnez s10, 2271b
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
	addi a0, a7, 0
2460:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2460b
2461:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	ld a6, 8(a4)
	ld a7, 8(a0)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a0)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 2462f
2464:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2464b
	j 2463f
2462:
2463:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2465f
2467:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 24(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 24(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 32(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 32(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 40(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 40(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2467b
	j 2466f
2465:
2466:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	slli s2, t0, 3
	sub a0, a0, s2
	addi a0, a0, 8
	addi a1, a1, -1
	bnez a1, 2461b
	slli s2, t0, 3
	addi s2, s2, 16
	add a6, a5, s2
	slli s3, s2, 1
	sub a7, a5, s3
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2468:
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
	bnez t5, 2468b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2469:
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
	bnez t5, 2469b
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
2470:
	lbu s0, 0(t3)
	sb s0, 0(t4)
	addi t4, t4, 1
	addi t3, t3, -1
	addi t5, t5, -1
	bnez t5, 2470b
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
2471:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2471b
	addi a2, a7, 0
	add a2, a2, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
2472:
	lbu s7, 0(s9)
	slli s7, s7, 56
	addi s9, s9, 1
	addi s8, zero, 8
2473:
	srli s4, s7, 63
	slli s7, s7, 1
	addi t3, a5, 0
	addi t4, a2, 0
	addi t5, t0, 0
2474:
	ld s2, 0(t4)
	slli s3, s2, 1
	add s3, s3, s4
	srli s4, s2, 63
	sd s3, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2474b
	sd s4, 0(t3)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2475:
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
	bnez t5, 2475b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2476:
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
	bnez t5, 2476b
	addi s8, s8, -1
	bnez s8, 2473b
	addi s10, s10, -1
	bnez s10, 2472b
	addi s7, ra, 0
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
2477:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2477b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
2478:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 2478b
	sub a7, a7, s5
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
	addi t5, t0, 0
	addi t2, zero, 0
2479:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2479b
	addi s0, zero, 0
	sltu s1, s0, t2
	addi a0, s1, -1
	ld a1, 0(s6)
	and a0, a0, a1
	andi a0, a0, 1
221:
29:
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
	addi t0, zero, 0
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

vg_dsa_parameter_search_init:
	.option push
	.option arch, +m, +c
	addi t3, zero, 128
	beq a1, t3, 20f
	addi t3, zero, 256
	beq a1, t3, 22f
	addi t3, zero, 384
	beq a1, t3, 24f
	addi t2, zero, 0
	sd t2, 0(a0)
	sd t2, 8(a0)
	sd t2, 16(a0)
	sd t2, 24(a0)
	addi a0, zero, 0
	j 25f
24:
	lui t2, 1
	sd t2, 0(a0)
	sd a1, 8(a0)
	slli t2, a1, 15
	add t2, t2, a1
	sd t2, 16(a0)
	slli t2, a1, 9
	sd t2, 24(a0)
	addi a0, zero, 1
25:
	j 23f
22:
	lui t2, 1
	sd t2, 0(a0)
	sd a1, 8(a0)
	slli t2, a1, 15
	add t2, t2, a1
	sd t2, 16(a0)
	slli t2, a1, 9
	sd t2, 24(a0)
	addi a0, zero, 1
23:
	j 21f
20:
	lui t2, 1
	sd t2, 0(a0)
	sd a1, 8(a0)
	slli t2, a1, 15
	add t2, t2, a1
	sd t2, 16(a0)
	slli t2, a1, 9
	sd t2, 24(a0)
	addi a0, zero, 1
21:
	addi t0, zero, 0
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

vg_dsa_parameter_search:
	.option push
	.option arch, +m, +c
	ld t2, 0(a7)
	addi t3, zero, 0
	sd s0, 184(a5)
	sd s1, 192(a5)
	sd s2, 200(a5)
	sd s3, 208(a5)
	sd s4, 216(a5)
	sd s5, 224(a5)
	sd s7, 232(a5)
	sd s8, 240(a5)
	sd s9, 248(a5)
	sd s10, 256(a5)
	sd s11, 264(a5)
	sd s6, 272(a5)
	sd ra, 120(a5)
	sd a0, 0(a5)
	sd a2, 152(a5)
	sd a3, 72(a5)
	sd a4, 80(a5)
	sd a7, 160(a5)
	sd a6, 168(a5)
	sd t2, 16(a5)
	sd t3, 24(a5)
	addi s6, a5, 0
	ld t3, 160(s6)
	ld t2, 8(t3)
	addi t3, zero, 128
	beq t2, t3, 20f
	addi t3, zero, 256
	beq t2, t3, 22f
	addi t2, zero, 0
	sd t2, 320(s6)
	sd t2, 328(s6)
	sd t2, 336(s6)
	sd t2, 344(s6)
	sd t2, 352(s6)
	sd t2, 360(s6)
	sd t2, 368(s6)
	sd t2, 376(s6)
	addi t2, zero, 128
	sb t2, 352(s6)
	addi t2, zero, 1
	sb t2, 382(s6)
	addi t2, zero, 0
	sb t2, 383(s6)
24:
	ld t2, 24(s6)
	sd t2, 144(s6)
	ld t3, 16(s6)
	beqz t3, 25f
	ld t3, 80(s6)
	sub t3, t3, t2
	addi t4, zero, 32
	bltu t3, t4, 27f
	ld t3, 72(s6)
	add t3, t3, t2
	sd t3, 8(s6)
	addi t2, t2, 32
	sd t2, 24(s6)
	addi t2, zero, 2
	sd t2, 64(s6)
	ld a0, 8(s6)
	addi a1, s6, 320
	addi a2, zero, 32
29:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 29b
	addi a0, s6, 384
	lui t0, 434334
	addiw t0, t0, 1639
	sb t0, 0(a0)
	srli t1, t0, 8
	sb t1, 1(a0)
	srli t1, t0, 16
	sb t1, 2(a0)
	srli t1, t0, 24
	sb t1, 3(a0)
	lui t0, 767611
	addiw t0, t0, -379
	sb t0, 4(a0)
	srli t1, t0, 8
	sb t1, 5(a0)
	srli t1, t0, 16
	sb t1, 6(a0)
	srli t1, t0, 24
	sb t1, 7(a0)
	lui t0, 247535
	addiw t0, t0, 882
	sb t0, 8(a0)
	srli t1, t0, 8
	sb t1, 9(a0)
	srli t1, t0, 16
	sb t1, 10(a0)
	srli t1, t0, 24
	sb t1, 11(a0)
	lui t0, 677119
	addiw t0, t0, 1338
	sb t0, 12(a0)
	srli t1, t0, 8
	sb t1, 13(a0)
	srli t1, t0, 16
	sb t1, 14(a0)
	srli t1, t0, 24
	sb t1, 15(a0)
	lui t0, 332005
	addiw t0, t0, 639
	sb t0, 16(a0)
	srli t1, t0, 8
	sb t1, 17(a0)
	srli t1, t0, 16
	sb t1, 18(a0)
	srli t1, t0, 24
	sb t1, 19(a0)
	lui t0, 634967
	addiw t0, t0, -1908
	sb t0, 20(a0)
	srli t1, t0, 8
	sb t1, 21(a0)
	srli t1, t0, 16
	sb t1, 22(a0)
	srli t1, t0, 24
	sb t1, 23(a0)
	lui t0, 129086
	addiw t0, t0, -1621
	sb t0, 24(a0)
	srli t1, t0, 8
	sb t1, 25(a0)
	srli t1, t0, 16
	sb t1, 26(a0)
	srli t1, t0, 24
	sb t1, 27(a0)
	lui t0, 376333
	addiw t0, t0, -743
	sb t0, 28(a0)
	srli t1, t0, 8
	sb t1, 29(a0)
	srli t1, t0, 16
	sb t1, 30(a0)
	srli t1, t0, 24
	sb t1, 31(a0)
	addi a0, s6, 384
	addi a1, s6, 320
	addi a2, zero, 1
	addi a3, s6, 416
	call {vg_sha256_compress}
	addi s1, s6, 384
	addi s3, s6, 512
	lbu t1, 0(s1)
	lbu t2, 1(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 2(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 3(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 0(s3)
	srli t2, t1, 16
	sb t2, 1(s3)
	srli t2, t1, 8
	sb t2, 2(s3)
	srli t2, t1, 0
	sb t2, 3(s3)
	lbu t1, 4(s1)
	lbu t2, 5(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 6(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 7(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 4(s3)
	srli t2, t1, 16
	sb t2, 5(s3)
	srli t2, t1, 8
	sb t2, 6(s3)
	srli t2, t1, 0
	sb t2, 7(s3)
	lbu t1, 8(s1)
	lbu t2, 9(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 10(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 11(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 8(s3)
	srli t2, t1, 16
	sb t2, 9(s3)
	srli t2, t1, 8
	sb t2, 10(s3)
	srli t2, t1, 0
	sb t2, 11(s3)
	lbu t1, 12(s1)
	lbu t2, 13(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 14(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 15(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 12(s3)
	srli t2, t1, 16
	sb t2, 13(s3)
	srli t2, t1, 8
	sb t2, 14(s3)
	srli t2, t1, 0
	sb t2, 15(s3)
	lbu t1, 16(s1)
	lbu t2, 17(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 18(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 19(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 16(s3)
	srli t2, t1, 16
	sb t2, 17(s3)
	srli t2, t1, 8
	sb t2, 18(s3)
	srli t2, t1, 0
	sb t2, 19(s3)
	lbu t1, 20(s1)
	lbu t2, 21(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 22(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 23(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 20(s3)
	srli t2, t1, 16
	sb t2, 21(s3)
	srli t2, t1, 8
	sb t2, 22(s3)
	srli t2, t1, 0
	sb t2, 23(s3)
	lbu t1, 24(s1)
	lbu t2, 25(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 26(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 27(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 24(s3)
	srli t2, t1, 16
	sb t2, 25(s3)
	srli t2, t1, 8
	sb t2, 26(s3)
	srli t2, t1, 0
	sb t2, 27(s3)
	lbu t1, 28(s1)
	lbu t2, 29(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 30(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 31(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 28(s3)
	srli t2, t1, 16
	sb t2, 29(s3)
	srli t2, t1, 8
	sb t2, 30(s3)
	srli t2, t1, 0
	sb t2, 31(s3)
	lbu t2, 512(s6)
	ori t2, t2, 128
	sb t2, 512(s6)
	lbu t2, 543(s6)
	ori t2, t2, 1
	sb t2, 543(s6)
	addi a0, s6, 512
	lui a1, 7
	add a1, a1, s6
	addi a1, a1, 0
	addi a2, zero, 32
210:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 210b
	lui a0, 7
	add a0, a0, s6
	ld a1, 168(s6)
	lui t3, 7
	srli t3, t3, 3
	sub a1, a1, t3
	ld t2, 24(s6)
	ld a2, 72(s6)
	ld a3, 80(s6)
	add a2, a2, t2
	sub a3, a3, t2
	addi a4, s6, 112
	beqz a3, 211f
	j 212f
211:
	ld a2, 72(s6)
212:
	call {vg_dsa_probable_prime_256}
	slli a0, a0, 32
	srli a0, a0, 32
	sd a0, 88(s6)
	beqz a0, 213f
	ld t3, 112(s6)
	ld t4, 24(s6)
	add t4, t4, t3
	sd t4, 24(s6)
	j 214f
213:
214:
	ld t2, 88(s6)
	addi t2, t2, 0
	beqz t2, 215f
	ld t2, 88(s6)
	addi t2, t2, -1
	beqz t2, 217f
	j 218f
217:
	addi t2, zero, 0
	sd t2, 32(s6)
	addi t2, zero, 1
	sd t2, 40(s6)
	addi t2, zero, 4
	sd t2, 96(s6)
219:
	ld a0, 8(s6)
	addi a1, s6, 320
	addi a2, zero, 32
220:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 220b
	addi a0, s6, 351
	ld a2, 40(s6)
	addi a2, a2, 0
	addi a3, zero, 32
221:
	lbu a1, 0(a0)
	add a1, a1, a2
	sb a1, 0(a0)
	srli a2, a1, 8
	addi a0, a0, -1
	addi a3, a3, -1
	bnez a3, 221b
	addi a0, s6, 384
	lui t0, 434334
	addiw t0, t0, 1639
	sb t0, 0(a0)
	srli t1, t0, 8
	sb t1, 1(a0)
	srli t1, t0, 16
	sb t1, 2(a0)
	srli t1, t0, 24
	sb t1, 3(a0)
	lui t0, 767611
	addiw t0, t0, -379
	sb t0, 4(a0)
	srli t1, t0, 8
	sb t1, 5(a0)
	srli t1, t0, 16
	sb t1, 6(a0)
	srli t1, t0, 24
	sb t1, 7(a0)
	lui t0, 247535
	addiw t0, t0, 882
	sb t0, 8(a0)
	srli t1, t0, 8
	sb t1, 9(a0)
	srli t1, t0, 16
	sb t1, 10(a0)
	srli t1, t0, 24
	sb t1, 11(a0)
	lui t0, 677119
	addiw t0, t0, 1338
	sb t0, 12(a0)
	srli t1, t0, 8
	sb t1, 13(a0)
	srli t1, t0, 16
	sb t1, 14(a0)
	srli t1, t0, 24
	sb t1, 15(a0)
	lui t0, 332005
	addiw t0, t0, 639
	sb t0, 16(a0)
	srli t1, t0, 8
	sb t1, 17(a0)
	srli t1, t0, 16
	sb t1, 18(a0)
	srli t1, t0, 24
	sb t1, 19(a0)
	lui t0, 634967
	addiw t0, t0, -1908
	sb t0, 20(a0)
	srli t1, t0, 8
	sb t1, 21(a0)
	srli t1, t0, 16
	sb t1, 22(a0)
	srli t1, t0, 24
	sb t1, 23(a0)
	lui t0, 129086
	addiw t0, t0, -1621
	sb t0, 24(a0)
	srli t1, t0, 8
	sb t1, 25(a0)
	srli t1, t0, 16
	sb t1, 26(a0)
	srli t1, t0, 24
	sb t1, 27(a0)
	lui t0, 376333
	addiw t0, t0, -743
	sb t0, 28(a0)
	srli t1, t0, 8
	sb t1, 29(a0)
	srli t1, t0, 16
	sb t1, 30(a0)
	srli t1, t0, 24
	sb t1, 31(a0)
	addi a0, s6, 384
	addi a1, s6, 320
	addi a2, zero, 1
	addi a3, s6, 416
	call {vg_sha256_compress}
	addi s1, s6, 384
	addi s3, s6, 928
	lbu t1, 0(s1)
	lbu t2, 1(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 2(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 3(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 0(s3)
	srli t2, t1, 16
	sb t2, 1(s3)
	srli t2, t1, 8
	sb t2, 2(s3)
	srli t2, t1, 0
	sb t2, 3(s3)
	lbu t1, 4(s1)
	lbu t2, 5(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 6(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 7(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 4(s3)
	srli t2, t1, 16
	sb t2, 5(s3)
	srli t2, t1, 8
	sb t2, 6(s3)
	srli t2, t1, 0
	sb t2, 7(s3)
	lbu t1, 8(s1)
	lbu t2, 9(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 10(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 11(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 8(s3)
	srli t2, t1, 16
	sb t2, 9(s3)
	srli t2, t1, 8
	sb t2, 10(s3)
	srli t2, t1, 0
	sb t2, 11(s3)
	lbu t1, 12(s1)
	lbu t2, 13(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 14(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 15(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 12(s3)
	srli t2, t1, 16
	sb t2, 13(s3)
	srli t2, t1, 8
	sb t2, 14(s3)
	srli t2, t1, 0
	sb t2, 15(s3)
	lbu t1, 16(s1)
	lbu t2, 17(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 18(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 19(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 16(s3)
	srli t2, t1, 16
	sb t2, 17(s3)
	srli t2, t1, 8
	sb t2, 18(s3)
	srli t2, t1, 0
	sb t2, 19(s3)
	lbu t1, 20(s1)
	lbu t2, 21(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 22(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 23(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 20(s3)
	srli t2, t1, 16
	sb t2, 21(s3)
	srli t2, t1, 8
	sb t2, 22(s3)
	srli t2, t1, 0
	sb t2, 23(s3)
	lbu t1, 24(s1)
	lbu t2, 25(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 26(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 27(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 24(s3)
	srli t2, t1, 16
	sb t2, 25(s3)
	srli t2, t1, 8
	sb t2, 26(s3)
	srli t2, t1, 0
	sb t2, 27(s3)
	lbu t1, 28(s1)
	lbu t2, 29(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 30(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 31(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 28(s3)
	srli t2, t1, 16
	sb t2, 29(s3)
	srli t2, t1, 8
	sb t2, 30(s3)
	srli t2, t1, 0
	sb t2, 31(s3)
	ld a0, 8(s6)
	addi a1, s6, 320
	addi a2, zero, 32
222:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 222b
	addi a0, s6, 351
	ld a2, 40(s6)
	addi a2, a2, 1
	addi a3, zero, 32
223:
	lbu a1, 0(a0)
	add a1, a1, a2
	sb a1, 0(a0)
	srli a2, a1, 8
	addi a0, a0, -1
	addi a3, a3, -1
	bnez a3, 223b
	addi a0, s6, 384
	lui t0, 434334
	addiw t0, t0, 1639
	sb t0, 0(a0)
	srli t1, t0, 8
	sb t1, 1(a0)
	srli t1, t0, 16
	sb t1, 2(a0)
	srli t1, t0, 24
	sb t1, 3(a0)
	lui t0, 767611
	addiw t0, t0, -379
	sb t0, 4(a0)
	srli t1, t0, 8
	sb t1, 5(a0)
	srli t1, t0, 16
	sb t1, 6(a0)
	srli t1, t0, 24
	sb t1, 7(a0)
	lui t0, 247535
	addiw t0, t0, 882
	sb t0, 8(a0)
	srli t1, t0, 8
	sb t1, 9(a0)
	srli t1, t0, 16
	sb t1, 10(a0)
	srli t1, t0, 24
	sb t1, 11(a0)
	lui t0, 677119
	addiw t0, t0, 1338
	sb t0, 12(a0)
	srli t1, t0, 8
	sb t1, 13(a0)
	srli t1, t0, 16
	sb t1, 14(a0)
	srli t1, t0, 24
	sb t1, 15(a0)
	lui t0, 332005
	addiw t0, t0, 639
	sb t0, 16(a0)
	srli t1, t0, 8
	sb t1, 17(a0)
	srli t1, t0, 16
	sb t1, 18(a0)
	srli t1, t0, 24
	sb t1, 19(a0)
	lui t0, 634967
	addiw t0, t0, -1908
	sb t0, 20(a0)
	srli t1, t0, 8
	sb t1, 21(a0)
	srli t1, t0, 16
	sb t1, 22(a0)
	srli t1, t0, 24
	sb t1, 23(a0)
	lui t0, 129086
	addiw t0, t0, -1621
	sb t0, 24(a0)
	srli t1, t0, 8
	sb t1, 25(a0)
	srli t1, t0, 16
	sb t1, 26(a0)
	srli t1, t0, 24
	sb t1, 27(a0)
	lui t0, 376333
	addiw t0, t0, -743
	sb t0, 28(a0)
	srli t1, t0, 8
	sb t1, 29(a0)
	srli t1, t0, 16
	sb t1, 30(a0)
	srli t1, t0, 24
	sb t1, 31(a0)
	addi a0, s6, 384
	addi a1, s6, 320
	addi a2, zero, 1
	addi a3, s6, 416
	call {vg_sha256_compress}
	addi s1, s6, 384
	addi s3, s6, 896
	lbu t1, 0(s1)
	lbu t2, 1(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 2(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 3(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 0(s3)
	srli t2, t1, 16
	sb t2, 1(s3)
	srli t2, t1, 8
	sb t2, 2(s3)
	srli t2, t1, 0
	sb t2, 3(s3)
	lbu t1, 4(s1)
	lbu t2, 5(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 6(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 7(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 4(s3)
	srli t2, t1, 16
	sb t2, 5(s3)
	srli t2, t1, 8
	sb t2, 6(s3)
	srli t2, t1, 0
	sb t2, 7(s3)
	lbu t1, 8(s1)
	lbu t2, 9(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 10(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 11(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 8(s3)
	srli t2, t1, 16
	sb t2, 9(s3)
	srli t2, t1, 8
	sb t2, 10(s3)
	srli t2, t1, 0
	sb t2, 11(s3)
	lbu t1, 12(s1)
	lbu t2, 13(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 14(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 15(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 12(s3)
	srli t2, t1, 16
	sb t2, 13(s3)
	srli t2, t1, 8
	sb t2, 14(s3)
	srli t2, t1, 0
	sb t2, 15(s3)
	lbu t1, 16(s1)
	lbu t2, 17(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 18(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 19(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 16(s3)
	srli t2, t1, 16
	sb t2, 17(s3)
	srli t2, t1, 8
	sb t2, 18(s3)
	srli t2, t1, 0
	sb t2, 19(s3)
	lbu t1, 20(s1)
	lbu t2, 21(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 22(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 23(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 20(s3)
	srli t2, t1, 16
	sb t2, 21(s3)
	srli t2, t1, 8
	sb t2, 22(s3)
	srli t2, t1, 0
	sb t2, 23(s3)
	lbu t1, 24(s1)
	lbu t2, 25(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 26(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 27(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 24(s3)
	srli t2, t1, 16
	sb t2, 25(s3)
	srli t2, t1, 8
	sb t2, 26(s3)
	srli t2, t1, 0
	sb t2, 27(s3)
	lbu t1, 28(s1)
	lbu t2, 29(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 30(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 31(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 28(s3)
	srli t2, t1, 16
	sb t2, 29(s3)
	srli t2, t1, 8
	sb t2, 30(s3)
	srli t2, t1, 0
	sb t2, 31(s3)
	ld a0, 8(s6)
	addi a1, s6, 320
	addi a2, zero, 32
224:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 224b
	addi a0, s6, 351
	ld a2, 40(s6)
	addi a2, a2, 2
	addi a3, zero, 32
225:
	lbu a1, 0(a0)
	add a1, a1, a2
	sb a1, 0(a0)
	srli a2, a1, 8
	addi a0, a0, -1
	addi a3, a3, -1
	bnez a3, 225b
	addi a0, s6, 384
	lui t0, 434334
	addiw t0, t0, 1639
	sb t0, 0(a0)
	srli t1, t0, 8
	sb t1, 1(a0)
	srli t1, t0, 16
	sb t1, 2(a0)
	srli t1, t0, 24
	sb t1, 3(a0)
	lui t0, 767611
	addiw t0, t0, -379
	sb t0, 4(a0)
	srli t1, t0, 8
	sb t1, 5(a0)
	srli t1, t0, 16
	sb t1, 6(a0)
	srli t1, t0, 24
	sb t1, 7(a0)
	lui t0, 247535
	addiw t0, t0, 882
	sb t0, 8(a0)
	srli t1, t0, 8
	sb t1, 9(a0)
	srli t1, t0, 16
	sb t1, 10(a0)
	srli t1, t0, 24
	sb t1, 11(a0)
	lui t0, 677119
	addiw t0, t0, 1338
	sb t0, 12(a0)
	srli t1, t0, 8
	sb t1, 13(a0)
	srli t1, t0, 16
	sb t1, 14(a0)
	srli t1, t0, 24
	sb t1, 15(a0)
	lui t0, 332005
	addiw t0, t0, 639
	sb t0, 16(a0)
	srli t1, t0, 8
	sb t1, 17(a0)
	srli t1, t0, 16
	sb t1, 18(a0)
	srli t1, t0, 24
	sb t1, 19(a0)
	lui t0, 634967
	addiw t0, t0, -1908
	sb t0, 20(a0)
	srli t1, t0, 8
	sb t1, 21(a0)
	srli t1, t0, 16
	sb t1, 22(a0)
	srli t1, t0, 24
	sb t1, 23(a0)
	lui t0, 129086
	addiw t0, t0, -1621
	sb t0, 24(a0)
	srli t1, t0, 8
	sb t1, 25(a0)
	srli t1, t0, 16
	sb t1, 26(a0)
	srli t1, t0, 24
	sb t1, 27(a0)
	lui t0, 376333
	addiw t0, t0, -743
	sb t0, 28(a0)
	srli t1, t0, 8
	sb t1, 29(a0)
	srli t1, t0, 16
	sb t1, 30(a0)
	srli t1, t0, 24
	sb t1, 31(a0)
	addi a0, s6, 384
	addi a1, s6, 320
	addi a2, zero, 1
	addi a3, s6, 416
	call {vg_sha256_compress}
	addi s1, s6, 384
	addi s3, s6, 864
	lbu t1, 0(s1)
	lbu t2, 1(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 2(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 3(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 0(s3)
	srli t2, t1, 16
	sb t2, 1(s3)
	srli t2, t1, 8
	sb t2, 2(s3)
	srli t2, t1, 0
	sb t2, 3(s3)
	lbu t1, 4(s1)
	lbu t2, 5(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 6(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 7(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 4(s3)
	srli t2, t1, 16
	sb t2, 5(s3)
	srli t2, t1, 8
	sb t2, 6(s3)
	srli t2, t1, 0
	sb t2, 7(s3)
	lbu t1, 8(s1)
	lbu t2, 9(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 10(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 11(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 8(s3)
	srli t2, t1, 16
	sb t2, 9(s3)
	srli t2, t1, 8
	sb t2, 10(s3)
	srli t2, t1, 0
	sb t2, 11(s3)
	lbu t1, 12(s1)
	lbu t2, 13(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 14(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 15(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 12(s3)
	srli t2, t1, 16
	sb t2, 13(s3)
	srli t2, t1, 8
	sb t2, 14(s3)
	srli t2, t1, 0
	sb t2, 15(s3)
	lbu t1, 16(s1)
	lbu t2, 17(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 18(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 19(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 16(s3)
	srli t2, t1, 16
	sb t2, 17(s3)
	srli t2, t1, 8
	sb t2, 18(s3)
	srli t2, t1, 0
	sb t2, 19(s3)
	lbu t1, 20(s1)
	lbu t2, 21(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 22(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 23(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 20(s3)
	srli t2, t1, 16
	sb t2, 21(s3)
	srli t2, t1, 8
	sb t2, 22(s3)
	srli t2, t1, 0
	sb t2, 23(s3)
	lbu t1, 24(s1)
	lbu t2, 25(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 26(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 27(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 24(s3)
	srli t2, t1, 16
	sb t2, 25(s3)
	srli t2, t1, 8
	sb t2, 26(s3)
	srli t2, t1, 0
	sb t2, 27(s3)
	lbu t1, 28(s1)
	lbu t2, 29(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 30(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 31(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 28(s3)
	srli t2, t1, 16
	sb t2, 29(s3)
	srli t2, t1, 8
	sb t2, 30(s3)
	srli t2, t1, 0
	sb t2, 31(s3)
	ld a0, 8(s6)
	addi a1, s6, 320
	addi a2, zero, 32
226:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 226b
	addi a0, s6, 351
	ld a2, 40(s6)
	addi a2, a2, 3
	addi a3, zero, 32
227:
	lbu a1, 0(a0)
	add a1, a1, a2
	sb a1, 0(a0)
	srli a2, a1, 8
	addi a0, a0, -1
	addi a3, a3, -1
	bnez a3, 227b
	addi a0, s6, 384
	lui t0, 434334
	addiw t0, t0, 1639
	sb t0, 0(a0)
	srli t1, t0, 8
	sb t1, 1(a0)
	srli t1, t0, 16
	sb t1, 2(a0)
	srli t1, t0, 24
	sb t1, 3(a0)
	lui t0, 767611
	addiw t0, t0, -379
	sb t0, 4(a0)
	srli t1, t0, 8
	sb t1, 5(a0)
	srli t1, t0, 16
	sb t1, 6(a0)
	srli t1, t0, 24
	sb t1, 7(a0)
	lui t0, 247535
	addiw t0, t0, 882
	sb t0, 8(a0)
	srli t1, t0, 8
	sb t1, 9(a0)
	srli t1, t0, 16
	sb t1, 10(a0)
	srli t1, t0, 24
	sb t1, 11(a0)
	lui t0, 677119
	addiw t0, t0, 1338
	sb t0, 12(a0)
	srli t1, t0, 8
	sb t1, 13(a0)
	srli t1, t0, 16
	sb t1, 14(a0)
	srli t1, t0, 24
	sb t1, 15(a0)
	lui t0, 332005
	addiw t0, t0, 639
	sb t0, 16(a0)
	srli t1, t0, 8
	sb t1, 17(a0)
	srli t1, t0, 16
	sb t1, 18(a0)
	srli t1, t0, 24
	sb t1, 19(a0)
	lui t0, 634967
	addiw t0, t0, -1908
	sb t0, 20(a0)
	srli t1, t0, 8
	sb t1, 21(a0)
	srli t1, t0, 16
	sb t1, 22(a0)
	srli t1, t0, 24
	sb t1, 23(a0)
	lui t0, 129086
	addiw t0, t0, -1621
	sb t0, 24(a0)
	srli t1, t0, 8
	sb t1, 25(a0)
	srli t1, t0, 16
	sb t1, 26(a0)
	srli t1, t0, 24
	sb t1, 27(a0)
	lui t0, 376333
	addiw t0, t0, -743
	sb t0, 28(a0)
	srli t1, t0, 8
	sb t1, 29(a0)
	srli t1, t0, 16
	sb t1, 30(a0)
	srli t1, t0, 24
	sb t1, 31(a0)
	addi a0, s6, 384
	addi a1, s6, 320
	addi a2, zero, 1
	addi a3, s6, 416
	call {vg_sha256_compress}
	addi s1, s6, 384
	addi s3, s6, 832
	lbu t1, 0(s1)
	lbu t2, 1(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 2(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 3(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 0(s3)
	srli t2, t1, 16
	sb t2, 1(s3)
	srli t2, t1, 8
	sb t2, 2(s3)
	srli t2, t1, 0
	sb t2, 3(s3)
	lbu t1, 4(s1)
	lbu t2, 5(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 6(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 7(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 4(s3)
	srli t2, t1, 16
	sb t2, 5(s3)
	srli t2, t1, 8
	sb t2, 6(s3)
	srli t2, t1, 0
	sb t2, 7(s3)
	lbu t1, 8(s1)
	lbu t2, 9(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 10(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 11(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 8(s3)
	srli t2, t1, 16
	sb t2, 9(s3)
	srli t2, t1, 8
	sb t2, 10(s3)
	srli t2, t1, 0
	sb t2, 11(s3)
	lbu t1, 12(s1)
	lbu t2, 13(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 14(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 15(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 12(s3)
	srli t2, t1, 16
	sb t2, 13(s3)
	srli t2, t1, 8
	sb t2, 14(s3)
	srli t2, t1, 0
	sb t2, 15(s3)
	lbu t1, 16(s1)
	lbu t2, 17(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 18(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 19(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 16(s3)
	srli t2, t1, 16
	sb t2, 17(s3)
	srli t2, t1, 8
	sb t2, 18(s3)
	srli t2, t1, 0
	sb t2, 19(s3)
	lbu t1, 20(s1)
	lbu t2, 21(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 22(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 23(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 20(s3)
	srli t2, t1, 16
	sb t2, 21(s3)
	srli t2, t1, 8
	sb t2, 22(s3)
	srli t2, t1, 0
	sb t2, 23(s3)
	lbu t1, 24(s1)
	lbu t2, 25(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 26(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 27(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 24(s3)
	srli t2, t1, 16
	sb t2, 25(s3)
	srli t2, t1, 8
	sb t2, 26(s3)
	srli t2, t1, 0
	sb t2, 27(s3)
	lbu t1, 28(s1)
	lbu t2, 29(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 30(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 31(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 28(s3)
	srli t2, t1, 16
	sb t2, 29(s3)
	srli t2, t1, 8
	sb t2, 30(s3)
	srli t2, t1, 0
	sb t2, 31(s3)
	ld a0, 8(s6)
	addi a1, s6, 320
	addi a2, zero, 32
228:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 228b
	addi a0, s6, 351
	ld a2, 40(s6)
	addi a2, a2, 4
	addi a3, zero, 32
229:
	lbu a1, 0(a0)
	add a1, a1, a2
	sb a1, 0(a0)
	srli a2, a1, 8
	addi a0, a0, -1
	addi a3, a3, -1
	bnez a3, 229b
	addi a0, s6, 384
	lui t0, 434334
	addiw t0, t0, 1639
	sb t0, 0(a0)
	srli t1, t0, 8
	sb t1, 1(a0)
	srli t1, t0, 16
	sb t1, 2(a0)
	srli t1, t0, 24
	sb t1, 3(a0)
	lui t0, 767611
	addiw t0, t0, -379
	sb t0, 4(a0)
	srli t1, t0, 8
	sb t1, 5(a0)
	srli t1, t0, 16
	sb t1, 6(a0)
	srli t1, t0, 24
	sb t1, 7(a0)
	lui t0, 247535
	addiw t0, t0, 882
	sb t0, 8(a0)
	srli t1, t0, 8
	sb t1, 9(a0)
	srli t1, t0, 16
	sb t1, 10(a0)
	srli t1, t0, 24
	sb t1, 11(a0)
	lui t0, 677119
	addiw t0, t0, 1338
	sb t0, 12(a0)
	srli t1, t0, 8
	sb t1, 13(a0)
	srli t1, t0, 16
	sb t1, 14(a0)
	srli t1, t0, 24
	sb t1, 15(a0)
	lui t0, 332005
	addiw t0, t0, 639
	sb t0, 16(a0)
	srli t1, t0, 8
	sb t1, 17(a0)
	srli t1, t0, 16
	sb t1, 18(a0)
	srli t1, t0, 24
	sb t1, 19(a0)
	lui t0, 634967
	addiw t0, t0, -1908
	sb t0, 20(a0)
	srli t1, t0, 8
	sb t1, 21(a0)
	srli t1, t0, 16
	sb t1, 22(a0)
	srli t1, t0, 24
	sb t1, 23(a0)
	lui t0, 129086
	addiw t0, t0, -1621
	sb t0, 24(a0)
	srli t1, t0, 8
	sb t1, 25(a0)
	srli t1, t0, 16
	sb t1, 26(a0)
	srli t1, t0, 24
	sb t1, 27(a0)
	lui t0, 376333
	addiw t0, t0, -743
	sb t0, 28(a0)
	srli t1, t0, 8
	sb t1, 29(a0)
	srli t1, t0, 16
	sb t1, 30(a0)
	srli t1, t0, 24
	sb t1, 31(a0)
	addi a0, s6, 384
	addi a1, s6, 320
	addi a2, zero, 1
	addi a3, s6, 416
	call {vg_sha256_compress}
	addi s1, s6, 384
	addi s3, s6, 800
	lbu t1, 0(s1)
	lbu t2, 1(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 2(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 3(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 0(s3)
	srli t2, t1, 16
	sb t2, 1(s3)
	srli t2, t1, 8
	sb t2, 2(s3)
	srli t2, t1, 0
	sb t2, 3(s3)
	lbu t1, 4(s1)
	lbu t2, 5(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 6(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 7(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 4(s3)
	srli t2, t1, 16
	sb t2, 5(s3)
	srli t2, t1, 8
	sb t2, 6(s3)
	srli t2, t1, 0
	sb t2, 7(s3)
	lbu t1, 8(s1)
	lbu t2, 9(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 10(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 11(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 8(s3)
	srli t2, t1, 16
	sb t2, 9(s3)
	srli t2, t1, 8
	sb t2, 10(s3)
	srli t2, t1, 0
	sb t2, 11(s3)
	lbu t1, 12(s1)
	lbu t2, 13(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 14(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 15(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 12(s3)
	srli t2, t1, 16
	sb t2, 13(s3)
	srli t2, t1, 8
	sb t2, 14(s3)
	srli t2, t1, 0
	sb t2, 15(s3)
	lbu t1, 16(s1)
	lbu t2, 17(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 18(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 19(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 16(s3)
	srli t2, t1, 16
	sb t2, 17(s3)
	srli t2, t1, 8
	sb t2, 18(s3)
	srli t2, t1, 0
	sb t2, 19(s3)
	lbu t1, 20(s1)
	lbu t2, 21(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 22(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 23(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 20(s3)
	srli t2, t1, 16
	sb t2, 21(s3)
	srli t2, t1, 8
	sb t2, 22(s3)
	srli t2, t1, 0
	sb t2, 23(s3)
	lbu t1, 24(s1)
	lbu t2, 25(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 26(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 27(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 24(s3)
	srli t2, t1, 16
	sb t2, 25(s3)
	srli t2, t1, 8
	sb t2, 26(s3)
	srli t2, t1, 0
	sb t2, 27(s3)
	lbu t1, 28(s1)
	lbu t2, 29(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 30(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 31(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 28(s3)
	srli t2, t1, 16
	sb t2, 29(s3)
	srli t2, t1, 8
	sb t2, 30(s3)
	srli t2, t1, 0
	sb t2, 31(s3)
	ld a0, 8(s6)
	addi a1, s6, 320
	addi a2, zero, 32
230:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 230b
	addi a0, s6, 351
	ld a2, 40(s6)
	addi a2, a2, 5
	addi a3, zero, 32
231:
	lbu a1, 0(a0)
	add a1, a1, a2
	sb a1, 0(a0)
	srli a2, a1, 8
	addi a0, a0, -1
	addi a3, a3, -1
	bnez a3, 231b
	addi a0, s6, 384
	lui t0, 434334
	addiw t0, t0, 1639
	sb t0, 0(a0)
	srli t1, t0, 8
	sb t1, 1(a0)
	srli t1, t0, 16
	sb t1, 2(a0)
	srli t1, t0, 24
	sb t1, 3(a0)
	lui t0, 767611
	addiw t0, t0, -379
	sb t0, 4(a0)
	srli t1, t0, 8
	sb t1, 5(a0)
	srli t1, t0, 16
	sb t1, 6(a0)
	srli t1, t0, 24
	sb t1, 7(a0)
	lui t0, 247535
	addiw t0, t0, 882
	sb t0, 8(a0)
	srli t1, t0, 8
	sb t1, 9(a0)
	srli t1, t0, 16
	sb t1, 10(a0)
	srli t1, t0, 24
	sb t1, 11(a0)
	lui t0, 677119
	addiw t0, t0, 1338
	sb t0, 12(a0)
	srli t1, t0, 8
	sb t1, 13(a0)
	srli t1, t0, 16
	sb t1, 14(a0)
	srli t1, t0, 24
	sb t1, 15(a0)
	lui t0, 332005
	addiw t0, t0, 639
	sb t0, 16(a0)
	srli t1, t0, 8
	sb t1, 17(a0)
	srli t1, t0, 16
	sb t1, 18(a0)
	srli t1, t0, 24
	sb t1, 19(a0)
	lui t0, 634967
	addiw t0, t0, -1908
	sb t0, 20(a0)
	srli t1, t0, 8
	sb t1, 21(a0)
	srli t1, t0, 16
	sb t1, 22(a0)
	srli t1, t0, 24
	sb t1, 23(a0)
	lui t0, 129086
	addiw t0, t0, -1621
	sb t0, 24(a0)
	srli t1, t0, 8
	sb t1, 25(a0)
	srli t1, t0, 16
	sb t1, 26(a0)
	srli t1, t0, 24
	sb t1, 27(a0)
	lui t0, 376333
	addiw t0, t0, -743
	sb t0, 28(a0)
	srli t1, t0, 8
	sb t1, 29(a0)
	srli t1, t0, 16
	sb t1, 30(a0)
	srli t1, t0, 24
	sb t1, 31(a0)
	addi a0, s6, 384
	addi a1, s6, 320
	addi a2, zero, 1
	addi a3, s6, 416
	call {vg_sha256_compress}
	addi s1, s6, 384
	addi s3, s6, 768
	lbu t1, 0(s1)
	lbu t2, 1(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 2(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 3(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 0(s3)
	srli t2, t1, 16
	sb t2, 1(s3)
	srli t2, t1, 8
	sb t2, 2(s3)
	srli t2, t1, 0
	sb t2, 3(s3)
	lbu t1, 4(s1)
	lbu t2, 5(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 6(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 7(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 4(s3)
	srli t2, t1, 16
	sb t2, 5(s3)
	srli t2, t1, 8
	sb t2, 6(s3)
	srli t2, t1, 0
	sb t2, 7(s3)
	lbu t1, 8(s1)
	lbu t2, 9(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 10(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 11(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 8(s3)
	srli t2, t1, 16
	sb t2, 9(s3)
	srli t2, t1, 8
	sb t2, 10(s3)
	srli t2, t1, 0
	sb t2, 11(s3)
	lbu t1, 12(s1)
	lbu t2, 13(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 14(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 15(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 12(s3)
	srli t2, t1, 16
	sb t2, 13(s3)
	srli t2, t1, 8
	sb t2, 14(s3)
	srli t2, t1, 0
	sb t2, 15(s3)
	lbu t1, 16(s1)
	lbu t2, 17(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 18(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 19(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 16(s3)
	srli t2, t1, 16
	sb t2, 17(s3)
	srli t2, t1, 8
	sb t2, 18(s3)
	srli t2, t1, 0
	sb t2, 19(s3)
	lbu t1, 20(s1)
	lbu t2, 21(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 22(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 23(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 20(s3)
	srli t2, t1, 16
	sb t2, 21(s3)
	srli t2, t1, 8
	sb t2, 22(s3)
	srli t2, t1, 0
	sb t2, 23(s3)
	lbu t1, 24(s1)
	lbu t2, 25(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 26(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 27(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 24(s3)
	srli t2, t1, 16
	sb t2, 25(s3)
	srli t2, t1, 8
	sb t2, 26(s3)
	srli t2, t1, 0
	sb t2, 27(s3)
	lbu t1, 28(s1)
	lbu t2, 29(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 30(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 31(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 28(s3)
	srli t2, t1, 16
	sb t2, 29(s3)
	srli t2, t1, 8
	sb t2, 30(s3)
	srli t2, t1, 0
	sb t2, 31(s3)
	ld a0, 8(s6)
	addi a1, s6, 320
	addi a2, zero, 32
232:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 232b
	addi a0, s6, 351
	ld a2, 40(s6)
	addi a2, a2, 6
	addi a3, zero, 32
233:
	lbu a1, 0(a0)
	add a1, a1, a2
	sb a1, 0(a0)
	srli a2, a1, 8
	addi a0, a0, -1
	addi a3, a3, -1
	bnez a3, 233b
	addi a0, s6, 384
	lui t0, 434334
	addiw t0, t0, 1639
	sb t0, 0(a0)
	srli t1, t0, 8
	sb t1, 1(a0)
	srli t1, t0, 16
	sb t1, 2(a0)
	srli t1, t0, 24
	sb t1, 3(a0)
	lui t0, 767611
	addiw t0, t0, -379
	sb t0, 4(a0)
	srli t1, t0, 8
	sb t1, 5(a0)
	srli t1, t0, 16
	sb t1, 6(a0)
	srli t1, t0, 24
	sb t1, 7(a0)
	lui t0, 247535
	addiw t0, t0, 882
	sb t0, 8(a0)
	srli t1, t0, 8
	sb t1, 9(a0)
	srli t1, t0, 16
	sb t1, 10(a0)
	srli t1, t0, 24
	sb t1, 11(a0)
	lui t0, 677119
	addiw t0, t0, 1338
	sb t0, 12(a0)
	srli t1, t0, 8
	sb t1, 13(a0)
	srli t1, t0, 16
	sb t1, 14(a0)
	srli t1, t0, 24
	sb t1, 15(a0)
	lui t0, 332005
	addiw t0, t0, 639
	sb t0, 16(a0)
	srli t1, t0, 8
	sb t1, 17(a0)
	srli t1, t0, 16
	sb t1, 18(a0)
	srli t1, t0, 24
	sb t1, 19(a0)
	lui t0, 634967
	addiw t0, t0, -1908
	sb t0, 20(a0)
	srli t1, t0, 8
	sb t1, 21(a0)
	srli t1, t0, 16
	sb t1, 22(a0)
	srli t1, t0, 24
	sb t1, 23(a0)
	lui t0, 129086
	addiw t0, t0, -1621
	sb t0, 24(a0)
	srli t1, t0, 8
	sb t1, 25(a0)
	srli t1, t0, 16
	sb t1, 26(a0)
	srli t1, t0, 24
	sb t1, 27(a0)
	lui t0, 376333
	addiw t0, t0, -743
	sb t0, 28(a0)
	srli t1, t0, 8
	sb t1, 29(a0)
	srli t1, t0, 16
	sb t1, 30(a0)
	srli t1, t0, 24
	sb t1, 31(a0)
	addi a0, s6, 384
	addi a1, s6, 320
	addi a2, zero, 1
	addi a3, s6, 416
	call {vg_sha256_compress}
	addi s1, s6, 384
	addi s3, s6, 736
	lbu t1, 0(s1)
	lbu t2, 1(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 2(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 3(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 0(s3)
	srli t2, t1, 16
	sb t2, 1(s3)
	srli t2, t1, 8
	sb t2, 2(s3)
	srli t2, t1, 0
	sb t2, 3(s3)
	lbu t1, 4(s1)
	lbu t2, 5(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 6(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 7(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 4(s3)
	srli t2, t1, 16
	sb t2, 5(s3)
	srli t2, t1, 8
	sb t2, 6(s3)
	srli t2, t1, 0
	sb t2, 7(s3)
	lbu t1, 8(s1)
	lbu t2, 9(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 10(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 11(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 8(s3)
	srli t2, t1, 16
	sb t2, 9(s3)
	srli t2, t1, 8
	sb t2, 10(s3)
	srli t2, t1, 0
	sb t2, 11(s3)
	lbu t1, 12(s1)
	lbu t2, 13(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 14(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 15(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 12(s3)
	srli t2, t1, 16
	sb t2, 13(s3)
	srli t2, t1, 8
	sb t2, 14(s3)
	srli t2, t1, 0
	sb t2, 15(s3)
	lbu t1, 16(s1)
	lbu t2, 17(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 18(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 19(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 16(s3)
	srli t2, t1, 16
	sb t2, 17(s3)
	srli t2, t1, 8
	sb t2, 18(s3)
	srli t2, t1, 0
	sb t2, 19(s3)
	lbu t1, 20(s1)
	lbu t2, 21(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 22(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 23(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 20(s3)
	srli t2, t1, 16
	sb t2, 21(s3)
	srli t2, t1, 8
	sb t2, 22(s3)
	srli t2, t1, 0
	sb t2, 23(s3)
	lbu t1, 24(s1)
	lbu t2, 25(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 26(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 27(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 24(s3)
	srli t2, t1, 16
	sb t2, 25(s3)
	srli t2, t1, 8
	sb t2, 26(s3)
	srli t2, t1, 0
	sb t2, 27(s3)
	lbu t1, 28(s1)
	lbu t2, 29(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 30(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 31(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 28(s3)
	srli t2, t1, 16
	sb t2, 29(s3)
	srli t2, t1, 8
	sb t2, 30(s3)
	srli t2, t1, 0
	sb t2, 31(s3)
	ld a0, 8(s6)
	addi a1, s6, 320
	addi a2, zero, 32
234:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 234b
	addi a0, s6, 351
	ld a2, 40(s6)
	addi a2, a2, 7
	addi a3, zero, 32
235:
	lbu a1, 0(a0)
	add a1, a1, a2
	sb a1, 0(a0)
	srli a2, a1, 8
	addi a0, a0, -1
	addi a3, a3, -1
	bnez a3, 235b
	addi a0, s6, 384
	lui t0, 434334
	addiw t0, t0, 1639
	sb t0, 0(a0)
	srli t1, t0, 8
	sb t1, 1(a0)
	srli t1, t0, 16
	sb t1, 2(a0)
	srli t1, t0, 24
	sb t1, 3(a0)
	lui t0, 767611
	addiw t0, t0, -379
	sb t0, 4(a0)
	srli t1, t0, 8
	sb t1, 5(a0)
	srli t1, t0, 16
	sb t1, 6(a0)
	srli t1, t0, 24
	sb t1, 7(a0)
	lui t0, 247535
	addiw t0, t0, 882
	sb t0, 8(a0)
	srli t1, t0, 8
	sb t1, 9(a0)
	srli t1, t0, 16
	sb t1, 10(a0)
	srli t1, t0, 24
	sb t1, 11(a0)
	lui t0, 677119
	addiw t0, t0, 1338
	sb t0, 12(a0)
	srli t1, t0, 8
	sb t1, 13(a0)
	srli t1, t0, 16
	sb t1, 14(a0)
	srli t1, t0, 24
	sb t1, 15(a0)
	lui t0, 332005
	addiw t0, t0, 639
	sb t0, 16(a0)
	srli t1, t0, 8
	sb t1, 17(a0)
	srli t1, t0, 16
	sb t1, 18(a0)
	srli t1, t0, 24
	sb t1, 19(a0)
	lui t0, 634967
	addiw t0, t0, -1908
	sb t0, 20(a0)
	srli t1, t0, 8
	sb t1, 21(a0)
	srli t1, t0, 16
	sb t1, 22(a0)
	srli t1, t0, 24
	sb t1, 23(a0)
	lui t0, 129086
	addiw t0, t0, -1621
	sb t0, 24(a0)
	srli t1, t0, 8
	sb t1, 25(a0)
	srli t1, t0, 16
	sb t1, 26(a0)
	srli t1, t0, 24
	sb t1, 27(a0)
	lui t0, 376333
	addiw t0, t0, -743
	sb t0, 28(a0)
	srli t1, t0, 8
	sb t1, 29(a0)
	srli t1, t0, 16
	sb t1, 30(a0)
	srli t1, t0, 24
	sb t1, 31(a0)
	addi a0, s6, 384
	addi a1, s6, 320
	addi a2, zero, 1
	addi a3, s6, 416
	call {vg_sha256_compress}
	addi s1, s6, 384
	addi s3, s6, 704
	lbu t1, 0(s1)
	lbu t2, 1(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 2(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 3(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 0(s3)
	srli t2, t1, 16
	sb t2, 1(s3)
	srli t2, t1, 8
	sb t2, 2(s3)
	srli t2, t1, 0
	sb t2, 3(s3)
	lbu t1, 4(s1)
	lbu t2, 5(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 6(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 7(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 4(s3)
	srli t2, t1, 16
	sb t2, 5(s3)
	srli t2, t1, 8
	sb t2, 6(s3)
	srli t2, t1, 0
	sb t2, 7(s3)
	lbu t1, 8(s1)
	lbu t2, 9(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 10(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 11(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 8(s3)
	srli t2, t1, 16
	sb t2, 9(s3)
	srli t2, t1, 8
	sb t2, 10(s3)
	srli t2, t1, 0
	sb t2, 11(s3)
	lbu t1, 12(s1)
	lbu t2, 13(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 14(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 15(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 12(s3)
	srli t2, t1, 16
	sb t2, 13(s3)
	srli t2, t1, 8
	sb t2, 14(s3)
	srli t2, t1, 0
	sb t2, 15(s3)
	lbu t1, 16(s1)
	lbu t2, 17(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 18(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 19(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 16(s3)
	srli t2, t1, 16
	sb t2, 17(s3)
	srli t2, t1, 8
	sb t2, 18(s3)
	srli t2, t1, 0
	sb t2, 19(s3)
	lbu t1, 20(s1)
	lbu t2, 21(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 22(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 23(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 20(s3)
	srli t2, t1, 16
	sb t2, 21(s3)
	srli t2, t1, 8
	sb t2, 22(s3)
	srli t2, t1, 0
	sb t2, 23(s3)
	lbu t1, 24(s1)
	lbu t2, 25(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 26(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 27(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 24(s3)
	srli t2, t1, 16
	sb t2, 25(s3)
	srli t2, t1, 8
	sb t2, 26(s3)
	srli t2, t1, 0
	sb t2, 27(s3)
	lbu t1, 28(s1)
	lbu t2, 29(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 30(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 31(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 28(s3)
	srli t2, t1, 16
	sb t2, 29(s3)
	srli t2, t1, 8
	sb t2, 30(s3)
	srli t2, t1, 0
	sb t2, 31(s3)
	ld a0, 8(s6)
	addi a1, s6, 320
	addi a2, zero, 32
236:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 236b
	addi a0, s6, 351
	ld a2, 40(s6)
	addi a2, a2, 8
	addi a3, zero, 32
237:
	lbu a1, 0(a0)
	add a1, a1, a2
	sb a1, 0(a0)
	srli a2, a1, 8
	addi a0, a0, -1
	addi a3, a3, -1
	bnez a3, 237b
	addi a0, s6, 384
	lui t0, 434334
	addiw t0, t0, 1639
	sb t0, 0(a0)
	srli t1, t0, 8
	sb t1, 1(a0)
	srli t1, t0, 16
	sb t1, 2(a0)
	srli t1, t0, 24
	sb t1, 3(a0)
	lui t0, 767611
	addiw t0, t0, -379
	sb t0, 4(a0)
	srli t1, t0, 8
	sb t1, 5(a0)
	srli t1, t0, 16
	sb t1, 6(a0)
	srli t1, t0, 24
	sb t1, 7(a0)
	lui t0, 247535
	addiw t0, t0, 882
	sb t0, 8(a0)
	srli t1, t0, 8
	sb t1, 9(a0)
	srli t1, t0, 16
	sb t1, 10(a0)
	srli t1, t0, 24
	sb t1, 11(a0)
	lui t0, 677119
	addiw t0, t0, 1338
	sb t0, 12(a0)
	srli t1, t0, 8
	sb t1, 13(a0)
	srli t1, t0, 16
	sb t1, 14(a0)
	srli t1, t0, 24
	sb t1, 15(a0)
	lui t0, 332005
	addiw t0, t0, 639
	sb t0, 16(a0)
	srli t1, t0, 8
	sb t1, 17(a0)
	srli t1, t0, 16
	sb t1, 18(a0)
	srli t1, t0, 24
	sb t1, 19(a0)
	lui t0, 634967
	addiw t0, t0, -1908
	sb t0, 20(a0)
	srli t1, t0, 8
	sb t1, 21(a0)
	srli t1, t0, 16
	sb t1, 22(a0)
	srli t1, t0, 24
	sb t1, 23(a0)
	lui t0, 129086
	addiw t0, t0, -1621
	sb t0, 24(a0)
	srli t1, t0, 8
	sb t1, 25(a0)
	srli t1, t0, 16
	sb t1, 26(a0)
	srli t1, t0, 24
	sb t1, 27(a0)
	lui t0, 376333
	addiw t0, t0, -743
	sb t0, 28(a0)
	srli t1, t0, 8
	sb t1, 29(a0)
	srli t1, t0, 16
	sb t1, 30(a0)
	srli t1, t0, 24
	sb t1, 31(a0)
	addi a0, s6, 384
	addi a1, s6, 320
	addi a2, zero, 1
	addi a3, s6, 416
	call {vg_sha256_compress}
	addi s1, s6, 384
	addi s3, s6, 672
	lbu t1, 0(s1)
	lbu t2, 1(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 2(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 3(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 0(s3)
	srli t2, t1, 16
	sb t2, 1(s3)
	srli t2, t1, 8
	sb t2, 2(s3)
	srli t2, t1, 0
	sb t2, 3(s3)
	lbu t1, 4(s1)
	lbu t2, 5(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 6(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 7(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 4(s3)
	srli t2, t1, 16
	sb t2, 5(s3)
	srli t2, t1, 8
	sb t2, 6(s3)
	srli t2, t1, 0
	sb t2, 7(s3)
	lbu t1, 8(s1)
	lbu t2, 9(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 10(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 11(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 8(s3)
	srli t2, t1, 16
	sb t2, 9(s3)
	srli t2, t1, 8
	sb t2, 10(s3)
	srli t2, t1, 0
	sb t2, 11(s3)
	lbu t1, 12(s1)
	lbu t2, 13(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 14(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 15(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 12(s3)
	srli t2, t1, 16
	sb t2, 13(s3)
	srli t2, t1, 8
	sb t2, 14(s3)
	srli t2, t1, 0
	sb t2, 15(s3)
	lbu t1, 16(s1)
	lbu t2, 17(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 18(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 19(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 16(s3)
	srli t2, t1, 16
	sb t2, 17(s3)
	srli t2, t1, 8
	sb t2, 18(s3)
	srli t2, t1, 0
	sb t2, 19(s3)
	lbu t1, 20(s1)
	lbu t2, 21(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 22(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 23(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 20(s3)
	srli t2, t1, 16
	sb t2, 21(s3)
	srli t2, t1, 8
	sb t2, 22(s3)
	srli t2, t1, 0
	sb t2, 23(s3)
	lbu t1, 24(s1)
	lbu t2, 25(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 26(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 27(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 24(s3)
	srli t2, t1, 16
	sb t2, 25(s3)
	srli t2, t1, 8
	sb t2, 26(s3)
	srli t2, t1, 0
	sb t2, 27(s3)
	lbu t1, 28(s1)
	lbu t2, 29(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 30(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 31(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 28(s3)
	srli t2, t1, 16
	sb t2, 29(s3)
	srli t2, t1, 8
	sb t2, 30(s3)
	srli t2, t1, 0
	sb t2, 31(s3)
	ld a0, 8(s6)
	addi a1, s6, 320
	addi a2, zero, 32
238:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 238b
	addi a0, s6, 351
	ld a2, 40(s6)
	addi a2, a2, 9
	addi a3, zero, 32
239:
	lbu a1, 0(a0)
	add a1, a1, a2
	sb a1, 0(a0)
	srli a2, a1, 8
	addi a0, a0, -1
	addi a3, a3, -1
	bnez a3, 239b
	addi a0, s6, 384
	lui t0, 434334
	addiw t0, t0, 1639
	sb t0, 0(a0)
	srli t1, t0, 8
	sb t1, 1(a0)
	srli t1, t0, 16
	sb t1, 2(a0)
	srli t1, t0, 24
	sb t1, 3(a0)
	lui t0, 767611
	addiw t0, t0, -379
	sb t0, 4(a0)
	srli t1, t0, 8
	sb t1, 5(a0)
	srli t1, t0, 16
	sb t1, 6(a0)
	srli t1, t0, 24
	sb t1, 7(a0)
	lui t0, 247535
	addiw t0, t0, 882
	sb t0, 8(a0)
	srli t1, t0, 8
	sb t1, 9(a0)
	srli t1, t0, 16
	sb t1, 10(a0)
	srli t1, t0, 24
	sb t1, 11(a0)
	lui t0, 677119
	addiw t0, t0, 1338
	sb t0, 12(a0)
	srli t1, t0, 8
	sb t1, 13(a0)
	srli t1, t0, 16
	sb t1, 14(a0)
	srli t1, t0, 24
	sb t1, 15(a0)
	lui t0, 332005
	addiw t0, t0, 639
	sb t0, 16(a0)
	srli t1, t0, 8
	sb t1, 17(a0)
	srli t1, t0, 16
	sb t1, 18(a0)
	srli t1, t0, 24
	sb t1, 19(a0)
	lui t0, 634967
	addiw t0, t0, -1908
	sb t0, 20(a0)
	srli t1, t0, 8
	sb t1, 21(a0)
	srli t1, t0, 16
	sb t1, 22(a0)
	srli t1, t0, 24
	sb t1, 23(a0)
	lui t0, 129086
	addiw t0, t0, -1621
	sb t0, 24(a0)
	srli t1, t0, 8
	sb t1, 25(a0)
	srli t1, t0, 16
	sb t1, 26(a0)
	srli t1, t0, 24
	sb t1, 27(a0)
	lui t0, 376333
	addiw t0, t0, -743
	sb t0, 28(a0)
	srli t1, t0, 8
	sb t1, 29(a0)
	srli t1, t0, 16
	sb t1, 30(a0)
	srli t1, t0, 24
	sb t1, 31(a0)
	addi a0, s6, 384
	addi a1, s6, 320
	addi a2, zero, 1
	addi a3, s6, 416
	call {vg_sha256_compress}
	addi s1, s6, 384
	addi s3, s6, 640
	lbu t1, 0(s1)
	lbu t2, 1(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 2(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 3(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 0(s3)
	srli t2, t1, 16
	sb t2, 1(s3)
	srli t2, t1, 8
	sb t2, 2(s3)
	srli t2, t1, 0
	sb t2, 3(s3)
	lbu t1, 4(s1)
	lbu t2, 5(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 6(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 7(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 4(s3)
	srli t2, t1, 16
	sb t2, 5(s3)
	srli t2, t1, 8
	sb t2, 6(s3)
	srli t2, t1, 0
	sb t2, 7(s3)
	lbu t1, 8(s1)
	lbu t2, 9(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 10(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 11(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 8(s3)
	srli t2, t1, 16
	sb t2, 9(s3)
	srli t2, t1, 8
	sb t2, 10(s3)
	srli t2, t1, 0
	sb t2, 11(s3)
	lbu t1, 12(s1)
	lbu t2, 13(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 14(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 15(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 12(s3)
	srli t2, t1, 16
	sb t2, 13(s3)
	srli t2, t1, 8
	sb t2, 14(s3)
	srli t2, t1, 0
	sb t2, 15(s3)
	lbu t1, 16(s1)
	lbu t2, 17(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 18(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 19(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 16(s3)
	srli t2, t1, 16
	sb t2, 17(s3)
	srli t2, t1, 8
	sb t2, 18(s3)
	srli t2, t1, 0
	sb t2, 19(s3)
	lbu t1, 20(s1)
	lbu t2, 21(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 22(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 23(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 20(s3)
	srli t2, t1, 16
	sb t2, 21(s3)
	srli t2, t1, 8
	sb t2, 22(s3)
	srli t2, t1, 0
	sb t2, 23(s3)
	lbu t1, 24(s1)
	lbu t2, 25(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 26(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 27(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 24(s3)
	srli t2, t1, 16
	sb t2, 25(s3)
	srli t2, t1, 8
	sb t2, 26(s3)
	srli t2, t1, 0
	sb t2, 27(s3)
	lbu t1, 28(s1)
	lbu t2, 29(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 30(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 31(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 28(s3)
	srli t2, t1, 16
	sb t2, 29(s3)
	srli t2, t1, 8
	sb t2, 30(s3)
	srli t2, t1, 0
	sb t2, 31(s3)
	ld a0, 8(s6)
	addi a1, s6, 320
	addi a2, zero, 32
240:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 240b
	addi a0, s6, 351
	ld a2, 40(s6)
	addi a2, a2, 10
	addi a3, zero, 32
241:
	lbu a1, 0(a0)
	add a1, a1, a2
	sb a1, 0(a0)
	srli a2, a1, 8
	addi a0, a0, -1
	addi a3, a3, -1
	bnez a3, 241b
	addi a0, s6, 384
	lui t0, 434334
	addiw t0, t0, 1639
	sb t0, 0(a0)
	srli t1, t0, 8
	sb t1, 1(a0)
	srli t1, t0, 16
	sb t1, 2(a0)
	srli t1, t0, 24
	sb t1, 3(a0)
	lui t0, 767611
	addiw t0, t0, -379
	sb t0, 4(a0)
	srli t1, t0, 8
	sb t1, 5(a0)
	srli t1, t0, 16
	sb t1, 6(a0)
	srli t1, t0, 24
	sb t1, 7(a0)
	lui t0, 247535
	addiw t0, t0, 882
	sb t0, 8(a0)
	srli t1, t0, 8
	sb t1, 9(a0)
	srli t1, t0, 16
	sb t1, 10(a0)
	srli t1, t0, 24
	sb t1, 11(a0)
	lui t0, 677119
	addiw t0, t0, 1338
	sb t0, 12(a0)
	srli t1, t0, 8
	sb t1, 13(a0)
	srli t1, t0, 16
	sb t1, 14(a0)
	srli t1, t0, 24
	sb t1, 15(a0)
	lui t0, 332005
	addiw t0, t0, 639
	sb t0, 16(a0)
	srli t1, t0, 8
	sb t1, 17(a0)
	srli t1, t0, 16
	sb t1, 18(a0)
	srli t1, t0, 24
	sb t1, 19(a0)
	lui t0, 634967
	addiw t0, t0, -1908
	sb t0, 20(a0)
	srli t1, t0, 8
	sb t1, 21(a0)
	srli t1, t0, 16
	sb t1, 22(a0)
	srli t1, t0, 24
	sb t1, 23(a0)
	lui t0, 129086
	addiw t0, t0, -1621
	sb t0, 24(a0)
	srli t1, t0, 8
	sb t1, 25(a0)
	srli t1, t0, 16
	sb t1, 26(a0)
	srli t1, t0, 24
	sb t1, 27(a0)
	lui t0, 376333
	addiw t0, t0, -743
	sb t0, 28(a0)
	srli t1, t0, 8
	sb t1, 29(a0)
	srli t1, t0, 16
	sb t1, 30(a0)
	srli t1, t0, 24
	sb t1, 31(a0)
	addi a0, s6, 384
	addi a1, s6, 320
	addi a2, zero, 1
	addi a3, s6, 416
	call {vg_sha256_compress}
	addi s1, s6, 384
	addi s3, s6, 608
	lbu t1, 0(s1)
	lbu t2, 1(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 2(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 3(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 0(s3)
	srli t2, t1, 16
	sb t2, 1(s3)
	srli t2, t1, 8
	sb t2, 2(s3)
	srli t2, t1, 0
	sb t2, 3(s3)
	lbu t1, 4(s1)
	lbu t2, 5(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 6(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 7(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 4(s3)
	srli t2, t1, 16
	sb t2, 5(s3)
	srli t2, t1, 8
	sb t2, 6(s3)
	srli t2, t1, 0
	sb t2, 7(s3)
	lbu t1, 8(s1)
	lbu t2, 9(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 10(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 11(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 8(s3)
	srli t2, t1, 16
	sb t2, 9(s3)
	srli t2, t1, 8
	sb t2, 10(s3)
	srli t2, t1, 0
	sb t2, 11(s3)
	lbu t1, 12(s1)
	lbu t2, 13(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 14(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 15(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 12(s3)
	srli t2, t1, 16
	sb t2, 13(s3)
	srli t2, t1, 8
	sb t2, 14(s3)
	srli t2, t1, 0
	sb t2, 15(s3)
	lbu t1, 16(s1)
	lbu t2, 17(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 18(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 19(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 16(s3)
	srli t2, t1, 16
	sb t2, 17(s3)
	srli t2, t1, 8
	sb t2, 18(s3)
	srli t2, t1, 0
	sb t2, 19(s3)
	lbu t1, 20(s1)
	lbu t2, 21(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 22(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 23(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 20(s3)
	srli t2, t1, 16
	sb t2, 21(s3)
	srli t2, t1, 8
	sb t2, 22(s3)
	srli t2, t1, 0
	sb t2, 23(s3)
	lbu t1, 24(s1)
	lbu t2, 25(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 26(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 27(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 24(s3)
	srli t2, t1, 16
	sb t2, 25(s3)
	srli t2, t1, 8
	sb t2, 26(s3)
	srli t2, t1, 0
	sb t2, 27(s3)
	lbu t1, 28(s1)
	lbu t2, 29(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 30(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 31(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 28(s3)
	srli t2, t1, 16
	sb t2, 29(s3)
	srli t2, t1, 8
	sb t2, 30(s3)
	srli t2, t1, 0
	sb t2, 31(s3)
	ld a0, 8(s6)
	addi a1, s6, 320
	addi a2, zero, 32
242:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 242b
	addi a0, s6, 351
	ld a2, 40(s6)
	addi a2, a2, 11
	addi a3, zero, 32
243:
	lbu a1, 0(a0)
	add a1, a1, a2
	sb a1, 0(a0)
	srli a2, a1, 8
	addi a0, a0, -1
	addi a3, a3, -1
	bnez a3, 243b
	addi a0, s6, 384
	lui t0, 434334
	addiw t0, t0, 1639
	sb t0, 0(a0)
	srli t1, t0, 8
	sb t1, 1(a0)
	srli t1, t0, 16
	sb t1, 2(a0)
	srli t1, t0, 24
	sb t1, 3(a0)
	lui t0, 767611
	addiw t0, t0, -379
	sb t0, 4(a0)
	srli t1, t0, 8
	sb t1, 5(a0)
	srli t1, t0, 16
	sb t1, 6(a0)
	srli t1, t0, 24
	sb t1, 7(a0)
	lui t0, 247535
	addiw t0, t0, 882
	sb t0, 8(a0)
	srli t1, t0, 8
	sb t1, 9(a0)
	srli t1, t0, 16
	sb t1, 10(a0)
	srli t1, t0, 24
	sb t1, 11(a0)
	lui t0, 677119
	addiw t0, t0, 1338
	sb t0, 12(a0)
	srli t1, t0, 8
	sb t1, 13(a0)
	srli t1, t0, 16
	sb t1, 14(a0)
	srli t1, t0, 24
	sb t1, 15(a0)
	lui t0, 332005
	addiw t0, t0, 639
	sb t0, 16(a0)
	srli t1, t0, 8
	sb t1, 17(a0)
	srli t1, t0, 16
	sb t1, 18(a0)
	srli t1, t0, 24
	sb t1, 19(a0)
	lui t0, 634967
	addiw t0, t0, -1908
	sb t0, 20(a0)
	srli t1, t0, 8
	sb t1, 21(a0)
	srli t1, t0, 16
	sb t1, 22(a0)
	srli t1, t0, 24
	sb t1, 23(a0)
	lui t0, 129086
	addiw t0, t0, -1621
	sb t0, 24(a0)
	srli t1, t0, 8
	sb t1, 25(a0)
	srli t1, t0, 16
	sb t1, 26(a0)
	srli t1, t0, 24
	sb t1, 27(a0)
	lui t0, 376333
	addiw t0, t0, -743
	sb t0, 28(a0)
	srli t1, t0, 8
	sb t1, 29(a0)
	srli t1, t0, 16
	sb t1, 30(a0)
	srli t1, t0, 24
	sb t1, 31(a0)
	addi a0, s6, 384
	addi a1, s6, 320
	addi a2, zero, 1
	addi a3, s6, 416
	call {vg_sha256_compress}
	addi s1, s6, 384
	addi s3, s6, 576
	lbu t1, 0(s1)
	lbu t2, 1(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 2(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 3(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 0(s3)
	srli t2, t1, 16
	sb t2, 1(s3)
	srli t2, t1, 8
	sb t2, 2(s3)
	srli t2, t1, 0
	sb t2, 3(s3)
	lbu t1, 4(s1)
	lbu t2, 5(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 6(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 7(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 4(s3)
	srli t2, t1, 16
	sb t2, 5(s3)
	srli t2, t1, 8
	sb t2, 6(s3)
	srli t2, t1, 0
	sb t2, 7(s3)
	lbu t1, 8(s1)
	lbu t2, 9(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 10(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 11(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 8(s3)
	srli t2, t1, 16
	sb t2, 9(s3)
	srli t2, t1, 8
	sb t2, 10(s3)
	srli t2, t1, 0
	sb t2, 11(s3)
	lbu t1, 12(s1)
	lbu t2, 13(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 14(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 15(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 12(s3)
	srli t2, t1, 16
	sb t2, 13(s3)
	srli t2, t1, 8
	sb t2, 14(s3)
	srli t2, t1, 0
	sb t2, 15(s3)
	lbu t1, 16(s1)
	lbu t2, 17(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 18(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 19(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 16(s3)
	srli t2, t1, 16
	sb t2, 17(s3)
	srli t2, t1, 8
	sb t2, 18(s3)
	srli t2, t1, 0
	sb t2, 19(s3)
	lbu t1, 20(s1)
	lbu t2, 21(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 22(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 23(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 20(s3)
	srli t2, t1, 16
	sb t2, 21(s3)
	srli t2, t1, 8
	sb t2, 22(s3)
	srli t2, t1, 0
	sb t2, 23(s3)
	lbu t1, 24(s1)
	lbu t2, 25(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 26(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 27(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 24(s3)
	srli t2, t1, 16
	sb t2, 25(s3)
	srli t2, t1, 8
	sb t2, 26(s3)
	srli t2, t1, 0
	sb t2, 27(s3)
	lbu t1, 28(s1)
	lbu t2, 29(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 30(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 31(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 28(s3)
	srli t2, t1, 16
	sb t2, 29(s3)
	srli t2, t1, 8
	sb t2, 30(s3)
	srli t2, t1, 0
	sb t2, 31(s3)
	lbu t2, 576(s6)
	ori t2, t2, 128
	sb t2, 576(s6)
	lui s11, 5
	add s11, s11, s6
	addi s10, zero, 400
	addi s9, zero, 48
	addi t3, zero, 15
	mul t3, t3, s10
	srli t3, t3, 3
	addi t0, s11, 256
	addi t5, zero, 0
244:
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t3, t3, -1
	bnez t3, 244b
	addi t0, zero, 11
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t5, zero, 1
	sd t5, 0(t0)
	addi a0, s6, 576
	addi a1, zero, 384
	addi t1, a0, 0
	addi t3, a1, 0
	addi t0, zero, 0
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	add t0, t0, t3
	addi t0, t0, -1
245:
	lbu t5, 0(t1)
	sb t5, 0(t0)
	addi t1, t1, 1
	addi t0, t0, -1
	addi t3, t3, -1
	bnez t3, 245b
	addi a0, s6, 576
	addi a1, zero, 384
	addi t1, a0, 0
	addi t3, a1, 0
	addi t0, zero, 4
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	add t0, t0, t3
	addi t0, t0, -1
246:
	lbu t5, 0(t1)
	sb t5, 0(t0)
	addi t1, t1, 1
	addi t0, t0, -1
	addi t3, t3, -1
	bnez t3, 246b
	addi a0, s6, 512
	addi a1, zero, 32
	addi t1, a0, 0
	addi t3, a1, 0
	addi t0, zero, 2
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	add t0, t0, t3
	addi t0, t0, -1
247:
	lbu t5, 0(t1)
	sb t5, 0(t0)
	addi t1, t1, 1
	addi t0, t0, -1
	addi t3, t3, -1
	bnez t3, 247b
	addi a1, zero, 32
	addi s8, a1, 7
	srli s8, s8, 3
	addi t0, zero, 1
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t3, s9, 1
	addi t5, zero, 0
248:
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t3, t3, -1
	bnez t3, 248b
	slli s7, s9, 6
	addi a4, zero, -1
249:
	addi t2, zero, 0
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t5, s7, -1
	srli t5, t5, 6
	slli t5, t5, 3
	add t2, t2, t5
	ld t5, 0(t2)
	srli t3, t5, 63
	addi t0, zero, 1
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 2
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	andi t4, a4, 1
	addi t2, s8, 1
	andi t2, t2, 3
	beqz t2, 250f
252:
	ld t5, 0(t0)
	slli t6, t5, 1
	or t6, t6, t3
	srli t3, t5, 63
	ld t5, 0(t1)
	xor t5, t5, a4
	add t6, t6, t4
	sltu a5, t6, t4
	add t6, t6, t5
	sltu t4, t6, t5
	or t4, t4, a5
	sd t6, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t2, t2, -1
	bnez t2, 252b
	j 251f
250:
251:
	addi t2, s8, 1
	srli t2, t2, 2
	beqz t2, 253f
255:
	ld t5, 0(t0)
	slli t6, t5, 1
	or t6, t6, t3
	srli t3, t5, 63
	ld t5, 0(t1)
	xor t5, t5, a4
	add t6, t6, t4
	sltu a5, t6, t4
	add t6, t6, t5
	sltu t4, t6, t5
	or t4, t4, a5
	sd t6, 0(t0)
	ld t5, 8(t0)
	slli t6, t5, 1
	or t6, t6, t3
	srli t3, t5, 63
	ld t5, 8(t1)
	xor t5, t5, a4
	add t6, t6, t4
	sltu a5, t6, t4
	add t6, t6, t5
	sltu t4, t6, t5
	or t4, t4, a5
	sd t6, 8(t0)
	ld t5, 16(t0)
	slli t6, t5, 1
	or t6, t6, t3
	srli t3, t5, 63
	ld t5, 16(t1)
	xor t5, t5, a4
	add t6, t6, t4
	sltu a5, t6, t4
	add t6, t6, t5
	sltu t4, t6, t5
	or t4, t4, a5
	sd t6, 16(t0)
	ld t5, 24(t0)
	slli t6, t5, 1
	or t6, t6, t3
	srli t3, t5, 63
	ld t5, 24(t1)
	xor t5, t5, a4
	add t6, t6, t4
	sltu a5, t6, t4
	add t6, t6, t5
	sltu t4, t6, t5
	or t4, t4, a5
	sd t6, 24(t0)
	addi t0, t0, 32
	addi t1, t1, 32
	addi t2, t2, -1
	bnez t2, 255b
	j 254f
253:
254:
	srli t5, t6, 63
	addi a4, t5, -1
	andi a5, a4, 1
	addi t2, zero, 0
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t5, s7, -1
	srli t5, t5, 6
	slli t5, t5, 3
	add t2, t2, t5
	ld t5, 0(t2)
	slli t5, t5, 1
	or t5, t5, a5
	sd t5, 0(t2)
	addi s7, s7, -1
	bnez s7, 249b
	addi t0, zero, 1
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 2
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	xori a4, a4, -1
	addi t4, zero, 0
	addi t3, s8, 1
256:
	ld t5, 0(t0)
	ld t6, 0(t1)
	and t6, t6, a4
	add t5, t5, t4
	sltu a5, t5, t4
	add t5, t5, t6
	sltu t4, t5, t6
	or t4, t4, a5
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 256b
	addi t0, zero, 5
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 4
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 1
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
257:
	ld t5, 0(t1)
	ld t6, 0(t2)
	sltu a4, t5, t6
	sub t5, t5, t6
	sltu t6, t5, t4
	sub t5, t5, t4
	or t4, a4, t6
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 257b
	addi t0, zero, 0
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld t5, 0(t0)
	andi t5, t5, 1
	sd t5, 160(s11)
	addi t0, zero, 6
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 13
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 2
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	ld t4, 160(s11)
	addi t5, zero, 0
	sub t4, t5, t4
	addi t3, s9, 0
258:
	ld t5, 0(t1)
	ld t6, 0(t2)
	xor t6, t6, t5
	and t6, t6, t4
	xor t6, t6, t5
	sd t6, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 258b
	addi t0, zero, 7
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 5
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 6
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
259:
	ld t5, 0(t1)
	ld t6, 0(t2)
	sltu a4, t5, t6
	sub t5, t5, t6
	sltu t6, t5, t4
	sub t5, t5, t4
	or t4, a4, t6
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 259b
	addi t0, zero, 8
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 7
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
260:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 260b
	addi t0, zero, 8
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld t5, 0(t0)
	ori t5, t5, 1
	sd t5, 0(t0)
	addi t0, zero, 9
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 0
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
261:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 261b
	addi t0, zero, 9
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld t5, 0(t0)
	andi t5, t5, -2
	sd t5, 0(t0)
	addi a0, s6, 960
	addi a1, zero, 384
	addi t4, zero, -1
	addi t1, zero, 8
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	add t1, t1, a1
	addi t1, t1, -1
	addi t0, a0, 0
	addi t3, a1, 0
262:
	lbu t5, 0(t1)
	and t5, t5, t4
	sb t5, 0(t0)
	addi t0, t0, 1
	addi t1, t1, -1
	addi t3, t3, -1
	bnez t3, 262b
	addi a0, s6, 1344
	addi a1, zero, 353
	addi t4, zero, -1
	addi t1, zero, 9
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	add t1, t1, a1
	addi t1, t1, -1
	addi t0, a0, 0
	addi t3, a1, 0
263:
	lbu t5, 0(t1)
	and t5, t5, t4
	sb t5, 0(t0)
	addi t0, t0, 1
	addi t1, t1, -1
	addi t3, t3, -1
	bnez t3, 263b
	lbu t2, 960(s6)
	srli t2, t2, 7
	beqz t2, 264f
	addi a0, s6, 960
	lui a1, 7
	add a1, a1, s6
	addi a1, a1, 0
	addi a2, zero, 384
266:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 266b
	lui a0, 7
	add a0, a0, s6
	ld a1, 168(s6)
	lui t3, 7
	srli t3, t3, 3
	sub a1, a1, t3
	ld t2, 24(s6)
	ld a2, 72(s6)
	ld a3, 80(s6)
	add a2, a2, t2
	sub a3, a3, t2
	addi a4, s6, 112
	beqz a3, 267f
	j 268f
267:
	ld a2, 72(s6)
268:
	call {vg_dsa_probable_prime_3072}
	slli a0, a0, 32
	srli a0, a0, 32
	sd a0, 88(s6)
	beqz a0, 269f
	ld t3, 112(s6)
	ld t4, 24(s6)
	add t4, t4, t3
	sd t4, 24(s6)
	j 270f
269:
270:
	ld t2, 88(s6)
	addi t2, t2, 0
	beqz t2, 271f
	ld t2, 88(s6)
	addi t2, t2, -1
	beqz t2, 273f
	j 274f
273:
	addi t2, zero, 1
	sd t2, 96(s6)
274:
	j 272f
271:
	addi t2, zero, 0
	sd t2, 96(s6)
272:
	j 265f
264:
265:
	ld t2, 96(s6)
	addi t2, t2, -4
	beqz t2, 275f
	j 276f
275:
	ld t3, 32(s6)
	addi t3, t3, 1
	sd t3, 32(s6)
	ld t4, 40(s6)
	addi t4, t4, 12
	sd t4, 40(s6)
	addi t2, zero, 384
	slli t2, t2, 5
	sub t2, t3, t2
	beqz t2, 277f
	j 278f
277:
	addi t2, zero, 2
	sd t2, 96(s6)
278:
276:
	ld t2, 96(s6)
	addi t2, t2, -4
	beqz t2, 219b
	ld t2, 96(s6)
	addi t2, t2, 0
	beqz t2, 279f
	ld t2, 96(s6)
	addi t2, t2, -1
	beqz t2, 281f
	j 282f
281:
	ld t2, 72(s6)
	ld t3, 24(s6)
	add t2, t2, t3
	sd t2, 48(s6)
	sd t2, 128(s6)
	ld t4, 80(s6)
	sub t4, t4, t3
	addi t5, zero, 384
	slli t5, t5, 7
	bltu t4, t5, 283f
	sd t5, 56(s6)
	addi t2, zero, 1
	sd t2, 136(s6)
	j 284f
283:
	sd t4, 56(s6)
	addi t2, zero, 0
	sd t2, 136(s6)
284:
	addi t2, zero, 4
	sd t2, 104(s6)
285:
	ld t2, 56(s6)
	addi t3, zero, 384
	bltu t2, t3, 286f
	lui s11, 5
	add s11, s11, s6
	addi s10, zero, 400
	addi s9, zero, 48
	addi t0, zero, 10
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 13
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
288:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 288b
	ld a0, 48(s6)
	addi a1, zero, 384
	addi t1, a0, 0
	addi t3, a1, 0
	addi t0, zero, 10
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	add t0, t0, t3
	addi t0, t0, -1
289:
	lbu t5, 0(t1)
	sb t5, 0(t0)
	addi t1, t1, 1
	addi t0, t0, -1
	addi t3, t3, -1
	bnez t3, 289b
	addi t0, zero, 14
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 11
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 10
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
290:
	ld t5, 0(t1)
	ld t6, 0(t2)
	sltu a4, t5, t6
	sub t5, t5, t6
	sltu t6, t5, t4
	sub t5, t5, t4
	or t4, a4, t6
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 290b
	sd t4, 168(s11)
	addi t0, zero, 14
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 10
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 7
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
291:
	ld t5, 0(t1)
	ld t6, 0(t2)
	sltu a4, t5, t6
	sub t5, t5, t6
	sltu t6, t5, t4
	sub t5, t5, t4
	or t4, a4, t6
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 291b
	sd t4, 176(s11)
	ld t5, 168(s11)
	ld t6, 176(s11)
	and t5, t5, t6
	sd t5, 168(s11)
	ld t2, 168(s11)
	beqz t2, 292f
	lui a7, 2
	add a7, a7, s6
	addi a7, a7, 256
	addi t0, zero, 48
	addi s5, zero, 400
	addi s7, s6, 960
	addi s8, zero, 384
	add t3, a7, s5
	addi t3, t3, -16
	addi s0, zero, 0
	sd s0, 0(t3)
	addi t3, a7, 0
	addi t5, t0, 0
	addi s0, zero, 0
294:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 294b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
295:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 295b
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
296:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 296b
	addi s0, zero, 1
	sd s0, 0(a2)
	slli a1, t0, 7
297:
	addi t3, a5, 0
	addi t4, a2, 0
	addi t5, t0, 0
	addi s4, zero, 0
298:
	ld s2, 0(t4)
	slli s3, s2, 1
	add s3, s3, s4
	srli s4, s2, 63
	sd s3, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 298b
	sd s4, 0(t3)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
299:
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
	bnez t5, 299b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2100:
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
	bnez t5, 2100b
	addi a1, a1, -1
	bnez a1, 297b
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
2101:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2101b
	ld s7, 48(s6)
	addi s8, zero, 384
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
2102:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2102b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
2103:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 2103b
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
2104:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2104b
	addi s9, s6, 1344
	addi s10, zero, 353
	call {vg_bignum_pow_win}
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t3, t3, -16
	addi s0, zero, 0
	sd s0, 0(t3)
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
2105:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2105b
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
2106:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2106b
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
2107:
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
	bnez t5, 2107b
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
2108:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2108b
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
2109:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2109b
	addi s0, zero, 0
	sltu s1, s0, t2
	addi a2, s1, -1
	or a1, a1, a2
	xor a1, a1, a2
	addi a0, a1, 0
	andi a0, a0, 1
	xori a0, a0, 1
	beqz a0, 2110f
	j 2111f
2110:
	addi s7, s6, 1728
	addi s8, zero, 384
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s8
	addi t3, t3, -1
	addi t4, s7, 0
	addi t5, s8, 0
2112:
	lbu s0, 0(t3)
	sb s0, 0(t4)
	addi t4, t4, 1
	addi t3, t3, -1
	addi t5, t5, -1
	bnez t5, 2112b
	addi t2, zero, 1
	sd t2, 104(s6)
2111:
	j 293f
292:
293:
	ld t2, 48(s6)
	addi t2, t2, 384
	sd t2, 48(s6)
	ld t2, 56(s6)
	addi t2, t2, -384
	sd t2, 56(s6)
	j 287f
286:
	addi t2, zero, 2
	sd t2, 104(s6)
287:
	ld t2, 104(s6)
	addi t2, t2, -4
	beqz t2, 285b
	ld t2, 48(s6)
	ld t3, 128(s6)
	sub t2, t2, t3
	ld t3, 24(s6)
	add t3, t3, t2
	sd t3, 24(s6)
	ld t2, 104(s6)
	addi t2, t2, -1
	beqz t2, 2113f
	ld t2, 136(s6)
	beqz t2, 2115f
	j 2116f
2115:
	addi t2, zero, 0
	sd t2, 64(s6)
2116:
	j 2114f
2113:
	addi a0, s6, 960
	lui a1, 1
	add a1, a1, s6
	addi a1, a1, 0
	addi a2, zero, 384
2117:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 2117b
	addi a0, s6, 512
	lui a1, 1
	add a1, a1, s6
	addi a1, a1, 384
	addi a2, zero, 32
2118:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 2118b
	addi a0, s6, 1728
	lui a1, 1
	add a1, a1, s6
	addi a1, a1, 416
	addi a2, zero, 384
2119:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 2119b
	lui a0, 1
	add a0, a0, s6
	addi a1, zero, 800
	addi a2, zero, 384
	addi a3, zero, 32
	lui a4, 7
	add a4, a4, s6
	ld a5, 168(s6)
	lui t3, 7
	srli t3, t3, 3
	sub a5, a5, t3
	call {vg_dsa_check_parameters}
	slli a0, a0, 32
	srli a0, a0, 32
	addi t2, a0, -1
	beqz t2, 2120f
	j 2121f
2120:
	addi t2, zero, 1
	sd t2, 64(s6)
2121:
2114:
282:
	j 280f
279:
	addi t2, zero, 0
	sd t2, 64(s6)
280:
218:
	j 216f
215:
	addi t2, zero, 0
	sd t2, 64(s6)
216:
	ld t2, 64(s6)
	addi t2, t2, -2
	beqz t2, 2122f
	j 2123f
2122:
	ld t2, 16(s6)
	addi t2, t2, -1
	sd t2, 16(s6)
2123:
	j 28f
27:
	addi t2, zero, 0
	sd t2, 64(s6)
28:
	j 26f
25:
	addi t2, zero, 3
	sd t2, 64(s6)
26:
	ld t2, 64(s6)
	addi t2, t2, -2
	beqz t2, 24b
	ld t2, 64(s6)
	addi t2, t2, -1
	beqz t2, 2124f
	ld a0, 0(s6)
	addi a1, zero, 800
	addi t0, a0, 0
	addi t3, a1, 0
	addi t5, zero, 0
2126:
	sb t5, 0(t0)
	addi t0, t0, 1
	addi t3, t3, -1
	bnez t3, 2126b
	ld t2, 64(s6)
	addi t2, t2, -3
	beqz t2, 2127f
	ld t4, 80(s6)
	ld t3, 144(s6)
	sub t4, t4, t3
	addi t5, zero, 384
	slli t5, t5, 15
	addi t5, t5, 384
	bltu t4, t5, 2129f
	addi t4, zero, 0
	addi t5, zero, 0
	ld t2, 144(s6)
	ld t3, 152(s6)
	sd t2, 0(t3)
	ld t3, 160(s6)
	sd t4, 0(t3)
	sd t5, 24(t3)
	addi a0, zero, 3
	j 2130f
2129:
	addi t3, zero, 384
	slli t3, t3, 8
	bltu t4, t3, 2131f
	j 2132f
2131:
	addi t4, t3, 0
2132:
	add t4, t4, t4
	bltu t4, t5, 2133f
	j 2134f
2133:
	addi t5, t4, 0
2134:
	ld t4, 16(s6)
	ld t2, 144(s6)
	ld t3, 152(s6)
	sd t2, 0(t3)
	ld t3, 160(s6)
	sd t4, 0(t3)
	sd t5, 24(t3)
	addi a0, zero, 0
2130:
	j 2128f
2127:
	addi t4, zero, 0
	addi t5, zero, 0
	ld t2, 144(s6)
	ld t3, 152(s6)
	sd t2, 0(t3)
	ld t3, 160(s6)
	sd t4, 0(t3)
	sd t5, 24(t3)
	addi a0, zero, 3
2128:
	j 2125f
2124:
	lui a0, 1
	add a0, a0, s6
	ld a1, 0(s6)
	addi a2, zero, 800
2135:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 2135b
	addi t4, zero, 0
	addi t5, zero, 0
	ld t2, 24(s6)
	ld t3, 152(s6)
	sd t2, 0(t3)
	ld t3, 160(s6)
	sd t4, 0(t3)
	sd t5, 24(t3)
	addi a0, zero, 1
2125:
	j 23f
22:
	addi t2, zero, 0
	sd t2, 320(s6)
	sd t2, 328(s6)
	sd t2, 336(s6)
	sd t2, 344(s6)
	sd t2, 352(s6)
	sd t2, 360(s6)
	sd t2, 368(s6)
	sd t2, 376(s6)
	addi t2, zero, 128
	sb t2, 352(s6)
	addi t2, zero, 1
	sb t2, 382(s6)
	addi t2, zero, 0
	sb t2, 383(s6)
2136:
	ld t2, 24(s6)
	sd t2, 144(s6)
	ld t3, 16(s6)
	beqz t3, 2137f
	ld t3, 80(s6)
	sub t3, t3, t2
	addi t4, zero, 32
	bltu t3, t4, 2139f
	ld t3, 72(s6)
	add t3, t3, t2
	sd t3, 8(s6)
	addi t2, t2, 32
	sd t2, 24(s6)
	addi t2, zero, 2
	sd t2, 64(s6)
	ld a0, 8(s6)
	addi a1, s6, 320
	addi a2, zero, 32
2141:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 2141b
	addi a0, s6, 384
	lui t0, 434334
	addiw t0, t0, 1639
	sb t0, 0(a0)
	srli t1, t0, 8
	sb t1, 1(a0)
	srli t1, t0, 16
	sb t1, 2(a0)
	srli t1, t0, 24
	sb t1, 3(a0)
	lui t0, 767611
	addiw t0, t0, -379
	sb t0, 4(a0)
	srli t1, t0, 8
	sb t1, 5(a0)
	srli t1, t0, 16
	sb t1, 6(a0)
	srli t1, t0, 24
	sb t1, 7(a0)
	lui t0, 247535
	addiw t0, t0, 882
	sb t0, 8(a0)
	srli t1, t0, 8
	sb t1, 9(a0)
	srli t1, t0, 16
	sb t1, 10(a0)
	srli t1, t0, 24
	sb t1, 11(a0)
	lui t0, 677119
	addiw t0, t0, 1338
	sb t0, 12(a0)
	srli t1, t0, 8
	sb t1, 13(a0)
	srli t1, t0, 16
	sb t1, 14(a0)
	srli t1, t0, 24
	sb t1, 15(a0)
	lui t0, 332005
	addiw t0, t0, 639
	sb t0, 16(a0)
	srli t1, t0, 8
	sb t1, 17(a0)
	srli t1, t0, 16
	sb t1, 18(a0)
	srli t1, t0, 24
	sb t1, 19(a0)
	lui t0, 634967
	addiw t0, t0, -1908
	sb t0, 20(a0)
	srli t1, t0, 8
	sb t1, 21(a0)
	srli t1, t0, 16
	sb t1, 22(a0)
	srli t1, t0, 24
	sb t1, 23(a0)
	lui t0, 129086
	addiw t0, t0, -1621
	sb t0, 24(a0)
	srli t1, t0, 8
	sb t1, 25(a0)
	srli t1, t0, 16
	sb t1, 26(a0)
	srli t1, t0, 24
	sb t1, 27(a0)
	lui t0, 376333
	addiw t0, t0, -743
	sb t0, 28(a0)
	srli t1, t0, 8
	sb t1, 29(a0)
	srli t1, t0, 16
	sb t1, 30(a0)
	srli t1, t0, 24
	sb t1, 31(a0)
	addi a0, s6, 384
	addi a1, s6, 320
	addi a2, zero, 1
	addi a3, s6, 416
	call {vg_sha256_compress}
	addi s1, s6, 384
	addi s3, s6, 512
	lbu t1, 0(s1)
	lbu t2, 1(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 2(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 3(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 0(s3)
	srli t2, t1, 16
	sb t2, 1(s3)
	srli t2, t1, 8
	sb t2, 2(s3)
	srli t2, t1, 0
	sb t2, 3(s3)
	lbu t1, 4(s1)
	lbu t2, 5(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 6(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 7(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 4(s3)
	srli t2, t1, 16
	sb t2, 5(s3)
	srli t2, t1, 8
	sb t2, 6(s3)
	srli t2, t1, 0
	sb t2, 7(s3)
	lbu t1, 8(s1)
	lbu t2, 9(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 10(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 11(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 8(s3)
	srli t2, t1, 16
	sb t2, 9(s3)
	srli t2, t1, 8
	sb t2, 10(s3)
	srli t2, t1, 0
	sb t2, 11(s3)
	lbu t1, 12(s1)
	lbu t2, 13(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 14(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 15(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 12(s3)
	srli t2, t1, 16
	sb t2, 13(s3)
	srli t2, t1, 8
	sb t2, 14(s3)
	srli t2, t1, 0
	sb t2, 15(s3)
	lbu t1, 16(s1)
	lbu t2, 17(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 18(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 19(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 16(s3)
	srli t2, t1, 16
	sb t2, 17(s3)
	srli t2, t1, 8
	sb t2, 18(s3)
	srli t2, t1, 0
	sb t2, 19(s3)
	lbu t1, 20(s1)
	lbu t2, 21(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 22(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 23(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 20(s3)
	srli t2, t1, 16
	sb t2, 21(s3)
	srli t2, t1, 8
	sb t2, 22(s3)
	srli t2, t1, 0
	sb t2, 23(s3)
	lbu t1, 24(s1)
	lbu t2, 25(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 26(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 27(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 24(s3)
	srli t2, t1, 16
	sb t2, 25(s3)
	srli t2, t1, 8
	sb t2, 26(s3)
	srli t2, t1, 0
	sb t2, 27(s3)
	lbu t1, 28(s1)
	lbu t2, 29(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 30(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 31(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 28(s3)
	srli t2, t1, 16
	sb t2, 29(s3)
	srli t2, t1, 8
	sb t2, 30(s3)
	srli t2, t1, 0
	sb t2, 31(s3)
	lbu t2, 512(s6)
	ori t2, t2, 128
	sb t2, 512(s6)
	lbu t2, 543(s6)
	ori t2, t2, 1
	sb t2, 543(s6)
	addi a0, s6, 512
	lui a1, 6
	add a1, a1, s6
	addi a1, a1, 0
	addi a2, zero, 32
2142:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 2142b
	lui a0, 6
	add a0, a0, s6
	ld a1, 168(s6)
	lui t3, 6
	srli t3, t3, 3
	sub a1, a1, t3
	ld t2, 24(s6)
	ld a2, 72(s6)
	ld a3, 80(s6)
	add a2, a2, t2
	sub a3, a3, t2
	addi a4, s6, 112
	beqz a3, 2143f
	j 2144f
2143:
	ld a2, 72(s6)
2144:
	call {vg_dsa_probable_prime_256}
	slli a0, a0, 32
	srli a0, a0, 32
	sd a0, 88(s6)
	beqz a0, 2145f
	ld t3, 112(s6)
	ld t4, 24(s6)
	add t4, t4, t3
	sd t4, 24(s6)
	j 2146f
2145:
2146:
	ld t2, 88(s6)
	addi t2, t2, 0
	beqz t2, 2147f
	ld t2, 88(s6)
	addi t2, t2, -1
	beqz t2, 2149f
	j 2150f
2149:
	addi t2, zero, 0
	sd t2, 32(s6)
	addi t2, zero, 1
	sd t2, 40(s6)
	addi t2, zero, 4
	sd t2, 96(s6)
2151:
	ld a0, 8(s6)
	addi a1, s6, 320
	addi a2, zero, 32
2152:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 2152b
	addi a0, s6, 351
	ld a2, 40(s6)
	addi a2, a2, 0
	addi a3, zero, 32
2153:
	lbu a1, 0(a0)
	add a1, a1, a2
	sb a1, 0(a0)
	srli a2, a1, 8
	addi a0, a0, -1
	addi a3, a3, -1
	bnez a3, 2153b
	addi a0, s6, 384
	lui t0, 434334
	addiw t0, t0, 1639
	sb t0, 0(a0)
	srli t1, t0, 8
	sb t1, 1(a0)
	srli t1, t0, 16
	sb t1, 2(a0)
	srli t1, t0, 24
	sb t1, 3(a0)
	lui t0, 767611
	addiw t0, t0, -379
	sb t0, 4(a0)
	srli t1, t0, 8
	sb t1, 5(a0)
	srli t1, t0, 16
	sb t1, 6(a0)
	srli t1, t0, 24
	sb t1, 7(a0)
	lui t0, 247535
	addiw t0, t0, 882
	sb t0, 8(a0)
	srli t1, t0, 8
	sb t1, 9(a0)
	srli t1, t0, 16
	sb t1, 10(a0)
	srli t1, t0, 24
	sb t1, 11(a0)
	lui t0, 677119
	addiw t0, t0, 1338
	sb t0, 12(a0)
	srli t1, t0, 8
	sb t1, 13(a0)
	srli t1, t0, 16
	sb t1, 14(a0)
	srli t1, t0, 24
	sb t1, 15(a0)
	lui t0, 332005
	addiw t0, t0, 639
	sb t0, 16(a0)
	srli t1, t0, 8
	sb t1, 17(a0)
	srli t1, t0, 16
	sb t1, 18(a0)
	srli t1, t0, 24
	sb t1, 19(a0)
	lui t0, 634967
	addiw t0, t0, -1908
	sb t0, 20(a0)
	srli t1, t0, 8
	sb t1, 21(a0)
	srli t1, t0, 16
	sb t1, 22(a0)
	srli t1, t0, 24
	sb t1, 23(a0)
	lui t0, 129086
	addiw t0, t0, -1621
	sb t0, 24(a0)
	srli t1, t0, 8
	sb t1, 25(a0)
	srli t1, t0, 16
	sb t1, 26(a0)
	srli t1, t0, 24
	sb t1, 27(a0)
	lui t0, 376333
	addiw t0, t0, -743
	sb t0, 28(a0)
	srli t1, t0, 8
	sb t1, 29(a0)
	srli t1, t0, 16
	sb t1, 30(a0)
	srli t1, t0, 24
	sb t1, 31(a0)
	addi a0, s6, 384
	addi a1, s6, 320
	addi a2, zero, 1
	addi a3, s6, 416
	call {vg_sha256_compress}
	addi s1, s6, 384
	addi s3, s6, 800
	lbu t1, 0(s1)
	lbu t2, 1(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 2(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 3(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 0(s3)
	srli t2, t1, 16
	sb t2, 1(s3)
	srli t2, t1, 8
	sb t2, 2(s3)
	srli t2, t1, 0
	sb t2, 3(s3)
	lbu t1, 4(s1)
	lbu t2, 5(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 6(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 7(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 4(s3)
	srli t2, t1, 16
	sb t2, 5(s3)
	srli t2, t1, 8
	sb t2, 6(s3)
	srli t2, t1, 0
	sb t2, 7(s3)
	lbu t1, 8(s1)
	lbu t2, 9(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 10(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 11(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 8(s3)
	srli t2, t1, 16
	sb t2, 9(s3)
	srli t2, t1, 8
	sb t2, 10(s3)
	srli t2, t1, 0
	sb t2, 11(s3)
	lbu t1, 12(s1)
	lbu t2, 13(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 14(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 15(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 12(s3)
	srli t2, t1, 16
	sb t2, 13(s3)
	srli t2, t1, 8
	sb t2, 14(s3)
	srli t2, t1, 0
	sb t2, 15(s3)
	lbu t1, 16(s1)
	lbu t2, 17(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 18(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 19(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 16(s3)
	srli t2, t1, 16
	sb t2, 17(s3)
	srli t2, t1, 8
	sb t2, 18(s3)
	srli t2, t1, 0
	sb t2, 19(s3)
	lbu t1, 20(s1)
	lbu t2, 21(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 22(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 23(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 20(s3)
	srli t2, t1, 16
	sb t2, 21(s3)
	srli t2, t1, 8
	sb t2, 22(s3)
	srli t2, t1, 0
	sb t2, 23(s3)
	lbu t1, 24(s1)
	lbu t2, 25(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 26(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 27(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 24(s3)
	srli t2, t1, 16
	sb t2, 25(s3)
	srli t2, t1, 8
	sb t2, 26(s3)
	srli t2, t1, 0
	sb t2, 27(s3)
	lbu t1, 28(s1)
	lbu t2, 29(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 30(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 31(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 28(s3)
	srli t2, t1, 16
	sb t2, 29(s3)
	srli t2, t1, 8
	sb t2, 30(s3)
	srli t2, t1, 0
	sb t2, 31(s3)
	ld a0, 8(s6)
	addi a1, s6, 320
	addi a2, zero, 32
2154:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 2154b
	addi a0, s6, 351
	ld a2, 40(s6)
	addi a2, a2, 1
	addi a3, zero, 32
2155:
	lbu a1, 0(a0)
	add a1, a1, a2
	sb a1, 0(a0)
	srli a2, a1, 8
	addi a0, a0, -1
	addi a3, a3, -1
	bnez a3, 2155b
	addi a0, s6, 384
	lui t0, 434334
	addiw t0, t0, 1639
	sb t0, 0(a0)
	srli t1, t0, 8
	sb t1, 1(a0)
	srli t1, t0, 16
	sb t1, 2(a0)
	srli t1, t0, 24
	sb t1, 3(a0)
	lui t0, 767611
	addiw t0, t0, -379
	sb t0, 4(a0)
	srli t1, t0, 8
	sb t1, 5(a0)
	srli t1, t0, 16
	sb t1, 6(a0)
	srli t1, t0, 24
	sb t1, 7(a0)
	lui t0, 247535
	addiw t0, t0, 882
	sb t0, 8(a0)
	srli t1, t0, 8
	sb t1, 9(a0)
	srli t1, t0, 16
	sb t1, 10(a0)
	srli t1, t0, 24
	sb t1, 11(a0)
	lui t0, 677119
	addiw t0, t0, 1338
	sb t0, 12(a0)
	srli t1, t0, 8
	sb t1, 13(a0)
	srli t1, t0, 16
	sb t1, 14(a0)
	srli t1, t0, 24
	sb t1, 15(a0)
	lui t0, 332005
	addiw t0, t0, 639
	sb t0, 16(a0)
	srli t1, t0, 8
	sb t1, 17(a0)
	srli t1, t0, 16
	sb t1, 18(a0)
	srli t1, t0, 24
	sb t1, 19(a0)
	lui t0, 634967
	addiw t0, t0, -1908
	sb t0, 20(a0)
	srli t1, t0, 8
	sb t1, 21(a0)
	srli t1, t0, 16
	sb t1, 22(a0)
	srli t1, t0, 24
	sb t1, 23(a0)
	lui t0, 129086
	addiw t0, t0, -1621
	sb t0, 24(a0)
	srli t1, t0, 8
	sb t1, 25(a0)
	srli t1, t0, 16
	sb t1, 26(a0)
	srli t1, t0, 24
	sb t1, 27(a0)
	lui t0, 376333
	addiw t0, t0, -743
	sb t0, 28(a0)
	srli t1, t0, 8
	sb t1, 29(a0)
	srli t1, t0, 16
	sb t1, 30(a0)
	srli t1, t0, 24
	sb t1, 31(a0)
	addi a0, s6, 384
	addi a1, s6, 320
	addi a2, zero, 1
	addi a3, s6, 416
	call {vg_sha256_compress}
	addi s1, s6, 384
	addi s3, s6, 768
	lbu t1, 0(s1)
	lbu t2, 1(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 2(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 3(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 0(s3)
	srli t2, t1, 16
	sb t2, 1(s3)
	srli t2, t1, 8
	sb t2, 2(s3)
	srli t2, t1, 0
	sb t2, 3(s3)
	lbu t1, 4(s1)
	lbu t2, 5(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 6(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 7(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 4(s3)
	srli t2, t1, 16
	sb t2, 5(s3)
	srli t2, t1, 8
	sb t2, 6(s3)
	srli t2, t1, 0
	sb t2, 7(s3)
	lbu t1, 8(s1)
	lbu t2, 9(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 10(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 11(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 8(s3)
	srli t2, t1, 16
	sb t2, 9(s3)
	srli t2, t1, 8
	sb t2, 10(s3)
	srli t2, t1, 0
	sb t2, 11(s3)
	lbu t1, 12(s1)
	lbu t2, 13(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 14(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 15(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 12(s3)
	srli t2, t1, 16
	sb t2, 13(s3)
	srli t2, t1, 8
	sb t2, 14(s3)
	srli t2, t1, 0
	sb t2, 15(s3)
	lbu t1, 16(s1)
	lbu t2, 17(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 18(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 19(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 16(s3)
	srli t2, t1, 16
	sb t2, 17(s3)
	srli t2, t1, 8
	sb t2, 18(s3)
	srli t2, t1, 0
	sb t2, 19(s3)
	lbu t1, 20(s1)
	lbu t2, 21(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 22(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 23(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 20(s3)
	srli t2, t1, 16
	sb t2, 21(s3)
	srli t2, t1, 8
	sb t2, 22(s3)
	srli t2, t1, 0
	sb t2, 23(s3)
	lbu t1, 24(s1)
	lbu t2, 25(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 26(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 27(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 24(s3)
	srli t2, t1, 16
	sb t2, 25(s3)
	srli t2, t1, 8
	sb t2, 26(s3)
	srli t2, t1, 0
	sb t2, 27(s3)
	lbu t1, 28(s1)
	lbu t2, 29(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 30(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 31(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 28(s3)
	srli t2, t1, 16
	sb t2, 29(s3)
	srli t2, t1, 8
	sb t2, 30(s3)
	srli t2, t1, 0
	sb t2, 31(s3)
	ld a0, 8(s6)
	addi a1, s6, 320
	addi a2, zero, 32
2156:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 2156b
	addi a0, s6, 351
	ld a2, 40(s6)
	addi a2, a2, 2
	addi a3, zero, 32
2157:
	lbu a1, 0(a0)
	add a1, a1, a2
	sb a1, 0(a0)
	srli a2, a1, 8
	addi a0, a0, -1
	addi a3, a3, -1
	bnez a3, 2157b
	addi a0, s6, 384
	lui t0, 434334
	addiw t0, t0, 1639
	sb t0, 0(a0)
	srli t1, t0, 8
	sb t1, 1(a0)
	srli t1, t0, 16
	sb t1, 2(a0)
	srli t1, t0, 24
	sb t1, 3(a0)
	lui t0, 767611
	addiw t0, t0, -379
	sb t0, 4(a0)
	srli t1, t0, 8
	sb t1, 5(a0)
	srli t1, t0, 16
	sb t1, 6(a0)
	srli t1, t0, 24
	sb t1, 7(a0)
	lui t0, 247535
	addiw t0, t0, 882
	sb t0, 8(a0)
	srli t1, t0, 8
	sb t1, 9(a0)
	srli t1, t0, 16
	sb t1, 10(a0)
	srli t1, t0, 24
	sb t1, 11(a0)
	lui t0, 677119
	addiw t0, t0, 1338
	sb t0, 12(a0)
	srli t1, t0, 8
	sb t1, 13(a0)
	srli t1, t0, 16
	sb t1, 14(a0)
	srli t1, t0, 24
	sb t1, 15(a0)
	lui t0, 332005
	addiw t0, t0, 639
	sb t0, 16(a0)
	srli t1, t0, 8
	sb t1, 17(a0)
	srli t1, t0, 16
	sb t1, 18(a0)
	srli t1, t0, 24
	sb t1, 19(a0)
	lui t0, 634967
	addiw t0, t0, -1908
	sb t0, 20(a0)
	srli t1, t0, 8
	sb t1, 21(a0)
	srli t1, t0, 16
	sb t1, 22(a0)
	srli t1, t0, 24
	sb t1, 23(a0)
	lui t0, 129086
	addiw t0, t0, -1621
	sb t0, 24(a0)
	srli t1, t0, 8
	sb t1, 25(a0)
	srli t1, t0, 16
	sb t1, 26(a0)
	srli t1, t0, 24
	sb t1, 27(a0)
	lui t0, 376333
	addiw t0, t0, -743
	sb t0, 28(a0)
	srli t1, t0, 8
	sb t1, 29(a0)
	srli t1, t0, 16
	sb t1, 30(a0)
	srli t1, t0, 24
	sb t1, 31(a0)
	addi a0, s6, 384
	addi a1, s6, 320
	addi a2, zero, 1
	addi a3, s6, 416
	call {vg_sha256_compress}
	addi s1, s6, 384
	addi s3, s6, 736
	lbu t1, 0(s1)
	lbu t2, 1(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 2(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 3(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 0(s3)
	srli t2, t1, 16
	sb t2, 1(s3)
	srli t2, t1, 8
	sb t2, 2(s3)
	srli t2, t1, 0
	sb t2, 3(s3)
	lbu t1, 4(s1)
	lbu t2, 5(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 6(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 7(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 4(s3)
	srli t2, t1, 16
	sb t2, 5(s3)
	srli t2, t1, 8
	sb t2, 6(s3)
	srli t2, t1, 0
	sb t2, 7(s3)
	lbu t1, 8(s1)
	lbu t2, 9(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 10(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 11(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 8(s3)
	srli t2, t1, 16
	sb t2, 9(s3)
	srli t2, t1, 8
	sb t2, 10(s3)
	srli t2, t1, 0
	sb t2, 11(s3)
	lbu t1, 12(s1)
	lbu t2, 13(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 14(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 15(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 12(s3)
	srli t2, t1, 16
	sb t2, 13(s3)
	srli t2, t1, 8
	sb t2, 14(s3)
	srli t2, t1, 0
	sb t2, 15(s3)
	lbu t1, 16(s1)
	lbu t2, 17(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 18(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 19(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 16(s3)
	srli t2, t1, 16
	sb t2, 17(s3)
	srli t2, t1, 8
	sb t2, 18(s3)
	srli t2, t1, 0
	sb t2, 19(s3)
	lbu t1, 20(s1)
	lbu t2, 21(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 22(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 23(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 20(s3)
	srli t2, t1, 16
	sb t2, 21(s3)
	srli t2, t1, 8
	sb t2, 22(s3)
	srli t2, t1, 0
	sb t2, 23(s3)
	lbu t1, 24(s1)
	lbu t2, 25(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 26(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 27(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 24(s3)
	srli t2, t1, 16
	sb t2, 25(s3)
	srli t2, t1, 8
	sb t2, 26(s3)
	srli t2, t1, 0
	sb t2, 27(s3)
	lbu t1, 28(s1)
	lbu t2, 29(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 30(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 31(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 28(s3)
	srli t2, t1, 16
	sb t2, 29(s3)
	srli t2, t1, 8
	sb t2, 30(s3)
	srli t2, t1, 0
	sb t2, 31(s3)
	ld a0, 8(s6)
	addi a1, s6, 320
	addi a2, zero, 32
2158:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 2158b
	addi a0, s6, 351
	ld a2, 40(s6)
	addi a2, a2, 3
	addi a3, zero, 32
2159:
	lbu a1, 0(a0)
	add a1, a1, a2
	sb a1, 0(a0)
	srli a2, a1, 8
	addi a0, a0, -1
	addi a3, a3, -1
	bnez a3, 2159b
	addi a0, s6, 384
	lui t0, 434334
	addiw t0, t0, 1639
	sb t0, 0(a0)
	srli t1, t0, 8
	sb t1, 1(a0)
	srli t1, t0, 16
	sb t1, 2(a0)
	srli t1, t0, 24
	sb t1, 3(a0)
	lui t0, 767611
	addiw t0, t0, -379
	sb t0, 4(a0)
	srli t1, t0, 8
	sb t1, 5(a0)
	srli t1, t0, 16
	sb t1, 6(a0)
	srli t1, t0, 24
	sb t1, 7(a0)
	lui t0, 247535
	addiw t0, t0, 882
	sb t0, 8(a0)
	srli t1, t0, 8
	sb t1, 9(a0)
	srli t1, t0, 16
	sb t1, 10(a0)
	srli t1, t0, 24
	sb t1, 11(a0)
	lui t0, 677119
	addiw t0, t0, 1338
	sb t0, 12(a0)
	srli t1, t0, 8
	sb t1, 13(a0)
	srli t1, t0, 16
	sb t1, 14(a0)
	srli t1, t0, 24
	sb t1, 15(a0)
	lui t0, 332005
	addiw t0, t0, 639
	sb t0, 16(a0)
	srli t1, t0, 8
	sb t1, 17(a0)
	srli t1, t0, 16
	sb t1, 18(a0)
	srli t1, t0, 24
	sb t1, 19(a0)
	lui t0, 634967
	addiw t0, t0, -1908
	sb t0, 20(a0)
	srli t1, t0, 8
	sb t1, 21(a0)
	srli t1, t0, 16
	sb t1, 22(a0)
	srli t1, t0, 24
	sb t1, 23(a0)
	lui t0, 129086
	addiw t0, t0, -1621
	sb t0, 24(a0)
	srli t1, t0, 8
	sb t1, 25(a0)
	srli t1, t0, 16
	sb t1, 26(a0)
	srli t1, t0, 24
	sb t1, 27(a0)
	lui t0, 376333
	addiw t0, t0, -743
	sb t0, 28(a0)
	srli t1, t0, 8
	sb t1, 29(a0)
	srli t1, t0, 16
	sb t1, 30(a0)
	srli t1, t0, 24
	sb t1, 31(a0)
	addi a0, s6, 384
	addi a1, s6, 320
	addi a2, zero, 1
	addi a3, s6, 416
	call {vg_sha256_compress}
	addi s1, s6, 384
	addi s3, s6, 704
	lbu t1, 0(s1)
	lbu t2, 1(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 2(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 3(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 0(s3)
	srli t2, t1, 16
	sb t2, 1(s3)
	srli t2, t1, 8
	sb t2, 2(s3)
	srli t2, t1, 0
	sb t2, 3(s3)
	lbu t1, 4(s1)
	lbu t2, 5(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 6(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 7(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 4(s3)
	srli t2, t1, 16
	sb t2, 5(s3)
	srli t2, t1, 8
	sb t2, 6(s3)
	srli t2, t1, 0
	sb t2, 7(s3)
	lbu t1, 8(s1)
	lbu t2, 9(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 10(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 11(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 8(s3)
	srli t2, t1, 16
	sb t2, 9(s3)
	srli t2, t1, 8
	sb t2, 10(s3)
	srli t2, t1, 0
	sb t2, 11(s3)
	lbu t1, 12(s1)
	lbu t2, 13(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 14(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 15(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 12(s3)
	srli t2, t1, 16
	sb t2, 13(s3)
	srli t2, t1, 8
	sb t2, 14(s3)
	srli t2, t1, 0
	sb t2, 15(s3)
	lbu t1, 16(s1)
	lbu t2, 17(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 18(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 19(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 16(s3)
	srli t2, t1, 16
	sb t2, 17(s3)
	srli t2, t1, 8
	sb t2, 18(s3)
	srli t2, t1, 0
	sb t2, 19(s3)
	lbu t1, 20(s1)
	lbu t2, 21(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 22(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 23(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 20(s3)
	srli t2, t1, 16
	sb t2, 21(s3)
	srli t2, t1, 8
	sb t2, 22(s3)
	srli t2, t1, 0
	sb t2, 23(s3)
	lbu t1, 24(s1)
	lbu t2, 25(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 26(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 27(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 24(s3)
	srli t2, t1, 16
	sb t2, 25(s3)
	srli t2, t1, 8
	sb t2, 26(s3)
	srli t2, t1, 0
	sb t2, 27(s3)
	lbu t1, 28(s1)
	lbu t2, 29(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 30(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 31(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 28(s3)
	srli t2, t1, 16
	sb t2, 29(s3)
	srli t2, t1, 8
	sb t2, 30(s3)
	srli t2, t1, 0
	sb t2, 31(s3)
	ld a0, 8(s6)
	addi a1, s6, 320
	addi a2, zero, 32
2160:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 2160b
	addi a0, s6, 351
	ld a2, 40(s6)
	addi a2, a2, 4
	addi a3, zero, 32
2161:
	lbu a1, 0(a0)
	add a1, a1, a2
	sb a1, 0(a0)
	srli a2, a1, 8
	addi a0, a0, -1
	addi a3, a3, -1
	bnez a3, 2161b
	addi a0, s6, 384
	lui t0, 434334
	addiw t0, t0, 1639
	sb t0, 0(a0)
	srli t1, t0, 8
	sb t1, 1(a0)
	srli t1, t0, 16
	sb t1, 2(a0)
	srli t1, t0, 24
	sb t1, 3(a0)
	lui t0, 767611
	addiw t0, t0, -379
	sb t0, 4(a0)
	srli t1, t0, 8
	sb t1, 5(a0)
	srli t1, t0, 16
	sb t1, 6(a0)
	srli t1, t0, 24
	sb t1, 7(a0)
	lui t0, 247535
	addiw t0, t0, 882
	sb t0, 8(a0)
	srli t1, t0, 8
	sb t1, 9(a0)
	srli t1, t0, 16
	sb t1, 10(a0)
	srli t1, t0, 24
	sb t1, 11(a0)
	lui t0, 677119
	addiw t0, t0, 1338
	sb t0, 12(a0)
	srli t1, t0, 8
	sb t1, 13(a0)
	srli t1, t0, 16
	sb t1, 14(a0)
	srli t1, t0, 24
	sb t1, 15(a0)
	lui t0, 332005
	addiw t0, t0, 639
	sb t0, 16(a0)
	srli t1, t0, 8
	sb t1, 17(a0)
	srli t1, t0, 16
	sb t1, 18(a0)
	srli t1, t0, 24
	sb t1, 19(a0)
	lui t0, 634967
	addiw t0, t0, -1908
	sb t0, 20(a0)
	srli t1, t0, 8
	sb t1, 21(a0)
	srli t1, t0, 16
	sb t1, 22(a0)
	srli t1, t0, 24
	sb t1, 23(a0)
	lui t0, 129086
	addiw t0, t0, -1621
	sb t0, 24(a0)
	srli t1, t0, 8
	sb t1, 25(a0)
	srli t1, t0, 16
	sb t1, 26(a0)
	srli t1, t0, 24
	sb t1, 27(a0)
	lui t0, 376333
	addiw t0, t0, -743
	sb t0, 28(a0)
	srli t1, t0, 8
	sb t1, 29(a0)
	srli t1, t0, 16
	sb t1, 30(a0)
	srli t1, t0, 24
	sb t1, 31(a0)
	addi a0, s6, 384
	addi a1, s6, 320
	addi a2, zero, 1
	addi a3, s6, 416
	call {vg_sha256_compress}
	addi s1, s6, 384
	addi s3, s6, 672
	lbu t1, 0(s1)
	lbu t2, 1(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 2(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 3(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 0(s3)
	srli t2, t1, 16
	sb t2, 1(s3)
	srli t2, t1, 8
	sb t2, 2(s3)
	srli t2, t1, 0
	sb t2, 3(s3)
	lbu t1, 4(s1)
	lbu t2, 5(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 6(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 7(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 4(s3)
	srli t2, t1, 16
	sb t2, 5(s3)
	srli t2, t1, 8
	sb t2, 6(s3)
	srli t2, t1, 0
	sb t2, 7(s3)
	lbu t1, 8(s1)
	lbu t2, 9(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 10(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 11(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 8(s3)
	srli t2, t1, 16
	sb t2, 9(s3)
	srli t2, t1, 8
	sb t2, 10(s3)
	srli t2, t1, 0
	sb t2, 11(s3)
	lbu t1, 12(s1)
	lbu t2, 13(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 14(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 15(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 12(s3)
	srli t2, t1, 16
	sb t2, 13(s3)
	srli t2, t1, 8
	sb t2, 14(s3)
	srli t2, t1, 0
	sb t2, 15(s3)
	lbu t1, 16(s1)
	lbu t2, 17(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 18(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 19(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 16(s3)
	srli t2, t1, 16
	sb t2, 17(s3)
	srli t2, t1, 8
	sb t2, 18(s3)
	srli t2, t1, 0
	sb t2, 19(s3)
	lbu t1, 20(s1)
	lbu t2, 21(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 22(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 23(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 20(s3)
	srli t2, t1, 16
	sb t2, 21(s3)
	srli t2, t1, 8
	sb t2, 22(s3)
	srli t2, t1, 0
	sb t2, 23(s3)
	lbu t1, 24(s1)
	lbu t2, 25(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 26(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 27(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 24(s3)
	srli t2, t1, 16
	sb t2, 25(s3)
	srli t2, t1, 8
	sb t2, 26(s3)
	srli t2, t1, 0
	sb t2, 27(s3)
	lbu t1, 28(s1)
	lbu t2, 29(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 30(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 31(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 28(s3)
	srli t2, t1, 16
	sb t2, 29(s3)
	srli t2, t1, 8
	sb t2, 30(s3)
	srli t2, t1, 0
	sb t2, 31(s3)
	ld a0, 8(s6)
	addi a1, s6, 320
	addi a2, zero, 32
2162:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 2162b
	addi a0, s6, 351
	ld a2, 40(s6)
	addi a2, a2, 5
	addi a3, zero, 32
2163:
	lbu a1, 0(a0)
	add a1, a1, a2
	sb a1, 0(a0)
	srli a2, a1, 8
	addi a0, a0, -1
	addi a3, a3, -1
	bnez a3, 2163b
	addi a0, s6, 384
	lui t0, 434334
	addiw t0, t0, 1639
	sb t0, 0(a0)
	srli t1, t0, 8
	sb t1, 1(a0)
	srli t1, t0, 16
	sb t1, 2(a0)
	srli t1, t0, 24
	sb t1, 3(a0)
	lui t0, 767611
	addiw t0, t0, -379
	sb t0, 4(a0)
	srli t1, t0, 8
	sb t1, 5(a0)
	srli t1, t0, 16
	sb t1, 6(a0)
	srli t1, t0, 24
	sb t1, 7(a0)
	lui t0, 247535
	addiw t0, t0, 882
	sb t0, 8(a0)
	srli t1, t0, 8
	sb t1, 9(a0)
	srli t1, t0, 16
	sb t1, 10(a0)
	srli t1, t0, 24
	sb t1, 11(a0)
	lui t0, 677119
	addiw t0, t0, 1338
	sb t0, 12(a0)
	srli t1, t0, 8
	sb t1, 13(a0)
	srli t1, t0, 16
	sb t1, 14(a0)
	srli t1, t0, 24
	sb t1, 15(a0)
	lui t0, 332005
	addiw t0, t0, 639
	sb t0, 16(a0)
	srli t1, t0, 8
	sb t1, 17(a0)
	srli t1, t0, 16
	sb t1, 18(a0)
	srli t1, t0, 24
	sb t1, 19(a0)
	lui t0, 634967
	addiw t0, t0, -1908
	sb t0, 20(a0)
	srli t1, t0, 8
	sb t1, 21(a0)
	srli t1, t0, 16
	sb t1, 22(a0)
	srli t1, t0, 24
	sb t1, 23(a0)
	lui t0, 129086
	addiw t0, t0, -1621
	sb t0, 24(a0)
	srli t1, t0, 8
	sb t1, 25(a0)
	srli t1, t0, 16
	sb t1, 26(a0)
	srli t1, t0, 24
	sb t1, 27(a0)
	lui t0, 376333
	addiw t0, t0, -743
	sb t0, 28(a0)
	srli t1, t0, 8
	sb t1, 29(a0)
	srli t1, t0, 16
	sb t1, 30(a0)
	srli t1, t0, 24
	sb t1, 31(a0)
	addi a0, s6, 384
	addi a1, s6, 320
	addi a2, zero, 1
	addi a3, s6, 416
	call {vg_sha256_compress}
	addi s1, s6, 384
	addi s3, s6, 640
	lbu t1, 0(s1)
	lbu t2, 1(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 2(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 3(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 0(s3)
	srli t2, t1, 16
	sb t2, 1(s3)
	srli t2, t1, 8
	sb t2, 2(s3)
	srli t2, t1, 0
	sb t2, 3(s3)
	lbu t1, 4(s1)
	lbu t2, 5(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 6(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 7(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 4(s3)
	srli t2, t1, 16
	sb t2, 5(s3)
	srli t2, t1, 8
	sb t2, 6(s3)
	srli t2, t1, 0
	sb t2, 7(s3)
	lbu t1, 8(s1)
	lbu t2, 9(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 10(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 11(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 8(s3)
	srli t2, t1, 16
	sb t2, 9(s3)
	srli t2, t1, 8
	sb t2, 10(s3)
	srli t2, t1, 0
	sb t2, 11(s3)
	lbu t1, 12(s1)
	lbu t2, 13(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 14(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 15(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 12(s3)
	srli t2, t1, 16
	sb t2, 13(s3)
	srli t2, t1, 8
	sb t2, 14(s3)
	srli t2, t1, 0
	sb t2, 15(s3)
	lbu t1, 16(s1)
	lbu t2, 17(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 18(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 19(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 16(s3)
	srli t2, t1, 16
	sb t2, 17(s3)
	srli t2, t1, 8
	sb t2, 18(s3)
	srli t2, t1, 0
	sb t2, 19(s3)
	lbu t1, 20(s1)
	lbu t2, 21(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 22(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 23(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 20(s3)
	srli t2, t1, 16
	sb t2, 21(s3)
	srli t2, t1, 8
	sb t2, 22(s3)
	srli t2, t1, 0
	sb t2, 23(s3)
	lbu t1, 24(s1)
	lbu t2, 25(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 26(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 27(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 24(s3)
	srli t2, t1, 16
	sb t2, 25(s3)
	srli t2, t1, 8
	sb t2, 26(s3)
	srli t2, t1, 0
	sb t2, 27(s3)
	lbu t1, 28(s1)
	lbu t2, 29(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 30(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 31(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 28(s3)
	srli t2, t1, 16
	sb t2, 29(s3)
	srli t2, t1, 8
	sb t2, 30(s3)
	srli t2, t1, 0
	sb t2, 31(s3)
	ld a0, 8(s6)
	addi a1, s6, 320
	addi a2, zero, 32
2164:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 2164b
	addi a0, s6, 351
	ld a2, 40(s6)
	addi a2, a2, 6
	addi a3, zero, 32
2165:
	lbu a1, 0(a0)
	add a1, a1, a2
	sb a1, 0(a0)
	srli a2, a1, 8
	addi a0, a0, -1
	addi a3, a3, -1
	bnez a3, 2165b
	addi a0, s6, 384
	lui t0, 434334
	addiw t0, t0, 1639
	sb t0, 0(a0)
	srli t1, t0, 8
	sb t1, 1(a0)
	srli t1, t0, 16
	sb t1, 2(a0)
	srli t1, t0, 24
	sb t1, 3(a0)
	lui t0, 767611
	addiw t0, t0, -379
	sb t0, 4(a0)
	srli t1, t0, 8
	sb t1, 5(a0)
	srli t1, t0, 16
	sb t1, 6(a0)
	srli t1, t0, 24
	sb t1, 7(a0)
	lui t0, 247535
	addiw t0, t0, 882
	sb t0, 8(a0)
	srli t1, t0, 8
	sb t1, 9(a0)
	srli t1, t0, 16
	sb t1, 10(a0)
	srli t1, t0, 24
	sb t1, 11(a0)
	lui t0, 677119
	addiw t0, t0, 1338
	sb t0, 12(a0)
	srli t1, t0, 8
	sb t1, 13(a0)
	srli t1, t0, 16
	sb t1, 14(a0)
	srli t1, t0, 24
	sb t1, 15(a0)
	lui t0, 332005
	addiw t0, t0, 639
	sb t0, 16(a0)
	srli t1, t0, 8
	sb t1, 17(a0)
	srli t1, t0, 16
	sb t1, 18(a0)
	srli t1, t0, 24
	sb t1, 19(a0)
	lui t0, 634967
	addiw t0, t0, -1908
	sb t0, 20(a0)
	srli t1, t0, 8
	sb t1, 21(a0)
	srli t1, t0, 16
	sb t1, 22(a0)
	srli t1, t0, 24
	sb t1, 23(a0)
	lui t0, 129086
	addiw t0, t0, -1621
	sb t0, 24(a0)
	srli t1, t0, 8
	sb t1, 25(a0)
	srli t1, t0, 16
	sb t1, 26(a0)
	srli t1, t0, 24
	sb t1, 27(a0)
	lui t0, 376333
	addiw t0, t0, -743
	sb t0, 28(a0)
	srli t1, t0, 8
	sb t1, 29(a0)
	srli t1, t0, 16
	sb t1, 30(a0)
	srli t1, t0, 24
	sb t1, 31(a0)
	addi a0, s6, 384
	addi a1, s6, 320
	addi a2, zero, 1
	addi a3, s6, 416
	call {vg_sha256_compress}
	addi s1, s6, 384
	addi s3, s6, 608
	lbu t1, 0(s1)
	lbu t2, 1(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 2(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 3(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 0(s3)
	srli t2, t1, 16
	sb t2, 1(s3)
	srli t2, t1, 8
	sb t2, 2(s3)
	srli t2, t1, 0
	sb t2, 3(s3)
	lbu t1, 4(s1)
	lbu t2, 5(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 6(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 7(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 4(s3)
	srli t2, t1, 16
	sb t2, 5(s3)
	srli t2, t1, 8
	sb t2, 6(s3)
	srli t2, t1, 0
	sb t2, 7(s3)
	lbu t1, 8(s1)
	lbu t2, 9(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 10(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 11(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 8(s3)
	srli t2, t1, 16
	sb t2, 9(s3)
	srli t2, t1, 8
	sb t2, 10(s3)
	srli t2, t1, 0
	sb t2, 11(s3)
	lbu t1, 12(s1)
	lbu t2, 13(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 14(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 15(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 12(s3)
	srli t2, t1, 16
	sb t2, 13(s3)
	srli t2, t1, 8
	sb t2, 14(s3)
	srli t2, t1, 0
	sb t2, 15(s3)
	lbu t1, 16(s1)
	lbu t2, 17(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 18(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 19(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 16(s3)
	srli t2, t1, 16
	sb t2, 17(s3)
	srli t2, t1, 8
	sb t2, 18(s3)
	srli t2, t1, 0
	sb t2, 19(s3)
	lbu t1, 20(s1)
	lbu t2, 21(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 22(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 23(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 20(s3)
	srli t2, t1, 16
	sb t2, 21(s3)
	srli t2, t1, 8
	sb t2, 22(s3)
	srli t2, t1, 0
	sb t2, 23(s3)
	lbu t1, 24(s1)
	lbu t2, 25(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 26(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 27(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 24(s3)
	srli t2, t1, 16
	sb t2, 25(s3)
	srli t2, t1, 8
	sb t2, 26(s3)
	srli t2, t1, 0
	sb t2, 27(s3)
	lbu t1, 28(s1)
	lbu t2, 29(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 30(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 31(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 28(s3)
	srli t2, t1, 16
	sb t2, 29(s3)
	srli t2, t1, 8
	sb t2, 30(s3)
	srli t2, t1, 0
	sb t2, 31(s3)
	ld a0, 8(s6)
	addi a1, s6, 320
	addi a2, zero, 32
2166:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 2166b
	addi a0, s6, 351
	ld a2, 40(s6)
	addi a2, a2, 7
	addi a3, zero, 32
2167:
	lbu a1, 0(a0)
	add a1, a1, a2
	sb a1, 0(a0)
	srli a2, a1, 8
	addi a0, a0, -1
	addi a3, a3, -1
	bnez a3, 2167b
	addi a0, s6, 384
	lui t0, 434334
	addiw t0, t0, 1639
	sb t0, 0(a0)
	srli t1, t0, 8
	sb t1, 1(a0)
	srli t1, t0, 16
	sb t1, 2(a0)
	srli t1, t0, 24
	sb t1, 3(a0)
	lui t0, 767611
	addiw t0, t0, -379
	sb t0, 4(a0)
	srli t1, t0, 8
	sb t1, 5(a0)
	srli t1, t0, 16
	sb t1, 6(a0)
	srli t1, t0, 24
	sb t1, 7(a0)
	lui t0, 247535
	addiw t0, t0, 882
	sb t0, 8(a0)
	srli t1, t0, 8
	sb t1, 9(a0)
	srli t1, t0, 16
	sb t1, 10(a0)
	srli t1, t0, 24
	sb t1, 11(a0)
	lui t0, 677119
	addiw t0, t0, 1338
	sb t0, 12(a0)
	srli t1, t0, 8
	sb t1, 13(a0)
	srli t1, t0, 16
	sb t1, 14(a0)
	srli t1, t0, 24
	sb t1, 15(a0)
	lui t0, 332005
	addiw t0, t0, 639
	sb t0, 16(a0)
	srli t1, t0, 8
	sb t1, 17(a0)
	srli t1, t0, 16
	sb t1, 18(a0)
	srli t1, t0, 24
	sb t1, 19(a0)
	lui t0, 634967
	addiw t0, t0, -1908
	sb t0, 20(a0)
	srli t1, t0, 8
	sb t1, 21(a0)
	srli t1, t0, 16
	sb t1, 22(a0)
	srli t1, t0, 24
	sb t1, 23(a0)
	lui t0, 129086
	addiw t0, t0, -1621
	sb t0, 24(a0)
	srli t1, t0, 8
	sb t1, 25(a0)
	srli t1, t0, 16
	sb t1, 26(a0)
	srli t1, t0, 24
	sb t1, 27(a0)
	lui t0, 376333
	addiw t0, t0, -743
	sb t0, 28(a0)
	srli t1, t0, 8
	sb t1, 29(a0)
	srli t1, t0, 16
	sb t1, 30(a0)
	srli t1, t0, 24
	sb t1, 31(a0)
	addi a0, s6, 384
	addi a1, s6, 320
	addi a2, zero, 1
	addi a3, s6, 416
	call {vg_sha256_compress}
	addi s1, s6, 384
	addi s3, s6, 576
	lbu t1, 0(s1)
	lbu t2, 1(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 2(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 3(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 0(s3)
	srli t2, t1, 16
	sb t2, 1(s3)
	srli t2, t1, 8
	sb t2, 2(s3)
	srli t2, t1, 0
	sb t2, 3(s3)
	lbu t1, 4(s1)
	lbu t2, 5(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 6(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 7(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 4(s3)
	srli t2, t1, 16
	sb t2, 5(s3)
	srli t2, t1, 8
	sb t2, 6(s3)
	srli t2, t1, 0
	sb t2, 7(s3)
	lbu t1, 8(s1)
	lbu t2, 9(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 10(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 11(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 8(s3)
	srli t2, t1, 16
	sb t2, 9(s3)
	srli t2, t1, 8
	sb t2, 10(s3)
	srli t2, t1, 0
	sb t2, 11(s3)
	lbu t1, 12(s1)
	lbu t2, 13(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 14(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 15(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 12(s3)
	srli t2, t1, 16
	sb t2, 13(s3)
	srli t2, t1, 8
	sb t2, 14(s3)
	srli t2, t1, 0
	sb t2, 15(s3)
	lbu t1, 16(s1)
	lbu t2, 17(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 18(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 19(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 16(s3)
	srli t2, t1, 16
	sb t2, 17(s3)
	srli t2, t1, 8
	sb t2, 18(s3)
	srli t2, t1, 0
	sb t2, 19(s3)
	lbu t1, 20(s1)
	lbu t2, 21(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 22(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 23(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 20(s3)
	srli t2, t1, 16
	sb t2, 21(s3)
	srli t2, t1, 8
	sb t2, 22(s3)
	srli t2, t1, 0
	sb t2, 23(s3)
	lbu t1, 24(s1)
	lbu t2, 25(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 26(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 27(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 24(s3)
	srli t2, t1, 16
	sb t2, 25(s3)
	srli t2, t1, 8
	sb t2, 26(s3)
	srli t2, t1, 0
	sb t2, 27(s3)
	lbu t1, 28(s1)
	lbu t2, 29(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 30(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 31(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 28(s3)
	srli t2, t1, 16
	sb t2, 29(s3)
	srli t2, t1, 8
	sb t2, 30(s3)
	srli t2, t1, 0
	sb t2, 31(s3)
	lbu t2, 576(s6)
	ori t2, t2, 128
	sb t2, 576(s6)
	lui s11, 4
	add s11, s11, s6
	addi s10, zero, 272
	addi s9, zero, 32
	addi t3, zero, 15
	mul t3, t3, s10
	srli t3, t3, 3
	addi t0, s11, 256
	addi t5, zero, 0
2168:
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t3, t3, -1
	bnez t3, 2168b
	addi t0, zero, 11
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t5, zero, 1
	sd t5, 0(t0)
	addi a0, s6, 576
	addi a1, zero, 256
	addi t1, a0, 0
	addi t3, a1, 0
	addi t0, zero, 0
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	add t0, t0, t3
	addi t0, t0, -1
2169:
	lbu t5, 0(t1)
	sb t5, 0(t0)
	addi t1, t1, 1
	addi t0, t0, -1
	addi t3, t3, -1
	bnez t3, 2169b
	addi a0, s6, 576
	addi a1, zero, 256
	addi t1, a0, 0
	addi t3, a1, 0
	addi t0, zero, 4
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	add t0, t0, t3
	addi t0, t0, -1
2170:
	lbu t5, 0(t1)
	sb t5, 0(t0)
	addi t1, t1, 1
	addi t0, t0, -1
	addi t3, t3, -1
	bnez t3, 2170b
	addi a0, s6, 512
	addi a1, zero, 32
	addi t1, a0, 0
	addi t3, a1, 0
	addi t0, zero, 2
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	add t0, t0, t3
	addi t0, t0, -1
2171:
	lbu t5, 0(t1)
	sb t5, 0(t0)
	addi t1, t1, 1
	addi t0, t0, -1
	addi t3, t3, -1
	bnez t3, 2171b
	addi a1, zero, 32
	addi s8, a1, 7
	srli s8, s8, 3
	addi t0, zero, 1
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t3, s9, 1
	addi t5, zero, 0
2172:
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t3, t3, -1
	bnez t3, 2172b
	slli s7, s9, 6
	addi a4, zero, -1
2173:
	addi t2, zero, 0
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t5, s7, -1
	srli t5, t5, 6
	slli t5, t5, 3
	add t2, t2, t5
	ld t5, 0(t2)
	srli t3, t5, 63
	addi t0, zero, 1
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 2
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	andi t4, a4, 1
	addi t2, s8, 1
	andi t2, t2, 3
	beqz t2, 2174f
2176:
	ld t5, 0(t0)
	slli t6, t5, 1
	or t6, t6, t3
	srli t3, t5, 63
	ld t5, 0(t1)
	xor t5, t5, a4
	add t6, t6, t4
	sltu a5, t6, t4
	add t6, t6, t5
	sltu t4, t6, t5
	or t4, t4, a5
	sd t6, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t2, t2, -1
	bnez t2, 2176b
	j 2175f
2174:
2175:
	addi t2, s8, 1
	srli t2, t2, 2
	beqz t2, 2177f
2179:
	ld t5, 0(t0)
	slli t6, t5, 1
	or t6, t6, t3
	srli t3, t5, 63
	ld t5, 0(t1)
	xor t5, t5, a4
	add t6, t6, t4
	sltu a5, t6, t4
	add t6, t6, t5
	sltu t4, t6, t5
	or t4, t4, a5
	sd t6, 0(t0)
	ld t5, 8(t0)
	slli t6, t5, 1
	or t6, t6, t3
	srli t3, t5, 63
	ld t5, 8(t1)
	xor t5, t5, a4
	add t6, t6, t4
	sltu a5, t6, t4
	add t6, t6, t5
	sltu t4, t6, t5
	or t4, t4, a5
	sd t6, 8(t0)
	ld t5, 16(t0)
	slli t6, t5, 1
	or t6, t6, t3
	srli t3, t5, 63
	ld t5, 16(t1)
	xor t5, t5, a4
	add t6, t6, t4
	sltu a5, t6, t4
	add t6, t6, t5
	sltu t4, t6, t5
	or t4, t4, a5
	sd t6, 16(t0)
	ld t5, 24(t0)
	slli t6, t5, 1
	or t6, t6, t3
	srli t3, t5, 63
	ld t5, 24(t1)
	xor t5, t5, a4
	add t6, t6, t4
	sltu a5, t6, t4
	add t6, t6, t5
	sltu t4, t6, t5
	or t4, t4, a5
	sd t6, 24(t0)
	addi t0, t0, 32
	addi t1, t1, 32
	addi t2, t2, -1
	bnez t2, 2179b
	j 2178f
2177:
2178:
	srli t5, t6, 63
	addi a4, t5, -1
	andi a5, a4, 1
	addi t2, zero, 0
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t5, s7, -1
	srli t5, t5, 6
	slli t5, t5, 3
	add t2, t2, t5
	ld t5, 0(t2)
	slli t5, t5, 1
	or t5, t5, a5
	sd t5, 0(t2)
	addi s7, s7, -1
	bnez s7, 2173b
	addi t0, zero, 1
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 2
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	xori a4, a4, -1
	addi t4, zero, 0
	addi t3, s8, 1
2180:
	ld t5, 0(t0)
	ld t6, 0(t1)
	and t6, t6, a4
	add t5, t5, t4
	sltu a5, t5, t4
	add t5, t5, t6
	sltu t4, t5, t6
	or t4, t4, a5
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 2180b
	addi t0, zero, 5
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 4
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 1
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
2181:
	ld t5, 0(t1)
	ld t6, 0(t2)
	sltu a4, t5, t6
	sub t5, t5, t6
	sltu t6, t5, t4
	sub t5, t5, t4
	or t4, a4, t6
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 2181b
	addi t0, zero, 0
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld t5, 0(t0)
	andi t5, t5, 1
	sd t5, 160(s11)
	addi t0, zero, 6
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 13
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 2
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	ld t4, 160(s11)
	addi t5, zero, 0
	sub t4, t5, t4
	addi t3, s9, 0
2182:
	ld t5, 0(t1)
	ld t6, 0(t2)
	xor t6, t6, t5
	and t6, t6, t4
	xor t6, t6, t5
	sd t6, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 2182b
	addi t0, zero, 7
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 5
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 6
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
2183:
	ld t5, 0(t1)
	ld t6, 0(t2)
	sltu a4, t5, t6
	sub t5, t5, t6
	sltu t6, t5, t4
	sub t5, t5, t4
	or t4, a4, t6
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 2183b
	addi t0, zero, 8
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 7
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
2184:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 2184b
	addi t0, zero, 8
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld t5, 0(t0)
	ori t5, t5, 1
	sd t5, 0(t0)
	addi t0, zero, 9
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 0
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
2185:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 2185b
	addi t0, zero, 9
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld t5, 0(t0)
	andi t5, t5, -2
	sd t5, 0(t0)
	addi a0, s6, 960
	addi a1, zero, 256
	addi t4, zero, -1
	addi t1, zero, 8
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	add t1, t1, a1
	addi t1, t1, -1
	addi t0, a0, 0
	addi t3, a1, 0
2186:
	lbu t5, 0(t1)
	and t5, t5, t4
	sb t5, 0(t0)
	addi t0, t0, 1
	addi t1, t1, -1
	addi t3, t3, -1
	bnez t3, 2186b
	addi a0, s6, 1344
	addi a1, zero, 225
	addi t4, zero, -1
	addi t1, zero, 9
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	add t1, t1, a1
	addi t1, t1, -1
	addi t0, a0, 0
	addi t3, a1, 0
2187:
	lbu t5, 0(t1)
	and t5, t5, t4
	sb t5, 0(t0)
	addi t0, t0, 1
	addi t1, t1, -1
	addi t3, t3, -1
	bnez t3, 2187b
	lbu t2, 960(s6)
	srli t2, t2, 7
	beqz t2, 2188f
	addi a0, s6, 960
	lui a1, 6
	add a1, a1, s6
	addi a1, a1, 0
	addi a2, zero, 256
2190:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 2190b
	lui a0, 6
	add a0, a0, s6
	ld a1, 168(s6)
	lui t3, 6
	srli t3, t3, 3
	sub a1, a1, t3
	ld t2, 24(s6)
	ld a2, 72(s6)
	ld a3, 80(s6)
	add a2, a2, t2
	sub a3, a3, t2
	addi a4, s6, 112
	beqz a3, 2191f
	j 2192f
2191:
	ld a2, 72(s6)
2192:
	call {vg_dsa_probable_prime_2048}
	slli a0, a0, 32
	srli a0, a0, 32
	sd a0, 88(s6)
	beqz a0, 2193f
	ld t3, 112(s6)
	ld t4, 24(s6)
	add t4, t4, t3
	sd t4, 24(s6)
	j 2194f
2193:
2194:
	ld t2, 88(s6)
	addi t2, t2, 0
	beqz t2, 2195f
	ld t2, 88(s6)
	addi t2, t2, -1
	beqz t2, 2197f
	j 2198f
2197:
	addi t2, zero, 1
	sd t2, 96(s6)
2198:
	j 2196f
2195:
	addi t2, zero, 0
	sd t2, 96(s6)
2196:
	j 2189f
2188:
2189:
	ld t2, 96(s6)
	addi t2, t2, -4
	beqz t2, 2199f
	j 2200f
2199:
	ld t3, 32(s6)
	addi t3, t3, 1
	sd t3, 32(s6)
	ld t4, 40(s6)
	addi t4, t4, 8
	sd t4, 40(s6)
	addi t2, zero, 256
	slli t2, t2, 5
	sub t2, t3, t2
	beqz t2, 2201f
	j 2202f
2201:
	addi t2, zero, 2
	sd t2, 96(s6)
2202:
2200:
	ld t2, 96(s6)
	addi t2, t2, -4
	beqz t2, 2151b
	ld t2, 96(s6)
	addi t2, t2, 0
	beqz t2, 2203f
	ld t2, 96(s6)
	addi t2, t2, -1
	beqz t2, 2205f
	j 2206f
2205:
	ld t2, 72(s6)
	ld t3, 24(s6)
	add t2, t2, t3
	sd t2, 48(s6)
	sd t2, 128(s6)
	ld t4, 80(s6)
	sub t4, t4, t3
	addi t5, zero, 256
	slli t5, t5, 7
	bltu t4, t5, 2207f
	sd t5, 56(s6)
	addi t2, zero, 1
	sd t2, 136(s6)
	j 2208f
2207:
	sd t4, 56(s6)
	addi t2, zero, 0
	sd t2, 136(s6)
2208:
	addi t2, zero, 4
	sd t2, 104(s6)
2209:
	ld t2, 56(s6)
	addi t3, zero, 256
	bltu t2, t3, 2210f
	lui s11, 4
	add s11, s11, s6
	addi s10, zero, 272
	addi s9, zero, 32
	addi t0, zero, 10
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 13
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
2212:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 2212b
	ld a0, 48(s6)
	addi a1, zero, 256
	addi t1, a0, 0
	addi t3, a1, 0
	addi t0, zero, 10
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	add t0, t0, t3
	addi t0, t0, -1
2213:
	lbu t5, 0(t1)
	sb t5, 0(t0)
	addi t1, t1, 1
	addi t0, t0, -1
	addi t3, t3, -1
	bnez t3, 2213b
	addi t0, zero, 14
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 11
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 10
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
2214:
	ld t5, 0(t1)
	ld t6, 0(t2)
	sltu a4, t5, t6
	sub t5, t5, t6
	sltu t6, t5, t4
	sub t5, t5, t4
	or t4, a4, t6
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 2214b
	sd t4, 168(s11)
	addi t0, zero, 14
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 10
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 7
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
2215:
	ld t5, 0(t1)
	ld t6, 0(t2)
	sltu a4, t5, t6
	sub t5, t5, t6
	sltu t6, t5, t4
	sub t5, t5, t4
	or t4, a4, t6
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 2215b
	sd t4, 176(s11)
	ld t5, 168(s11)
	ld t6, 176(s11)
	and t5, t5, t6
	sd t5, 168(s11)
	ld t2, 168(s11)
	beqz t2, 2216f
	lui a7, 2
	add a7, a7, s6
	addi a7, a7, 256
	addi t0, zero, 32
	addi s5, zero, 272
	addi s7, s6, 960
	addi s8, zero, 256
	add t3, a7, s5
	addi t3, t3, -16
	addi s0, zero, 0
	sd s0, 0(t3)
	addi t3, a7, 0
	addi t5, t0, 0
	addi s0, zero, 0
2218:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2218b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
2219:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 2219b
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
2220:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2220b
	addi s0, zero, 1
	sd s0, 0(a2)
	slli a1, t0, 7
2221:
	addi t3, a5, 0
	addi t4, a2, 0
	addi t5, t0, 0
	addi s4, zero, 0
2222:
	ld s2, 0(t4)
	slli s3, s2, 1
	add s3, s3, s4
	srli s4, s2, 63
	sd s3, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2222b
	sd s4, 0(t3)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2223:
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
	bnez t5, 2223b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2224:
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
	bnez t5, 2224b
	addi a1, a1, -1
	bnez a1, 2221b
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
2225:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2225b
	ld s7, 48(s6)
	addi s8, zero, 256
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
2226:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2226b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
2227:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 2227b
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
2228:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2228b
	addi s9, s6, 1344
	addi s10, zero, 225
	call {vg_bignum_pow_win}
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t3, t3, -16
	addi s0, zero, 0
	sd s0, 0(t3)
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
2229:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2229b
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
2230:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2230b
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
2231:
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
	bnez t5, 2231b
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
2232:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2232b
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
2233:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2233b
	addi s0, zero, 0
	sltu s1, s0, t2
	addi a2, s1, -1
	or a1, a1, a2
	xor a1, a1, a2
	addi a0, a1, 0
	andi a0, a0, 1
	xori a0, a0, 1
	beqz a0, 2234f
	j 2235f
2234:
	addi s7, s6, 1728
	addi s8, zero, 256
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s8
	addi t3, t3, -1
	addi t4, s7, 0
	addi t5, s8, 0
2236:
	lbu s0, 0(t3)
	sb s0, 0(t4)
	addi t4, t4, 1
	addi t3, t3, -1
	addi t5, t5, -1
	bnez t5, 2236b
	addi t2, zero, 1
	sd t2, 104(s6)
2235:
	j 2217f
2216:
2217:
	ld t2, 48(s6)
	addi t2, t2, 256
	sd t2, 48(s6)
	ld t2, 56(s6)
	addi t2, t2, -256
	sd t2, 56(s6)
	j 2211f
2210:
	addi t2, zero, 2
	sd t2, 104(s6)
2211:
	ld t2, 104(s6)
	addi t2, t2, -4
	beqz t2, 2209b
	ld t2, 48(s6)
	ld t3, 128(s6)
	sub t2, t2, t3
	ld t3, 24(s6)
	add t3, t3, t2
	sd t3, 24(s6)
	ld t2, 104(s6)
	addi t2, t2, -1
	beqz t2, 2237f
	ld t2, 136(s6)
	beqz t2, 2239f
	j 2240f
2239:
	addi t2, zero, 0
	sd t2, 64(s6)
2240:
	j 2238f
2237:
	addi a0, s6, 960
	lui a1, 1
	add a1, a1, s6
	addi a1, a1, 0
	addi a2, zero, 256
2241:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 2241b
	addi a0, s6, 512
	lui a1, 1
	add a1, a1, s6
	addi a1, a1, 256
	addi a2, zero, 32
2242:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 2242b
	addi a0, s6, 1728
	lui a1, 1
	add a1, a1, s6
	addi a1, a1, 288
	addi a2, zero, 256
2243:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 2243b
	lui a0, 1
	add a0, a0, s6
	addi a1, zero, 544
	addi a2, zero, 256
	addi a3, zero, 32
	lui a4, 6
	add a4, a4, s6
	ld a5, 168(s6)
	lui t3, 6
	srli t3, t3, 3
	sub a5, a5, t3
	call {vg_dsa_check_parameters}
	slli a0, a0, 32
	srli a0, a0, 32
	addi t2, a0, -1
	beqz t2, 2244f
	j 2245f
2244:
	addi t2, zero, 1
	sd t2, 64(s6)
2245:
2238:
2206:
	j 2204f
2203:
	addi t2, zero, 0
	sd t2, 64(s6)
2204:
2150:
	j 2148f
2147:
	addi t2, zero, 0
	sd t2, 64(s6)
2148:
	ld t2, 64(s6)
	addi t2, t2, -2
	beqz t2, 2246f
	j 2247f
2246:
	ld t2, 16(s6)
	addi t2, t2, -1
	sd t2, 16(s6)
2247:
	j 2140f
2139:
	addi t2, zero, 0
	sd t2, 64(s6)
2140:
	j 2138f
2137:
	addi t2, zero, 3
	sd t2, 64(s6)
2138:
	ld t2, 64(s6)
	addi t2, t2, -2
	beqz t2, 2136b
	ld t2, 64(s6)
	addi t2, t2, -1
	beqz t2, 2248f
	ld a0, 0(s6)
	addi a1, zero, 544
	addi t0, a0, 0
	addi t3, a1, 0
	addi t5, zero, 0
2250:
	sb t5, 0(t0)
	addi t0, t0, 1
	addi t3, t3, -1
	bnez t3, 2250b
	ld t2, 64(s6)
	addi t2, t2, -3
	beqz t2, 2251f
	ld t4, 80(s6)
	ld t3, 144(s6)
	sub t4, t4, t3
	addi t5, zero, 256
	slli t5, t5, 15
	addi t5, t5, 256
	bltu t4, t5, 2253f
	addi t4, zero, 0
	addi t5, zero, 0
	ld t2, 144(s6)
	ld t3, 152(s6)
	sd t2, 0(t3)
	ld t3, 160(s6)
	sd t4, 0(t3)
	sd t5, 24(t3)
	addi a0, zero, 3
	j 2254f
2253:
	addi t3, zero, 256
	slli t3, t3, 8
	bltu t4, t3, 2255f
	j 2256f
2255:
	addi t4, t3, 0
2256:
	add t4, t4, t4
	bltu t4, t5, 2257f
	j 2258f
2257:
	addi t5, t4, 0
2258:
	ld t4, 16(s6)
	ld t2, 144(s6)
	ld t3, 152(s6)
	sd t2, 0(t3)
	ld t3, 160(s6)
	sd t4, 0(t3)
	sd t5, 24(t3)
	addi a0, zero, 0
2254:
	j 2252f
2251:
	addi t4, zero, 0
	addi t5, zero, 0
	ld t2, 144(s6)
	ld t3, 152(s6)
	sd t2, 0(t3)
	ld t3, 160(s6)
	sd t4, 0(t3)
	sd t5, 24(t3)
	addi a0, zero, 3
2252:
	j 2249f
2248:
	lui a0, 1
	add a0, a0, s6
	ld a1, 0(s6)
	addi a2, zero, 544
2259:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 2259b
	addi t4, zero, 0
	addi t5, zero, 0
	ld t2, 24(s6)
	ld t3, 152(s6)
	sd t2, 0(t3)
	ld t3, 160(s6)
	sd t4, 0(t3)
	sd t5, 24(t3)
	addi a0, zero, 1
2249:
23:
	j 21f
20:
	addi t2, zero, 0
	sd t2, 320(s6)
	sd t2, 328(s6)
	sd t2, 336(s6)
	sd t2, 344(s6)
	sd t2, 352(s6)
	sd t2, 360(s6)
	sd t2, 368(s6)
	sd t2, 376(s6)
	addi t2, zero, 128
	sb t2, 340(s6)
	addi t2, zero, 0
	sb t2, 382(s6)
	addi t2, zero, 160
	sb t2, 383(s6)
2260:
	ld t2, 24(s6)
	sd t2, 144(s6)
	ld t3, 16(s6)
	beqz t3, 2261f
	ld t3, 80(s6)
	sub t3, t3, t2
	addi t4, zero, 20
	bltu t3, t4, 2263f
	ld t3, 72(s6)
	add t3, t3, t2
	sd t3, 8(s6)
	addi t2, t2, 20
	sd t2, 24(s6)
	addi t2, zero, 2
	sd t2, 64(s6)
	ld a0, 8(s6)
	addi a1, s6, 320
	addi a2, zero, 20
2265:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 2265b
	addi a0, s6, 384
	lui t0, 422994
	addiw t0, t0, 769
	sb t0, 0(a0)
	srli t1, t0, 8
	sb t1, 1(a0)
	srli t1, t0, 16
	sb t1, 2(a0)
	srli t1, t0, 24
	sb t1, 3(a0)
	lui t0, 982235
	addiw t0, t0, -1143
	sb t0, 4(a0)
	srli t1, t0, 8
	sb t1, 5(a0)
	srli t1, t0, 16
	sb t1, 6(a0)
	srli t1, t0, 24
	sb t1, 7(a0)
	lui t0, 625582
	addiw t0, t0, -770
	sb t0, 8(a0)
	srli t1, t0, 8
	sb t1, 9(a0)
	srli t1, t0, 16
	sb t1, 10(a0)
	srli t1, t0, 24
	sb t1, 11(a0)
	lui t0, 66341
	addiw t0, t0, 1142
	sb t0, 12(a0)
	srli t1, t0, 8
	sb t1, 13(a0)
	srli t1, t0, 16
	sb t1, 14(a0)
	srli t1, t0, 24
	sb t1, 15(a0)
	lui t0, 802094
	addiw t0, t0, 496
	sb t0, 16(a0)
	srli t1, t0, 8
	sb t1, 17(a0)
	srli t1, t0, 16
	sb t1, 18(a0)
	srli t1, t0, 24
	sb t1, 19(a0)
	addi a0, s6, 384
	addi a1, s6, 320
	addi a2, zero, 1
	addi a3, s6, 416
	call {vg_sha1_compress}
	addi s1, s6, 384
	addi s3, s6, 512
	lbu t1, 0(s1)
	lbu t2, 1(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 2(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 3(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 0(s3)
	srli t2, t1, 16
	sb t2, 1(s3)
	srli t2, t1, 8
	sb t2, 2(s3)
	srli t2, t1, 0
	sb t2, 3(s3)
	lbu t1, 4(s1)
	lbu t2, 5(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 6(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 7(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 4(s3)
	srli t2, t1, 16
	sb t2, 5(s3)
	srli t2, t1, 8
	sb t2, 6(s3)
	srli t2, t1, 0
	sb t2, 7(s3)
	lbu t1, 8(s1)
	lbu t2, 9(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 10(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 11(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 8(s3)
	srli t2, t1, 16
	sb t2, 9(s3)
	srli t2, t1, 8
	sb t2, 10(s3)
	srli t2, t1, 0
	sb t2, 11(s3)
	lbu t1, 12(s1)
	lbu t2, 13(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 14(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 15(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 12(s3)
	srli t2, t1, 16
	sb t2, 13(s3)
	srli t2, t1, 8
	sb t2, 14(s3)
	srli t2, t1, 0
	sb t2, 15(s3)
	lbu t1, 16(s1)
	lbu t2, 17(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 18(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 19(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 16(s3)
	srli t2, t1, 16
	sb t2, 17(s3)
	srli t2, t1, 8
	sb t2, 18(s3)
	srli t2, t1, 0
	sb t2, 19(s3)
	lbu t2, 512(s6)
	ori t2, t2, 128
	sb t2, 512(s6)
	lbu t2, 531(s6)
	ori t2, t2, 1
	sb t2, 531(s6)
	addi a0, s6, 512
	lui a1, 5
	add a1, a1, s6
	addi a1, a1, 0
	addi a2, zero, 20
2266:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 2266b
	lui a0, 5
	add a0, a0, s6
	ld a1, 168(s6)
	lui t3, 5
	srli t3, t3, 3
	sub a1, a1, t3
	ld t2, 24(s6)
	ld a2, 72(s6)
	ld a3, 80(s6)
	add a2, a2, t2
	sub a3, a3, t2
	addi a4, s6, 112
	beqz a3, 2267f
	j 2268f
2267:
	ld a2, 72(s6)
2268:
	call {vg_dsa_probable_prime_160}
	slli a0, a0, 32
	srli a0, a0, 32
	sd a0, 88(s6)
	beqz a0, 2269f
	ld t3, 112(s6)
	ld t4, 24(s6)
	add t4, t4, t3
	sd t4, 24(s6)
	j 2270f
2269:
2270:
	ld t2, 88(s6)
	addi t2, t2, 0
	beqz t2, 2271f
	ld t2, 88(s6)
	addi t2, t2, -1
	beqz t2, 2273f
	j 2274f
2273:
	addi t2, zero, 0
	sd t2, 32(s6)
	addi t2, zero, 1
	sd t2, 40(s6)
	addi t2, zero, 4
	sd t2, 96(s6)
2275:
	ld a0, 8(s6)
	addi a1, s6, 320
	addi a2, zero, 20
2276:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 2276b
	addi a0, s6, 339
	ld a2, 40(s6)
	addi a2, a2, 0
	addi a3, zero, 20
2277:
	lbu a1, 0(a0)
	add a1, a1, a2
	sb a1, 0(a0)
	srli a2, a1, 8
	addi a0, a0, -1
	addi a3, a3, -1
	bnez a3, 2277b
	addi a0, s6, 384
	lui t0, 422994
	addiw t0, t0, 769
	sb t0, 0(a0)
	srli t1, t0, 8
	sb t1, 1(a0)
	srli t1, t0, 16
	sb t1, 2(a0)
	srli t1, t0, 24
	sb t1, 3(a0)
	lui t0, 982235
	addiw t0, t0, -1143
	sb t0, 4(a0)
	srli t1, t0, 8
	sb t1, 5(a0)
	srli t1, t0, 16
	sb t1, 6(a0)
	srli t1, t0, 24
	sb t1, 7(a0)
	lui t0, 625582
	addiw t0, t0, -770
	sb t0, 8(a0)
	srli t1, t0, 8
	sb t1, 9(a0)
	srli t1, t0, 16
	sb t1, 10(a0)
	srli t1, t0, 24
	sb t1, 11(a0)
	lui t0, 66341
	addiw t0, t0, 1142
	sb t0, 12(a0)
	srli t1, t0, 8
	sb t1, 13(a0)
	srli t1, t0, 16
	sb t1, 14(a0)
	srli t1, t0, 24
	sb t1, 15(a0)
	lui t0, 802094
	addiw t0, t0, 496
	sb t0, 16(a0)
	srli t1, t0, 8
	sb t1, 17(a0)
	srli t1, t0, 16
	sb t1, 18(a0)
	srli t1, t0, 24
	sb t1, 19(a0)
	addi a0, s6, 384
	addi a1, s6, 320
	addi a2, zero, 1
	addi a3, s6, 416
	call {vg_sha1_compress}
	addi s1, s6, 384
	addi s3, s6, 684
	lbu t1, 0(s1)
	lbu t2, 1(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 2(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 3(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 0(s3)
	srli t2, t1, 16
	sb t2, 1(s3)
	srli t2, t1, 8
	sb t2, 2(s3)
	srli t2, t1, 0
	sb t2, 3(s3)
	lbu t1, 4(s1)
	lbu t2, 5(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 6(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 7(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 4(s3)
	srli t2, t1, 16
	sb t2, 5(s3)
	srli t2, t1, 8
	sb t2, 6(s3)
	srli t2, t1, 0
	sb t2, 7(s3)
	lbu t1, 8(s1)
	lbu t2, 9(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 10(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 11(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 8(s3)
	srli t2, t1, 16
	sb t2, 9(s3)
	srli t2, t1, 8
	sb t2, 10(s3)
	srli t2, t1, 0
	sb t2, 11(s3)
	lbu t1, 12(s1)
	lbu t2, 13(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 14(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 15(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 12(s3)
	srli t2, t1, 16
	sb t2, 13(s3)
	srli t2, t1, 8
	sb t2, 14(s3)
	srli t2, t1, 0
	sb t2, 15(s3)
	lbu t1, 16(s1)
	lbu t2, 17(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 18(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 19(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 16(s3)
	srli t2, t1, 16
	sb t2, 17(s3)
	srli t2, t1, 8
	sb t2, 18(s3)
	srli t2, t1, 0
	sb t2, 19(s3)
	ld a0, 8(s6)
	addi a1, s6, 320
	addi a2, zero, 20
2278:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 2278b
	addi a0, s6, 339
	ld a2, 40(s6)
	addi a2, a2, 1
	addi a3, zero, 20
2279:
	lbu a1, 0(a0)
	add a1, a1, a2
	sb a1, 0(a0)
	srli a2, a1, 8
	addi a0, a0, -1
	addi a3, a3, -1
	bnez a3, 2279b
	addi a0, s6, 384
	lui t0, 422994
	addiw t0, t0, 769
	sb t0, 0(a0)
	srli t1, t0, 8
	sb t1, 1(a0)
	srli t1, t0, 16
	sb t1, 2(a0)
	srli t1, t0, 24
	sb t1, 3(a0)
	lui t0, 982235
	addiw t0, t0, -1143
	sb t0, 4(a0)
	srli t1, t0, 8
	sb t1, 5(a0)
	srli t1, t0, 16
	sb t1, 6(a0)
	srli t1, t0, 24
	sb t1, 7(a0)
	lui t0, 625582
	addiw t0, t0, -770
	sb t0, 8(a0)
	srli t1, t0, 8
	sb t1, 9(a0)
	srli t1, t0, 16
	sb t1, 10(a0)
	srli t1, t0, 24
	sb t1, 11(a0)
	lui t0, 66341
	addiw t0, t0, 1142
	sb t0, 12(a0)
	srli t1, t0, 8
	sb t1, 13(a0)
	srli t1, t0, 16
	sb t1, 14(a0)
	srli t1, t0, 24
	sb t1, 15(a0)
	lui t0, 802094
	addiw t0, t0, 496
	sb t0, 16(a0)
	srli t1, t0, 8
	sb t1, 17(a0)
	srli t1, t0, 16
	sb t1, 18(a0)
	srli t1, t0, 24
	sb t1, 19(a0)
	addi a0, s6, 384
	addi a1, s6, 320
	addi a2, zero, 1
	addi a3, s6, 416
	call {vg_sha1_compress}
	addi s1, s6, 384
	addi s3, s6, 664
	lbu t1, 0(s1)
	lbu t2, 1(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 2(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 3(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 0(s3)
	srli t2, t1, 16
	sb t2, 1(s3)
	srli t2, t1, 8
	sb t2, 2(s3)
	srli t2, t1, 0
	sb t2, 3(s3)
	lbu t1, 4(s1)
	lbu t2, 5(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 6(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 7(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 4(s3)
	srli t2, t1, 16
	sb t2, 5(s3)
	srli t2, t1, 8
	sb t2, 6(s3)
	srli t2, t1, 0
	sb t2, 7(s3)
	lbu t1, 8(s1)
	lbu t2, 9(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 10(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 11(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 8(s3)
	srli t2, t1, 16
	sb t2, 9(s3)
	srli t2, t1, 8
	sb t2, 10(s3)
	srli t2, t1, 0
	sb t2, 11(s3)
	lbu t1, 12(s1)
	lbu t2, 13(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 14(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 15(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 12(s3)
	srli t2, t1, 16
	sb t2, 13(s3)
	srli t2, t1, 8
	sb t2, 14(s3)
	srli t2, t1, 0
	sb t2, 15(s3)
	lbu t1, 16(s1)
	lbu t2, 17(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 18(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 19(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 16(s3)
	srli t2, t1, 16
	sb t2, 17(s3)
	srli t2, t1, 8
	sb t2, 18(s3)
	srli t2, t1, 0
	sb t2, 19(s3)
	ld a0, 8(s6)
	addi a1, s6, 320
	addi a2, zero, 20
2280:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 2280b
	addi a0, s6, 339
	ld a2, 40(s6)
	addi a2, a2, 2
	addi a3, zero, 20
2281:
	lbu a1, 0(a0)
	add a1, a1, a2
	sb a1, 0(a0)
	srli a2, a1, 8
	addi a0, a0, -1
	addi a3, a3, -1
	bnez a3, 2281b
	addi a0, s6, 384
	lui t0, 422994
	addiw t0, t0, 769
	sb t0, 0(a0)
	srli t1, t0, 8
	sb t1, 1(a0)
	srli t1, t0, 16
	sb t1, 2(a0)
	srli t1, t0, 24
	sb t1, 3(a0)
	lui t0, 982235
	addiw t0, t0, -1143
	sb t0, 4(a0)
	srli t1, t0, 8
	sb t1, 5(a0)
	srli t1, t0, 16
	sb t1, 6(a0)
	srli t1, t0, 24
	sb t1, 7(a0)
	lui t0, 625582
	addiw t0, t0, -770
	sb t0, 8(a0)
	srli t1, t0, 8
	sb t1, 9(a0)
	srli t1, t0, 16
	sb t1, 10(a0)
	srli t1, t0, 24
	sb t1, 11(a0)
	lui t0, 66341
	addiw t0, t0, 1142
	sb t0, 12(a0)
	srli t1, t0, 8
	sb t1, 13(a0)
	srli t1, t0, 16
	sb t1, 14(a0)
	srli t1, t0, 24
	sb t1, 15(a0)
	lui t0, 802094
	addiw t0, t0, 496
	sb t0, 16(a0)
	srli t1, t0, 8
	sb t1, 17(a0)
	srli t1, t0, 16
	sb t1, 18(a0)
	srli t1, t0, 24
	sb t1, 19(a0)
	addi a0, s6, 384
	addi a1, s6, 320
	addi a2, zero, 1
	addi a3, s6, 416
	call {vg_sha1_compress}
	addi s1, s6, 384
	addi s3, s6, 644
	lbu t1, 0(s1)
	lbu t2, 1(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 2(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 3(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 0(s3)
	srli t2, t1, 16
	sb t2, 1(s3)
	srli t2, t1, 8
	sb t2, 2(s3)
	srli t2, t1, 0
	sb t2, 3(s3)
	lbu t1, 4(s1)
	lbu t2, 5(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 6(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 7(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 4(s3)
	srli t2, t1, 16
	sb t2, 5(s3)
	srli t2, t1, 8
	sb t2, 6(s3)
	srli t2, t1, 0
	sb t2, 7(s3)
	lbu t1, 8(s1)
	lbu t2, 9(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 10(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 11(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 8(s3)
	srli t2, t1, 16
	sb t2, 9(s3)
	srli t2, t1, 8
	sb t2, 10(s3)
	srli t2, t1, 0
	sb t2, 11(s3)
	lbu t1, 12(s1)
	lbu t2, 13(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 14(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 15(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 12(s3)
	srli t2, t1, 16
	sb t2, 13(s3)
	srli t2, t1, 8
	sb t2, 14(s3)
	srli t2, t1, 0
	sb t2, 15(s3)
	lbu t1, 16(s1)
	lbu t2, 17(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 18(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 19(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 16(s3)
	srli t2, t1, 16
	sb t2, 17(s3)
	srli t2, t1, 8
	sb t2, 18(s3)
	srli t2, t1, 0
	sb t2, 19(s3)
	ld a0, 8(s6)
	addi a1, s6, 320
	addi a2, zero, 20
2282:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 2282b
	addi a0, s6, 339
	ld a2, 40(s6)
	addi a2, a2, 3
	addi a3, zero, 20
2283:
	lbu a1, 0(a0)
	add a1, a1, a2
	sb a1, 0(a0)
	srli a2, a1, 8
	addi a0, a0, -1
	addi a3, a3, -1
	bnez a3, 2283b
	addi a0, s6, 384
	lui t0, 422994
	addiw t0, t0, 769
	sb t0, 0(a0)
	srli t1, t0, 8
	sb t1, 1(a0)
	srli t1, t0, 16
	sb t1, 2(a0)
	srli t1, t0, 24
	sb t1, 3(a0)
	lui t0, 982235
	addiw t0, t0, -1143
	sb t0, 4(a0)
	srli t1, t0, 8
	sb t1, 5(a0)
	srli t1, t0, 16
	sb t1, 6(a0)
	srli t1, t0, 24
	sb t1, 7(a0)
	lui t0, 625582
	addiw t0, t0, -770
	sb t0, 8(a0)
	srli t1, t0, 8
	sb t1, 9(a0)
	srli t1, t0, 16
	sb t1, 10(a0)
	srli t1, t0, 24
	sb t1, 11(a0)
	lui t0, 66341
	addiw t0, t0, 1142
	sb t0, 12(a0)
	srli t1, t0, 8
	sb t1, 13(a0)
	srli t1, t0, 16
	sb t1, 14(a0)
	srli t1, t0, 24
	sb t1, 15(a0)
	lui t0, 802094
	addiw t0, t0, 496
	sb t0, 16(a0)
	srli t1, t0, 8
	sb t1, 17(a0)
	srli t1, t0, 16
	sb t1, 18(a0)
	srli t1, t0, 24
	sb t1, 19(a0)
	addi a0, s6, 384
	addi a1, s6, 320
	addi a2, zero, 1
	addi a3, s6, 416
	call {vg_sha1_compress}
	addi s1, s6, 384
	addi s3, s6, 624
	lbu t1, 0(s1)
	lbu t2, 1(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 2(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 3(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 0(s3)
	srli t2, t1, 16
	sb t2, 1(s3)
	srli t2, t1, 8
	sb t2, 2(s3)
	srli t2, t1, 0
	sb t2, 3(s3)
	lbu t1, 4(s1)
	lbu t2, 5(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 6(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 7(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 4(s3)
	srli t2, t1, 16
	sb t2, 5(s3)
	srli t2, t1, 8
	sb t2, 6(s3)
	srli t2, t1, 0
	sb t2, 7(s3)
	lbu t1, 8(s1)
	lbu t2, 9(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 10(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 11(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 8(s3)
	srli t2, t1, 16
	sb t2, 9(s3)
	srli t2, t1, 8
	sb t2, 10(s3)
	srli t2, t1, 0
	sb t2, 11(s3)
	lbu t1, 12(s1)
	lbu t2, 13(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 14(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 15(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 12(s3)
	srli t2, t1, 16
	sb t2, 13(s3)
	srli t2, t1, 8
	sb t2, 14(s3)
	srli t2, t1, 0
	sb t2, 15(s3)
	lbu t1, 16(s1)
	lbu t2, 17(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 18(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 19(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 16(s3)
	srli t2, t1, 16
	sb t2, 17(s3)
	srli t2, t1, 8
	sb t2, 18(s3)
	srli t2, t1, 0
	sb t2, 19(s3)
	ld a0, 8(s6)
	addi a1, s6, 320
	addi a2, zero, 20
2284:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 2284b
	addi a0, s6, 339
	ld a2, 40(s6)
	addi a2, a2, 4
	addi a3, zero, 20
2285:
	lbu a1, 0(a0)
	add a1, a1, a2
	sb a1, 0(a0)
	srli a2, a1, 8
	addi a0, a0, -1
	addi a3, a3, -1
	bnez a3, 2285b
	addi a0, s6, 384
	lui t0, 422994
	addiw t0, t0, 769
	sb t0, 0(a0)
	srli t1, t0, 8
	sb t1, 1(a0)
	srli t1, t0, 16
	sb t1, 2(a0)
	srli t1, t0, 24
	sb t1, 3(a0)
	lui t0, 982235
	addiw t0, t0, -1143
	sb t0, 4(a0)
	srli t1, t0, 8
	sb t1, 5(a0)
	srli t1, t0, 16
	sb t1, 6(a0)
	srli t1, t0, 24
	sb t1, 7(a0)
	lui t0, 625582
	addiw t0, t0, -770
	sb t0, 8(a0)
	srli t1, t0, 8
	sb t1, 9(a0)
	srli t1, t0, 16
	sb t1, 10(a0)
	srli t1, t0, 24
	sb t1, 11(a0)
	lui t0, 66341
	addiw t0, t0, 1142
	sb t0, 12(a0)
	srli t1, t0, 8
	sb t1, 13(a0)
	srli t1, t0, 16
	sb t1, 14(a0)
	srli t1, t0, 24
	sb t1, 15(a0)
	lui t0, 802094
	addiw t0, t0, 496
	sb t0, 16(a0)
	srli t1, t0, 8
	sb t1, 17(a0)
	srli t1, t0, 16
	sb t1, 18(a0)
	srli t1, t0, 24
	sb t1, 19(a0)
	addi a0, s6, 384
	addi a1, s6, 320
	addi a2, zero, 1
	addi a3, s6, 416
	call {vg_sha1_compress}
	addi s1, s6, 384
	addi s3, s6, 604
	lbu t1, 0(s1)
	lbu t2, 1(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 2(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 3(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 0(s3)
	srli t2, t1, 16
	sb t2, 1(s3)
	srli t2, t1, 8
	sb t2, 2(s3)
	srli t2, t1, 0
	sb t2, 3(s3)
	lbu t1, 4(s1)
	lbu t2, 5(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 6(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 7(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 4(s3)
	srli t2, t1, 16
	sb t2, 5(s3)
	srli t2, t1, 8
	sb t2, 6(s3)
	srli t2, t1, 0
	sb t2, 7(s3)
	lbu t1, 8(s1)
	lbu t2, 9(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 10(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 11(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 8(s3)
	srli t2, t1, 16
	sb t2, 9(s3)
	srli t2, t1, 8
	sb t2, 10(s3)
	srli t2, t1, 0
	sb t2, 11(s3)
	lbu t1, 12(s1)
	lbu t2, 13(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 14(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 15(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 12(s3)
	srli t2, t1, 16
	sb t2, 13(s3)
	srli t2, t1, 8
	sb t2, 14(s3)
	srli t2, t1, 0
	sb t2, 15(s3)
	lbu t1, 16(s1)
	lbu t2, 17(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 18(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 19(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 16(s3)
	srli t2, t1, 16
	sb t2, 17(s3)
	srli t2, t1, 8
	sb t2, 18(s3)
	srli t2, t1, 0
	sb t2, 19(s3)
	ld a0, 8(s6)
	addi a1, s6, 320
	addi a2, zero, 20
2286:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 2286b
	addi a0, s6, 339
	ld a2, 40(s6)
	addi a2, a2, 5
	addi a3, zero, 20
2287:
	lbu a1, 0(a0)
	add a1, a1, a2
	sb a1, 0(a0)
	srli a2, a1, 8
	addi a0, a0, -1
	addi a3, a3, -1
	bnez a3, 2287b
	addi a0, s6, 384
	lui t0, 422994
	addiw t0, t0, 769
	sb t0, 0(a0)
	srli t1, t0, 8
	sb t1, 1(a0)
	srli t1, t0, 16
	sb t1, 2(a0)
	srli t1, t0, 24
	sb t1, 3(a0)
	lui t0, 982235
	addiw t0, t0, -1143
	sb t0, 4(a0)
	srli t1, t0, 8
	sb t1, 5(a0)
	srli t1, t0, 16
	sb t1, 6(a0)
	srli t1, t0, 24
	sb t1, 7(a0)
	lui t0, 625582
	addiw t0, t0, -770
	sb t0, 8(a0)
	srli t1, t0, 8
	sb t1, 9(a0)
	srli t1, t0, 16
	sb t1, 10(a0)
	srli t1, t0, 24
	sb t1, 11(a0)
	lui t0, 66341
	addiw t0, t0, 1142
	sb t0, 12(a0)
	srli t1, t0, 8
	sb t1, 13(a0)
	srli t1, t0, 16
	sb t1, 14(a0)
	srli t1, t0, 24
	sb t1, 15(a0)
	lui t0, 802094
	addiw t0, t0, 496
	sb t0, 16(a0)
	srli t1, t0, 8
	sb t1, 17(a0)
	srli t1, t0, 16
	sb t1, 18(a0)
	srli t1, t0, 24
	sb t1, 19(a0)
	addi a0, s6, 384
	addi a1, s6, 320
	addi a2, zero, 1
	addi a3, s6, 416
	call {vg_sha1_compress}
	addi s1, s6, 384
	addi s3, s6, 584
	lbu t1, 0(s1)
	lbu t2, 1(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 2(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 3(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 0(s3)
	srli t2, t1, 16
	sb t2, 1(s3)
	srli t2, t1, 8
	sb t2, 2(s3)
	srli t2, t1, 0
	sb t2, 3(s3)
	lbu t1, 4(s1)
	lbu t2, 5(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 6(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 7(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 4(s3)
	srli t2, t1, 16
	sb t2, 5(s3)
	srli t2, t1, 8
	sb t2, 6(s3)
	srli t2, t1, 0
	sb t2, 7(s3)
	lbu t1, 8(s1)
	lbu t2, 9(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 10(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 11(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 8(s3)
	srli t2, t1, 16
	sb t2, 9(s3)
	srli t2, t1, 8
	sb t2, 10(s3)
	srli t2, t1, 0
	sb t2, 11(s3)
	lbu t1, 12(s1)
	lbu t2, 13(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 14(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 15(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 12(s3)
	srli t2, t1, 16
	sb t2, 13(s3)
	srli t2, t1, 8
	sb t2, 14(s3)
	srli t2, t1, 0
	sb t2, 15(s3)
	lbu t1, 16(s1)
	lbu t2, 17(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 18(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 19(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 16(s3)
	srli t2, t1, 16
	sb t2, 17(s3)
	srli t2, t1, 8
	sb t2, 18(s3)
	srli t2, t1, 0
	sb t2, 19(s3)
	ld a0, 8(s6)
	addi a1, s6, 320
	addi a2, zero, 20
2288:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 2288b
	addi a0, s6, 339
	ld a2, 40(s6)
	addi a2, a2, 6
	addi a3, zero, 20
2289:
	lbu a1, 0(a0)
	add a1, a1, a2
	sb a1, 0(a0)
	srli a2, a1, 8
	addi a0, a0, -1
	addi a3, a3, -1
	bnez a3, 2289b
	addi a0, s6, 384
	lui t0, 422994
	addiw t0, t0, 769
	sb t0, 0(a0)
	srli t1, t0, 8
	sb t1, 1(a0)
	srli t1, t0, 16
	sb t1, 2(a0)
	srli t1, t0, 24
	sb t1, 3(a0)
	lui t0, 982235
	addiw t0, t0, -1143
	sb t0, 4(a0)
	srli t1, t0, 8
	sb t1, 5(a0)
	srli t1, t0, 16
	sb t1, 6(a0)
	srli t1, t0, 24
	sb t1, 7(a0)
	lui t0, 625582
	addiw t0, t0, -770
	sb t0, 8(a0)
	srli t1, t0, 8
	sb t1, 9(a0)
	srli t1, t0, 16
	sb t1, 10(a0)
	srli t1, t0, 24
	sb t1, 11(a0)
	lui t0, 66341
	addiw t0, t0, 1142
	sb t0, 12(a0)
	srli t1, t0, 8
	sb t1, 13(a0)
	srli t1, t0, 16
	sb t1, 14(a0)
	srli t1, t0, 24
	sb t1, 15(a0)
	lui t0, 802094
	addiw t0, t0, 496
	sb t0, 16(a0)
	srli t1, t0, 8
	sb t1, 17(a0)
	srli t1, t0, 16
	sb t1, 18(a0)
	srli t1, t0, 24
	sb t1, 19(a0)
	addi a0, s6, 384
	addi a1, s6, 320
	addi a2, zero, 1
	addi a3, s6, 416
	call {vg_sha1_compress}
	addi s1, s6, 384
	addi s3, s6, 564
	lbu t1, 0(s1)
	lbu t2, 1(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 2(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 3(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 0(s3)
	srli t2, t1, 16
	sb t2, 1(s3)
	srli t2, t1, 8
	sb t2, 2(s3)
	srli t2, t1, 0
	sb t2, 3(s3)
	lbu t1, 4(s1)
	lbu t2, 5(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 6(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 7(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 4(s3)
	srli t2, t1, 16
	sb t2, 5(s3)
	srli t2, t1, 8
	sb t2, 6(s3)
	srli t2, t1, 0
	sb t2, 7(s3)
	lbu t1, 8(s1)
	lbu t2, 9(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 10(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 11(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 8(s3)
	srli t2, t1, 16
	sb t2, 9(s3)
	srli t2, t1, 8
	sb t2, 10(s3)
	srli t2, t1, 0
	sb t2, 11(s3)
	lbu t1, 12(s1)
	lbu t2, 13(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 14(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 15(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 12(s3)
	srli t2, t1, 16
	sb t2, 13(s3)
	srli t2, t1, 8
	sb t2, 14(s3)
	srli t2, t1, 0
	sb t2, 15(s3)
	lbu t1, 16(s1)
	lbu t2, 17(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 18(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 19(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 16(s3)
	srli t2, t1, 16
	sb t2, 17(s3)
	srli t2, t1, 8
	sb t2, 18(s3)
	srli t2, t1, 0
	sb t2, 19(s3)
	lbu t2, 576(s6)
	ori t2, t2, 128
	sb t2, 576(s6)
	lui s11, 4
	add s11, s11, s6
	addi s10, zero, 144
	addi s9, zero, 16
	addi t3, zero, 15
	mul t3, t3, s10
	srli t3, t3, 3
	addi t0, s11, 256
	addi t5, zero, 0
2290:
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t3, t3, -1
	bnez t3, 2290b
	addi t0, zero, 11
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t5, zero, 1
	sd t5, 0(t0)
	addi a0, s6, 576
	addi a1, zero, 128
	addi t1, a0, 0
	addi t3, a1, 0
	addi t0, zero, 0
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	add t0, t0, t3
	addi t0, t0, -1
2291:
	lbu t5, 0(t1)
	sb t5, 0(t0)
	addi t1, t1, 1
	addi t0, t0, -1
	addi t3, t3, -1
	bnez t3, 2291b
	addi a0, s6, 576
	addi a1, zero, 128
	addi t1, a0, 0
	addi t3, a1, 0
	addi t0, zero, 4
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	add t0, t0, t3
	addi t0, t0, -1
2292:
	lbu t5, 0(t1)
	sb t5, 0(t0)
	addi t1, t1, 1
	addi t0, t0, -1
	addi t3, t3, -1
	bnez t3, 2292b
	addi a0, s6, 512
	addi a1, zero, 20
	addi t1, a0, 0
	addi t3, a1, 0
	addi t0, zero, 2
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	add t0, t0, t3
	addi t0, t0, -1
2293:
	lbu t5, 0(t1)
	sb t5, 0(t0)
	addi t1, t1, 1
	addi t0, t0, -1
	addi t3, t3, -1
	bnez t3, 2293b
	addi a1, zero, 20
	addi s8, a1, 7
	srli s8, s8, 3
	addi t0, zero, 1
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t3, s9, 1
	addi t5, zero, 0
2294:
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t3, t3, -1
	bnez t3, 2294b
	slli s7, s9, 6
	addi a4, zero, -1
2295:
	addi t2, zero, 0
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t5, s7, -1
	srli t5, t5, 6
	slli t5, t5, 3
	add t2, t2, t5
	ld t5, 0(t2)
	srli t3, t5, 63
	addi t0, zero, 1
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 2
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	andi t4, a4, 1
	addi t2, s8, 1
	andi t2, t2, 3
	beqz t2, 2296f
2298:
	ld t5, 0(t0)
	slli t6, t5, 1
	or t6, t6, t3
	srli t3, t5, 63
	ld t5, 0(t1)
	xor t5, t5, a4
	add t6, t6, t4
	sltu a5, t6, t4
	add t6, t6, t5
	sltu t4, t6, t5
	or t4, t4, a5
	sd t6, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t2, t2, -1
	bnez t2, 2298b
	j 2297f
2296:
2297:
	addi t2, s8, 1
	srli t2, t2, 2
	beqz t2, 2299f
2301:
	ld t5, 0(t0)
	slli t6, t5, 1
	or t6, t6, t3
	srli t3, t5, 63
	ld t5, 0(t1)
	xor t5, t5, a4
	add t6, t6, t4
	sltu a5, t6, t4
	add t6, t6, t5
	sltu t4, t6, t5
	or t4, t4, a5
	sd t6, 0(t0)
	ld t5, 8(t0)
	slli t6, t5, 1
	or t6, t6, t3
	srli t3, t5, 63
	ld t5, 8(t1)
	xor t5, t5, a4
	add t6, t6, t4
	sltu a5, t6, t4
	add t6, t6, t5
	sltu t4, t6, t5
	or t4, t4, a5
	sd t6, 8(t0)
	ld t5, 16(t0)
	slli t6, t5, 1
	or t6, t6, t3
	srli t3, t5, 63
	ld t5, 16(t1)
	xor t5, t5, a4
	add t6, t6, t4
	sltu a5, t6, t4
	add t6, t6, t5
	sltu t4, t6, t5
	or t4, t4, a5
	sd t6, 16(t0)
	ld t5, 24(t0)
	slli t6, t5, 1
	or t6, t6, t3
	srli t3, t5, 63
	ld t5, 24(t1)
	xor t5, t5, a4
	add t6, t6, t4
	sltu a5, t6, t4
	add t6, t6, t5
	sltu t4, t6, t5
	or t4, t4, a5
	sd t6, 24(t0)
	addi t0, t0, 32
	addi t1, t1, 32
	addi t2, t2, -1
	bnez t2, 2301b
	j 2300f
2299:
2300:
	srli t5, t6, 63
	addi a4, t5, -1
	andi a5, a4, 1
	addi t2, zero, 0
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t5, s7, -1
	srli t5, t5, 6
	slli t5, t5, 3
	add t2, t2, t5
	ld t5, 0(t2)
	slli t5, t5, 1
	or t5, t5, a5
	sd t5, 0(t2)
	addi s7, s7, -1
	bnez s7, 2295b
	addi t0, zero, 1
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 2
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	xori a4, a4, -1
	addi t4, zero, 0
	addi t3, s8, 1
2302:
	ld t5, 0(t0)
	ld t6, 0(t1)
	and t6, t6, a4
	add t5, t5, t4
	sltu a5, t5, t4
	add t5, t5, t6
	sltu t4, t5, t6
	or t4, t4, a5
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 2302b
	addi t0, zero, 5
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 4
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 1
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
2303:
	ld t5, 0(t1)
	ld t6, 0(t2)
	sltu a4, t5, t6
	sub t5, t5, t6
	sltu t6, t5, t4
	sub t5, t5, t4
	or t4, a4, t6
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 2303b
	addi t0, zero, 0
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld t5, 0(t0)
	andi t5, t5, 1
	sd t5, 160(s11)
	addi t0, zero, 6
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 13
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 2
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	ld t4, 160(s11)
	addi t5, zero, 0
	sub t4, t5, t4
	addi t3, s9, 0
2304:
	ld t5, 0(t1)
	ld t6, 0(t2)
	xor t6, t6, t5
	and t6, t6, t4
	xor t6, t6, t5
	sd t6, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 2304b
	addi t0, zero, 7
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 5
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 6
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
2305:
	ld t5, 0(t1)
	ld t6, 0(t2)
	sltu a4, t5, t6
	sub t5, t5, t6
	sltu t6, t5, t4
	sub t5, t5, t4
	or t4, a4, t6
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 2305b
	addi t0, zero, 8
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 7
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
2306:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 2306b
	addi t0, zero, 8
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld t5, 0(t0)
	ori t5, t5, 1
	sd t5, 0(t0)
	addi t0, zero, 9
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 0
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
2307:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 2307b
	addi t0, zero, 9
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld t5, 0(t0)
	andi t5, t5, -2
	sd t5, 0(t0)
	addi a0, s6, 960
	addi a1, zero, 128
	addi t4, zero, -1
	addi t1, zero, 8
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	add t1, t1, a1
	addi t1, t1, -1
	addi t0, a0, 0
	addi t3, a1, 0
2308:
	lbu t5, 0(t1)
	and t5, t5, t4
	sb t5, 0(t0)
	addi t0, t0, 1
	addi t1, t1, -1
	addi t3, t3, -1
	bnez t3, 2308b
	addi a0, s6, 1344
	addi a1, zero, 109
	addi t4, zero, -1
	addi t1, zero, 9
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	add t1, t1, a1
	addi t1, t1, -1
	addi t0, a0, 0
	addi t3, a1, 0
2309:
	lbu t5, 0(t1)
	and t5, t5, t4
	sb t5, 0(t0)
	addi t0, t0, 1
	addi t1, t1, -1
	addi t3, t3, -1
	bnez t3, 2309b
	lbu t2, 960(s6)
	srli t2, t2, 7
	beqz t2, 2310f
	addi a0, s6, 960
	lui a1, 5
	add a1, a1, s6
	addi a1, a1, 0
	addi a2, zero, 128
2312:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 2312b
	lui a0, 5
	add a0, a0, s6
	ld a1, 168(s6)
	lui t3, 5
	srli t3, t3, 3
	sub a1, a1, t3
	ld t2, 24(s6)
	ld a2, 72(s6)
	ld a3, 80(s6)
	add a2, a2, t2
	sub a3, a3, t2
	addi a4, s6, 112
	beqz a3, 2313f
	j 2314f
2313:
	ld a2, 72(s6)
2314:
	call {vg_dsa_probable_prime_1024}
	slli a0, a0, 32
	srli a0, a0, 32
	sd a0, 88(s6)
	beqz a0, 2315f
	ld t3, 112(s6)
	ld t4, 24(s6)
	add t4, t4, t3
	sd t4, 24(s6)
	j 2316f
2315:
2316:
	ld t2, 88(s6)
	addi t2, t2, 0
	beqz t2, 2317f
	ld t2, 88(s6)
	addi t2, t2, -1
	beqz t2, 2319f
	j 2320f
2319:
	addi t2, zero, 1
	sd t2, 96(s6)
2320:
	j 2318f
2317:
	addi t2, zero, 0
	sd t2, 96(s6)
2318:
	j 2311f
2310:
2311:
	ld t2, 96(s6)
	addi t2, t2, -4
	beqz t2, 2321f
	j 2322f
2321:
	ld t3, 32(s6)
	addi t3, t3, 1
	sd t3, 32(s6)
	ld t4, 40(s6)
	addi t4, t4, 7
	sd t4, 40(s6)
	addi t2, zero, 128
	slli t2, t2, 5
	sub t2, t3, t2
	beqz t2, 2323f
	j 2324f
2323:
	addi t2, zero, 2
	sd t2, 96(s6)
2324:
2322:
	ld t2, 96(s6)
	addi t2, t2, -4
	beqz t2, 2275b
	ld t2, 96(s6)
	addi t2, t2, 0
	beqz t2, 2325f
	ld t2, 96(s6)
	addi t2, t2, -1
	beqz t2, 2327f
	j 2328f
2327:
	ld t2, 72(s6)
	ld t3, 24(s6)
	add t2, t2, t3
	sd t2, 48(s6)
	sd t2, 128(s6)
	ld t4, 80(s6)
	sub t4, t4, t3
	addi t5, zero, 128
	slli t5, t5, 7
	bltu t4, t5, 2329f
	sd t5, 56(s6)
	addi t2, zero, 1
	sd t2, 136(s6)
	j 2330f
2329:
	sd t4, 56(s6)
	addi t2, zero, 0
	sd t2, 136(s6)
2330:
	addi t2, zero, 4
	sd t2, 104(s6)
2331:
	ld t2, 56(s6)
	addi t3, zero, 128
	bltu t2, t3, 2332f
	lui s11, 4
	add s11, s11, s6
	addi s10, zero, 144
	addi s9, zero, 16
	addi t0, zero, 10
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 13
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
2334:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 2334b
	ld a0, 48(s6)
	addi a1, zero, 128
	addi t1, a0, 0
	addi t3, a1, 0
	addi t0, zero, 10
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	add t0, t0, t3
	addi t0, t0, -1
2335:
	lbu t5, 0(t1)
	sb t5, 0(t0)
	addi t1, t1, 1
	addi t0, t0, -1
	addi t3, t3, -1
	bnez t3, 2335b
	addi t0, zero, 14
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 11
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 10
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
2336:
	ld t5, 0(t1)
	ld t6, 0(t2)
	sltu a4, t5, t6
	sub t5, t5, t6
	sltu t6, t5, t4
	sub t5, t5, t4
	or t4, a4, t6
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 2336b
	sd t4, 168(s11)
	addi t0, zero, 14
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 10
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 7
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
2337:
	ld t5, 0(t1)
	ld t6, 0(t2)
	sltu a4, t5, t6
	sub t5, t5, t6
	sltu t6, t5, t4
	sub t5, t5, t4
	or t4, a4, t6
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 2337b
	sd t4, 176(s11)
	ld t5, 168(s11)
	ld t6, 176(s11)
	and t5, t5, t6
	sd t5, 168(s11)
	ld t2, 168(s11)
	beqz t2, 2338f
	lui a7, 2
	add a7, a7, s6
	addi a7, a7, 256
	addi t0, zero, 16
	addi s5, zero, 144
	addi s7, s6, 960
	addi s8, zero, 128
	add t3, a7, s5
	addi t3, t3, -16
	addi s0, zero, 0
	sd s0, 0(t3)
	addi t3, a7, 0
	addi t5, t0, 0
	addi s0, zero, 0
2340:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2340b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
2341:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 2341b
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
2342:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2342b
	addi s0, zero, 1
	sd s0, 0(a2)
	slli a1, t0, 7
2343:
	addi t3, a5, 0
	addi t4, a2, 0
	addi t5, t0, 0
	addi s4, zero, 0
2344:
	ld s2, 0(t4)
	slli s3, s2, 1
	add s3, s3, s4
	srli s4, s2, 63
	sd s3, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2344b
	sd s4, 0(t3)
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
	addi a1, a1, -1
	bnez a1, 2343b
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
2347:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2347b
	ld s7, 48(s6)
	addi s8, zero, 128
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
2348:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2348b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
2349:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 2349b
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
2350:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2350b
	addi s9, s6, 1344
	addi s10, zero, 109
	call {vg_bignum_pow_win}
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t3, t3, -16
	addi s0, zero, 0
	sd s0, 0(t3)
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
2351:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2351b
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
2352:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2352b
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
2353:
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
	bnez t5, 2353b
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
2354:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2354b
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
2355:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2355b
	addi s0, zero, 0
	sltu s1, s0, t2
	addi a2, s1, -1
	or a1, a1, a2
	xor a1, a1, a2
	addi a0, a1, 0
	andi a0, a0, 1
	xori a0, a0, 1
	beqz a0, 2356f
	j 2357f
2356:
	addi s7, s6, 1728
	addi s8, zero, 128
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s8
	addi t3, t3, -1
	addi t4, s7, 0
	addi t5, s8, 0
2358:
	lbu s0, 0(t3)
	sb s0, 0(t4)
	addi t4, t4, 1
	addi t3, t3, -1
	addi t5, t5, -1
	bnez t5, 2358b
	addi t2, zero, 1
	sd t2, 104(s6)
2357:
	j 2339f
2338:
2339:
	ld t2, 48(s6)
	addi t2, t2, 128
	sd t2, 48(s6)
	ld t2, 56(s6)
	addi t2, t2, -128
	sd t2, 56(s6)
	j 2333f
2332:
	addi t2, zero, 2
	sd t2, 104(s6)
2333:
	ld t2, 104(s6)
	addi t2, t2, -4
	beqz t2, 2331b
	ld t2, 48(s6)
	ld t3, 128(s6)
	sub t2, t2, t3
	ld t3, 24(s6)
	add t3, t3, t2
	sd t3, 24(s6)
	ld t2, 104(s6)
	addi t2, t2, -1
	beqz t2, 2359f
	ld t2, 136(s6)
	beqz t2, 2361f
	j 2362f
2361:
	addi t2, zero, 0
	sd t2, 64(s6)
2362:
	j 2360f
2359:
	addi a0, s6, 960
	lui a1, 1
	add a1, a1, s6
	addi a1, a1, 0
	addi a2, zero, 128
2363:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 2363b
	addi a0, s6, 512
	lui a1, 1
	add a1, a1, s6
	addi a1, a1, 128
	addi a2, zero, 20
2364:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 2364b
	addi a0, s6, 1728
	lui a1, 1
	add a1, a1, s6
	addi a1, a1, 148
	addi a2, zero, 128
2365:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 2365b
	lui a0, 1
	add a0, a0, s6
	addi a1, zero, 276
	addi a2, zero, 128
	addi a3, zero, 20
	lui a4, 5
	add a4, a4, s6
	ld a5, 168(s6)
	lui t3, 5
	srli t3, t3, 3
	sub a5, a5, t3
	call {vg_dsa_check_parameters}
	slli a0, a0, 32
	srli a0, a0, 32
	addi t2, a0, -1
	beqz t2, 2366f
	j 2367f
2366:
	addi t2, zero, 1
	sd t2, 64(s6)
2367:
2360:
2328:
	j 2326f
2325:
	addi t2, zero, 0
	sd t2, 64(s6)
2326:
2274:
	j 2272f
2271:
	addi t2, zero, 0
	sd t2, 64(s6)
2272:
	ld t2, 64(s6)
	addi t2, t2, -2
	beqz t2, 2368f
	j 2369f
2368:
	ld t2, 16(s6)
	addi t2, t2, -1
	sd t2, 16(s6)
2369:
	j 2264f
2263:
	addi t2, zero, 0
	sd t2, 64(s6)
2264:
	j 2262f
2261:
	addi t2, zero, 3
	sd t2, 64(s6)
2262:
	ld t2, 64(s6)
	addi t2, t2, -2
	beqz t2, 2260b
	ld t2, 64(s6)
	addi t2, t2, -1
	beqz t2, 2370f
	ld a0, 0(s6)
	addi a1, zero, 276
	addi t0, a0, 0
	addi t3, a1, 0
	addi t5, zero, 0
2372:
	sb t5, 0(t0)
	addi t0, t0, 1
	addi t3, t3, -1
	bnez t3, 2372b
	ld t2, 64(s6)
	addi t2, t2, -3
	beqz t2, 2373f
	ld t4, 80(s6)
	ld t3, 144(s6)
	sub t4, t4, t3
	addi t5, zero, 128
	slli t5, t5, 15
	addi t5, t5, 128
	bltu t4, t5, 2375f
	addi t4, zero, 0
	addi t5, zero, 0
	ld t2, 144(s6)
	ld t3, 152(s6)
	sd t2, 0(t3)
	ld t3, 160(s6)
	sd t4, 0(t3)
	sd t5, 24(t3)
	addi a0, zero, 3
	j 2376f
2375:
	addi t3, zero, 128
	slli t3, t3, 8
	bltu t4, t3, 2377f
	j 2378f
2377:
	addi t4, t3, 0
2378:
	add t4, t4, t4
	bltu t4, t5, 2379f
	j 2380f
2379:
	addi t5, t4, 0
2380:
	ld t4, 16(s6)
	ld t2, 144(s6)
	ld t3, 152(s6)
	sd t2, 0(t3)
	ld t3, 160(s6)
	sd t4, 0(t3)
	sd t5, 24(t3)
	addi a0, zero, 0
2376:
	j 2374f
2373:
	addi t4, zero, 0
	addi t5, zero, 0
	ld t2, 144(s6)
	ld t3, 152(s6)
	sd t2, 0(t3)
	ld t3, 160(s6)
	sd t4, 0(t3)
	sd t5, 24(t3)
	addi a0, zero, 3
2374:
	j 2371f
2370:
	lui a0, 1
	add a0, a0, s6
	ld a1, 0(s6)
	addi a2, zero, 276
2381:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 2381b
	addi t4, zero, 0
	addi t5, zero, 0
	ld t2, 24(s6)
	ld t3, 152(s6)
	sd t2, 0(t3)
	ld t3, 160(s6)
	sd t4, 0(t3)
	sd t5, 24(t3)
	addi a0, zero, 1
2371:
21:
	ld ra, 120(s6)
	ld s0, 184(s6)
	ld s1, 192(s6)
	ld s2, 200(s6)
	ld s3, 208(s6)
	ld s4, 216(s6)
	ld s5, 224(s6)
	ld s7, 232(s6)
	ld s8, 240(s6)
	ld s9, 248(s6)
	ld s10, 256(s6)
	ld s11, 264(s6)
	ld s6, 272(s6)
	addi t0, zero, 0
	addi sp, sp, -512
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
	addi sp, sp, 512
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
