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
	slli t3, t0, 3
	add t3, t3, a7
	addi t3, t3, -8
	ld s0, 0(t3)
	beqz s0, 246f
	addi t3, zero, 4
	bltu t0, t3, 248f
	slli t3, t0, 3
	add t3, t3, a7
	addi t3, t3, -8
	ld s0, 0(t3)
	addi a1, zero, 0
	addi t5, zero, 63
250:
	srli s1, s0, 63
	xori s1, s1, 1
	sll s0, s0, s1
	add a1, a1, s1
	addi t5, t5, -1
	bnez t5, 250b
	addi s0, zero, 1
	sll s0, s0, a1
	slli t3, t0, 3
	add t3, t3, a7
	addi t3, t3, -24
	ld s2, 16(t3)
	ld s3, 8(t3)
	sll s2, s2, a1
	mulhu s4, s3, s0
	add s2, s2, s4
	mul s3, s3, s0
	ld s1, 0(t3)
	mulhu s1, s1, s0
	add s3, s3, s1
	sd s0, 0(a6)
	sd s2, 8(a6)
	sd s3, 24(a6)
	addi a4, zero, 0
	addi s3, zero, -1
	sub s3, s3, s2
	addi s4, zero, 0
	addi t5, zero, 64
251:
	srli s1, s3, 63
	slli s3, s3, 1
	ori s3, s3, 1
	sltu s0, s3, s2
	xori s0, s0, 1
	or s0, s0, s1
	sub s1, a4, s0
	and s1, s1, s2
	sub s3, s3, s1
	slli s4, s4, 1
	or s4, s4, s0
	addi t5, t5, -1
	bnez t5, 251b
	sd s4, 16(a6)
	addi t3, a2, 0
	addi t5, t0, 0
	addi s0, zero, 0
252:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 252b
	sd a4, 0(t3)
	addi s0, zero, 62
	sltu s0, s0, t0
	addi s1, zero, 125
	sltu s1, s1, t0
	add s0, s0, s1
	addi s0, s0, 1
	add a1, t0, s0
	addi a1, a1, 1
	slli s1, t0, 6
	add s1, s1, t0
	slli s2, s0, 6
	sub s2, s2, s0
	sub s1, s1, s2
	srli s2, s1, 6
	slli s2, s2, 3
	add s2, s2, a2
	andi s1, s1, 63
	addi s3, zero, 1
	sll s3, s3, s1
	sd s3, 0(s2)
253:
	slli t3, t0, 3
	add t3, t3, a2
	addi t3, t3, -16
	ld t4, 16(t3)
	ld t5, 8(t3)
	ld t6, 0(t3)
	ld s0, 0(a6)
	ld s2, 8(a6)
	ld s3, 16(a6)
	mul t4, t4, s0
	mulhu s1, t5, s0
	add t4, t4, s1
	mul t5, t5, s0
	mulhu s1, t6, s0
	add t5, t5, s1
	sub a3, s2, t4
	mul s0, s3, t4
	mulhu s1, s3, t4
	add s0, s0, t5
	sltu t6, s0, t5
	add s1, s1, t4
	add s1, s1, t6
	addi s1, s1, 1
	mul t6, s1, s2
	sub t6, t5, t6
	sltu s4, s0, t6
	sub s1, s1, s4
	sub s4, a4, s4
	and s4, s4, s2
	add t6, t6, s4
	sltu s4, t6, s2
	xori s4, s4, 1
	add s1, s1, s4
	sltu s4, a4, a3
	addi s4, s4, -1
	or s1, s1, s4
	ld s0, 0(a6)
	ld t6, 0(t3)
	addi a0, t3, -8
	ld a0, 0(a0)
	mul t6, t6, s0
	mulhu a0, a0, s0
	add t6, t6, a0
	ld a0, 24(a6)
	mul s0, s1, a0
	mulhu a3, s1, a0
	mul s3, s1, s2
	mulhu s4, s1, s2
	add s3, s3, a3
	sltu a3, s3, a3
	add s4, s4, a3
	sltu a3, t6, s0
	sub t6, t6, s0
	sltu s0, t5, s3
	sub t5, t5, s3
	sltu s3, t5, a3
	sub t5, t5, a3
	or a3, s0, s3
	sub t4, t4, s4
	sub t4, t4, a3
	srli a3, t4, 63
	sub s1, s1, a3
	sub a3, a4, a3
	and s0, a0, a3
	and s3, s2, a3
	add t6, t6, s0
	sltu s0, t6, s0
	add t5, t5, s3
	sltu s3, t5, s3
	add t5, t5, s0
	sltu s0, t5, s0
	or s3, s3, s0
	add t4, t4, s3
	srli a3, t4, 63
	sub s1, s1, a3
	sltu s4, a4, s1
	sub s1, s1, s4
	addi t6, zero, 0
	addi t3, a2, 0
	addi t4, a7, 0
	addi t5, t0, 0
	addi s0, zero, 0
	addi s4, zero, 0
254:
	ld s2, 0(t4)
	mul s3, s2, s1
	mulhu s2, s2, s1
	add s3, s3, s0
	sltu s0, s3, s0
	add s0, s2, s0
	ld a0, 0(t3)
	sltu s2, a0, s3
	sub s3, a0, s3
	sltu a3, s3, s4
	sub s3, s3, s4
	or s4, s2, a3
	srli a0, t6, 1
	slli a3, s3, 63
	or a0, a0, a3
	sd a0, 0(t3)
	addi t6, s3, 0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 254b
	ld a0, 0(t3)
	sub s3, a0, s0
	sub s3, s3, s4
	srli a0, t6, 1
	slli a3, s3, 63
	or a0, a0, a3
	sd a0, 0(t3)
	addi a1, a1, -1
	bnez a1, 253b
	addi t3, a2, 0
	addi t4, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
	ld s2, 0(a2)
255:
	ld s3, 8(t3)
	srli s2, s2, 63
	slli a0, s3, 1
	or s2, s2, a0
	sd s2, 0(t3)
	ld a0, 0(t4)
	sltu s0, s2, a0
	sub s2, s2, a0
	sltu a3, s2, s4
	or s4, s0, a3
	addi s2, s3, 0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 255b
	srli s2, s2, 63
	sd s2, 0(t3)
	sltu s4, s2, s4
	xori s4, s4, 1
	sub s1, a4, s4
	addi t3, a2, 0
	addi t4, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
256:
	ld s2, 0(t3)
	ld s3, 0(t4)
	and s3, s3, s1
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu a3, s2, s4
	sub s2, s2, s4
	or s4, s0, a3
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 256b
	ld s2, 0(t3)
	sub s2, s2, s4
	sd s2, 0(t3)
	j 249f
248:
	addi t3, a2, 0
	addi t5, t0, 0
	addi s0, zero, 0
257:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 257b
	slli t3, t0, 3
	add t3, t3, a2
	addi t3, t3, -8
	addi s0, zero, 1
	sd s0, 0(t3)
	addi a1, t0, 64
258:
	addi t3, a5, 0
	addi t4, a2, 0
	addi t5, t0, 0
	addi s4, zero, 0
259:
	ld s2, 0(t4)
	slli s3, s2, 1
	add s3, s3, s4
	srli s4, s2, 63
	sd s3, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 259b
	sd s4, 0(t3)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
260:
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
	bnez t5, 260b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
261:
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
	bnez t5, 261b
	addi a1, a1, -1
	bnez a1, 258b
	addi s7, zero, 6
262:
	addi a3, a2, 0
	addi a4, a2, 0
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
	addi a0, a7, 0
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
	beqz t5, 265f
267:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
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
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 16(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 24(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 24(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 8(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 24(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 32(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 32(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 16(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 32(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 40(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 40(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 24(t3)
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
	slli s2, t0, 3
	sub a0, a0, s2
	addi a0, a0, 8
	addi a1, a1, -1
	bnez a1, 264b
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
	addi s7, s7, -1
	bnez s7, 262b
249:
	j 247f
246:
	addi t3, a2, 0
	addi t5, t0, 0
	addi s0, zero, 0
273:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 273b
	addi s0, zero, 1
	sd s0, 0(a2)
	slli a1, t0, 7
274:
	addi t3, a5, 0
	addi t4, a2, 0
	addi t5, t0, 0
	addi s4, zero, 0
275:
	ld s2, 0(t4)
	slli s3, s2, 1
	add s3, s3, s4
	srli s4, s2, 63
	sd s3, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 275b
	sd s4, 0(t3)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
276:
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
	bnez t5, 276b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
277:
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
	bnez t5, 277b
	addi a1, a1, -1
	bnez a1, 274b
247:
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
278:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 278b
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
279:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 279b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
280:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 280b
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
281:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 281b
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
282:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 282b
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
283:
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
	bnez t5, 283b
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
284:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 284b
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
285:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 285b
	addi s0, zero, 0
	sltu s1, s0, t2
	addi a2, s1, -1
	or a1, a1, a2
	xor a1, a1, a2
	addi a0, a1, 0
	andi a0, a0, 1
	xori a0, a0, 1
	beqz a0, 286f
	j 287f
286:
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
288:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 288b
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
289:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 289b
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
290:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 290b
	addi s0, zero, 0
	sltu s1, s0, t2
	addi a0, s1, -1
	andi a0, a0, 1
	xori a0, a0, 1
287:
	beqz a0, 291f
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
293:
	sb s0, 0(t4)
	addi t4, t4, 1
	addi t5, t5, -1
	bnez t5, 293b
	addi a0, zero, 0
	j 292f
291:
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
296:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 296b
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
297:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 297b
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
298:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 298b
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
299:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 299b
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
2100:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2100b
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
2101:
	lbu s0, 0(t3)
	sb s0, 0(t4)
	addi t4, t4, 1
	addi t3, t3, -1
	addi t5, t5, -1
	bnez t5, 2101b
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
2104:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2104b
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
2105:
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
	bnez t5, 2105b
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
2106:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2106b
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
2107:
	lbu s0, 0(t3)
	and s0, s0, a4
	sb s0, 0(t4)
	addi t3, t3, 1
	addi t4, t4, 1
	addi t5, t5, -1
	bnez t5, 2107b
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
2108:
	lbu s0, 0(t3)
	and s0, s0, a4
	sb s0, 0(t4)
	addi t3, t3, 1
	addi t4, t4, 1
	addi t5, t5, -1
	bnez t5, 2108b
	addi t3, ra, 0
	ld t5, 16(s6)
	slli t5, t5, 32
	srli t5, t5, 48
2109:
	lbu s0, 0(t3)
	and s0, s0, a4
	sb s0, 0(t4)
	addi t3, t3, 1
	addi t4, t4, 1
	addi t5, t5, -1
	bnez t5, 2109b
	andi a0, a4, 1
292:
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
	addiw a0, a0, 0
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
	slli t3, t0, 3
	add t3, t3, a7
	addi t3, t3, -8
	ld s0, 0(t3)
	beqz s0, 240f
	addi t3, zero, 4
	bltu t0, t3, 242f
	slli t3, t0, 3
	add t3, t3, a7
	addi t3, t3, -8
	ld s0, 0(t3)
	addi a1, zero, 0
	addi t5, zero, 63
244:
	srli s1, s0, 63
	xori s1, s1, 1
	sll s0, s0, s1
	add a1, a1, s1
	addi t5, t5, -1
	bnez t5, 244b
	addi s0, zero, 1
	sll s0, s0, a1
	slli t3, t0, 3
	add t3, t3, a7
	addi t3, t3, -24
	ld s2, 16(t3)
	ld s3, 8(t3)
	sll s2, s2, a1
	mulhu s4, s3, s0
	add s2, s2, s4
	mul s3, s3, s0
	ld s1, 0(t3)
	mulhu s1, s1, s0
	add s3, s3, s1
	sd s0, 0(a6)
	sd s2, 8(a6)
	sd s3, 24(a6)
	addi a4, zero, 0
	addi s3, zero, -1
	sub s3, s3, s2
	addi s4, zero, 0
	addi t5, zero, 64
245:
	srli s1, s3, 63
	slli s3, s3, 1
	ori s3, s3, 1
	sltu s0, s3, s2
	xori s0, s0, 1
	or s0, s0, s1
	sub s1, a4, s0
	and s1, s1, s2
	sub s3, s3, s1
	slli s4, s4, 1
	or s4, s4, s0
	addi t5, t5, -1
	bnez t5, 245b
	sd s4, 16(a6)
	addi t3, a2, 0
	addi t5, t0, 0
	addi s0, zero, 0
246:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 246b
	sd a4, 0(t3)
	addi s0, zero, 62
	sltu s0, s0, t0
	addi s1, zero, 125
	sltu s1, s1, t0
	add s0, s0, s1
	addi s0, s0, 1
	add a1, t0, s0
	addi a1, a1, 1
	slli s1, t0, 6
	add s1, s1, t0
	slli s2, s0, 6
	sub s2, s2, s0
	sub s1, s1, s2
	srli s2, s1, 6
	slli s2, s2, 3
	add s2, s2, a2
	andi s1, s1, 63
	addi s3, zero, 1
	sll s3, s3, s1
	sd s3, 0(s2)
247:
	slli t3, t0, 3
	add t3, t3, a2
	addi t3, t3, -16
	ld t4, 16(t3)
	ld t5, 8(t3)
	ld t6, 0(t3)
	ld s0, 0(a6)
	ld s2, 8(a6)
	ld s3, 16(a6)
	mul t4, t4, s0
	mulhu s1, t5, s0
	add t4, t4, s1
	mul t5, t5, s0
	mulhu s1, t6, s0
	add t5, t5, s1
	sub a3, s2, t4
	mul s0, s3, t4
	mulhu s1, s3, t4
	add s0, s0, t5
	sltu t6, s0, t5
	add s1, s1, t4
	add s1, s1, t6
	addi s1, s1, 1
	mul t6, s1, s2
	sub t6, t5, t6
	sltu s4, s0, t6
	sub s1, s1, s4
	sub s4, a4, s4
	and s4, s4, s2
	add t6, t6, s4
	sltu s4, t6, s2
	xori s4, s4, 1
	add s1, s1, s4
	sltu s4, a4, a3
	addi s4, s4, -1
	or s1, s1, s4
	ld s0, 0(a6)
	ld t6, 0(t3)
	addi a0, t3, -8
	ld a0, 0(a0)
	mul t6, t6, s0
	mulhu a0, a0, s0
	add t6, t6, a0
	ld a0, 24(a6)
	mul s0, s1, a0
	mulhu a3, s1, a0
	mul s3, s1, s2
	mulhu s4, s1, s2
	add s3, s3, a3
	sltu a3, s3, a3
	add s4, s4, a3
	sltu a3, t6, s0
	sub t6, t6, s0
	sltu s0, t5, s3
	sub t5, t5, s3
	sltu s3, t5, a3
	sub t5, t5, a3
	or a3, s0, s3
	sub t4, t4, s4
	sub t4, t4, a3
	srli a3, t4, 63
	sub s1, s1, a3
	sub a3, a4, a3
	and s0, a0, a3
	and s3, s2, a3
	add t6, t6, s0
	sltu s0, t6, s0
	add t5, t5, s3
	sltu s3, t5, s3
	add t5, t5, s0
	sltu s0, t5, s0
	or s3, s3, s0
	add t4, t4, s3
	srli a3, t4, 63
	sub s1, s1, a3
	sltu s4, a4, s1
	sub s1, s1, s4
	addi t6, zero, 0
	addi t3, a2, 0
	addi t4, a7, 0
	addi t5, t0, 0
	addi s0, zero, 0
	addi s4, zero, 0
248:
	ld s2, 0(t4)
	mul s3, s2, s1
	mulhu s2, s2, s1
	add s3, s3, s0
	sltu s0, s3, s0
	add s0, s2, s0
	ld a0, 0(t3)
	sltu s2, a0, s3
	sub s3, a0, s3
	sltu a3, s3, s4
	sub s3, s3, s4
	or s4, s2, a3
	srli a0, t6, 1
	slli a3, s3, 63
	or a0, a0, a3
	sd a0, 0(t3)
	addi t6, s3, 0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 248b
	ld a0, 0(t3)
	sub s3, a0, s0
	sub s3, s3, s4
	srli a0, t6, 1
	slli a3, s3, 63
	or a0, a0, a3
	sd a0, 0(t3)
	addi a1, a1, -1
	bnez a1, 247b
	addi t3, a2, 0
	addi t4, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
	ld s2, 0(a2)
249:
	ld s3, 8(t3)
	srli s2, s2, 63
	slli a0, s3, 1
	or s2, s2, a0
	sd s2, 0(t3)
	ld a0, 0(t4)
	sltu s0, s2, a0
	sub s2, s2, a0
	sltu a3, s2, s4
	or s4, s0, a3
	addi s2, s3, 0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 249b
	srli s2, s2, 63
	sd s2, 0(t3)
	sltu s4, s2, s4
	xori s4, s4, 1
	sub s1, a4, s4
	addi t3, a2, 0
	addi t4, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
250:
	ld s2, 0(t3)
	ld s3, 0(t4)
	and s3, s3, s1
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu a3, s2, s4
	sub s2, s2, s4
	or s4, s0, a3
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 250b
	ld s2, 0(t3)
	sub s2, s2, s4
	sd s2, 0(t3)
	j 243f
242:
	addi t3, a2, 0
	addi t5, t0, 0
	addi s0, zero, 0
251:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 251b
	slli t3, t0, 3
	add t3, t3, a2
	addi t3, t3, -8
	addi s0, zero, 1
	sd s0, 0(t3)
	addi a1, t0, 64
252:
	addi t3, a5, 0
	addi t4, a2, 0
	addi t5, t0, 0
	addi s4, zero, 0
253:
	ld s2, 0(t4)
	slli s3, s2, 1
	add s3, s3, s4
	srli s4, s2, 63
	sd s3, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 253b
	sd s4, 0(t3)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
254:
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
	bnez t5, 254b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
255:
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
	bnez t5, 255b
	addi a1, a1, -1
	bnez a1, 252b
	addi s7, zero, 6
256:
	addi a3, a2, 0
	addi a4, a2, 0
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
	addi a0, a7, 0
257:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 257b
258:
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
	beqz t5, 259f
261:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 261b
	j 260f
259:
260:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 262f
264:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 16(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 24(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 24(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 8(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 24(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 32(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 32(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 16(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 32(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 40(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 40(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 264b
	j 263f
262:
263:
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
	bnez a1, 258b
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
265:
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
	bnez t5, 265b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
266:
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
	bnez t5, 266b
	addi s7, s7, -1
	bnez s7, 256b
243:
	j 241f
240:
	addi t3, a2, 0
	addi t5, t0, 0
	addi s0, zero, 0
267:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 267b
	addi s0, zero, 1
	sd s0, 0(a2)
	slli a1, t0, 7
268:
	addi t3, a5, 0
	addi t4, a2, 0
	addi t5, t0, 0
	addi s4, zero, 0
269:
	ld s2, 0(t4)
	slli s3, s2, 1
	add s3, s3, s4
	srli s4, s2, 63
	sd s3, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 269b
	sd s4, 0(t3)
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
	addi a1, a1, -1
	bnez a1, 268b
241:
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
272:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 272b
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
273:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 273b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
274:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 274b
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
275:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 275b
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
276:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 276b
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
277:
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
	bnez t5, 277b
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
278:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 278b
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
	addi a0, a1, 0
	andi a0, a0, 1
	xori a0, a0, 1
	beqz a0, 280f
	j 281f
280:
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
282:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 282b
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
283:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 283b
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
284:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 284b
	addi s0, zero, 0
	sltu s1, s0, t2
	addi a0, s1, -1
	andi a0, a0, 1
	xori a0, a0, 1
281:
	beqz a0, 285f
	addi a0, zero, 0
	j 286f
285:
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
287:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 287b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
288:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 288b
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
289:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 289b
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
290:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 290b
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
291:
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
	bnez t5, 291b
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
292:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 292b
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
293:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 293b
	addi s0, zero, 0
	sltu s1, s0, t2
	addi a2, s1, -1
	or a1, a1, a2
	xor a1, a1, a2
	addi a0, a1, 0
	andi a0, a0, 1
	xori a0, a0, 1
	beqz a0, 294f
	addi a0, zero, 0
	j 295f
294:
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
296:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 296b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
297:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 297b
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
298:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 298b
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
299:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 299b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
2100:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 2100b
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
2101:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2101b
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
2102:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2102b
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
2103:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2103b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
2104:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 2104b
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
2105:
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
	bnez t5, 2105b
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
2106:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2106b
	addi s0, zero, 0
	sltu s1, s0, t2
	addi a2, s1, -1
	or a1, a1, a2
	xor a1, a1, a2
	and a4, a4, a1
	andi a0, a4, 1
295:
286:
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
	addiw a0, a0, 0
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
	addiw a0, a0, 0
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
	addiw a0, a0, 0
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
	slli t3, t0, 3
	add t3, t3, a7
	addi t3, t3, -8
	ld s0, 0(t3)
	beqz s0, 240f
	addi t3, zero, 4
	bltu t0, t3, 242f
	slli t3, t0, 3
	add t3, t3, a7
	addi t3, t3, -8
	ld s0, 0(t3)
	addi a1, zero, 0
	addi t5, zero, 63
244:
	srli s1, s0, 63
	xori s1, s1, 1
	sll s0, s0, s1
	add a1, a1, s1
	addi t5, t5, -1
	bnez t5, 244b
	addi s0, zero, 1
	sll s0, s0, a1
	slli t3, t0, 3
	add t3, t3, a7
	addi t3, t3, -24
	ld s2, 16(t3)
	ld s3, 8(t3)
	sll s2, s2, a1
	mulhu s4, s3, s0
	add s2, s2, s4
	mul s3, s3, s0
	ld s1, 0(t3)
	mulhu s1, s1, s0
	add s3, s3, s1
	sd s0, 0(a6)
	sd s2, 8(a6)
	sd s3, 24(a6)
	addi a4, zero, 0
	addi s3, zero, -1
	sub s3, s3, s2
	addi s4, zero, 0
	addi t5, zero, 64
245:
	srli s1, s3, 63
	slli s3, s3, 1
	ori s3, s3, 1
	sltu s0, s3, s2
	xori s0, s0, 1
	or s0, s0, s1
	sub s1, a4, s0
	and s1, s1, s2
	sub s3, s3, s1
	slli s4, s4, 1
	or s4, s4, s0
	addi t5, t5, -1
	bnez t5, 245b
	sd s4, 16(a6)
	addi t3, a2, 0
	addi t5, t0, 0
	addi s0, zero, 0
246:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 246b
	sd a4, 0(t3)
	addi s0, zero, 62
	sltu s0, s0, t0
	addi s1, zero, 125
	sltu s1, s1, t0
	add s0, s0, s1
	addi s0, s0, 1
	add a1, t0, s0
	addi a1, a1, 1
	slli s1, t0, 6
	add s1, s1, t0
	slli s2, s0, 6
	sub s2, s2, s0
	sub s1, s1, s2
	srli s2, s1, 6
	slli s2, s2, 3
	add s2, s2, a2
	andi s1, s1, 63
	addi s3, zero, 1
	sll s3, s3, s1
	sd s3, 0(s2)
247:
	slli t3, t0, 3
	add t3, t3, a2
	addi t3, t3, -16
	ld t4, 16(t3)
	ld t5, 8(t3)
	ld t6, 0(t3)
	ld s0, 0(a6)
	ld s2, 8(a6)
	ld s3, 16(a6)
	mul t4, t4, s0
	mulhu s1, t5, s0
	add t4, t4, s1
	mul t5, t5, s0
	mulhu s1, t6, s0
	add t5, t5, s1
	sub a3, s2, t4
	mul s0, s3, t4
	mulhu s1, s3, t4
	add s0, s0, t5
	sltu t6, s0, t5
	add s1, s1, t4
	add s1, s1, t6
	addi s1, s1, 1
	mul t6, s1, s2
	sub t6, t5, t6
	sltu s4, s0, t6
	sub s1, s1, s4
	sub s4, a4, s4
	and s4, s4, s2
	add t6, t6, s4
	sltu s4, t6, s2
	xori s4, s4, 1
	add s1, s1, s4
	sltu s4, a4, a3
	addi s4, s4, -1
	or s1, s1, s4
	ld s0, 0(a6)
	ld t6, 0(t3)
	addi a0, t3, -8
	ld a0, 0(a0)
	mul t6, t6, s0
	mulhu a0, a0, s0
	add t6, t6, a0
	ld a0, 24(a6)
	mul s0, s1, a0
	mulhu a3, s1, a0
	mul s3, s1, s2
	mulhu s4, s1, s2
	add s3, s3, a3
	sltu a3, s3, a3
	add s4, s4, a3
	sltu a3, t6, s0
	sub t6, t6, s0
	sltu s0, t5, s3
	sub t5, t5, s3
	sltu s3, t5, a3
	sub t5, t5, a3
	or a3, s0, s3
	sub t4, t4, s4
	sub t4, t4, a3
	srli a3, t4, 63
	sub s1, s1, a3
	sub a3, a4, a3
	and s0, a0, a3
	and s3, s2, a3
	add t6, t6, s0
	sltu s0, t6, s0
	add t5, t5, s3
	sltu s3, t5, s3
	add t5, t5, s0
	sltu s0, t5, s0
	or s3, s3, s0
	add t4, t4, s3
	srli a3, t4, 63
	sub s1, s1, a3
	sltu s4, a4, s1
	sub s1, s1, s4
	addi t6, zero, 0
	addi t3, a2, 0
	addi t4, a7, 0
	addi t5, t0, 0
	addi s0, zero, 0
	addi s4, zero, 0
248:
	ld s2, 0(t4)
	mul s3, s2, s1
	mulhu s2, s2, s1
	add s3, s3, s0
	sltu s0, s3, s0
	add s0, s2, s0
	ld a0, 0(t3)
	sltu s2, a0, s3
	sub s3, a0, s3
	sltu a3, s3, s4
	sub s3, s3, s4
	or s4, s2, a3
	srli a0, t6, 1
	slli a3, s3, 63
	or a0, a0, a3
	sd a0, 0(t3)
	addi t6, s3, 0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 248b
	ld a0, 0(t3)
	sub s3, a0, s0
	sub s3, s3, s4
	srli a0, t6, 1
	slli a3, s3, 63
	or a0, a0, a3
	sd a0, 0(t3)
	addi a1, a1, -1
	bnez a1, 247b
	addi t3, a2, 0
	addi t4, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
	ld s2, 0(a2)
249:
	ld s3, 8(t3)
	srli s2, s2, 63
	slli a0, s3, 1
	or s2, s2, a0
	sd s2, 0(t3)
	ld a0, 0(t4)
	sltu s0, s2, a0
	sub s2, s2, a0
	sltu a3, s2, s4
	or s4, s0, a3
	addi s2, s3, 0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 249b
	srli s2, s2, 63
	sd s2, 0(t3)
	sltu s4, s2, s4
	xori s4, s4, 1
	sub s1, a4, s4
	addi t3, a2, 0
	addi t4, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
250:
	ld s2, 0(t3)
	ld s3, 0(t4)
	and s3, s3, s1
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu a3, s2, s4
	sub s2, s2, s4
	or s4, s0, a3
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 250b
	ld s2, 0(t3)
	sub s2, s2, s4
	sd s2, 0(t3)
	j 243f
242:
	addi t3, a2, 0
	addi t5, t0, 0
	addi s0, zero, 0
251:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 251b
	slli t3, t0, 3
	add t3, t3, a2
	addi t3, t3, -8
	addi s0, zero, 1
	sd s0, 0(t3)
	addi a1, t0, 64
252:
	addi t3, a5, 0
	addi t4, a2, 0
	addi t5, t0, 0
	addi s4, zero, 0
253:
	ld s2, 0(t4)
	slli s3, s2, 1
	add s3, s3, s4
	srli s4, s2, 63
	sd s3, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 253b
	sd s4, 0(t3)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
254:
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
	bnez t5, 254b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
255:
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
	bnez t5, 255b
	addi a1, a1, -1
	bnez a1, 252b
	addi s7, zero, 6
256:
	addi a3, a2, 0
	addi a4, a2, 0
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
	addi a0, a7, 0
257:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 257b
258:
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
	beqz t5, 259f
261:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 261b
	j 260f
259:
260:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 262f
264:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 16(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 24(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 24(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 8(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 24(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 32(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 32(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 16(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 32(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 40(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 40(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 264b
	j 263f
262:
263:
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
	bnez a1, 258b
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
265:
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
	bnez t5, 265b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
266:
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
	bnez t5, 266b
	addi s7, s7, -1
	bnez s7, 256b
243:
	j 241f
240:
	addi t3, a2, 0
	addi t5, t0, 0
	addi s0, zero, 0
267:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 267b
	addi s0, zero, 1
	sd s0, 0(a2)
	slli a1, t0, 7
268:
	addi t3, a5, 0
	addi t4, a2, 0
	addi t5, t0, 0
	addi s4, zero, 0
269:
	ld s2, 0(t4)
	slli s3, s2, 1
	add s3, s3, s4
	srli s4, s2, 63
	sd s3, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 269b
	sd s4, 0(t3)
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
	addi a1, a1, -1
	bnez a1, 268b
241:
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
272:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 272b
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
273:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 273b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
274:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 274b
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
275:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 275b
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
276:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 276b
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
277:
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
	bnez t5, 277b
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
278:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 278b
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
	addi a0, a1, 0
	andi a0, a0, 1
	xori a0, a0, 1
	beqz a0, 280f
	j 281f
280:
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
282:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 282b
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
283:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 283b
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
284:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 284b
	addi s0, zero, 0
	sltu s1, s0, t2
	addi a0, s1, -1
	andi a0, a0, 1
	xori a0, a0, 1
281:
	beqz a0, 285f
	addi a0, zero, 0
	j 286f
285:
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
287:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 287b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
288:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 288b
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
289:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 289b
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
290:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 290b
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
291:
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
	bnez t5, 291b
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
292:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 292b
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
293:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 293b
	addi s0, zero, 0
	sltu s1, s0, t2
	addi a2, s1, -1
	or a1, a1, a2
	xor a1, a1, a2
	addi a0, a1, 0
	andi a0, a0, 1
	xori a0, a0, 1
	beqz a0, 294f
	j 295f
294:
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
296:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 296b
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
297:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 297b
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
298:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 298b
	addi s0, zero, 0
	sltu s1, s0, t2
	addi a0, s1, -1
	andi a0, a0, 1
	xori a0, a0, 1
295:
	beqz a0, 299f
	addi a0, zero, 0
	j 2100f
299:
	addi a0, zero, 1
2100:
286:
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
	addiw a0, a0, 0
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
	slli t3, t0, 3
	add t3, t3, a7
	addi t3, t3, -8
	ld s0, 0(t3)
	beqz s0, 226f
	addi t3, zero, 4
	bltu t0, t3, 228f
	slli t3, t0, 3
	add t3, t3, a7
	addi t3, t3, -8
	ld s0, 0(t3)
	addi a1, zero, 0
	addi t5, zero, 63
230:
	srli s1, s0, 63
	xori s1, s1, 1
	sll s0, s0, s1
	add a1, a1, s1
	addi t5, t5, -1
	bnez t5, 230b
	addi s0, zero, 1
	sll s0, s0, a1
	slli t3, t0, 3
	add t3, t3, a7
	addi t3, t3, -24
	ld s2, 16(t3)
	ld s3, 8(t3)
	sll s2, s2, a1
	mulhu s4, s3, s0
	add s2, s2, s4
	mul s3, s3, s0
	ld s1, 0(t3)
	mulhu s1, s1, s0
	add s3, s3, s1
	sd s0, 0(a6)
	sd s2, 8(a6)
	sd s3, 24(a6)
	addi a4, zero, 0
	addi s3, zero, -1
	sub s3, s3, s2
	addi s4, zero, 0
	addi t5, zero, 64
231:
	srli s1, s3, 63
	slli s3, s3, 1
	ori s3, s3, 1
	sltu s0, s3, s2
	xori s0, s0, 1
	or s0, s0, s1
	sub s1, a4, s0
	and s1, s1, s2
	sub s3, s3, s1
	slli s4, s4, 1
	or s4, s4, s0
	addi t5, t5, -1
	bnez t5, 231b
	sd s4, 16(a6)
	addi t3, a2, 0
	addi t5, t0, 0
	addi s0, zero, 0
232:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 232b
	sd a4, 0(t3)
	addi s0, zero, 62
	sltu s0, s0, t0
	addi s1, zero, 125
	sltu s1, s1, t0
	add s0, s0, s1
	addi s0, s0, 1
	add a1, t0, s0
	addi a1, a1, 1
	slli s1, t0, 6
	add s1, s1, t0
	slli s2, s0, 6
	sub s2, s2, s0
	sub s1, s1, s2
	srli s2, s1, 6
	slli s2, s2, 3
	add s2, s2, a2
	andi s1, s1, 63
	addi s3, zero, 1
	sll s3, s3, s1
	sd s3, 0(s2)
233:
	slli t3, t0, 3
	add t3, t3, a2
	addi t3, t3, -16
	ld t4, 16(t3)
	ld t5, 8(t3)
	ld t6, 0(t3)
	ld s0, 0(a6)
	ld s2, 8(a6)
	ld s3, 16(a6)
	mul t4, t4, s0
	mulhu s1, t5, s0
	add t4, t4, s1
	mul t5, t5, s0
	mulhu s1, t6, s0
	add t5, t5, s1
	sub a3, s2, t4
	mul s0, s3, t4
	mulhu s1, s3, t4
	add s0, s0, t5
	sltu t6, s0, t5
	add s1, s1, t4
	add s1, s1, t6
	addi s1, s1, 1
	mul t6, s1, s2
	sub t6, t5, t6
	sltu s4, s0, t6
	sub s1, s1, s4
	sub s4, a4, s4
	and s4, s4, s2
	add t6, t6, s4
	sltu s4, t6, s2
	xori s4, s4, 1
	add s1, s1, s4
	sltu s4, a4, a3
	addi s4, s4, -1
	or s1, s1, s4
	ld s0, 0(a6)
	ld t6, 0(t3)
	addi a0, t3, -8
	ld a0, 0(a0)
	mul t6, t6, s0
	mulhu a0, a0, s0
	add t6, t6, a0
	ld a0, 24(a6)
	mul s0, s1, a0
	mulhu a3, s1, a0
	mul s3, s1, s2
	mulhu s4, s1, s2
	add s3, s3, a3
	sltu a3, s3, a3
	add s4, s4, a3
	sltu a3, t6, s0
	sub t6, t6, s0
	sltu s0, t5, s3
	sub t5, t5, s3
	sltu s3, t5, a3
	sub t5, t5, a3
	or a3, s0, s3
	sub t4, t4, s4
	sub t4, t4, a3
	srli a3, t4, 63
	sub s1, s1, a3
	sub a3, a4, a3
	and s0, a0, a3
	and s3, s2, a3
	add t6, t6, s0
	sltu s0, t6, s0
	add t5, t5, s3
	sltu s3, t5, s3
	add t5, t5, s0
	sltu s0, t5, s0
	or s3, s3, s0
	add t4, t4, s3
	srli a3, t4, 63
	sub s1, s1, a3
	sltu s4, a4, s1
	sub s1, s1, s4
	addi t6, zero, 0
	addi t3, a2, 0
	addi t4, a7, 0
	addi t5, t0, 0
	addi s0, zero, 0
	addi s4, zero, 0
234:
	ld s2, 0(t4)
	mul s3, s2, s1
	mulhu s2, s2, s1
	add s3, s3, s0
	sltu s0, s3, s0
	add s0, s2, s0
	ld a0, 0(t3)
	sltu s2, a0, s3
	sub s3, a0, s3
	sltu a3, s3, s4
	sub s3, s3, s4
	or s4, s2, a3
	srli a0, t6, 1
	slli a3, s3, 63
	or a0, a0, a3
	sd a0, 0(t3)
	addi t6, s3, 0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 234b
	ld a0, 0(t3)
	sub s3, a0, s0
	sub s3, s3, s4
	srli a0, t6, 1
	slli a3, s3, 63
	or a0, a0, a3
	sd a0, 0(t3)
	addi a1, a1, -1
	bnez a1, 233b
	addi t3, a2, 0
	addi t4, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
	ld s2, 0(a2)
235:
	ld s3, 8(t3)
	srli s2, s2, 63
	slli a0, s3, 1
	or s2, s2, a0
	sd s2, 0(t3)
	ld a0, 0(t4)
	sltu s0, s2, a0
	sub s2, s2, a0
	sltu a3, s2, s4
	or s4, s0, a3
	addi s2, s3, 0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 235b
	srli s2, s2, 63
	sd s2, 0(t3)
	sltu s4, s2, s4
	xori s4, s4, 1
	sub s1, a4, s4
	addi t3, a2, 0
	addi t4, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
236:
	ld s2, 0(t3)
	ld s3, 0(t4)
	and s3, s3, s1
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu a3, s2, s4
	sub s2, s2, s4
	or s4, s0, a3
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 236b
	ld s2, 0(t3)
	sub s2, s2, s4
	sd s2, 0(t3)
	j 229f
228:
	addi t3, a2, 0
	addi t5, t0, 0
	addi s0, zero, 0
237:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 237b
	slli t3, t0, 3
	add t3, t3, a2
	addi t3, t3, -8
	addi s0, zero, 1
	sd s0, 0(t3)
	addi a1, t0, 64
238:
	addi t3, a5, 0
	addi t4, a2, 0
	addi t5, t0, 0
	addi s4, zero, 0
239:
	ld s2, 0(t4)
	slli s3, s2, 1
	add s3, s3, s4
	srli s4, s2, 63
	sd s3, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 239b
	sd s4, 0(t3)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
240:
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
	bnez t5, 240b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
241:
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
	bnez t5, 241b
	addi a1, a1, -1
	bnez a1, 238b
	addi s7, zero, 6
242:
	addi a3, a2, 0
	addi a4, a2, 0
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
	addi a0, a7, 0
243:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 243b
244:
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
	beqz t5, 245f
247:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 247b
	j 246f
245:
246:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 248f
250:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 16(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 24(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 24(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 8(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 24(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 32(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 32(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 16(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 32(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 40(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 40(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 250b
	j 249f
248:
249:
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
	bnez a1, 244b
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
251:
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
	bnez t5, 251b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
252:
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
	bnez t5, 252b
	addi s7, s7, -1
	bnez s7, 242b
229:
	j 227f
226:
	addi t3, a2, 0
	addi t5, t0, 0
	addi s0, zero, 0
253:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 253b
	addi s0, zero, 1
	sd s0, 0(a2)
	slli a1, t0, 7
254:
	addi t3, a5, 0
	addi t4, a2, 0
	addi t5, t0, 0
	addi s4, zero, 0
255:
	ld s2, 0(t4)
	slli s3, s2, 1
	add s3, s3, s4
	srli s4, s2, 63
	sd s3, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 255b
	sd s4, 0(t3)
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
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
257:
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
	bnez t5, 257b
	addi a1, a1, -1
	bnez a1, 254b
227:
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
258:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 258b
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
261:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 261b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
262:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 262b
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
263:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 263b
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
266:
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
	bnez t5, 266b
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
267:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 267b
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
	slli t3, t0, 3
	add t3, t3, a7
	addi t3, t3, -8
	ld s0, 0(t3)
	beqz s0, 268f
	addi t3, zero, 4
	bltu t0, t3, 270f
	slli t3, t0, 3
	add t3, t3, a7
	addi t3, t3, -8
	ld s0, 0(t3)
	addi a1, zero, 0
	addi t5, zero, 63
272:
	srli s1, s0, 63
	xori s1, s1, 1
	sll s0, s0, s1
	add a1, a1, s1
	addi t5, t5, -1
	bnez t5, 272b
	addi s0, zero, 1
	sll s0, s0, a1
	slli t3, t0, 3
	add t3, t3, a7
	addi t3, t3, -24
	ld s2, 16(t3)
	ld s3, 8(t3)
	sll s2, s2, a1
	mulhu s4, s3, s0
	add s2, s2, s4
	mul s3, s3, s0
	ld s1, 0(t3)
	mulhu s1, s1, s0
	add s3, s3, s1
	sd s0, 0(a6)
	sd s2, 8(a6)
	sd s3, 24(a6)
	addi a4, zero, 0
	addi s3, zero, -1
	sub s3, s3, s2
	addi s4, zero, 0
	addi t5, zero, 64
273:
	srli s1, s3, 63
	slli s3, s3, 1
	ori s3, s3, 1
	sltu s0, s3, s2
	xori s0, s0, 1
	or s0, s0, s1
	sub s1, a4, s0
	and s1, s1, s2
	sub s3, s3, s1
	slli s4, s4, 1
	or s4, s4, s0
	addi t5, t5, -1
	bnez t5, 273b
	sd s4, 16(a6)
	addi t3, a2, 0
	addi t5, t0, 0
	addi s0, zero, 0
274:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 274b
	sd a4, 0(t3)
	addi s0, zero, 62
	sltu s0, s0, t0
	addi s1, zero, 125
	sltu s1, s1, t0
	add s0, s0, s1
	addi s0, s0, 1
	add a1, t0, s0
	addi a1, a1, 1
	slli s1, t0, 6
	add s1, s1, t0
	slli s2, s0, 6
	sub s2, s2, s0
	sub s1, s1, s2
	srli s2, s1, 6
	slli s2, s2, 3
	add s2, s2, a2
	andi s1, s1, 63
	addi s3, zero, 1
	sll s3, s3, s1
	sd s3, 0(s2)
275:
	slli t3, t0, 3
	add t3, t3, a2
	addi t3, t3, -16
	ld t4, 16(t3)
	ld t5, 8(t3)
	ld t6, 0(t3)
	ld s0, 0(a6)
	ld s2, 8(a6)
	ld s3, 16(a6)
	mul t4, t4, s0
	mulhu s1, t5, s0
	add t4, t4, s1
	mul t5, t5, s0
	mulhu s1, t6, s0
	add t5, t5, s1
	sub a3, s2, t4
	mul s0, s3, t4
	mulhu s1, s3, t4
	add s0, s0, t5
	sltu t6, s0, t5
	add s1, s1, t4
	add s1, s1, t6
	addi s1, s1, 1
	mul t6, s1, s2
	sub t6, t5, t6
	sltu s4, s0, t6
	sub s1, s1, s4
	sub s4, a4, s4
	and s4, s4, s2
	add t6, t6, s4
	sltu s4, t6, s2
	xori s4, s4, 1
	add s1, s1, s4
	sltu s4, a4, a3
	addi s4, s4, -1
	or s1, s1, s4
	ld s0, 0(a6)
	ld t6, 0(t3)
	addi a0, t3, -8
	ld a0, 0(a0)
	mul t6, t6, s0
	mulhu a0, a0, s0
	add t6, t6, a0
	ld a0, 24(a6)
	mul s0, s1, a0
	mulhu a3, s1, a0
	mul s3, s1, s2
	mulhu s4, s1, s2
	add s3, s3, a3
	sltu a3, s3, a3
	add s4, s4, a3
	sltu a3, t6, s0
	sub t6, t6, s0
	sltu s0, t5, s3
	sub t5, t5, s3
	sltu s3, t5, a3
	sub t5, t5, a3
	or a3, s0, s3
	sub t4, t4, s4
	sub t4, t4, a3
	srli a3, t4, 63
	sub s1, s1, a3
	sub a3, a4, a3
	and s0, a0, a3
	and s3, s2, a3
	add t6, t6, s0
	sltu s0, t6, s0
	add t5, t5, s3
	sltu s3, t5, s3
	add t5, t5, s0
	sltu s0, t5, s0
	or s3, s3, s0
	add t4, t4, s3
	srli a3, t4, 63
	sub s1, s1, a3
	sltu s4, a4, s1
	sub s1, s1, s4
	addi t6, zero, 0
	addi t3, a2, 0
	addi t4, a7, 0
	addi t5, t0, 0
	addi s0, zero, 0
	addi s4, zero, 0
276:
	ld s2, 0(t4)
	mul s3, s2, s1
	mulhu s2, s2, s1
	add s3, s3, s0
	sltu s0, s3, s0
	add s0, s2, s0
	ld a0, 0(t3)
	sltu s2, a0, s3
	sub s3, a0, s3
	sltu a3, s3, s4
	sub s3, s3, s4
	or s4, s2, a3
	srli a0, t6, 1
	slli a3, s3, 63
	or a0, a0, a3
	sd a0, 0(t3)
	addi t6, s3, 0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 276b
	ld a0, 0(t3)
	sub s3, a0, s0
	sub s3, s3, s4
	srli a0, t6, 1
	slli a3, s3, 63
	or a0, a0, a3
	sd a0, 0(t3)
	addi a1, a1, -1
	bnez a1, 275b
	addi t3, a2, 0
	addi t4, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
	ld s2, 0(a2)
277:
	ld s3, 8(t3)
	srli s2, s2, 63
	slli a0, s3, 1
	or s2, s2, a0
	sd s2, 0(t3)
	ld a0, 0(t4)
	sltu s0, s2, a0
	sub s2, s2, a0
	sltu a3, s2, s4
	or s4, s0, a3
	addi s2, s3, 0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 277b
	srli s2, s2, 63
	sd s2, 0(t3)
	sltu s4, s2, s4
	xori s4, s4, 1
	sub s1, a4, s4
	addi t3, a2, 0
	addi t4, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
278:
	ld s2, 0(t3)
	ld s3, 0(t4)
	and s3, s3, s1
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu a3, s2, s4
	sub s2, s2, s4
	or s4, s0, a3
	sd s2, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 278b
	ld s2, 0(t3)
	sub s2, s2, s4
	sd s2, 0(t3)
	j 271f
270:
	addi t3, a2, 0
	addi t5, t0, 0
	addi s0, zero, 0
279:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 279b
	slli t3, t0, 3
	add t3, t3, a2
	addi t3, t3, -8
	addi s0, zero, 1
	sd s0, 0(t3)
	addi a1, t0, 64
280:
	addi t3, a5, 0
	addi t4, a2, 0
	addi t5, t0, 0
	addi s4, zero, 0
281:
	ld s2, 0(t4)
	slli s3, s2, 1
	add s3, s3, s4
	srli s4, s2, 63
	sd s3, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 281b
	sd s4, 0(t3)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
282:
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
	bnez t5, 282b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
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
	addi a1, a1, -1
	bnez a1, 280b
	addi s7, zero, 6
284:
	addi a3, a2, 0
	addi a4, a2, 0
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
	addi a0, a7, 0
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
	beqz t5, 287f
289:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
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
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 16(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 24(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 24(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 8(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 24(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 32(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 32(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 16(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 32(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 40(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 40(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 24(t3)
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
	slli s2, t0, 3
	sub a0, a0, s2
	addi a0, a0, 8
	addi a1, a1, -1
	bnez a1, 286b
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
	addi s7, s7, -1
	bnez s7, 284b
271:
	j 269f
268:
	addi t3, a2, 0
	addi t5, t0, 0
	addi s0, zero, 0
295:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 295b
	addi s0, zero, 1
	sd s0, 0(a2)
	slli a1, t0, 7
296:
	addi t3, a5, 0
	addi t4, a2, 0
	addi t5, t0, 0
	addi s4, zero, 0
297:
	ld s2, 0(t4)
	slli s3, s2, 1
	add s3, s3, s4
	srli s4, s2, 63
	sd s3, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 297b
	sd s4, 0(t3)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
298:
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
	bnez t5, 298b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
299:
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
	bnez t5, 299b
	addi a1, a1, -1
	bnez a1, 296b
269:
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
2100:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2100b
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
2101:
	ld s2, 0(t3)
	sltu s0, s2, s4
	sub s2, s2, s4
	addi s4, s0, 0
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
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
2103:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2103b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
2104:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 2104b
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
2105:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2105b
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
	beqz a0, 2106f
	j 2107f
2106:
	addi s8, t3, 0
2107:
	ld s7, 8(s6)
	beqz s8, 2108f
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
2110:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2110b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
2111:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 2111b
	sub a7, a7, s5
	sub a7, a7, s5
	sub a7, a7, s5
	sub a7, a7, s5
	sub a7, a7, s5
	sub a7, a7, s5
	j 2109f
2108:
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t5, t0, 0
	addi s0, zero, 0
2112:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2112b
2109:
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
2113:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2113b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
2114:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 2114b
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
2115:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2115b
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
2116:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2116b
2117:
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
	beqz t5, 2118f
2120:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2120b
	j 2119f
2118:
2119:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2121f
2123:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 16(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 24(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 24(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 8(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 24(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 32(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 32(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 16(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 32(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 40(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 40(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2123b
	j 2122f
2121:
2122:
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
	bnez a1, 2117b
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
2124:
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
	bnez t5, 2124b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2125:
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
	bnez t5, 2125b
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
2126:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2126b
2127:
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
	beqz t5, 2128f
2130:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2130b
	j 2129f
2128:
2129:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2131f
2133:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 16(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 24(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 24(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 8(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 24(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 32(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 32(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 16(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 32(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 40(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 40(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2133b
	j 2132f
2131:
2132:
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
	bnez a1, 2127b
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
2134:
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
	bnez t5, 2134b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2135:
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
	bnez t5, 2135b
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
2136:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2136b
2137:
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
	beqz t5, 2138f
2140:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2140b
	j 2139f
2138:
2139:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2141f
2143:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 16(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 24(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 24(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 8(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 24(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 32(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 32(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 16(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 32(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 40(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 40(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2143b
	j 2142f
2141:
2142:
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
	bnez a1, 2137b
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
2144:
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
	bnez t5, 2144b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2145:
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
	bnez t5, 2145b
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
2146:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2146b
2147:
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
	beqz t5, 2148f
2150:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2150b
	j 2149f
2148:
2149:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2151f
2153:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 16(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 24(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 24(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 8(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 24(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 32(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 32(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 16(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 32(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 40(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 40(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2153b
	j 2152f
2151:
2152:
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
	bnez a1, 2147b
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
2154:
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
	bnez t5, 2154b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2155:
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
	bnez t5, 2155b
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
2156:
	lbu s0, 0(t3)
	sb s0, 0(t4)
	addi t4, t4, 1
	addi t3, t3, -1
	addi t5, t5, -1
	bnez t5, 2156b
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
2157:
	lbu s0, 0(t3)
	sb s0, 0(t4)
	addi t4, t4, 1
	addi t3, t3, -1
	addi t5, t5, -1
	bnez t5, 2157b
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
2158:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2158b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
2159:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 2159b
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
2160:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2160b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
2161:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 2161b
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
2162:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2162b
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
2163:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2163b
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
2164:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2164b
2165:
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
	beqz t5, 2166f
2168:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2168b
	j 2167f
2166:
2167:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2169f
2171:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 16(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 24(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 24(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 8(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 24(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 32(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 32(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 16(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 32(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 40(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 40(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2171b
	j 2170f
2169:
2170:
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
	bnez a1, 2165b
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
2172:
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
	bnez t5, 2172b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2173:
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
	bnez t5, 2173b
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
2174:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2174b
2175:
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
	beqz t5, 2176f
2178:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2178b
	j 2177f
2176:
2177:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2179f
2181:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 16(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 24(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 24(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 8(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 24(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 32(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 32(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 16(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 32(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 40(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 40(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2181b
	j 2180f
2179:
2180:
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
	bnez a1, 2175b
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
2182:
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
	bnez t5, 2182b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2183:
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
	bnez t5, 2183b
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
2184:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2184b
2185:
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
	beqz t5, 2186f
2188:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2188b
	j 2187f
2186:
2187:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2189f
2191:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 16(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 24(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 24(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 8(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 24(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 32(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 32(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 16(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 32(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 40(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 40(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2191b
	j 2190f
2189:
2190:
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
	bnez a1, 2185b
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
2192:
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
	bnez t5, 2192b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2193:
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
	bnez t5, 2193b
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
2194:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2194b
2195:
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
	beqz t5, 2196f
2198:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2198b
	j 2197f
2196:
2197:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2199f
2201:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 16(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 24(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 24(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 8(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 24(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 32(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 32(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 16(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 32(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 40(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 40(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2201b
	j 2200f
2199:
2200:
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
	bnez a1, 2195b
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
2202:
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
	bnez t5, 2202b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2203:
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
	bnez t5, 2203b
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
2204:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2204b
2205:
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
	beqz t5, 2206f
2208:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2208b
	j 2207f
2206:
2207:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2209f
2211:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 16(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 24(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 24(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 8(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 24(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 32(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 32(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 16(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 32(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 40(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 40(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2211b
	j 2210f
2209:
2210:
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
	bnez a1, 2205b
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
2212:
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
	bnez t5, 2212b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2213:
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
	bnez t5, 2213b
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
2214:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2214b
2215:
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
	beqz t5, 2216f
2218:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2218b
	j 2217f
2216:
2217:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2219f
2221:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 16(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 24(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 24(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 8(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 24(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 32(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 32(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 16(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 32(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 40(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 40(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2221b
	j 2220f
2219:
2220:
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
	bnez a1, 2215b
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
2222:
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
	bnez t5, 2222b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2223:
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
	bnez t5, 2223b
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
2224:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2224b
2225:
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
	beqz t5, 2226f
2228:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2228b
	j 2227f
2226:
2227:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2229f
2231:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 16(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 24(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 24(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 8(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 24(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 32(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 32(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 16(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 32(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 40(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 40(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2231b
	j 2230f
2229:
2230:
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
	bnez a1, 2225b
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
2232:
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
	bnez t5, 2232b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2233:
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
	bnez t5, 2233b
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
2234:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2234b
2235:
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
	beqz t5, 2236f
2238:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2238b
	j 2237f
2236:
2237:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2239f
2241:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 16(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 24(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 24(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 8(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 24(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 32(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 32(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 16(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 32(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 40(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 40(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2241b
	j 2240f
2239:
2240:
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
	bnez a1, 2235b
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
2242:
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
	bnez t5, 2242b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2243:
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
	bnez t5, 2243b
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
2244:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2244b
2245:
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
	beqz t5, 2246f
2248:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2248b
	j 2247f
2246:
2247:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2249f
2251:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 16(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 24(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 24(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 8(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 24(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 32(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 32(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 16(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 32(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 40(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 40(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2251b
	j 2250f
2249:
2250:
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
	bnez a1, 2245b
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
2252:
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
	bnez t5, 2252b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2253:
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
	bnez t5, 2253b
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
2254:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2254b
2255:
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
	beqz t5, 2256f
2258:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2258b
	j 2257f
2256:
2257:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2259f
2261:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 16(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 24(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 24(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 8(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 24(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 32(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 32(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 16(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 32(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 40(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 40(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2261b
	j 2260f
2259:
2260:
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
	bnez a1, 2255b
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
2262:
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
	bnez t5, 2262b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2263:
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
	bnez t5, 2263b
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
2264:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2264b
2265:
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
	beqz t5, 2266f
2268:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2268b
	j 2267f
2266:
2267:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2269f
2271:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 16(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 24(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 24(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 8(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 24(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 32(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 32(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 16(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 32(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 40(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 40(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2271b
	j 2270f
2269:
2270:
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
	bnez a1, 2265b
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
2272:
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
	bnez t5, 2272b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2273:
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
	bnez t5, 2273b
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
2274:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2274b
2275:
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
	beqz t5, 2276f
2278:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2278b
	j 2277f
2276:
2277:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2279f
2281:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 16(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 24(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 24(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 8(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 24(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 32(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 32(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 16(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 32(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 40(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 40(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2281b
	j 2280f
2279:
2280:
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
	bnez a1, 2275b
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
2282:
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
	bnez t5, 2282b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2283:
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
	bnez t5, 2283b
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
2284:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2284b
2285:
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
	beqz t5, 2286f
2288:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2288b
	j 2287f
2286:
2287:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2289f
2291:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 16(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 24(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 24(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 8(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 24(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 32(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 32(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 16(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 32(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 40(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 40(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2291b
	j 2290f
2289:
2290:
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
	bnez a1, 2285b
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
2292:
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
	bnez t5, 2292b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2293:
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
	bnez t5, 2293b
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
	beqz t5, 2296f
2298:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
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
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 16(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 24(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 24(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 8(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 24(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 32(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 32(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 16(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 32(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 40(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 40(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 24(t3)
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
	slli s2, t0, 3
	sub a0, a0, s2
	addi a0, a0, 8
	addi a1, a1, -1
	bnez a1, 2295b
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
	beqz t5, 2306f
2308:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
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
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 16(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 24(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 24(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 8(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 24(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 32(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 32(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 16(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 32(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 40(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 40(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 24(t3)
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
	slli s2, t0, 3
	sub a0, a0, s2
	addi a0, a0, 8
	addi a1, a1, -1
	bnez a1, 2305b
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
2314:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2314b
2315:
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
	beqz t5, 2316f
2318:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2318b
	j 2317f
2316:
2317:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2319f
2321:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 16(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 24(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 24(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 8(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 24(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 32(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 32(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 16(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 32(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 40(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 40(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2321b
	j 2320f
2319:
2320:
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
	bnez a1, 2315b
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
2322:
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
	bnez t5, 2322b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2323:
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
	bnez t5, 2323b
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
2324:
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
	bnez t5, 2324b
	ld s10, 16(s6)
	slli s10, s10, 32
	srli s10, s10, 48
2325:
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
2326:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2326b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2327:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2328f
2330:
	ld s2, 0(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 8(a0)
	sltu s1, a4, s1
	sd a4, 0(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 8(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 16(a0)
	add s3, a4, s3
	sd s4, 8(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 16(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 24(a0)
	sltu s1, a4, s1
	sd a4, 16(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 24(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 32(a0)
	add s3, a4, s3
	sd s4, 24(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 32(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 40(a0)
	sltu s1, a4, s1
	sd a4, 32(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 40(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 48(a0)
	add s3, a4, s3
	sd s4, 40(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 48(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 56(a0)
	sltu s1, a4, s1
	sd a4, 48(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 56(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 64(a0)
	add s3, a4, s3
	sd s4, 56(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	addi t4, t4, 64
	addi a0, a0, 64
	addi t5, t5, -1
	bnez t5, 2330b
	j 2329f
2328:
2329:
	beqz t6, 2331f
2333:
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
	bnez t6, 2333b
	j 2332f
2331:
2332:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2327b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2334:
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
	bnez t5, 2334b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2335:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2336f
2338:
	ld s2, 0(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 8(a0)
	sltu s1, a4, s1
	sd a4, 0(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 8(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 16(a0)
	add s3, a4, s3
	sd s4, 8(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 16(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 24(a0)
	sltu s1, a4, s1
	sd a4, 16(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 24(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 32(a0)
	add s3, a4, s3
	sd s4, 24(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 32(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 40(a0)
	sltu s1, a4, s1
	sd a4, 32(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 40(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 48(a0)
	add s3, a4, s3
	sd s4, 40(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 48(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 56(a0)
	sltu s1, a4, s1
	sd a4, 48(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 56(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 64(a0)
	add s3, a4, s3
	sd s4, 56(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	addi t4, t4, 64
	addi a0, a0, 64
	addi t5, t5, -1
	bnez t5, 2338b
	j 2337f
2336:
2337:
	beqz t6, 2339f
2341:
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
	bnez t6, 2341b
	j 2340f
2339:
2340:
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
	bnez t2, 2335b
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
2342:
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
	bnez t5, 2342b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2343:
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
	bnez t5, 2343b
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
2344:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2344b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2345:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2346f
2348:
	ld s2, 0(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 8(a0)
	sltu s1, a4, s1
	sd a4, 0(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 8(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 16(a0)
	add s3, a4, s3
	sd s4, 8(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 16(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 24(a0)
	sltu s1, a4, s1
	sd a4, 16(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 24(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 32(a0)
	add s3, a4, s3
	sd s4, 24(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 32(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 40(a0)
	sltu s1, a4, s1
	sd a4, 32(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 40(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 48(a0)
	add s3, a4, s3
	sd s4, 40(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 48(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 56(a0)
	sltu s1, a4, s1
	sd a4, 48(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 56(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 64(a0)
	add s3, a4, s3
	sd s4, 56(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	addi t4, t4, 64
	addi a0, a0, 64
	addi t5, t5, -1
	bnez t5, 2348b
	j 2347f
2346:
2347:
	beqz t6, 2349f
2351:
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
	bnez t6, 2351b
	j 2350f
2349:
2350:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2345b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2352:
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
	bnez t5, 2352b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2353:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2354f
2356:
	ld s2, 0(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 8(a0)
	sltu s1, a4, s1
	sd a4, 0(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 8(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 16(a0)
	add s3, a4, s3
	sd s4, 8(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 16(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 24(a0)
	sltu s1, a4, s1
	sd a4, 16(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 24(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 32(a0)
	add s3, a4, s3
	sd s4, 24(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 32(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 40(a0)
	sltu s1, a4, s1
	sd a4, 32(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 40(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 48(a0)
	add s3, a4, s3
	sd s4, 40(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 48(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 56(a0)
	sltu s1, a4, s1
	sd a4, 48(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 56(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 64(a0)
	add s3, a4, s3
	sd s4, 56(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	addi t4, t4, 64
	addi a0, a0, 64
	addi t5, t5, -1
	bnez t5, 2356b
	j 2355f
2354:
2355:
	beqz t6, 2357f
2359:
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
	bnez t6, 2359b
	j 2358f
2357:
2358:
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
	bnez t2, 2353b
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
2360:
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
	bnez t5, 2360b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2361:
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
	bnez t5, 2361b
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
2362:
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
	bnez t5, 2362b
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
2363:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2363b
2364:
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
	beqz t5, 2365f
2367:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2367b
	j 2366f
2365:
2366:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2368f
2370:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 16(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 24(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 24(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 8(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 24(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 32(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 32(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 16(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 32(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 40(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 40(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2370b
	j 2369f
2368:
2369:
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
	bnez a1, 2364b
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
2371:
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
	bnez t5, 2371b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2372:
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
	bnez t5, 2372b
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
2373:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2373b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2374:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2375f
2377:
	ld s2, 0(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 8(a0)
	sltu s1, a4, s1
	sd a4, 0(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 8(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 16(a0)
	add s3, a4, s3
	sd s4, 8(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 16(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 24(a0)
	sltu s1, a4, s1
	sd a4, 16(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 24(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 32(a0)
	add s3, a4, s3
	sd s4, 24(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 32(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 40(a0)
	sltu s1, a4, s1
	sd a4, 32(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 40(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 48(a0)
	add s3, a4, s3
	sd s4, 40(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 48(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 56(a0)
	sltu s1, a4, s1
	sd a4, 48(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 56(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 64(a0)
	add s3, a4, s3
	sd s4, 56(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	addi t4, t4, 64
	addi a0, a0, 64
	addi t5, t5, -1
	bnez t5, 2377b
	j 2376f
2375:
2376:
	beqz t6, 2378f
2380:
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
	bnez t6, 2380b
	j 2379f
2378:
2379:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2374b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2381:
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
	bnez t5, 2381b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2382:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2383f
2385:
	ld s2, 0(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 8(a0)
	sltu s1, a4, s1
	sd a4, 0(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 8(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 16(a0)
	add s3, a4, s3
	sd s4, 8(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 16(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 24(a0)
	sltu s1, a4, s1
	sd a4, 16(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 24(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 32(a0)
	add s3, a4, s3
	sd s4, 24(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 32(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 40(a0)
	sltu s1, a4, s1
	sd a4, 32(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 40(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 48(a0)
	add s3, a4, s3
	sd s4, 40(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 48(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 56(a0)
	sltu s1, a4, s1
	sd a4, 48(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 56(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 64(a0)
	add s3, a4, s3
	sd s4, 56(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	addi t4, t4, 64
	addi a0, a0, 64
	addi t5, t5, -1
	bnez t5, 2385b
	j 2384f
2383:
2384:
	beqz t6, 2386f
2388:
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
	bnez t6, 2388b
	j 2387f
2386:
2387:
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
	bnez t2, 2382b
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
2389:
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
	bnez t5, 2389b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2390:
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
	bnez t5, 2390b
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
2391:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2391b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2392:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2393f
2395:
	ld s2, 0(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 8(a0)
	sltu s1, a4, s1
	sd a4, 0(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 8(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 16(a0)
	add s3, a4, s3
	sd s4, 8(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 16(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 24(a0)
	sltu s1, a4, s1
	sd a4, 16(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 24(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 32(a0)
	add s3, a4, s3
	sd s4, 24(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 32(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 40(a0)
	sltu s1, a4, s1
	sd a4, 32(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 40(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 48(a0)
	add s3, a4, s3
	sd s4, 40(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 48(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 56(a0)
	sltu s1, a4, s1
	sd a4, 48(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 56(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 64(a0)
	add s3, a4, s3
	sd s4, 56(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	addi t4, t4, 64
	addi a0, a0, 64
	addi t5, t5, -1
	bnez t5, 2395b
	j 2394f
2393:
2394:
	beqz t6, 2396f
2398:
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
	bnez t6, 2398b
	j 2397f
2396:
2397:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2392b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2399:
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
	bnez t5, 2399b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2400:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2401f
2403:
	ld s2, 0(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 8(a0)
	sltu s1, a4, s1
	sd a4, 0(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 8(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 16(a0)
	add s3, a4, s3
	sd s4, 8(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 16(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 24(a0)
	sltu s1, a4, s1
	sd a4, 16(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 24(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 32(a0)
	add s3, a4, s3
	sd s4, 24(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 32(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 40(a0)
	sltu s1, a4, s1
	sd a4, 32(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 40(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 48(a0)
	add s3, a4, s3
	sd s4, 40(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 48(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 56(a0)
	sltu s1, a4, s1
	sd a4, 48(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 56(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 64(a0)
	add s3, a4, s3
	sd s4, 56(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	addi t4, t4, 64
	addi a0, a0, 64
	addi t5, t5, -1
	bnez t5, 2403b
	j 2402f
2401:
2402:
	beqz t6, 2404f
2406:
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
	bnez t6, 2406b
	j 2405f
2404:
2405:
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
	bnez t2, 2400b
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
2407:
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
	bnez t5, 2407b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2408:
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
	bnez t5, 2408b
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
2409:
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
	bnez t5, 2409b
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
2410:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2410b
2411:
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
	beqz t5, 2412f
2414:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2414b
	j 2413f
2412:
2413:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2415f
2417:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 16(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 24(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 24(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 8(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 24(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 32(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 32(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 16(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 32(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 40(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 40(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2417b
	j 2416f
2415:
2416:
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
	bnez a1, 2411b
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
2418:
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
	bnez t5, 2418b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2419:
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
	bnez t5, 2419b
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
2420:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2420b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2421:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2422f
2424:
	ld s2, 0(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 8(a0)
	sltu s1, a4, s1
	sd a4, 0(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 8(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 16(a0)
	add s3, a4, s3
	sd s4, 8(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 16(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 24(a0)
	sltu s1, a4, s1
	sd a4, 16(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 24(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 32(a0)
	add s3, a4, s3
	sd s4, 24(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 32(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 40(a0)
	sltu s1, a4, s1
	sd a4, 32(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 40(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 48(a0)
	add s3, a4, s3
	sd s4, 40(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 48(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 56(a0)
	sltu s1, a4, s1
	sd a4, 48(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 56(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 64(a0)
	add s3, a4, s3
	sd s4, 56(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	addi t4, t4, 64
	addi a0, a0, 64
	addi t5, t5, -1
	bnez t5, 2424b
	j 2423f
2422:
2423:
	beqz t6, 2425f
2427:
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
	bnez t6, 2427b
	j 2426f
2425:
2426:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2421b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2428:
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
	bnez t5, 2428b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2429:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2430f
2432:
	ld s2, 0(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 8(a0)
	sltu s1, a4, s1
	sd a4, 0(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 8(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 16(a0)
	add s3, a4, s3
	sd s4, 8(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 16(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 24(a0)
	sltu s1, a4, s1
	sd a4, 16(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 24(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 32(a0)
	add s3, a4, s3
	sd s4, 24(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 32(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 40(a0)
	sltu s1, a4, s1
	sd a4, 32(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 40(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 48(a0)
	add s3, a4, s3
	sd s4, 40(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 48(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 56(a0)
	sltu s1, a4, s1
	sd a4, 48(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 56(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 64(a0)
	add s3, a4, s3
	sd s4, 56(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	addi t4, t4, 64
	addi a0, a0, 64
	addi t5, t5, -1
	bnez t5, 2432b
	j 2431f
2430:
2431:
	beqz t6, 2433f
2435:
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
	bnez t6, 2435b
	j 2434f
2433:
2434:
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
	bnez t2, 2429b
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
2436:
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
	bnez t5, 2436b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2437:
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
	bnez t5, 2437b
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
2438:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2438b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2439:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2440f
2442:
	ld s2, 0(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 8(a0)
	sltu s1, a4, s1
	sd a4, 0(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 8(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 16(a0)
	add s3, a4, s3
	sd s4, 8(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 16(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 24(a0)
	sltu s1, a4, s1
	sd a4, 16(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 24(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 32(a0)
	add s3, a4, s3
	sd s4, 24(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 32(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 40(a0)
	sltu s1, a4, s1
	sd a4, 32(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 40(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 48(a0)
	add s3, a4, s3
	sd s4, 40(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 48(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 56(a0)
	sltu s1, a4, s1
	sd a4, 48(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 56(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 64(a0)
	add s3, a4, s3
	sd s4, 56(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	addi t4, t4, 64
	addi a0, a0, 64
	addi t5, t5, -1
	bnez t5, 2442b
	j 2441f
2440:
2441:
	beqz t6, 2443f
2445:
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
	bnez t6, 2445b
	j 2444f
2443:
2444:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2439b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2446:
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
	bnez t5, 2446b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2447:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2448f
2450:
	ld s2, 0(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 8(a0)
	sltu s1, a4, s1
	sd a4, 0(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 8(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 16(a0)
	add s3, a4, s3
	sd s4, 8(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 16(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 24(a0)
	sltu s1, a4, s1
	sd a4, 16(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 24(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 32(a0)
	add s3, a4, s3
	sd s4, 24(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 32(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 40(a0)
	sltu s1, a4, s1
	sd a4, 32(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 40(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 48(a0)
	add s3, a4, s3
	sd s4, 40(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 48(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 56(a0)
	sltu s1, a4, s1
	sd a4, 48(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 56(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 64(a0)
	add s3, a4, s3
	sd s4, 56(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	addi t4, t4, 64
	addi a0, a0, 64
	addi t5, t5, -1
	bnez t5, 2450b
	j 2449f
2448:
2449:
	beqz t6, 2451f
2453:
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
	bnez t6, 2453b
	j 2452f
2451:
2452:
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
	bnez t2, 2447b
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
2454:
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
	bnez t5, 2454b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2455:
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
	bnez t5, 2455b
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
2456:
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
	bnez t5, 2456b
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
2457:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2457b
2458:
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
	beqz t5, 2459f
2461:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2461b
	j 2460f
2459:
2460:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2462f
2464:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 16(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 24(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 24(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 8(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 24(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 32(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 32(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 16(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 32(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 40(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 40(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2464b
	j 2463f
2462:
2463:
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
	bnez a1, 2458b
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
2465:
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
	bnez t5, 2465b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2466:
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
	bnez t5, 2466b
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
2467:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2467b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2468:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2469f
2471:
	ld s2, 0(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 8(a0)
	sltu s1, a4, s1
	sd a4, 0(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 8(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 16(a0)
	add s3, a4, s3
	sd s4, 8(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 16(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 24(a0)
	sltu s1, a4, s1
	sd a4, 16(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 24(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 32(a0)
	add s3, a4, s3
	sd s4, 24(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 32(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 40(a0)
	sltu s1, a4, s1
	sd a4, 32(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 40(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 48(a0)
	add s3, a4, s3
	sd s4, 40(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 48(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 56(a0)
	sltu s1, a4, s1
	sd a4, 48(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 56(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 64(a0)
	add s3, a4, s3
	sd s4, 56(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	addi t4, t4, 64
	addi a0, a0, 64
	addi t5, t5, -1
	bnez t5, 2471b
	j 2470f
2469:
2470:
	beqz t6, 2472f
2474:
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
	bnez t6, 2474b
	j 2473f
2472:
2473:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2468b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2475:
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
	bnez t5, 2475b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2476:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2477f
2479:
	ld s2, 0(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 8(a0)
	sltu s1, a4, s1
	sd a4, 0(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 8(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 16(a0)
	add s3, a4, s3
	sd s4, 8(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 16(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 24(a0)
	sltu s1, a4, s1
	sd a4, 16(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 24(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 32(a0)
	add s3, a4, s3
	sd s4, 24(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 32(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 40(a0)
	sltu s1, a4, s1
	sd a4, 32(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 40(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 48(a0)
	add s3, a4, s3
	sd s4, 40(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 48(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 56(a0)
	sltu s1, a4, s1
	sd a4, 48(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 56(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 64(a0)
	add s3, a4, s3
	sd s4, 56(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	addi t4, t4, 64
	addi a0, a0, 64
	addi t5, t5, -1
	bnez t5, 2479b
	j 2478f
2477:
2478:
	beqz t6, 2480f
2482:
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
	bnez t6, 2482b
	j 2481f
2480:
2481:
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
	bnez t2, 2476b
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
2483:
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
	bnez t5, 2483b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2484:
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
	bnez t5, 2484b
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
2485:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2485b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2486:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2487f
2489:
	ld s2, 0(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 8(a0)
	sltu s1, a4, s1
	sd a4, 0(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 8(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 16(a0)
	add s3, a4, s3
	sd s4, 8(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 16(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 24(a0)
	sltu s1, a4, s1
	sd a4, 16(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 24(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 32(a0)
	add s3, a4, s3
	sd s4, 24(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 32(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 40(a0)
	sltu s1, a4, s1
	sd a4, 32(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 40(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 48(a0)
	add s3, a4, s3
	sd s4, 40(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 48(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 56(a0)
	sltu s1, a4, s1
	sd a4, 48(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 56(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 64(a0)
	add s3, a4, s3
	sd s4, 56(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	addi t4, t4, 64
	addi a0, a0, 64
	addi t5, t5, -1
	bnez t5, 2489b
	j 2488f
2487:
2488:
	beqz t6, 2490f
2492:
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
	bnez t6, 2492b
	j 2491f
2490:
2491:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2486b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2493:
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
	bnez t5, 2493b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2494:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2495f
2497:
	ld s2, 0(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 8(a0)
	sltu s1, a4, s1
	sd a4, 0(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 8(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 16(a0)
	add s3, a4, s3
	sd s4, 8(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 16(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 24(a0)
	sltu s1, a4, s1
	sd a4, 16(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 24(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 32(a0)
	add s3, a4, s3
	sd s4, 24(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 32(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 40(a0)
	sltu s1, a4, s1
	sd a4, 32(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 40(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 48(a0)
	add s3, a4, s3
	sd s4, 40(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 48(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 56(a0)
	sltu s1, a4, s1
	sd a4, 48(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 56(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 64(a0)
	add s3, a4, s3
	sd s4, 56(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	addi t4, t4, 64
	addi a0, a0, 64
	addi t5, t5, -1
	bnez t5, 2497b
	j 2496f
2495:
2496:
	beqz t6, 2498f
2500:
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
	bnez t6, 2500b
	j 2499f
2498:
2499:
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
	bnez t2, 2494b
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
2501:
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
	bnez t5, 2501b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2502:
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
	bnez t5, 2502b
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
2503:
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
	bnez t5, 2503b
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
2504:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2504b
2505:
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
	beqz t5, 2506f
2508:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2508b
	j 2507f
2506:
2507:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2509f
2511:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 16(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 24(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 24(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 8(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 24(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 32(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 32(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 16(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 32(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 40(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 40(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2511b
	j 2510f
2509:
2510:
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
	bnez a1, 2505b
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
2512:
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
	bnez t5, 2512b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2513:
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
	bnez t5, 2513b
	slli s7, s7, 2
	addi s10, s10, -1
	bnez s10, 2325b
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
2514:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2514b
2515:
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
	beqz t5, 2516f
2518:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2518b
	j 2517f
2516:
2517:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2519f
2521:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 16(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 24(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 24(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 8(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 24(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 32(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 32(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 16(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 32(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 40(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 40(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2521b
	j 2520f
2519:
2520:
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
	bnez a1, 2515b
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
2522:
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
	bnez t5, 2522b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2523:
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
	bnez t5, 2523b
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
2524:
	lbu s0, 0(t3)
	sb s0, 0(t4)
	addi t4, t4, 1
	addi t3, t3, -1
	addi t5, t5, -1
	bnez t5, 2524b
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
2525:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2525b
	addi a2, a7, 0
	add a2, a2, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
2526:
	lbu s7, 0(s9)
	slli s7, s7, 56
	addi s9, s9, 1
	addi s8, zero, 8
2527:
	srli s4, s7, 63
	slli s7, s7, 1
	addi t3, a5, 0
	addi t4, a2, 0
	addi t5, t0, 0
2528:
	ld s2, 0(t4)
	slli s3, s2, 1
	add s3, s3, s4
	srli s4, s2, 63
	sd s3, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2528b
	sd s4, 0(t3)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2529:
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
	bnez t5, 2529b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2530:
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
	bnez t5, 2530b
	addi s8, s8, -1
	bnez s8, 2527b
	addi s10, s10, -1
	bnez s10, 2526b
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
2531:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2531b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
2532:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 2532b
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
2533:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2533b
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
	addiw a0, a0, 0
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
	addiw a0, a0, 0
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
	addiw a0, a0, 0
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
