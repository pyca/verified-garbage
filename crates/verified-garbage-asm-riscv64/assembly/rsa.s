// The functions of `src/rsa.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_public_precompute:
	.option push
	.option arch, +m, +c
	sd s0, 128(a4)
	sd s1, 136(a4)
	sd s2, 144(a4)
	sd s3, 152(a4)
	sd s4, 160(a4)
	sd s5, 168(a4)
	sd s7, 176(a4)
	sd s8, 184(a4)
	sd s6, 192(a4)
	addi s6, a4, 0
	addi s5, a0, 0
	addi s7, a2, 0
	addi s8, a3, 0
	addi t0, a3, 7
	srli t0, t0, 3
	sd t0, 48(s6)
	slli a1, t0, 3
	addi a1, a1, 16
	addi a7, s6, 256
	add a2, a7, a1
	add a5, a2, a1
	add a6, a5, a1
	addi t3, a7, 0
	addi t5, t0, 0
	addi s0, zero, 0
20:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 20b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
21:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 21b
	add t4, s7, s8
	addi t4, t4, -1
	lbu s0, 0(t4)
	andi s0, s0, 1
	xori s0, s0, 1
	lbu t4, 0(s7)
	beqz t4, 22f
	j 23f
22:
	addi s0, zero, 1
23:
	addi t5, s8, -64
	beqz t5, 24f
	j 25f
24:
	srli t4, t4, 7
	xori t4, t4, 1
	or s0, s0, t4
25:
	beqz s0, 26f
	addi t3, s5, 0
	addi t5, t0, 0
	addi s0, zero, 0
28:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 28b
	addi t5, t0, 0
	addi s0, zero, 0
29:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 29b
	addi a0, zero, 0
	j 27f
26:
	addi t3, a2, 0
	addi t5, t0, 0
	addi s0, zero, 0
210:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 210b
	slli t3, t0, 3
	add t3, t3, a2
	addi t3, t3, -8
	addi s0, zero, 1
	sd s0, 0(t3)
	addi a1, t0, 64
211:
	addi t3, a5, 0
	addi t4, a2, 0
	addi t5, t0, 0
	addi s4, zero, 0
212:
	ld s2, 0(t4)
	slli s3, s2, 1
	add s3, s3, s4
	srli s4, s2, 63
	sd s3, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 212b
	sd s4, 0(t3)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
213:
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
	bnez t5, 213b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
214:
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
	bnez t5, 214b
	addi a1, a1, -1
	bnez a1, 211b
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
	addi a3, a2, 0
	addi a4, a2, 0
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
215:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 215b
216:
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
	beqz t5, 217f
219:
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
	bnez t5, 219b
	j 218f
217:
218:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 220f
222:
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
	bnez t5, 222b
	j 221f
220:
221:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	addi a1, a1, -1
	bnez a1, 216b
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
223:
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
	bnez t5, 223b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
224:
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
	bnez t5, 224b
	addi a3, a2, 0
	addi a4, a2, 0
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
225:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 225b
226:
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
	beqz t5, 227f
229:
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
	bnez t5, 229b
	j 228f
227:
228:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 230f
232:
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
	bnez t5, 232b
	j 231f
230:
231:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	addi a1, a1, -1
	bnez a1, 226b
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
233:
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
	bnez t5, 233b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
234:
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
	bnez t5, 234b
	addi a3, a2, 0
	addi a4, a2, 0
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
235:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 235b
236:
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
	beqz t5, 237f
239:
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
	bnez t5, 239b
	j 238f
237:
238:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 240f
242:
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
	bnez t5, 242b
	j 241f
240:
241:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	addi a1, a1, -1
	bnez a1, 236b
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
	addi a3, a2, 0
	addi a4, a2, 0
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
245:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 245b
246:
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
	beqz t5, 247f
249:
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
	bnez t5, 249b
	j 248f
247:
248:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 250f
252:
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
	bnez t5, 252b
	j 251f
250:
251:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	addi a1, a1, -1
	bnez a1, 246b
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
253:
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
	bnez t5, 253b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
254:
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
	bnez t5, 254b
	addi a3, a2, 0
	addi a4, a2, 0
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
255:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 255b
256:
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
	beqz t5, 257f
259:
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
	bnez t5, 259b
	j 258f
257:
258:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 260f
262:
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
	bnez t5, 262b
	j 261f
260:
261:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	addi a1, a1, -1
	bnez a1, 256b
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
263:
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
	bnez t5, 263b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
264:
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
	bnez t5, 264b
	addi a3, a2, 0
	addi a4, a2, 0
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
265:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 265b
266:
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
	beqz t5, 267f
269:
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
	bnez t5, 269b
	j 268f
267:
268:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 270f
272:
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
	bnez t5, 272b
	j 271f
270:
271:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	addi a1, a1, -1
	bnez a1, 266b
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
273:
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
	bnez t5, 273b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
274:
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
	bnez t5, 274b
	addi t3, s5, 0
	addi t4, a7, 0
	addi t5, t0, 0
275:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 275b
	addi t4, a2, 0
	addi t5, t0, 0
276:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 276b
	addi a0, zero, 1
27:
	ld s0, 128(s6)
	ld s1, 136(s6)
	ld s2, 144(s6)
	ld s3, 152(s6)
	ld s4, 160(s6)
	ld s5, 168(s6)
	ld s7, 176(s6)
	ld s8, 184(s6)
	ld s6, 192(s6)
	ret
	.option pop
