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

vg_rsa_public_precomputed_checked:
	.option push
	.option arch, +m, +c
	addi t0, sp, 0
	ld t0, 0(t0)
	sd s0, 128(t0)
	sd s1, 136(t0)
	sd s2, 144(t0)
	sd s3, 152(t0)
	sd s4, 160(t0)
	sd s5, 168(t0)
	sd s7, 176(t0)
	sd s8, 184(t0)
	sd s9, 192(t0)
	sd s10, 200(t0)
	sd s11, 208(t0)
	sd s6, 216(t0)
	addi s6, t0, 0
	addi s10, a0, 0
	addi s11, a1, 0
	addi t0, a1, 7
	srli t0, t0, 3
	slli s5, t0, 3
	addi s5, s5, 16
	addi a7, s6, 256
	addi s7, zero, 0
20:
	lbu t2, 0(a4)
	slli s7, s7, 8
	or s7, s7, t2
	srli t3, s7, 33
	addi t4, zero, 0
	sub t3, t4, t3
	srli t3, t3, 63
	sub t3, t4, t3
	addi t4, zero, 1
	slli t4, t4, 33
	xor t2, s7, t4
	and t2, t2, t3
	xor s7, s7, t2
	addi a4, a4, 1
	addi a5, a5, -1
	bnez a5, 20b
	addi t4, zero, 1
	and t2, s7, t4
	addi t3, s7, -3
	srli t3, t3, 63
	xor t3, t3, t4
	and t2, t2, t3
	slli t3, t4, 33
	sub t3, s7, t3
	srli t3, t3, 63
	and t2, t2, t3
	addi t3, zero, 0
	sub s9, t3, t2
	slli s7, s7, 31
	addi t3, a7, 0
	addi t4, a2, 0
	addi t5, t0, 0
21:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 21b
	add t3, a7, s5
	addi t5, t0, 0
22:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 22b
	addi a7, a7, 0
	add a7, a7, s5
	add a7, a7, s5
	add a7, a7, s5
	add a7, a7, s5
	addi a1, s7, 0
	addi s7, a6, 0
	addi s8, s11, 0
	addi t3, a7, 0
	addi t5, t0, 0
	addi s0, zero, 0
23:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 23b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
24:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 24b
	add t3, a7, s5
	addi t3, t3, -16
	addi s0, zero, 0
	sd s0, 0(t3)
	addi a7, s6, 256
	addi s7, a1, 0
	ld s0, 0(a7)
	ori s0, s0, 1
	sd s0, 0(a7)
	slli t3, t0, 3
	add t3, t3, a7
	addi t3, t3, -8
	ld s0, 0(t3)
	srli s1, s0, 1
	andi s2, s0, 1
	or s1, s1, s2
	addi s1, s1, -1
	srli s1, s1, 63
	or s0, s0, s1
	sd s0, 0(t3)
	add t3, a7, s5
	slli s1, t0, 3
	add s1, t3, s1
	addi s0, zero, 0
	sd s0, 0(s1)
	addi a5, a7, 0
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
25:
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
	bnez t5, 25b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a7, 0
	add t3, t3, s5
	addi t5, t0, 0
26:
	ld s0, 0(t3)
	and s0, s0, s4
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 26b
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
27:
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
	bnez t5, 27b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	and s9, s9, s4
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
28:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 28b
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
29:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 29b
210:
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
	beqz t5, 211f
213:
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
	bnez t5, 213b
	j 212f
211:
212:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 214f
216:
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
	bnez t5, 216b
	j 215f
214:
215:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	addi a1, a1, -1
	bnez a1, 210b
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
217:
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
	bnez t5, 217b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
218:
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
	bnez t5, 218b
	addi s8, zero, 33
219:
	srli t3, s7, 63
	slli s7, s7, 1
	addi s8, s8, -1
	addi t3, t3, -1
	and t3, t3, s8
	bnez t3, 219b
	addi s4, zero, -1
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
220:
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
	bnez t5, 220b
	bnez s8, 221f
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
223:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 223b
224:
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
	beqz t5, 225f
227:
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
	bnez t5, 227b
	j 226f
225:
226:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 228f
230:
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
	bnez t5, 230b
	j 229f
228:
229:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	addi a1, a1, -1
	bnez a1, 224b
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
231:
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
	bnez t5, 231b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
232:
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
	bnez t5, 232b
	j 222f
221:
	addi s8, s8, -1
	bnez s8, 233f
	j 234f
233:
235:
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
236:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 236b
237:
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
	beqz t5, 238f
240:
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
	bnez t5, 240b
	j 239f
238:
239:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 241f
243:
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
	bnez t5, 243b
	j 242f
241:
242:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	addi a1, a1, -1
	bnez a1, 237b
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
	srli t3, s7, 63
	slli s7, s7, 1
	bnez t3, 246f
	j 247f
246:
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
248:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 248b
249:
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
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 252b
	j 251f
250:
251:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 253f
255:
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
	bnez t5, 255b
	j 254f
253:
254:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	addi a1, a1, -1
	bnez a1, 249b
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
247:
	addi s8, s8, -1
	bnez s8, 235b
234:
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
258:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 258b
259:
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
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 262b
	j 261f
260:
261:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 263f
265:
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
	bnez t5, 265b
	j 264f
263:
264:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	addi a1, a1, -1
	bnez a1, 259b
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
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
267:
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
	bnez t5, 267b
	srli t3, s7, 63
	bnez t3, 268f
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
270:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 270b
271:
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
	beqz t5, 272f
274:
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
	bnez t5, 274b
	j 273f
272:
273:
	addi t5, t0, -1
	srli t5, t5, 2
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
	bnez t5, 277b
	j 276f
275:
276:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	addi a1, a1, -1
	bnez a1, 271b
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
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
279:
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
	bnez t5, 279b
	j 269f
268:
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
280:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 280b
281:
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
	beqz t5, 282f
284:
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
	bnez t5, 284b
	j 283f
282:
283:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 285f
287:
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
	bnez t5, 287b
	j 286f
285:
286:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	addi a1, a1, -1
	bnez a1, 281b
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
288:
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
	bnez t5, 288b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
289:
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
	bnez t5, 289b
269:
222:
	addi t4, a7, 0
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s11
	addi t4, t4, -1
	addi t3, s10, 0
	addi t5, s11, 0
290:
	lbu s0, 0(t4)
	and s0, s0, s9
	sb s0, 0(t3)
	addi t3, t3, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 290b
	addi a0, zero, 1
	and a0, a0, s9
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
	ld s6, 216(s6)
	ret
	.option pop

vg_rsa_private_checked:
	.option push
	.option arch, +m, +c
	addi sp, sp, -2032
	addi sp, sp, -1216
	addi t0, sp, 0
	sd s1, 96(t0)
	sd s2, 104(t0)
	sd s3, 112(t0)
	sd s4, 120(t0)
	sd s5, 128(t0)
	sd s6, 136(t0)
	sd ra, 144(t0)
	addi s1, a0, 0
	addi s2, a2, 0
	addi s3, a3, 0
	addi s4, a4, 0
	addi s5, a5, 0
	addi s6, a6, 0
	addi t6, sp, 2032
	addi t6, t6, 1216
	addi a0, t0, 176
	addi a1, s3, 0
	addi a4, s6, 0
	addi a5, s3, 0
	ld a6, 0(t6)
	ld a7, 8(t6)
	ld t1, 16(t6)
	sd t1, 0(t0)
	ld t1, 24(t6)
	sd t1, 8(t0)
	ld t1, 32(t6)
	sd t1, 16(t0)
	ld t1, 40(t6)
	sd t1, 24(t0)
	ld t1, 48(t6)
	sd t1, 32(t0)
	ld t1, 56(t6)
	sd t1, 40(t0)
	ld t1, 64(t6)
	sd t1, 48(t0)
	ld t1, 72(t6)
	sd t1, 56(t0)
	ld t1, 80(t6)
	sd t1, 64(t0)
	ld t1, 88(t6)
	sd t1, 72(t0)
	call {vg_rsa_private_crt}
	addi t0, sp, 0
	sd a0, 152(t0)
	addi a0, t0, 1200
	addi a1, s3, 7
	srli a1, a1, 3
	slli a1, a1, 1
	addi a2, s2, 0
	addi a3, s3, 0
	addi t6, sp, 2032
	addi t6, t6, 1216
	ld a4, 80(t6)
	ld a5, 88(t6)
	call {vg_rsa_public_precompute}
	addi t0, sp, 0
	addi a0, s1, 0
	addi a1, s3, 0
	addi a2, t0, 1200
	addi a3, s3, 7
	srli a3, a3, 3
	slli a3, a3, 1
	addi a4, s4, 0
	addi a5, s5, 0
	addi a6, t0, 176
	addi a7, s3, 0
	addi t6, sp, 2032
	addi t6, t6, 1216
	ld t1, 80(t6)
	sd t1, 0(t0)
	ld t1, 88(t6)
	sd t1, 8(t0)
	call {vg_rsa_public_precomputed_checked}
	addi t0, sp, 0
	sd a0, 160(t0)
	addi t2, s1, 0
	addi t3, s6, 0
	addi t4, zero, 0
	addi t5, s3, 0
20:
	lbu a1, 0(t2)
	lbu a2, 0(t3)
	xor a1, a1, a2
	or t4, t4, a1
	addi t2, t2, 1
	addi t3, t3, 1
	addi t5, t5, -1
	bnez t5, 20b
	addi t0, sp, 0
	ld a0, 152(t0)
	ld a1, 160(t0)
	and a0, a0, a1
	andi a0, a0, 1
	addi t4, t4, -1
	srli t4, t4, 63
	addi a1, zero, 2
	sub a1, a1, t4
	and t4, t4, a0
	addi a2, zero, 0
	sub a3, a2, t4
	sub a0, a2, a0
	and a0, a0, a1
	addi t5, s3, 0
	addi t2, s1, 0
	addi t3, t0, 176
21:
	lbu a1, 0(t3)
	and a1, a1, a3
	sb a1, 0(t2)
	addi a2, zero, 0
	sb a2, 0(t3)
	addi t2, t2, 1
	addi t3, t3, 1
	addi t5, t5, -1
	bnez t5, 21b
	addi t0, sp, 0
	ld ra, 144(t0)
	ld s1, 96(t0)
	ld s2, 104(t0)
	ld s3, 112(t0)
	ld s4, 120(t0)
	ld s5, 128(t0)
	ld s6, 136(t0)
	addi sp, sp, 1216
	addi sp, sp, 2032
	ret
	.option pop
