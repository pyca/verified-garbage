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
	slli t3, t0, 3
	add t3, t3, a7
	addi t3, t3, -8
	ld s0, 0(t3)
	addi a1, zero, 0
	addi t5, zero, 63
210:
	srli s1, s0, 63
	xori s1, s1, 1
	sll s0, s0, s1
	add a1, a1, s1
	addi t5, t5, -1
	bnez t5, 210b
	addi t3, a2, 0
	addi t5, t0, 0
	addi s0, zero, 0
211:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 211b
	slli t3, t0, 3
	add t3, t3, a2
	addi t3, t3, -8
	addi s1, zero, 63
	sub s1, s1, a1
	addi s0, zero, 1
	sll s0, s0, s1
	sd s0, 0(t3)
	add a1, a1, t0
	addi a1, a1, 1
212:
	addi t3, a5, 0
	addi t4, a2, 0
	addi t5, t0, 0
	addi s4, zero, 0
213:
	ld s2, 0(t4)
	slli s3, s2, 1
	add s3, s3, s4
	srli s4, s2, 63
	sd s3, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 213b
	sd s4, 0(t3)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
214:
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
	bnez t5, 214b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
215:
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
	bnez t5, 215b
	addi a1, a1, -1
	bnez a1, 212b
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
	slli s0, t0, 3
	addi s0, s0, 16
	add a6, a6, s0
	addi a3, a2, 0
	addi t3, a5, 0
	add t5, t0, t0
	addi t5, t5, 2
	addi s0, zero, 0
216:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 216b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
217:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 218f
220:
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
	ld s4, 8(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 16(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 24(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 32(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	ld s4, 32(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 40(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 32(t4)
	ld s4, 40(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 48(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 40(t4)
	ld s4, 48(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 56(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 48(t4)
	ld s4, 56(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 64(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 56(t4)
	addi t4, t4, 64
	addi a0, a0, 64
	addi t5, t5, -1
	bnez t5, 220b
	j 219f
218:
219:
	beqz t6, 221f
223:
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
	bnez t6, 223b
	j 222f
221:
222:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 217b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
224:
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
	bnez t5, 224b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
225:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 226f
228:
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
	ld s4, 8(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 16(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 24(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 32(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	ld s4, 32(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 40(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 32(t4)
	ld s4, 40(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 48(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 40(t4)
	ld s4, 48(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 56(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 48(t4)
	ld s4, 56(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 64(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 56(t4)
	addi t4, t4, 64
	addi a0, a0, 64
	addi t5, t5, -1
	bnez t5, 228b
	j 227f
226:
227:
	beqz t6, 229f
231:
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
	bnez t6, 231b
	j 230f
229:
230:
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
	bnez t2, 225b
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
	slli t3, t0, 3
	sub a5, a5, t3
	addi a3, a2, 0
	addi t3, a5, 0
	add t5, t0, t0
	addi t5, t5, 2
	addi s0, zero, 0
234:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 234b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
235:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 236f
238:
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
	ld s4, 8(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 16(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 24(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 32(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	ld s4, 32(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 40(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 32(t4)
	ld s4, 40(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 48(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 40(t4)
	ld s4, 48(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 56(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 48(t4)
	ld s4, 56(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 64(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 56(t4)
	addi t4, t4, 64
	addi a0, a0, 64
	addi t5, t5, -1
	bnez t5, 238b
	j 237f
236:
237:
	beqz t6, 239f
241:
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
	bnez t6, 241b
	j 240f
239:
240:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 235b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
242:
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
	bnez t5, 242b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
243:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 244f
246:
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
	ld s4, 8(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 16(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 24(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 32(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	ld s4, 32(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 40(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 32(t4)
	ld s4, 40(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 48(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 40(t4)
	ld s4, 48(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 56(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 48(t4)
	ld s4, 56(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 64(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 56(t4)
	addi t4, t4, 64
	addi a0, a0, 64
	addi t5, t5, -1
	bnez t5, 246b
	j 245f
244:
245:
	beqz t6, 247f
249:
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
	bnez t6, 249b
	j 248f
247:
248:
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
	bnez t2, 243b
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
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
251:
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
	bnez t5, 251b
	slli t3, t0, 3
	sub a5, a5, t3
	addi a3, a2, 0
	addi t3, a5, 0
	add t5, t0, t0
	addi t5, t5, 2
	addi s0, zero, 0
252:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 252b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
253:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 254f
256:
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
	ld s4, 8(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 16(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 24(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 32(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	ld s4, 32(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 40(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 32(t4)
	ld s4, 40(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 48(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 40(t4)
	ld s4, 48(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 56(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 48(t4)
	ld s4, 56(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 64(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 56(t4)
	addi t4, t4, 64
	addi a0, a0, 64
	addi t5, t5, -1
	bnez t5, 256b
	j 255f
254:
255:
	beqz t6, 257f
259:
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
	bnez t6, 259b
	j 258f
257:
258:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 253b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
260:
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
	bnez t5, 260b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
261:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 262f
264:
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
	ld s4, 8(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 16(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 24(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 32(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	ld s4, 32(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 40(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 32(t4)
	ld s4, 40(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 48(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 40(t4)
	ld s4, 48(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 56(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 48(t4)
	ld s4, 56(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 64(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 56(t4)
	addi t4, t4, 64
	addi a0, a0, 64
	addi t5, t5, -1
	bnez t5, 264b
	j 263f
262:
263:
	beqz t6, 265f
267:
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
	bnez t6, 267b
	j 266f
265:
266:
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
	bnez t2, 261b
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
268:
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
	bnez t5, 268b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
269:
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
	bnez t5, 269b
	slli t3, t0, 3
	sub a5, a5, t3
	addi a3, a2, 0
	addi t3, a5, 0
	add t5, t0, t0
	addi t5, t5, 2
	addi s0, zero, 0
270:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 270b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
271:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 272f
274:
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
	ld s4, 8(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 16(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 24(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 32(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	ld s4, 32(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 40(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 32(t4)
	ld s4, 40(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 48(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 40(t4)
	ld s4, 48(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 56(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 48(t4)
	ld s4, 56(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 64(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 56(t4)
	addi t4, t4, 64
	addi a0, a0, 64
	addi t5, t5, -1
	bnez t5, 274b
	j 273f
272:
273:
	beqz t6, 275f
277:
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
	bnez t6, 277b
	j 276f
275:
276:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 271b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
278:
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
	bnez t5, 278b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
279:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 280f
282:
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
	ld s4, 8(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 16(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 24(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 32(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	ld s4, 32(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 40(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 32(t4)
	ld s4, 40(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 48(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 40(t4)
	ld s4, 48(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 56(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 48(t4)
	ld s4, 56(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 64(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 56(t4)
	addi t4, t4, 64
	addi a0, a0, 64
	addi t5, t5, -1
	bnez t5, 282b
	j 281f
280:
281:
	beqz t6, 283f
285:
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
	bnez t6, 285b
	j 284f
283:
284:
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
	bnez t2, 279b
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
286:
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
	bnez t5, 286b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
287:
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
	bnez t5, 287b
	slli t3, t0, 3
	sub a5, a5, t3
	addi a3, a2, 0
	addi t3, a5, 0
	add t5, t0, t0
	addi t5, t5, 2
	addi s0, zero, 0
288:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 288b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
289:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 290f
292:
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
	ld s4, 8(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 16(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 24(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 32(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	ld s4, 32(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 40(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 32(t4)
	ld s4, 40(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 48(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 40(t4)
	ld s4, 48(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 56(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 48(t4)
	ld s4, 56(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 64(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 56(t4)
	addi t4, t4, 64
	addi a0, a0, 64
	addi t5, t5, -1
	bnez t5, 292b
	j 291f
290:
291:
	beqz t6, 293f
295:
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
	bnez t6, 295b
	j 294f
293:
294:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 289b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
296:
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
	bnez t5, 296b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
297:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 298f
2100:
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
	ld s4, 8(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 16(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 24(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 32(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	ld s4, 32(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 40(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 32(t4)
	ld s4, 40(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 48(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 40(t4)
	ld s4, 48(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 56(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 48(t4)
	ld s4, 56(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 64(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 56(t4)
	addi t4, t4, 64
	addi a0, a0, 64
	addi t5, t5, -1
	bnez t5, 2100b
	j 299f
298:
299:
	beqz t6, 2101f
2103:
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
	bnez t6, 2103b
	j 2102f
2101:
2102:
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
	bnez t2, 297b
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
2104:
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
	bnez t5, 2104b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2105:
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
	bnez t5, 2105b
	slli t3, t0, 3
	sub a5, a5, t3
	addi a3, a2, 0
	addi t3, a5, 0
	add t5, t0, t0
	addi t5, t5, 2
	addi s0, zero, 0
2106:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2106b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2107:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2108f
2110:
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
	ld s4, 8(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 16(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 24(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 32(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	ld s4, 32(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 40(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 32(t4)
	ld s4, 40(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 48(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 40(t4)
	ld s4, 48(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 56(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 48(t4)
	ld s4, 56(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 64(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 56(t4)
	addi t4, t4, 64
	addi a0, a0, 64
	addi t5, t5, -1
	bnez t5, 2110b
	j 2109f
2108:
2109:
	beqz t6, 2111f
2113:
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
	bnez t6, 2113b
	j 2112f
2111:
2112:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2107b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2114:
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
	bnez t5, 2114b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2115:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2116f
2118:
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
	ld s4, 8(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 16(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 8(t4)
	ld s4, 16(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 24(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 16(t4)
	ld s4, 24(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 32(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 24(t4)
	ld s4, 32(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 40(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 32(t4)
	ld s4, 40(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 48(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 40(t4)
	ld s4, 48(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 56(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 48(t4)
	ld s4, 56(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 64(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 56(t4)
	addi t4, t4, 64
	addi a0, a0, 64
	addi t5, t5, -1
	bnez t5, 2118b
	j 2117f
2116:
2117:
	beqz t6, 2119f
2121:
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
	bnez t6, 2121b
	j 2120f
2119:
2120:
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
	bnez t2, 2115b
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
2122:
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
	bnez t5, 2122b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2123:
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
	bnez t5, 2123b
	slli t3, t0, 3
	sub a5, a5, t3
	addi t3, s5, 0
	addi t4, a7, 0
	addi t5, t0, 0
2124:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2124b
	addi t4, a2, 0
	addi t5, t0, 0
2125:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2125b
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
	addi a0, a7, 0
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
	beqz t5, 211f
213:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
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
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 24(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
	ld a7, 24(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 32(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
	ld a7, 32(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 40(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
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
	slli s2, t0, 3
	sub a0, a0, s2
	addi a0, a0, 8
	addi a1, a1, -1
	bnez a1, 210b
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
	addi a0, a7, 0
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
	beqz t5, 225f
227:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
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
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 24(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
	ld a7, 24(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 32(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
	ld a7, 32(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 40(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
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
	slli s2, t0, 3
	sub a0, a0, s2
	addi a0, a0, 8
	addi a1, a1, -1
	bnez a1, 224b
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
	addi a0, a7, 0
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
	beqz t5, 238f
240:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
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
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 24(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
	ld a7, 24(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 32(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
	ld a7, 32(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 40(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
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
	slli s2, t0, 3
	sub a0, a0, s2
	addi a0, a0, 8
	addi a1, a1, -1
	bnez a1, 237b
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
	addi a0, a7, 0
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
	beqz t5, 250f
252:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
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
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 24(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
	ld a7, 24(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 32(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
	ld a7, 32(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 40(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
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
	slli s2, t0, 3
	sub a0, a0, s2
	addi a0, a0, 8
	addi a1, a1, -1
	bnez a1, 249b
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
	addi a0, a7, 0
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
	beqz t5, 260f
262:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
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
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 24(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
	ld a7, 24(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 32(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
	ld a7, 32(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 40(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
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
	slli s2, t0, 3
	sub a0, a0, s2
	addi a0, a0, 8
	addi a1, a1, -1
	bnez a1, 259b
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
	addi a0, a7, 0
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
	beqz t5, 272f
274:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
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
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 24(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
	ld a7, 24(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 32(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
	ld a7, 32(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 40(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
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
	slli s2, t0, 3
	sub a0, a0, s2
	addi a0, a0, 8
	addi a1, a1, -1
	bnez a1, 271b
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
	addi a0, a7, 0
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
	beqz t5, 282f
284:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
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
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 24(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
	ld a7, 24(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 32(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
	ld a7, 32(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 40(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
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
	slli s2, t0, 3
	sub a0, a0, s2
	addi a0, a0, 8
	addi a1, a1, -1
	bnez a1, 281b
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

vg_rsa_crt_values:
	.option push
	.option arch, +m, +c
	addi t0, sp, 0
	ld t0, 48(t0)
	sd s0, 0(t0)
	sd s1, 8(t0)
	sd s2, 16(t0)
	sd s3, 24(t0)
	sd s4, 32(t0)
	sd s5, 40(t0)
	sd s6, 48(t0)
	sd s7, 56(t0)
	sd s8, 64(t0)
	sd s9, 72(t0)
	sd s10, 80(t0)
	sd s11, 88(t0)
	addi s11, t0, 0
	addi s1, a6, 0
	addi s2, a7, 0
	addi a6, a4, 0
	addi a3, a2, 0
	addi a2, a0, 0
	addi t0, sp, 0
	ld s3, 0(t0)
	ld s4, 8(t0)
	ld s5, 16(t0)
	ld s6, 24(t0)
	ld a0, 32(t0)
	ld a1, 40(t0)
	addi s7, s1, 0
	addi s8, s2, 0
	add t4, s7, s8
	addi t4, t4, -1
	lbu s0, 0(t4)
	andi s0, s0, 1
	xori s0, s0, 1
	lbu t4, 0(s7)
	beqz t4, 20f
	j 21f
20:
	addi s0, zero, 1
21:
	addi t5, s8, -64
	beqz t5, 22f
	j 23f
22:
	srli t4, t4, 7
	xori t4, t4, 1
	or s0, s0, t4
23:
	beqz s0, 24f
	addi t0, a2, 0
	addi t3, s4, 0
	addi t5, zero, 0
26:
	sb t5, 0(t0)
	addi t0, t0, 1
	addi t3, t3, -1
	bnez t3, 26b
	addi t0, a3, 0
	addi t3, s6, 0
	addi t5, zero, 0
27:
	sb t5, 0(t0)
	addi t0, t0, 1
	addi t3, t3, -1
	bnez t3, 27b
	addi t0, a6, 0
	addi t3, s4, 0
	addi t5, zero, 0
28:
	sb t5, 0(t0)
	addi t0, t0, 1
	addi t3, t3, -1
	bnez t3, 28b
	addi a0, zero, 0
	j 25f
24:
	addi s9, s2, 7
	srli s9, s9, 3
	addi s10, s9, 2
	slli s10, s10, 3
	addi t3, zero, 25
	mul t3, t3, s10
	srli t3, t3, 3
	addi t0, s11, 256
	addi t5, zero, 0
29:
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t3, t3, -1
	bnez t3, 29b
	addi t1, s1, 0
	addi t3, s2, 0
	addi t0, zero, 18
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	add t0, t0, t3
	addi t0, t0, -1
210:
	lbu t5, 0(t1)
	sb t5, 0(t0)
	addi t1, t1, 1
	addi t0, t0, -1
	addi t3, t3, -1
	bnez t3, 210b
	addi t1, s3, 0
	addi t3, s4, 0
	addi t0, zero, 17
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	add t0, t0, t3
	addi t0, t0, -1
211:
	lbu t5, 0(t1)
	sb t5, 0(t0)
	addi t1, t1, 1
	addi t0, t0, -1
	addi t3, t3, -1
	bnez t3, 211b
	addi t1, s5, 0
	addi t3, s6, 0
	addi t0, zero, 16
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	add t0, t0, t3
	addi t0, t0, -1
212:
	lbu t5, 0(t1)
	sb t5, 0(t0)
	addi t1, t1, 1
	addi t0, t0, -1
	addi t3, t3, -1
	bnez t3, 212b
	addi t1, a0, 0
	addi t3, a1, 0
	addi t0, zero, 24
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	add t0, t0, t3
	addi t0, t0, -1
213:
	lbu t5, 0(t1)
	sb t5, 0(t0)
	addi t1, t1, 1
	addi t0, t0, -1
	addi t3, t3, -1
	bnez t3, 213b
	add t5, s4, s6
	slli t6, s9, 3
	sltu t5, t6, t5
	beqz t5, 214f
	addi t0, zero, 20
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 17
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
216:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 216b
	addi t0, zero, 17
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld t5, 0(t0)
	andi t5, t5, 1
	sd t5, 152(s11)
	addi s8, s4, 7
	srli s8, s8, 3
	addi t0, zero, 19
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t3, s9, 1
	addi t5, zero, 0
217:
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t3, t3, -1
	bnez t3, 217b
	slli s7, s9, 6
	addi a4, zero, -1
218:
	addi t2, zero, 18
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t5, s7, -1
	srli t5, t5, 6
	slli t5, t5, 3
	add t2, t2, t5
	ld t5, 0(t2)
	srli t3, t5, 63
	addi t0, zero, 19
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 20
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	andi t4, a4, 1
	addi t2, s8, 1
	andi t2, t2, 3
	beqz t2, 219f
221:
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
	bnez t2, 221b
	j 220f
219:
220:
	addi t2, s8, 1
	srli t2, t2, 2
	beqz t2, 222f
224:
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
	bnez t2, 224b
	j 223f
222:
223:
	srli t5, t6, 63
	addi a4, t5, -1
	andi a5, a4, 1
	addi t2, zero, 18
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
	bnez s7, 218b
	addi t0, zero, 19
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 20
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	xori a4, a4, -1
	addi t4, zero, 0
	addi t3, s8, 1
225:
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
	bnez t3, 225b
	addi t1, zero, 18
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 16
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t4, zero, 0
	addi t3, s9, 0
226:
	ld t5, 0(t1)
	ld t6, 0(t2)
	xor t5, t5, t6
	or t4, t4, t5
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 226b
	addi t5, zero, 0
	sltu t5, t5, t4
	xori t5, t5, 1
	sd t5, 160(s11)
	addi t1, zero, 19
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 10
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t4, zero, 0
	addi t3, s9, 0
227:
	ld t5, 0(t1)
	ld t6, 0(t2)
	xor t5, t5, t6
	or t4, t4, t5
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 227b
	addi t5, zero, 0
	sltu t5, t5, t4
	xori t5, t5, 1
	sd t5, 168(s11)
	j 215f
214:
	addi t0, zero, 17
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld t5, 0(t0)
	andi t5, t5, 1
	sd t5, 152(s11)
	addi s0, a2, 0
	addi s7, a3, 0
	addi a5, a6, 0
	addi a2, zero, 17
	mul a2, a2, s10
	add a2, a2, s11
	addi a2, a2, 256
	addi a3, zero, 19
	mul a3, a3, s10
	add a3, a3, s11
	addi a3, a3, 256
	addi s8, s9, 0
228:
	ld a6, 0(a2)
	addi t0, a3, 0
	addi t1, zero, 16
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s8, 0
	addi t4, zero, 0
229:
	ld t5, 0(t1)
	mul t6, a6, t5
	mulhu t5, a6, t5
	ld a4, 0(t0)
	add t6, t6, a4
	sltu a4, t6, a4
	add t5, t5, a4
	add t6, t6, t4
	sltu a4, t6, t4
	add t5, t5, a4
	sd t6, 0(t0)
	addi t4, t5, 0
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 229b
	addi a2, a2, 8
	addi a3, a3, 8
	addi s8, s8, -1
	bnez s8, 228b
	addi a2, s0, 0
	addi a3, s7, 0
	addi a6, a5, 0
	addi t1, zero, 19
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 18
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t4, zero, 0
	addi t3, s9, 0
230:
	ld t5, 0(t1)
	ld t6, 0(t2)
	xor t5, t5, t6
	or t4, t4, t5
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 230b
	addi t5, zero, 0
	sltu t5, t5, t4
	xori t5, t5, 1
	sd t5, 160(s11)
	addi t1, zero, 10
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 10
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t4, zero, 0
	addi t3, s9, 0
231:
	ld t5, 0(t1)
	ld t6, 0(t2)
	xor t5, t5, t6
	or t4, t4, t5
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 231b
	addi t5, zero, 0
	sltu t5, t5, t4
	xori t5, t5, 1
	sd t5, 168(s11)
215:
	addi t0, zero, 0
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 16
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
232:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 232b
	addi t0, zero, 8
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 17
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
233:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 233b
	addi t0, zero, 8
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld t5, 0(t0)
	ori t5, t5, 1
	sd t5, 0(t0)
	sltu t6, s4, s6
	addi t5, zero, 0
	sub t6, t5, t6
	sub t5, s4, s6
	and t5, t5, t6
	sub t5, s4, t5
	addi t5, t5, 3
	srli s8, t5, 2
	addi t0, zero, 15
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	add t3, s9, s9
	addi t3, t3, 2
	addi t5, zero, 0
234:
	sw t5, 0(t0)
	addi t0, t0, 4
	addi t3, t3, -1
	bnez t3, 234b
	addi t0, zero, 15
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t5, zero, 1
	sd t5, 0(t0)
	addi t0, zero, 2
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 8
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s8, 0
235:
	lwu t5, 0(t1)
	sw t5, 0(t0)
	addi t0, t0, 4
	addi t1, t1, 4
	addi t3, t3, -1
	bnez t3, 235b
	addi t1, zero, 2
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	slli t3, s8, 2
	add t1, t1, t3
	addi t5, zero, 0
	sw t5, 0(t1)
	addi t0, zero, 7
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t3, s8, 1
	addi t5, zero, 0
236:
	sw t5, 0(t0)
	addi t0, t0, 4
	addi t3, t3, -1
	bnez t3, 236b
	addi t0, zero, 7
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t5, zero, 1
	sw t5, 0(t0)
	addi t1, zero, 2
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 7
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s8, 1
	addi t4, zero, 0
237:
	lwu t5, 0(t1)
	lwu t6, 0(t2)
	xor t5, t5, t6
	or t4, t4, t5
	addi t1, t1, 4
	addi t2, t2, 4
	addi t3, t3, -1
	bnez t3, 237b
	addi t5, zero, 0
	sub t5, t5, t4
	srli t5, t5, 63
	xori t5, t5, 1
	slli t5, t5, 1
	addi t0, zero, 2
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	lwu t6, 0(t0)
	or t6, t6, t5
	sw t6, 0(t0)
	addi a4, zero, 2
	mul a4, a4, s10
	add a4, a4, s11
	addi a4, a4, 256
	lwu t5, 0(a4)
	addi t6, t5, 0
	mul a5, t5, t6
	addi t4, zero, 2
	sub a5, t4, a5
	mul t6, t6, a5
	mul a5, t5, t6
	addi t4, zero, 2
	sub a5, t4, a5
	mul t6, t6, a5
	mul a5, t5, t6
	addi t4, zero, 2
	sub a5, t4, a5
	mul t6, t6, a5
	mul a5, t5, t6
	addi t4, zero, 2
	sub a5, t4, a5
	mul t6, t6, a5
	addi a5, zero, 0
	sub t1, a5, t6
	addi a4, zero, 9
	mul a4, a4, s10
	add a4, a4, s11
	addi a4, a4, 256
	sd t1, 40(a4)
	addi t0, zero, 4
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 2
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s8, 1
238:
	lwu t5, 0(t1)
	sw t5, 0(t0)
	addi t0, t0, 4
	addi t1, t1, 4
	addi t3, t3, -1
	bnez t3, 238b
	addi t0, zero, 0
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	lwu a5, 0(t0)
	andi a5, a5, 1
	xori a5, a5, 1
	addi t0, zero, 5
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 0
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 2
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s8, 0
	addi t4, zero, 0
239:
	lwu t5, 0(t2)
	mul t5, a5, t5
	lwu t6, 0(t1)
	add t5, t5, t6
	add t5, t5, t4
	sw t5, 0(t0)
	srli t4, t5, 32
	addi t0, t0, 4
	addi t1, t1, 4
	addi t2, t2, 4
	addi t3, t3, -1
	bnez t3, 239b
	sw t4, 0(t0)
	addi t0, zero, 6
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t3, s8, 1
	addi t5, zero, 0
240:
	sw t5, 0(t0)
	addi t0, t0, 4
	addi t3, t3, -1
	bnez t3, 240b
	addi t0, zero, 9
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t5, zero, 1
	sd t5, 0(t0)
	addi s7, s8, 1
	add t5, s7, s7
	add s7, s7, t5
241:
	addi t0, zero, 4
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	lwu a4, 0(t0)
	addi t0, zero, 5
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	lwu t0, 0(t0)
	addi t6, zero, 9
	mul t6, t6, s10
	add t6, t6, s11
	addi t6, t6, 256
	ld t6, 0(t6)
	addi t1, zero, 1
	addi t2, zero, 0
	addi t3, zero, 0
	addi t4, zero, 1
	andi t5, t0, 1
	addi a5, zero, 0
	sub a5, a5, t5
	srli a7, t6, 63
	addi a7, a7, -1
	and a7, a7, a5
	xor t5, a4, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t0, t0, t5
	xor t5, t1, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t3, t3, t5
	xor t5, t2, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t4, t4, t5
	xor t6, t6, a7
	sub t6, t6, a7
	addi t6, t6, 2
	and t5, t0, a7
	add a4, a4, t5
	srli t0, t0, 1
	and t5, t3, a7
	add t1, t1, t5
	add t1, t1, t1
	and t5, t4, a7
	add t2, t2, t5
	add t2, t2, t2
	andi t5, t0, 1
	addi a5, zero, 0
	sub a5, a5, t5
	srli a7, t6, 63
	addi a7, a7, -1
	and a7, a7, a5
	xor t5, a4, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t0, t0, t5
	xor t5, t1, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t3, t3, t5
	xor t5, t2, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t4, t4, t5
	xor t6, t6, a7
	sub t6, t6, a7
	addi t6, t6, 2
	and t5, t0, a7
	add a4, a4, t5
	srli t0, t0, 1
	and t5, t3, a7
	add t1, t1, t5
	add t1, t1, t1
	and t5, t4, a7
	add t2, t2, t5
	add t2, t2, t2
	andi t5, t0, 1
	addi a5, zero, 0
	sub a5, a5, t5
	srli a7, t6, 63
	addi a7, a7, -1
	and a7, a7, a5
	xor t5, a4, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t0, t0, t5
	xor t5, t1, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t3, t3, t5
	xor t5, t2, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t4, t4, t5
	xor t6, t6, a7
	sub t6, t6, a7
	addi t6, t6, 2
	and t5, t0, a7
	add a4, a4, t5
	srli t0, t0, 1
	and t5, t3, a7
	add t1, t1, t5
	add t1, t1, t1
	and t5, t4, a7
	add t2, t2, t5
	add t2, t2, t2
	andi t5, t0, 1
	addi a5, zero, 0
	sub a5, a5, t5
	srli a7, t6, 63
	addi a7, a7, -1
	and a7, a7, a5
	xor t5, a4, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t0, t0, t5
	xor t5, t1, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t3, t3, t5
	xor t5, t2, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t4, t4, t5
	xor t6, t6, a7
	sub t6, t6, a7
	addi t6, t6, 2
	and t5, t0, a7
	add a4, a4, t5
	srli t0, t0, 1
	and t5, t3, a7
	add t1, t1, t5
	add t1, t1, t1
	and t5, t4, a7
	add t2, t2, t5
	add t2, t2, t2
	andi t5, t0, 1
	addi a5, zero, 0
	sub a5, a5, t5
	srli a7, t6, 63
	addi a7, a7, -1
	and a7, a7, a5
	xor t5, a4, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t0, t0, t5
	xor t5, t1, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t3, t3, t5
	xor t5, t2, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t4, t4, t5
	xor t6, t6, a7
	sub t6, t6, a7
	addi t6, t6, 2
	and t5, t0, a7
	add a4, a4, t5
	srli t0, t0, 1
	and t5, t3, a7
	add t1, t1, t5
	add t1, t1, t1
	and t5, t4, a7
	add t2, t2, t5
	add t2, t2, t2
	andi t5, t0, 1
	addi a5, zero, 0
	sub a5, a5, t5
	srli a7, t6, 63
	addi a7, a7, -1
	and a7, a7, a5
	xor t5, a4, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t0, t0, t5
	xor t5, t1, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t3, t3, t5
	xor t5, t2, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t4, t4, t5
	xor t6, t6, a7
	sub t6, t6, a7
	addi t6, t6, 2
	and t5, t0, a7
	add a4, a4, t5
	srli t0, t0, 1
	and t5, t3, a7
	add t1, t1, t5
	add t1, t1, t1
	and t5, t4, a7
	add t2, t2, t5
	add t2, t2, t2
	andi t5, t0, 1
	addi a5, zero, 0
	sub a5, a5, t5
	srli a7, t6, 63
	addi a7, a7, -1
	and a7, a7, a5
	xor t5, a4, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t0, t0, t5
	xor t5, t1, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t3, t3, t5
	xor t5, t2, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t4, t4, t5
	xor t6, t6, a7
	sub t6, t6, a7
	addi t6, t6, 2
	and t5, t0, a7
	add a4, a4, t5
	srli t0, t0, 1
	and t5, t3, a7
	add t1, t1, t5
	add t1, t1, t1
	and t5, t4, a7
	add t2, t2, t5
	add t2, t2, t2
	andi t5, t0, 1
	addi a5, zero, 0
	sub a5, a5, t5
	srli a7, t6, 63
	addi a7, a7, -1
	and a7, a7, a5
	xor t5, a4, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t0, t0, t5
	xor t5, t1, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t3, t3, t5
	xor t5, t2, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t4, t4, t5
	xor t6, t6, a7
	sub t6, t6, a7
	addi t6, t6, 2
	and t5, t0, a7
	add a4, a4, t5
	srli t0, t0, 1
	and t5, t3, a7
	add t1, t1, t5
	add t1, t1, t1
	and t5, t4, a7
	add t2, t2, t5
	add t2, t2, t2
	andi t5, t0, 1
	addi a5, zero, 0
	sub a5, a5, t5
	srli a7, t6, 63
	addi a7, a7, -1
	and a7, a7, a5
	xor t5, a4, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t0, t0, t5
	xor t5, t1, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t3, t3, t5
	xor t5, t2, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t4, t4, t5
	xor t6, t6, a7
	sub t6, t6, a7
	addi t6, t6, 2
	and t5, t0, a7
	add a4, a4, t5
	srli t0, t0, 1
	and t5, t3, a7
	add t1, t1, t5
	add t1, t1, t1
	and t5, t4, a7
	add t2, t2, t5
	add t2, t2, t2
	andi t5, t0, 1
	addi a5, zero, 0
	sub a5, a5, t5
	srli a7, t6, 63
	addi a7, a7, -1
	and a7, a7, a5
	xor t5, a4, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t0, t0, t5
	xor t5, t1, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t3, t3, t5
	xor t5, t2, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t4, t4, t5
	xor t6, t6, a7
	sub t6, t6, a7
	addi t6, t6, 2
	and t5, t0, a7
	add a4, a4, t5
	srli t0, t0, 1
	and t5, t3, a7
	add t1, t1, t5
	add t1, t1, t1
	and t5, t4, a7
	add t2, t2, t5
	add t2, t2, t2
	andi t5, t0, 1
	addi a5, zero, 0
	sub a5, a5, t5
	srli a7, t6, 63
	addi a7, a7, -1
	and a7, a7, a5
	xor t5, a4, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t0, t0, t5
	xor t5, t1, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t3, t3, t5
	xor t5, t2, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t4, t4, t5
	xor t6, t6, a7
	sub t6, t6, a7
	addi t6, t6, 2
	and t5, t0, a7
	add a4, a4, t5
	srli t0, t0, 1
	and t5, t3, a7
	add t1, t1, t5
	add t1, t1, t1
	and t5, t4, a7
	add t2, t2, t5
	add t2, t2, t2
	andi t5, t0, 1
	addi a5, zero, 0
	sub a5, a5, t5
	srli a7, t6, 63
	addi a7, a7, -1
	and a7, a7, a5
	xor t5, a4, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t0, t0, t5
	xor t5, t1, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t3, t3, t5
	xor t5, t2, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t4, t4, t5
	xor t6, t6, a7
	sub t6, t6, a7
	addi t6, t6, 2
	and t5, t0, a7
	add a4, a4, t5
	srli t0, t0, 1
	and t5, t3, a7
	add t1, t1, t5
	add t1, t1, t1
	and t5, t4, a7
	add t2, t2, t5
	add t2, t2, t2
	andi t5, t0, 1
	addi a5, zero, 0
	sub a5, a5, t5
	srli a7, t6, 63
	addi a7, a7, -1
	and a7, a7, a5
	xor t5, a4, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t0, t0, t5
	xor t5, t1, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t3, t3, t5
	xor t5, t2, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t4, t4, t5
	xor t6, t6, a7
	sub t6, t6, a7
	addi t6, t6, 2
	and t5, t0, a7
	add a4, a4, t5
	srli t0, t0, 1
	and t5, t3, a7
	add t1, t1, t5
	add t1, t1, t1
	and t5, t4, a7
	add t2, t2, t5
	add t2, t2, t2
	andi t5, t0, 1
	addi a5, zero, 0
	sub a5, a5, t5
	srli a7, t6, 63
	addi a7, a7, -1
	and a7, a7, a5
	xor t5, a4, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t0, t0, t5
	xor t5, t1, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t3, t3, t5
	xor t5, t2, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t4, t4, t5
	xor t6, t6, a7
	sub t6, t6, a7
	addi t6, t6, 2
	and t5, t0, a7
	add a4, a4, t5
	srli t0, t0, 1
	and t5, t3, a7
	add t1, t1, t5
	add t1, t1, t1
	and t5, t4, a7
	add t2, t2, t5
	add t2, t2, t2
	andi t5, t0, 1
	addi a5, zero, 0
	sub a5, a5, t5
	srli a7, t6, 63
	addi a7, a7, -1
	and a7, a7, a5
	xor t5, a4, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t0, t0, t5
	xor t5, t1, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t3, t3, t5
	xor t5, t2, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t4, t4, t5
	xor t6, t6, a7
	sub t6, t6, a7
	addi t6, t6, 2
	and t5, t0, a7
	add a4, a4, t5
	srli t0, t0, 1
	and t5, t3, a7
	add t1, t1, t5
	add t1, t1, t1
	and t5, t4, a7
	add t2, t2, t5
	add t2, t2, t2
	andi t5, t0, 1
	addi a5, zero, 0
	sub a5, a5, t5
	srli a7, t6, 63
	addi a7, a7, -1
	and a7, a7, a5
	xor t5, a4, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t0, t0, t5
	xor t5, t1, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t3, t3, t5
	xor t5, t2, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t4, t4, t5
	xor t6, t6, a7
	sub t6, t6, a7
	addi t6, t6, 2
	and t5, t0, a7
	add a4, a4, t5
	srli t0, t0, 1
	and t5, t3, a7
	add t1, t1, t5
	add t1, t1, t1
	and t5, t4, a7
	add t2, t2, t5
	add t2, t2, t2
	andi t5, t0, 1
	addi a5, zero, 0
	sub a5, a5, t5
	srli a7, t6, 63
	addi a7, a7, -1
	and a7, a7, a5
	xor t5, a4, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t0, t0, t5
	xor t5, t1, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t3, t3, t5
	xor t5, t2, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t4, t4, t5
	xor t6, t6, a7
	sub t6, t6, a7
	addi t6, t6, 2
	and t5, t0, a7
	add a4, a4, t5
	srli t0, t0, 1
	and t5, t3, a7
	add t1, t1, t5
	add t1, t1, t1
	and t5, t4, a7
	add t2, t2, t5
	add t2, t2, t2
	andi t5, t0, 1
	addi a5, zero, 0
	sub a5, a5, t5
	srli a7, t6, 63
	addi a7, a7, -1
	and a7, a7, a5
	xor t5, a4, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t0, t0, t5
	xor t5, t1, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t3, t3, t5
	xor t5, t2, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t4, t4, t5
	xor t6, t6, a7
	sub t6, t6, a7
	addi t6, t6, 2
	and t5, t0, a7
	add a4, a4, t5
	srli t0, t0, 1
	and t5, t3, a7
	add t1, t1, t5
	add t1, t1, t1
	and t5, t4, a7
	add t2, t2, t5
	add t2, t2, t2
	andi t5, t0, 1
	addi a5, zero, 0
	sub a5, a5, t5
	srli a7, t6, 63
	addi a7, a7, -1
	and a7, a7, a5
	xor t5, a4, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t0, t0, t5
	xor t5, t1, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t3, t3, t5
	xor t5, t2, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t4, t4, t5
	xor t6, t6, a7
	sub t6, t6, a7
	addi t6, t6, 2
	and t5, t0, a7
	add a4, a4, t5
	srli t0, t0, 1
	and t5, t3, a7
	add t1, t1, t5
	add t1, t1, t1
	and t5, t4, a7
	add t2, t2, t5
	add t2, t2, t2
	andi t5, t0, 1
	addi a5, zero, 0
	sub a5, a5, t5
	srli a7, t6, 63
	addi a7, a7, -1
	and a7, a7, a5
	xor t5, a4, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t0, t0, t5
	xor t5, t1, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t3, t3, t5
	xor t5, t2, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t4, t4, t5
	xor t6, t6, a7
	sub t6, t6, a7
	addi t6, t6, 2
	and t5, t0, a7
	add a4, a4, t5
	srli t0, t0, 1
	and t5, t3, a7
	add t1, t1, t5
	add t1, t1, t1
	and t5, t4, a7
	add t2, t2, t5
	add t2, t2, t2
	andi t5, t0, 1
	addi a5, zero, 0
	sub a5, a5, t5
	srli a7, t6, 63
	addi a7, a7, -1
	and a7, a7, a5
	xor t5, a4, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t0, t0, t5
	xor t5, t1, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t3, t3, t5
	xor t5, t2, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t4, t4, t5
	xor t6, t6, a7
	sub t6, t6, a7
	addi t6, t6, 2
	and t5, t0, a7
	add a4, a4, t5
	srli t0, t0, 1
	and t5, t3, a7
	add t1, t1, t5
	add t1, t1, t1
	and t5, t4, a7
	add t2, t2, t5
	add t2, t2, t2
	andi t5, t0, 1
	addi a5, zero, 0
	sub a5, a5, t5
	srli a7, t6, 63
	addi a7, a7, -1
	and a7, a7, a5
	xor t5, a4, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t0, t0, t5
	xor t5, t1, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t3, t3, t5
	xor t5, t2, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t4, t4, t5
	xor t6, t6, a7
	sub t6, t6, a7
	addi t6, t6, 2
	and t5, t0, a7
	add a4, a4, t5
	srli t0, t0, 1
	and t5, t3, a7
	add t1, t1, t5
	add t1, t1, t1
	and t5, t4, a7
	add t2, t2, t5
	add t2, t2, t2
	andi t5, t0, 1
	addi a5, zero, 0
	sub a5, a5, t5
	srli a7, t6, 63
	addi a7, a7, -1
	and a7, a7, a5
	xor t5, a4, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t0, t0, t5
	xor t5, t1, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t3, t3, t5
	xor t5, t2, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t4, t4, t5
	xor t6, t6, a7
	sub t6, t6, a7
	addi t6, t6, 2
	and t5, t0, a7
	add a4, a4, t5
	srli t0, t0, 1
	and t5, t3, a7
	add t1, t1, t5
	add t1, t1, t1
	and t5, t4, a7
	add t2, t2, t5
	add t2, t2, t2
	andi t5, t0, 1
	addi a5, zero, 0
	sub a5, a5, t5
	srli a7, t6, 63
	addi a7, a7, -1
	and a7, a7, a5
	xor t5, a4, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t0, t0, t5
	xor t5, t1, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t3, t3, t5
	xor t5, t2, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t4, t4, t5
	xor t6, t6, a7
	sub t6, t6, a7
	addi t6, t6, 2
	and t5, t0, a7
	add a4, a4, t5
	srli t0, t0, 1
	and t5, t3, a7
	add t1, t1, t5
	add t1, t1, t1
	and t5, t4, a7
	add t2, t2, t5
	add t2, t2, t2
	andi t5, t0, 1
	addi a5, zero, 0
	sub a5, a5, t5
	srli a7, t6, 63
	addi a7, a7, -1
	and a7, a7, a5
	xor t5, a4, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t0, t0, t5
	xor t5, t1, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t3, t3, t5
	xor t5, t2, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t4, t4, t5
	xor t6, t6, a7
	sub t6, t6, a7
	addi t6, t6, 2
	and t5, t0, a7
	add a4, a4, t5
	srli t0, t0, 1
	and t5, t3, a7
	add t1, t1, t5
	add t1, t1, t1
	and t5, t4, a7
	add t2, t2, t5
	add t2, t2, t2
	andi t5, t0, 1
	addi a5, zero, 0
	sub a5, a5, t5
	srli a7, t6, 63
	addi a7, a7, -1
	and a7, a7, a5
	xor t5, a4, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t0, t0, t5
	xor t5, t1, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t3, t3, t5
	xor t5, t2, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t4, t4, t5
	xor t6, t6, a7
	sub t6, t6, a7
	addi t6, t6, 2
	and t5, t0, a7
	add a4, a4, t5
	srli t0, t0, 1
	and t5, t3, a7
	add t1, t1, t5
	add t1, t1, t1
	and t5, t4, a7
	add t2, t2, t5
	add t2, t2, t2
	andi t5, t0, 1
	addi a5, zero, 0
	sub a5, a5, t5
	srli a7, t6, 63
	addi a7, a7, -1
	and a7, a7, a5
	xor t5, a4, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t0, t0, t5
	xor t5, t1, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t3, t3, t5
	xor t5, t2, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t4, t4, t5
	xor t6, t6, a7
	sub t6, t6, a7
	addi t6, t6, 2
	and t5, t0, a7
	add a4, a4, t5
	srli t0, t0, 1
	and t5, t3, a7
	add t1, t1, t5
	add t1, t1, t1
	and t5, t4, a7
	add t2, t2, t5
	add t2, t2, t2
	andi t5, t0, 1
	addi a5, zero, 0
	sub a5, a5, t5
	srli a7, t6, 63
	addi a7, a7, -1
	and a7, a7, a5
	xor t5, a4, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t0, t0, t5
	xor t5, t1, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t3, t3, t5
	xor t5, t2, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t4, t4, t5
	xor t6, t6, a7
	sub t6, t6, a7
	addi t6, t6, 2
	and t5, t0, a7
	add a4, a4, t5
	srli t0, t0, 1
	and t5, t3, a7
	add t1, t1, t5
	add t1, t1, t1
	and t5, t4, a7
	add t2, t2, t5
	add t2, t2, t2
	andi t5, t0, 1
	addi a5, zero, 0
	sub a5, a5, t5
	srli a7, t6, 63
	addi a7, a7, -1
	and a7, a7, a5
	xor t5, a4, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t0, t0, t5
	xor t5, t1, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t3, t3, t5
	xor t5, t2, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t4, t4, t5
	xor t6, t6, a7
	sub t6, t6, a7
	addi t6, t6, 2
	and t5, t0, a7
	add a4, a4, t5
	srli t0, t0, 1
	and t5, t3, a7
	add t1, t1, t5
	add t1, t1, t1
	and t5, t4, a7
	add t2, t2, t5
	add t2, t2, t2
	andi t5, t0, 1
	addi a5, zero, 0
	sub a5, a5, t5
	srli a7, t6, 63
	addi a7, a7, -1
	and a7, a7, a5
	xor t5, a4, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t0, t0, t5
	xor t5, t1, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t3, t3, t5
	xor t5, t2, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t4, t4, t5
	xor t6, t6, a7
	sub t6, t6, a7
	addi t6, t6, 2
	and t5, t0, a7
	add a4, a4, t5
	srli t0, t0, 1
	and t5, t3, a7
	add t1, t1, t5
	add t1, t1, t1
	and t5, t4, a7
	add t2, t2, t5
	add t2, t2, t2
	addi a4, zero, 9
	mul a4, a4, s10
	add a4, a4, s11
	addi a4, a4, 256
	sd t6, 0(a4)
	sd t1, 8(a4)
	sd t2, 16(a4)
	sd t3, 24(a4)
	sd t4, 32(a4)
	addi t0, zero, 11
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 4
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 5
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi a5, zero, 9
	mul a5, a5, s10
	add a5, a5, s11
	addi a5, a5, 256
	ld a5, 8(a5)
	addi a7, zero, 9
	mul a7, a7, s10
	add a7, a7, s11
	addi a7, a7, 256
	ld a7, 16(a7)
	addi t3, s8, 0
	addi t4, zero, 0
242:
	lwu t5, 0(t1)
	mul t5, a5, t5
	lwu t6, 0(t2)
	mul t6, a7, t6
	add t5, t5, t6
	add t5, t5, t4
	sw t5, 0(t0)
	srai t4, t5, 32
	addi t0, t0, 4
	addi t1, t1, 4
	addi t2, t2, 4
	addi t3, t3, -1
	bnez t3, 242b
	lwu t5, 0(t1)
	addiw t5, t5, 0
	mul t5, a5, t5
	lwu t6, 0(t2)
	addiw t6, t6, 0
	mul t6, a7, t6
	add t5, t5, t6
	add t5, t5, t4
	sw t5, 0(t0)
	srai t4, t5, 32
	sw t4, 4(t0)
	addi t0, zero, 12
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 4
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 5
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi a5, zero, 9
	mul a5, a5, s10
	add a5, a5, s11
	addi a5, a5, 256
	ld a5, 24(a5)
	addi a7, zero, 9
	mul a7, a7, s10
	add a7, a7, s11
	addi a7, a7, 256
	ld a7, 32(a7)
	addi t3, s8, 0
	addi t4, zero, 0
243:
	lwu t5, 0(t1)
	mul t5, a5, t5
	lwu t6, 0(t2)
	mul t6, a7, t6
	add t5, t5, t6
	add t5, t5, t4
	sw t5, 0(t0)
	srai t4, t5, 32
	addi t0, t0, 4
	addi t1, t1, 4
	addi t2, t2, 4
	addi t3, t3, -1
	bnez t3, 243b
	lwu t5, 0(t1)
	addiw t5, t5, 0
	mul t5, a5, t5
	lwu t6, 0(t2)
	addiw t6, t6, 0
	mul t6, a7, t6
	add t5, t5, t6
	add t5, t5, t4
	sw t5, 0(t0)
	srai t4, t5, 32
	sw t4, 4(t0)
	addi t0, zero, 4
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 11
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s8, 1
244:
	lwu t5, 0(t1)
	lwu t6, 4(t1)
	srli t5, t5, 30
	slli t6, t6, 2
	add t5, t5, t6
	sw t5, 0(t0)
	addi t0, t0, 4
	addi t1, t1, 4
	addi t3, t3, -1
	bnez t3, 244b
	addi t0, zero, 5
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 12
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s8, 1
245:
	lwu t5, 0(t1)
	lwu t6, 4(t1)
	srli t5, t5, 30
	slli t6, t6, 2
	add t5, t5, t6
	sw t5, 0(t0)
	addi t0, t0, 4
	addi t1, t1, 4
	addi t3, t3, -1
	bnez t3, 245b
	addi t0, zero, 11
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 6
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 7
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi a5, zero, 9
	mul a5, a5, s10
	add a5, a5, s11
	addi a5, a5, 256
	ld a5, 8(a5)
	addi a7, zero, 9
	mul a7, a7, s10
	add a7, a7, s11
	addi a7, a7, 256
	ld a7, 16(a7)
	addi t3, s8, 0
	addi t4, zero, 0
246:
	lwu t5, 0(t1)
	mul t5, a5, t5
	lwu t6, 0(t2)
	mul t6, a7, t6
	add t5, t5, t6
	add t5, t5, t4
	sw t5, 0(t0)
	srai t4, t5, 32
	addi t0, t0, 4
	addi t1, t1, 4
	addi t2, t2, 4
	addi t3, t3, -1
	bnez t3, 246b
	lwu t5, 0(t1)
	addiw t5, t5, 0
	mul t5, a5, t5
	lwu t6, 0(t2)
	addiw t6, t6, 0
	mul t6, a7, t6
	add t5, t5, t6
	add t5, t5, t4
	sw t5, 0(t0)
	srai t4, t5, 32
	sw t4, 4(t0)
	addi t0, zero, 12
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 6
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 7
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi a5, zero, 9
	mul a5, a5, s10
	add a5, a5, s11
	addi a5, a5, 256
	ld a5, 24(a5)
	addi a7, zero, 9
	mul a7, a7, s10
	add a7, a7, s11
	addi a7, a7, 256
	ld a7, 32(a7)
	addi t3, s8, 0
	addi t4, zero, 0
247:
	lwu t5, 0(t1)
	mul t5, a5, t5
	lwu t6, 0(t2)
	mul t6, a7, t6
	add t5, t5, t6
	add t5, t5, t4
	sw t5, 0(t0)
	srai t4, t5, 32
	addi t0, t0, 4
	addi t1, t1, 4
	addi t2, t2, 4
	addi t3, t3, -1
	bnez t3, 247b
	lwu t5, 0(t1)
	addiw t5, t5, 0
	mul t5, a5, t5
	lwu t6, 0(t2)
	addiw t6, t6, 0
	mul t6, a7, t6
	add t5, t5, t6
	add t5, t5, t4
	sw t5, 0(t0)
	srai t4, t5, 32
	sw t4, 4(t0)
	addi t0, zero, 11
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t6, zero, 9
	mul t6, t6, s10
	add t6, t6, s11
	addi t6, t6, 256
	ld t6, 40(t6)
	lwu t5, 0(t0)
	mul a5, t5, t6
	slli a5, a5, 32
	srli a5, a5, 32
	addi t0, zero, 11
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 11
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 2
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s8, 1
	addi t4, zero, 0
248:
	lwu t5, 0(t2)
	mul t5, a5, t5
	lwu t6, 0(t1)
	add t5, t5, t6
	add t5, t5, t4
	sw t5, 0(t0)
	srli t4, t5, 32
	addi t0, t0, 4
	addi t1, t1, 4
	addi t2, t2, 4
	addi t3, t3, -1
	bnez t3, 248b
	lwu t5, 0(t0)
	add t5, t5, t4
	sw t5, 0(t0)
	addi t0, zero, 13
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 11
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 2
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t1, t1, 4
	addi a5, zero, 1
	addi t3, s8, 1
	addi t4, zero, 0
249:
	lwu t5, 0(t2)
	mul t5, a5, t5
	lwu t6, 0(t1)
	add t5, t5, t6
	add t5, t5, t4
	sw t5, 0(t0)
	srli t4, t5, 32
	addi t0, t0, 4
	addi t1, t1, 4
	addi t2, t2, 4
	addi t3, t3, -1
	bnez t3, 249b
	addi t0, zero, 11
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
	addi t3, s8, 1
	addi t4, zero, 0
250:
	lwu t5, 0(t1)
	lwu t6, 0(t2)
	sub t5, t5, t6
	sub t5, t5, t4
	sw t5, 0(t0)
	srli t4, t5, 63
	addi t0, t0, 4
	addi t1, t1, 4
	addi t2, t2, 4
	addi t3, t3, -1
	bnez t3, 250b
	addi t0, zero, 13
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 11
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 13
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s8, 1
	addi t5, zero, 0
	sub t4, t5, t4
251:
	lwu t5, 0(t1)
	lwu t6, 0(t2)
	xor t6, t6, t5
	and t6, t6, t4
	xor t6, t6, t5
	sw t6, 0(t0)
	addi t0, t0, 4
	addi t1, t1, 4
	addi t2, t2, 4
	addi t3, t3, -1
	bnez t3, 251b
	addi t0, zero, 11
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
	addi t3, s8, 1
	addi t4, zero, 0
252:
	lwu t5, 0(t1)
	lwu t6, 0(t2)
	sub t5, t5, t6
	sub t5, t5, t4
	sw t5, 0(t0)
	srli t4, t5, 63
	addi t0, t0, 4
	addi t1, t1, 4
	addi t2, t2, 4
	addi t3, t3, -1
	bnez t3, 252b
	addi t0, zero, 6
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 11
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 13
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s8, 1
	addi t5, zero, 0
	sub t4, t5, t4
253:
	lwu t5, 0(t1)
	lwu t6, 0(t2)
	xor t6, t6, t5
	and t6, t6, t4
	xor t6, t6, t5
	sw t6, 0(t0)
	addi t0, t0, 4
	addi t1, t1, 4
	addi t2, t2, 4
	addi t3, t3, -1
	bnez t3, 253b
	addi t0, zero, 12
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t6, zero, 9
	mul t6, t6, s10
	add t6, t6, s11
	addi t6, t6, 256
	ld t6, 40(t6)
	lwu t5, 0(t0)
	mul a5, t5, t6
	slli a5, a5, 32
	srli a5, a5, 32
	addi t0, zero, 12
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 12
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 2
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s8, 1
	addi t4, zero, 0
254:
	lwu t5, 0(t2)
	mul t5, a5, t5
	lwu t6, 0(t1)
	add t5, t5, t6
	add t5, t5, t4
	sw t5, 0(t0)
	srli t4, t5, 32
	addi t0, t0, 4
	addi t1, t1, 4
	addi t2, t2, 4
	addi t3, t3, -1
	bnez t3, 254b
	lwu t5, 0(t0)
	add t5, t5, t4
	sw t5, 0(t0)
	addi t0, zero, 13
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 12
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 2
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t1, t1, 4
	addi a5, zero, 1
	addi t3, s8, 1
	addi t4, zero, 0
255:
	lwu t5, 0(t2)
	mul t5, a5, t5
	lwu t6, 0(t1)
	add t5, t5, t6
	add t5, t5, t4
	sw t5, 0(t0)
	srli t4, t5, 32
	addi t0, t0, 4
	addi t1, t1, 4
	addi t2, t2, 4
	addi t3, t3, -1
	bnez t3, 255b
	addi t0, zero, 12
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
	addi t3, s8, 1
	addi t4, zero, 0
256:
	lwu t5, 0(t1)
	lwu t6, 0(t2)
	sub t5, t5, t6
	sub t5, t5, t4
	sw t5, 0(t0)
	srli t4, t5, 63
	addi t0, t0, 4
	addi t1, t1, 4
	addi t2, t2, 4
	addi t3, t3, -1
	bnez t3, 256b
	addi t0, zero, 13
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 12
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 13
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s8, 1
	addi t5, zero, 0
	sub t4, t5, t4
257:
	lwu t5, 0(t1)
	lwu t6, 0(t2)
	xor t6, t6, t5
	and t6, t6, t4
	xor t6, t6, t5
	sw t6, 0(t0)
	addi t0, t0, 4
	addi t1, t1, 4
	addi t2, t2, 4
	addi t3, t3, -1
	bnez t3, 257b
	addi t0, zero, 12
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
	addi t3, s8, 1
	addi t4, zero, 0
258:
	lwu t5, 0(t1)
	lwu t6, 0(t2)
	sub t5, t5, t6
	sub t5, t5, t4
	sw t5, 0(t0)
	srli t4, t5, 63
	addi t0, t0, 4
	addi t1, t1, 4
	addi t2, t2, 4
	addi t3, t3, -1
	bnez t3, 258b
	addi t0, zero, 7
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 12
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 13
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s8, 1
	addi t5, zero, 0
	sub t4, t5, t4
259:
	lwu t5, 0(t1)
	lwu t6, 0(t2)
	xor t6, t6, t5
	and t6, t6, t4
	xor t6, t6, t5
	sw t6, 0(t0)
	addi t0, t0, 4
	addi t1, t1, 4
	addi t2, t2, 4
	addi t3, t3, -1
	bnez t3, 259b
	addi s7, s7, -1
	bnez s7, 241b
	addi t0, zero, 13
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 2
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 6
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s8, 1
	addi t4, zero, 0
260:
	lwu t5, 0(t1)
	lwu t6, 0(t2)
	sub t5, t5, t6
	sub t5, t5, t4
	sw t5, 0(t0)
	srli t4, t5, 63
	addi t0, t0, 4
	addi t1, t1, 4
	addi t2, t2, 4
	addi t3, t3, -1
	bnez t3, 260b
	addi t1, zero, 4
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	slli t3, s8, 2
	add t1, t1, t3
	lwu t4, 0(t1)
	srli t4, t4, 31
	addi t5, zero, 0
	sub t4, t5, t4
	addi t0, zero, 6
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 6
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 13
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s8, 1
261:
	lwu t5, 0(t1)
	lwu t6, 0(t2)
	xor t6, t6, t5
	and t6, t6, t4
	xor t6, t6, t5
	sw t6, 0(t0)
	addi t0, t0, 4
	addi t1, t1, 4
	addi t2, t2, 4
	addi t3, t3, -1
	bnez t3, 261b
	addi t0, zero, 11
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 6
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 2
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s8, 1
	addi t4, zero, 0
262:
	lwu t5, 0(t1)
	lwu t6, 0(t2)
	sub t5, t5, t6
	sub t5, t5, t4
	sw t5, 0(t0)
	srli t4, t5, 63
	addi t0, t0, 4
	addi t1, t1, 4
	addi t2, t2, 4
	addi t3, t3, -1
	bnez t3, 262b
	addi t0, zero, 6
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 11
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 6
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s8, 1
	addi t5, zero, 0
	sub t4, t5, t4
263:
	lwu t5, 0(t1)
	lwu t6, 0(t2)
	xor t6, t6, t5
	and t6, t6, t4
	xor t6, t6, t5
	sw t6, 0(t0)
	addi t0, t0, 4
	addi t1, t1, 4
	addi t2, t2, 4
	addi t3, t3, -1
	bnez t3, 263b
	addi s7, s8, 1
	add t5, s7, s7
	add s7, s7, t5
	add s7, s7, s7
264:
	addi a5, zero, 1
	addi t0, zero, 13
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 6
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 6
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s8, 1
	addi t4, zero, 0
265:
	lwu t5, 0(t2)
	mul t5, a5, t5
	lwu t6, 0(t1)
	add t5, t5, t6
	add t5, t5, t4
	sw t5, 0(t0)
	srli t4, t5, 32
	addi t0, t0, 4
	addi t1, t1, 4
	addi t2, t2, 4
	addi t3, t3, -1
	bnez t3, 265b
	addi t0, zero, 11
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
	addi t3, s8, 1
	addi t4, zero, 0
266:
	lwu t5, 0(t1)
	lwu t6, 0(t2)
	sub t5, t5, t6
	sub t5, t5, t4
	sw t5, 0(t0)
	srli t4, t5, 63
	addi t0, t0, 4
	addi t1, t1, 4
	addi t2, t2, 4
	addi t3, t3, -1
	bnez t3, 266b
	addi t0, zero, 6
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 11
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 13
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s8, 1
	addi t5, zero, 0
	sub t4, t5, t4
267:
	lwu t5, 0(t1)
	lwu t6, 0(t2)
	xor t6, t6, t5
	and t6, t6, t4
	xor t6, t6, t5
	sw t6, 0(t0)
	addi t0, t0, 4
	addi t1, t1, 4
	addi t2, t2, 4
	addi t3, t3, -1
	bnez t3, 267b
	addi s7, s7, -1
	bnez s7, 264b
	addi t0, zero, 1
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	add t3, s9, s9
	addi t3, t3, 2
	addi t5, zero, 0
268:
	sw t5, 0(t0)
	addi t0, t0, 4
	addi t3, t3, -1
	bnez t3, 268b
	addi t0, zero, 11
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 1
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 4
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s8, 1
	addi t4, zero, 0
269:
	lwu t5, 0(t1)
	lwu t6, 0(t2)
	sub t5, t5, t6
	sub t5, t5, t4
	sw t5, 0(t0)
	srli t4, t5, 63
	addi t0, t0, 4
	addi t1, t1, 4
	addi t2, t2, 4
	addi t3, t3, -1
	bnez t3, 269b
	addi t1, zero, 4
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	slli t3, s8, 2
	add t1, t1, t3
	lwu t4, 0(t1)
	srli t4, t4, 31
	addi t5, zero, 0
	sub t4, t5, t4
	addi t0, zero, 1
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 4
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 11
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s8, 1
270:
	lwu t5, 0(t1)
	lwu t6, 0(t2)
	xor t6, t6, t5
	and t6, t6, t4
	xor t6, t6, t5
	sw t6, 0(t0)
	addi t0, t0, 4
	addi t1, t1, 4
	addi t2, t2, 4
	addi t3, t3, -1
	bnez t3, 270b
	addi t0, zero, 3
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	add t3, s9, s9
	addi t3, t3, 2
	addi t5, zero, 0
271:
	sw t5, 0(t0)
	addi t0, t0, 4
	addi t3, t3, -1
	bnez t3, 271b
	addi t0, zero, 3
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 6
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s8, 1
272:
	lwu t5, 0(t1)
	sw t5, 0(t0)
	addi t0, t0, 4
	addi t1, t1, 4
	addi t3, t3, -1
	bnez t3, 272b
	addi t1, zero, 1
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 15
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t4, zero, 0
	addi t3, s9, 0
273:
	ld t5, 0(t1)
	ld t6, 0(t2)
	xor t5, t5, t6
	or t4, t4, t5
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 273b
	addi t5, zero, 0
	sltu t5, t5, t4
	xori t5, t5, 1
	sd t5, 176(s11)
	ld t5, 152(s11)
	ld t6, 160(s11)
	and t5, t5, t6
	sd t5, 184(s11)
	ld t5, 184(s11)
	ld t6, 168(s11)
	and t5, t5, t6
	sd t5, 184(s11)
	ld t5, 184(s11)
	ld t6, 176(s11)
	and t5, t5, t6
	sd t5, 184(s11)
	ld t4, 184(s11)
	addi t5, zero, 0
	sub t4, t5, t4
	addi t1, zero, 3
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	add t1, t1, s4
	addi t1, t1, -1
	addi t0, a6, 0
	addi t3, s4, 0
274:
	lbu t5, 0(t1)
	and t5, t5, t4
	sb t5, 0(t0)
	addi t0, t0, 1
	addi t1, t1, -1
	addi t3, t3, -1
	bnez t3, 274b
	addi t0, zero, 18
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 24
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
275:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 275b
	addi t0, zero, 20
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 17
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
276:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 276b
	addi t0, zero, 20
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld t5, 0(t0)
	andi t5, t5, -2
	sd t5, 0(t0)
	addi s8, s4, 7
	srli s8, s8, 3
	addi t0, zero, 22
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t3, s9, 1
	addi t5, zero, 0
277:
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t3, t3, -1
	bnez t3, 277b
	slli s7, s9, 6
	addi a4, zero, -1
278:
	addi t2, zero, 18
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t5, s7, -1
	srli t5, t5, 6
	slli t5, t5, 3
	add t2, t2, t5
	ld t5, 0(t2)
	srli t3, t5, 63
	addi t0, zero, 22
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 20
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	andi t4, a4, 1
	addi t2, s8, 1
	andi t2, t2, 3
	beqz t2, 279f
281:
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
	bnez t2, 281b
	j 280f
279:
280:
	addi t2, s8, 1
	srli t2, t2, 2
	beqz t2, 282f
284:
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
	bnez t2, 284b
	j 283f
282:
283:
	srli t5, t6, 63
	addi a4, t5, -1
	andi a5, a4, 1
	addi t2, zero, 18
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
	bnez s7, 278b
	addi t0, zero, 22
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 20
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	xori a4, a4, -1
	addi t4, zero, 0
	addi t3, s8, 1
285:
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
	bnez t3, 285b
	addi t0, zero, 18
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 24
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
286:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 286b
	addi t0, zero, 20
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 16
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
287:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 287b
	addi t0, zero, 20
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld t5, 0(t0)
	andi t5, t5, -2
	sd t5, 0(t0)
	addi s8, s6, 7
	srli s8, s8, 3
	addi t0, zero, 23
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t3, s9, 1
	addi t5, zero, 0
288:
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t3, t3, -1
	bnez t3, 288b
	slli s7, s9, 6
	addi a4, zero, -1
289:
	addi t2, zero, 18
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t5, s7, -1
	srli t5, t5, 6
	slli t5, t5, 3
	add t2, t2, t5
	ld t5, 0(t2)
	srli t3, t5, 63
	addi t0, zero, 23
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 20
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	andi t4, a4, 1
	addi t2, s8, 1
	andi t2, t2, 3
	beqz t2, 290f
292:
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
	bnez t2, 292b
	j 291f
290:
291:
	addi t2, s8, 1
	srli t2, t2, 2
	beqz t2, 293f
295:
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
	bnez t2, 295b
	j 294f
293:
294:
	srli t5, t6, 63
	addi a4, t5, -1
	andi a5, a4, 1
	addi t2, zero, 18
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
	bnez s7, 289b
	addi t0, zero, 23
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 20
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	xori a4, a4, -1
	addi t4, zero, 0
	addi t3, s8, 1
296:
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
	bnez t3, 296b
	ld t4, 184(s11)
	addi t5, zero, 0
	sub t4, t5, t4
	addi t1, zero, 22
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	add t1, t1, s4
	addi t1, t1, -1
	addi t0, a2, 0
	addi t3, s4, 0
297:
	lbu t5, 0(t1)
	and t5, t5, t4
	sb t5, 0(t0)
	addi t0, t0, 1
	addi t1, t1, -1
	addi t3, t3, -1
	bnez t3, 297b
	addi t1, zero, 23
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	add t1, t1, s6
	addi t1, t1, -1
	addi t0, a3, 0
	addi t3, s6, 0
298:
	lbu t5, 0(t1)
	and t5, t5, t4
	sb t5, 0(t0)
	addi t0, t0, 1
	addi t1, t1, -1
	addi t3, t3, -1
	bnez t3, 298b
	ld a0, 184(s11)
25:
	ld s0, 0(s11)
	ld s1, 8(s11)
	ld s2, 16(s11)
	ld s3, 24(s11)
	ld s4, 32(s11)
	ld s5, 40(s11)
	ld s6, 48(s11)
	ld s7, 56(s11)
	ld s8, 64(s11)
	ld s9, 72(s11)
	ld s10, 80(s11)
	ld s11, 88(s11)
	ret
	.option pop

vg_rsa_check_key:
	.option push
	.option arch, +m, +c
	addi t0, sp, 0
	ld t0, 64(t0)
	sd s0, 0(t0)
	sd s1, 8(t0)
	sd s2, 16(t0)
	sd s3, 24(t0)
	sd s4, 32(t0)
	sd s5, 40(t0)
	sd s6, 48(t0)
	sd s7, 56(t0)
	sd s8, 64(t0)
	sd s9, 72(t0)
	sd s10, 80(t0)
	sd s11, 88(t0)
	addi s11, t0, 0
	addi s1, a0, 0
	addi s2, a1, 0
	addi s3, a6, 0
	addi s4, a7, 0
	addi a0, a4, 0
	addi a1, a5, 0
	addi a4, a2, 0
	addi a5, a3, 0
	addi t0, sp, 0
	ld s5, 0(t0)
	ld s6, 8(t0)
	ld a2, 16(t0)
	ld a3, 32(t0)
	ld a6, 48(t0)
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
	addi a5, s9, 0
	addi a4, s7, 0
	addi s7, s1, 0
	addi s8, s2, 0
	add t4, s7, s8
	addi t4, t4, -1
	lbu s0, 0(t4)
	andi s0, s0, 1
	xori s0, s0, 1
	lbu t4, 0(s7)
	beqz t4, 21f
	j 22f
21:
	addi s0, zero, 1
22:
	addi t5, s8, -64
	beqz t5, 23f
	j 24f
23:
	srli t4, t4, 7
	xori t4, t4, 1
	or s0, s0, t4
24:
	addi t0, a5, 1
	or t0, t0, s0
	beqz t0, 25f
	addi a0, zero, 0
	j 26f
25:
	addi s9, s2, 7
	srli s9, s9, 3
	addi s10, s9, 2
	slli s10, s10, 3
	addi t3, zero, 24
	mul t3, t3, s10
	srli t3, t3, 3
	addi t0, s11, 256
	addi t5, zero, 0
27:
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t3, t3, -1
	bnez t3, 27b
	addi t0, zero, 3
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	srli t5, a4, 31
	sd t5, 0(t0)
	addi t1, s1, 0
	addi t3, s2, 0
	addi t0, zero, 2
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	add t0, t0, t3
	addi t0, t0, -1
28:
	lbu t5, 0(t1)
	sb t5, 0(t0)
	addi t1, t1, 1
	addi t0, t0, -1
	addi t3, t3, -1
	bnez t3, 28b
	addi t1, a0, 0
	addi t3, a1, 0
	addi t0, zero, 9
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	add t0, t0, t3
	addi t0, t0, -1
29:
	lbu t5, 0(t1)
	sb t5, 0(t0)
	addi t1, t1, 1
	addi t0, t0, -1
	addi t3, t3, -1
	bnez t3, 29b
	addi t1, s3, 0
	addi t3, s4, 0
	addi t0, zero, 4
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	add t0, t0, t3
	addi t0, t0, -1
210:
	lbu t5, 0(t1)
	sb t5, 0(t0)
	addi t1, t1, 1
	addi t0, t0, -1
	addi t3, t3, -1
	bnez t3, 210b
	addi t1, s5, 0
	addi t3, s6, 0
	addi t0, zero, 5
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	add t0, t0, t3
	addi t0, t0, -1
211:
	lbu t5, 0(t1)
	sb t5, 0(t0)
	addi t1, t1, 1
	addi t0, t0, -1
	addi t3, t3, -1
	bnez t3, 211b
	addi t1, a2, 0
	addi t3, s4, 0
	addi t0, zero, 6
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	add t0, t0, t3
	addi t0, t0, -1
212:
	lbu t5, 0(t1)
	sb t5, 0(t0)
	addi t1, t1, 1
	addi t0, t0, -1
	addi t3, t3, -1
	bnez t3, 212b
	addi t1, a3, 0
	addi t3, s6, 0
	addi t0, zero, 7
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	add t0, t0, t3
	addi t0, t0, -1
213:
	lbu t5, 0(t1)
	sb t5, 0(t0)
	addi t1, t1, 1
	addi t0, t0, -1
	addi t3, t3, -1
	bnez t3, 213b
	addi t1, a6, 0
	addi t3, s4, 0
	addi t0, zero, 8
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	add t0, t0, t3
	addi t0, t0, -1
214:
	lbu t5, 0(t1)
	sb t5, 0(t0)
	addi t1, t1, 1
	addi t0, t0, -1
	addi t3, t3, -1
	bnez t3, 214b
	addi s5, s4, 0
	addi t0, zero, 1
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t5, zero, 1
	sd t5, 0(t0)
	addi t0, zero, 4
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld t5, 0(t0)
	andi t5, t5, 1
	sd t5, 160(s11)
	addi t0, zero, 16
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 4
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
215:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 215b
	addi t0, zero, 16
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld t5, 0(t0)
	ori t5, t5, 1
	sd t5, 0(t0)
	addi t1, zero, 16
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 1
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t4, zero, 0
	addi t3, s9, 0
216:
	ld t5, 0(t1)
	ld t6, 0(t2)
	xor t5, t5, t6
	or t4, t4, t5
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 216b
	addi t5, zero, 0
	sltu t5, t5, t4
	xori t5, t5, 1
	sd t5, 152(s11)
	addi t0, zero, 16
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld t5, 0(t0)
	ld t6, 152(s11)
	slli t6, t6, 1
	or t5, t5, t6
	sd t5, 0(t0)
	addi t0, zero, 17
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 2
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
217:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 217b
	addi t0, zero, 20
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 1
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
218:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 218b
	addi a7, zero, 16
	mul a7, a7, s10
	add a7, a7, s11
	addi a7, a7, 256
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
	addi t0, s9, 0
	addi a5, zero, 18
	mul a5, a5, s10
	add a5, a5, s11
	addi a5, a5, 256
	addi a6, zero, 19
	mul a6, a6, s10
	add a6, a6, s11
	addi a6, a6, 256
	addi a2, zero, 21
	mul a2, a2, s10
	add a2, a2, s11
	addi a2, a2, 256
	addi a3, zero, 17
	mul a3, a3, s10
	add a3, a3, s11
	addi a3, a3, 256
	addi a4, zero, 20
	mul a4, a4, s10
	add a4, a4, s11
	addi a4, a4, 256
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
	addi a0, a7, 0
219:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 219b
220:
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
	beqz t5, 221f
223:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
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
	bnez t5, 223b
	j 222f
221:
222:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 224f
226:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 24(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
	ld a7, 24(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 32(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
	ld a7, 32(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 40(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
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
	bnez t5, 226b
	j 225f
224:
225:
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
	bnez a1, 220b
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
227:
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
	bnez t5, 227b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
228:
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
	bnez t5, 228b
	addi t1, zero, 21
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 0
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t4, zero, 0
	addi t3, s9, 0
229:
	ld t5, 0(t1)
	ld t6, 0(t2)
	xor t5, t5, t6
	or t4, t4, t5
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 229b
	addi t5, zero, 0
	sltu t5, t5, t4
	xori t5, t5, 1
	sd t5, 152(s11)
	ld t5, 160(s11)
	ld t6, 152(s11)
	and t5, t5, t6
	sd t5, 160(s11)
	addi t0, zero, 22
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 0
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
230:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 230b
	addi a2, zero, 4
	mul a2, a2, s10
	add a2, a2, s11
	addi a2, a2, 256
	addi a3, zero, 22
	mul a3, a3, s10
	add a3, a3, s11
	addi a3, a3, 256
	addi s8, s9, 0
231:
	ld a6, 0(a2)
	addi t0, a3, 0
	addi t1, zero, 5
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s8, 0
	addi t4, zero, 0
232:
	ld t5, 0(t1)
	mul t6, a6, t5
	mulhu t5, a6, t5
	ld a4, 0(t0)
	add t6, t6, a4
	sltu a4, t6, a4
	add t5, t5, a4
	add t6, t6, t4
	sltu a4, t6, t4
	add t5, t5, a4
	sd t6, 0(t0)
	addi t4, t5, 0
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 232b
	addi a2, a2, 8
	addi a3, a3, 8
	addi s8, s8, -1
	bnez s8, 231b
	addi t1, zero, 22
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 2
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t4, zero, 0
	addi t3, s9, 0
233:
	ld t5, 0(t1)
	ld t6, 0(t2)
	xor t5, t5, t6
	or t4, t4, t5
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 233b
	addi t5, zero, 0
	sltu t5, t5, t4
	xori t5, t5, 1
	sd t5, 152(s11)
	ld t5, 160(s11)
	ld t6, 152(s11)
	and t5, t5, t6
	sd t5, 160(s11)
	addi t0, zero, 23
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 8
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 4
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
234:
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
	bnez t3, 234b
	sd t4, 152(s11)
	ld t5, 160(s11)
	ld t6, 152(s11)
	and t5, t5, t6
	sd t5, 160(s11)
	addi t0, zero, 20
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 0
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 8
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	ld t4, 152(s11)
	addi t5, zero, 0
	sub t4, t5, t4
	addi t3, s9, 0
235:
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
	bnez t3, 235b
	addi t0, zero, 17
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 5
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
236:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 236b
	addi a7, zero, 16
	mul a7, a7, s10
	add a7, a7, s11
	addi a7, a7, 256
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
	addi t0, s9, 0
	addi a5, zero, 18
	mul a5, a5, s10
	add a5, a5, s11
	addi a5, a5, 256
	addi a6, zero, 19
	mul a6, a6, s10
	add a6, a6, s11
	addi a6, a6, 256
	addi a2, zero, 21
	mul a2, a2, s10
	add a2, a2, s11
	addi a2, a2, 256
	addi a3, zero, 17
	mul a3, a3, s10
	add a3, a3, s11
	addi a3, a3, 256
	addi a4, zero, 20
	mul a4, a4, s10
	add a4, a4, s11
	addi a4, a4, 256
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
	addi a0, a7, 0
237:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 237b
238:
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
	beqz t5, 239f
241:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
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
	bnez t5, 241b
	j 240f
239:
240:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 242f
244:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 24(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
	ld a7, 24(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 32(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
	ld a7, 32(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 40(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
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
	bnez t5, 244b
	j 243f
242:
243:
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
	bnez a1, 238b
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
245:
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
	bnez t5, 245b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
246:
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
	bnez t5, 246b
	addi t0, zero, 17
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 1
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
247:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 247b
	addi a7, zero, 16
	mul a7, a7, s10
	add a7, a7, s11
	addi a7, a7, 256
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
	addi t0, s9, 0
	addi a5, zero, 18
	mul a5, a5, s10
	add a5, a5, s11
	addi a5, a5, 256
	addi a6, zero, 19
	mul a6, a6, s10
	add a6, a6, s11
	addi a6, a6, 256
	addi a2, zero, 22
	mul a2, a2, s10
	add a2, a2, s11
	addi a2, a2, 256
	addi a3, zero, 17
	mul a3, a3, s10
	add a3, a3, s11
	addi a3, a3, 256
	addi a4, zero, 17
	mul a4, a4, s10
	add a4, a4, s11
	addi a4, a4, 256
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
	addi a0, a7, 0
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
	beqz t5, 250f
252:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
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
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 24(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
	ld a7, 24(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 32(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
	ld a7, 32(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 40(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
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
	slli s2, t0, 3
	sub a0, a0, s2
	addi a0, a0, 8
	addi a1, a1, -1
	bnez a1, 249b
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
	addi t1, zero, 21
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 22
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t4, zero, 0
	addi t3, s9, 0
258:
	ld t5, 0(t1)
	ld t6, 0(t2)
	xor t5, t5, t6
	or t4, t4, t5
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 258b
	addi t5, zero, 0
	sltu t5, t5, t4
	xori t5, t5, 1
	sd t5, 152(s11)
	ld t5, 160(s11)
	ld t6, 152(s11)
	and t5, t5, t6
	sd t5, 160(s11)
	addi t0, zero, 10
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 4
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
259:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 259b
	addi t0, zero, 10
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld t5, 0(t0)
	andi t5, t5, -2
	sd t5, 0(t0)
	addi t0, zero, 11
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 5
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
	addi t0, zero, 11
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld t5, 0(t0)
	andi t5, t5, -2
	sd t5, 0(t0)
	addi t0, zero, 23
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 6
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 10
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
261:
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
	bnez t3, 261b
	sd t4, 152(s11)
	ld t5, 160(s11)
	ld t6, 152(s11)
	and t5, t5, t6
	sd t5, 160(s11)
	addi t0, zero, 16
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 3
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
262:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 262b
	addi t0, zero, 17
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 6
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
263:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 263b
	addi t0, zero, 18
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 0
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
264:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 264b
	addi s7, zero, 33
265:
	addi t0, zero, 16
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld t5, 0(t0)
	andi t5, t5, 1
	sd t5, 136(s11)
	addi t0, zero, 19
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 0
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 17
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	ld t4, 136(s11)
	addi t5, zero, 0
	sub t4, t5, t4
	addi t3, s9, 0
266:
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
	bnez t3, 266b
	addi t0, zero, 20
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 0
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 19
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
267:
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
	bnez t3, 267b
	addi t0, zero, 21
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 18
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 20
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
268:
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
	bnez t3, 268b
	addi t0, zero, 22
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 21
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 10
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
269:
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
	bnez t3, 269b
	sd t4, 144(s11)
	addi t0, zero, 18
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 22
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 21
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	ld t4, 144(s11)
	addi t5, zero, 0
	sub t4, t5, t4
	addi t3, s9, 0
270:
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
	bnez t3, 270b
	addi t0, zero, 20
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 0
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 17
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
271:
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
	bnez t3, 271b
	addi t0, zero, 21
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 17
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 20
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
272:
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
	bnez t3, 272b
	addi t0, zero, 22
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 21
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 10
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
273:
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
	bnez t3, 273b
	sd t4, 144(s11)
	addi t0, zero, 17
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 22
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 21
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	ld t4, 144(s11)
	addi t5, zero, 0
	sub t4, t5, t4
	addi t3, s9, 0
274:
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
	bnez t3, 274b
	addi t4, zero, 0
	addi t0, zero, 16
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	slli t5, s9, 3
	add t5, t0, t5
	sd t4, 0(t5)
	addi t3, s9, 0
275:
	ld t5, 0(t0)
	ld t6, 8(t0)
	slli t6, t6, 63
	srli t5, t5, 1
	or t5, t5, t6
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t3, t3, -1
	bnez t3, 275b
	addi s7, s7, -1
	bnez s7, 265b
	addi t1, zero, 18
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 1
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t4, zero, 0
	addi t3, s9, 0
276:
	ld t5, 0(t1)
	ld t6, 0(t2)
	xor t5, t5, t6
	or t4, t4, t5
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 276b
	addi t5, zero, 0
	sltu t5, t5, t4
	xori t5, t5, 1
	sd t5, 152(s11)
	ld t5, 160(s11)
	ld t6, 152(s11)
	and t5, t5, t6
	sd t5, 160(s11)
	addi t0, zero, 23
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 7
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 11
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
277:
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
	bnez t3, 277b
	sd t4, 152(s11)
	ld t5, 160(s11)
	ld t6, 152(s11)
	and t5, t5, t6
	sd t5, 160(s11)
	addi t0, zero, 16
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 3
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
278:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 278b
	addi t0, zero, 17
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 7
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
279:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 279b
	addi t0, zero, 18
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 0
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
280:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 280b
	addi s7, zero, 33
281:
	addi t0, zero, 16
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld t5, 0(t0)
	andi t5, t5, 1
	sd t5, 136(s11)
	addi t0, zero, 19
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 0
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 17
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	ld t4, 136(s11)
	addi t5, zero, 0
	sub t4, t5, t4
	addi t3, s9, 0
282:
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
	bnez t3, 282b
	addi t0, zero, 20
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 0
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 19
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
283:
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
	bnez t3, 283b
	addi t0, zero, 21
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 18
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 20
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
284:
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
	bnez t3, 284b
	addi t0, zero, 22
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 21
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 11
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
285:
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
	bnez t3, 285b
	sd t4, 144(s11)
	addi t0, zero, 18
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 22
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 21
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	ld t4, 144(s11)
	addi t5, zero, 0
	sub t4, t5, t4
	addi t3, s9, 0
286:
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
	bnez t3, 286b
	addi t0, zero, 20
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 0
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 17
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
287:
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
	bnez t3, 287b
	addi t0, zero, 21
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 17
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 20
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
288:
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
	bnez t3, 288b
	addi t0, zero, 22
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 21
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 11
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
289:
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
	bnez t3, 289b
	sd t4, 144(s11)
	addi t0, zero, 17
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 22
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 21
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	ld t4, 144(s11)
	addi t5, zero, 0
	sub t4, t5, t4
	addi t3, s9, 0
290:
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
	bnez t3, 290b
	addi t4, zero, 0
	addi t0, zero, 16
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	slli t5, s9, 3
	add t5, t0, t5
	sd t4, 0(t5)
	addi t3, s9, 0
291:
	ld t5, 0(t0)
	ld t6, 8(t0)
	slli t6, t6, 63
	srli t5, t5, 1
	or t5, t5, t6
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t3, t3, -1
	bnez t3, 291b
	addi s7, s7, -1
	bnez s7, 281b
	addi t1, zero, 18
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 1
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t4, zero, 0
	addi t3, s9, 0
292:
	ld t5, 0(t1)
	ld t6, 0(t2)
	xor t5, t5, t6
	or t4, t4, t5
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 292b
	addi t5, zero, 0
	sltu t5, t5, t4
	xori t5, t5, 1
	sd t5, 152(s11)
	ld t5, 160(s11)
	ld t6, 152(s11)
	and t5, t5, t6
	sd t5, 160(s11)
	addi t0, zero, 23
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 9
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 2
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
293:
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
	bnez t3, 293b
	sd t4, 152(s11)
	ld t5, 160(s11)
	ld t6, 152(s11)
	and t5, t5, t6
	sd t5, 160(s11)
	addi t0, zero, 12
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 9
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
294:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 294b
	addi t0, zero, 14
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 10
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
295:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 295b
	addi s8, s5, 7
	srli s8, s8, 3
	addi t0, zero, 13
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t3, s9, 1
	addi t5, zero, 0
296:
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t3, t3, -1
	bnez t3, 296b
	slli s7, s9, 6
	addi a4, zero, -1
297:
	addi t2, zero, 12
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t5, s7, -1
	srli t5, t5, 6
	slli t5, t5, 3
	add t2, t2, t5
	ld t5, 0(t2)
	srli t3, t5, 63
	addi t0, zero, 13
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 14
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	andi t4, a4, 1
	addi t2, s8, 1
	andi t2, t2, 3
	beqz t2, 298f
2100:
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
	bnez t2, 2100b
	j 299f
298:
299:
	addi t2, s8, 1
	srli t2, t2, 2
	beqz t2, 2101f
2103:
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
	bnez t2, 2103b
	j 2102f
2101:
2102:
	srli t5, t6, 63
	addi a4, t5, -1
	andi a5, a4, 1
	addi t2, zero, 12
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
	bnez s7, 297b
	addi t0, zero, 13
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 14
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	xori a4, a4, -1
	addi t4, zero, 0
	addi t3, s8, 1
2104:
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
	bnez t3, 2104b
	addi t1, zero, 13
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 6
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t4, zero, 0
	addi t3, s9, 0
2105:
	ld t5, 0(t1)
	ld t6, 0(t2)
	xor t5, t5, t6
	or t4, t4, t5
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 2105b
	addi t5, zero, 0
	sltu t5, t5, t4
	xori t5, t5, 1
	sd t5, 152(s11)
	ld t5, 160(s11)
	ld t6, 152(s11)
	and t5, t5, t6
	sd t5, 160(s11)
	addi t0, zero, 12
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 9
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
2106:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 2106b
	addi t0, zero, 14
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 11
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
2107:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 2107b
	addi s8, s6, 7
	srli s8, s8, 3
	addi t0, zero, 13
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t3, s9, 1
	addi t5, zero, 0
2108:
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t3, t3, -1
	bnez t3, 2108b
	slli s7, s9, 6
	addi a4, zero, -1
2109:
	addi t2, zero, 12
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t5, s7, -1
	srli t5, t5, 6
	slli t5, t5, 3
	add t2, t2, t5
	ld t5, 0(t2)
	srli t3, t5, 63
	addi t0, zero, 13
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 14
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	andi t4, a4, 1
	addi t2, s8, 1
	andi t2, t2, 3
	beqz t2, 2110f
2112:
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
	bnez t2, 2112b
	j 2111f
2110:
2111:
	addi t2, s8, 1
	srli t2, t2, 2
	beqz t2, 2113f
2115:
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
	bnez t2, 2115b
	j 2114f
2113:
2114:
	srli t5, t6, 63
	addi a4, t5, -1
	andi a5, a4, 1
	addi t2, zero, 12
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
	bnez s7, 2109b
	addi t0, zero, 13
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 14
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	xori a4, a4, -1
	addi t4, zero, 0
	addi t3, s8, 1
2116:
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
	bnez t3, 2116b
	addi t1, zero, 13
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 7
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t4, zero, 0
	addi t3, s9, 0
2117:
	ld t5, 0(t1)
	ld t6, 0(t2)
	xor t5, t5, t6
	or t4, t4, t5
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 2117b
	addi t5, zero, 0
	sltu t5, t5, t4
	xori t5, t5, 1
	sd t5, 152(s11)
	ld t5, 160(s11)
	ld t6, 152(s11)
	and t5, t5, t6
	sd t5, 160(s11)
	ld a0, 160(s11)
26:
	ld s0, 0(s11)
	ld s1, 8(s11)
	ld s2, 16(s11)
	ld s3, 24(s11)
	ld s4, 32(s11)
	ld s5, 40(s11)
	ld s6, 48(s11)
	ld s7, 56(s11)
	ld s8, 64(s11)
	ld s9, 72(s11)
	ld s10, 80(s11)
	ld s11, 88(s11)
	ret
	.option pop

vg_rsa_check_crt_key:
	.option push
	.option arch, +m, +c
	addi t0, sp, 0
	ld t0, 48(t0)
	sd s0, 0(t0)
	sd s1, 8(t0)
	sd s2, 16(t0)
	sd s3, 24(t0)
	sd s4, 32(t0)
	sd s5, 40(t0)
	sd s6, 48(t0)
	sd s7, 56(t0)
	sd s8, 64(t0)
	sd s9, 72(t0)
	sd s10, 80(t0)
	sd s11, 88(t0)
	addi s11, t0, 0
	addi s1, a0, 0
	addi s2, a1, 0
	addi s3, a4, 0
	addi s4, a5, 0
	addi s5, a6, 0
	addi s6, a7, 0
	addi a4, a2, 0
	addi a5, a3, 0
	addi t0, sp, 0
	ld a2, 0(t0)
	ld a3, 16(t0)
	ld a6, 32(t0)
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
	addi a5, s9, 0
	addi a4, s7, 0
	addi s7, s1, 0
	addi s8, s2, 0
	add t4, s7, s8
	addi t4, t4, -1
	lbu s0, 0(t4)
	andi s0, s0, 1
	xori s0, s0, 1
	lbu t4, 0(s7)
	beqz t4, 21f
	j 22f
21:
	addi s0, zero, 1
22:
	addi t5, s8, -64
	beqz t5, 23f
	j 24f
23:
	srli t4, t4, 7
	xori t4, t4, 1
	or s0, s0, t4
24:
	addi t0, a5, 1
	or t0, t0, s0
	beqz t0, 25f
	addi a0, zero, 0
	j 26f
25:
	addi s9, s2, 7
	srli s9, s9, 3
	addi s10, s9, 2
	slli s10, s10, 3
	addi t3, zero, 24
	mul t3, t3, s10
	srli t3, t3, 3
	addi t0, s11, 256
	addi t5, zero, 0
27:
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t3, t3, -1
	bnez t3, 27b
	addi t0, zero, 3
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	srli t5, a4, 31
	sd t5, 0(t0)
	addi t1, s1, 0
	addi t3, s2, 0
	addi t0, zero, 2
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	add t0, t0, t3
	addi t0, t0, -1
28:
	lbu t5, 0(t1)
	sb t5, 0(t0)
	addi t1, t1, 1
	addi t0, t0, -1
	addi t3, t3, -1
	bnez t3, 28b
	addi t1, s3, 0
	addi t3, s4, 0
	addi t0, zero, 4
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	add t0, t0, t3
	addi t0, t0, -1
29:
	lbu t5, 0(t1)
	sb t5, 0(t0)
	addi t1, t1, 1
	addi t0, t0, -1
	addi t3, t3, -1
	bnez t3, 29b
	addi t1, s5, 0
	addi t3, s6, 0
	addi t0, zero, 5
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	add t0, t0, t3
	addi t0, t0, -1
210:
	lbu t5, 0(t1)
	sb t5, 0(t0)
	addi t1, t1, 1
	addi t0, t0, -1
	addi t3, t3, -1
	bnez t3, 210b
	addi t1, a2, 0
	addi t3, s4, 0
	addi t0, zero, 6
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	add t0, t0, t3
	addi t0, t0, -1
211:
	lbu t5, 0(t1)
	sb t5, 0(t0)
	addi t1, t1, 1
	addi t0, t0, -1
	addi t3, t3, -1
	bnez t3, 211b
	addi t1, a3, 0
	addi t3, s6, 0
	addi t0, zero, 7
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	add t0, t0, t3
	addi t0, t0, -1
212:
	lbu t5, 0(t1)
	sb t5, 0(t0)
	addi t1, t1, 1
	addi t0, t0, -1
	addi t3, t3, -1
	bnez t3, 212b
	addi t1, a6, 0
	addi t3, s4, 0
	addi t0, zero, 8
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	add t0, t0, t3
	addi t0, t0, -1
213:
	lbu t5, 0(t1)
	sb t5, 0(t0)
	addi t1, t1, 1
	addi t0, t0, -1
	addi t3, t3, -1
	bnez t3, 213b
	addi t0, zero, 1
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t5, zero, 1
	sd t5, 0(t0)
	addi t0, zero, 4
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld t5, 0(t0)
	andi t5, t5, 1
	sd t5, 160(s11)
	addi t0, zero, 16
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 4
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
214:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 214b
	addi t0, zero, 16
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld t5, 0(t0)
	ori t5, t5, 1
	sd t5, 0(t0)
	addi t1, zero, 16
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 1
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t4, zero, 0
	addi t3, s9, 0
215:
	ld t5, 0(t1)
	ld t6, 0(t2)
	xor t5, t5, t6
	or t4, t4, t5
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 215b
	addi t5, zero, 0
	sltu t5, t5, t4
	xori t5, t5, 1
	sd t5, 152(s11)
	addi t0, zero, 16
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld t5, 0(t0)
	ld t6, 152(s11)
	slli t6, t6, 1
	or t5, t5, t6
	sd t5, 0(t0)
	addi t0, zero, 17
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 2
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
216:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 216b
	addi t0, zero, 20
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 1
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
217:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 217b
	addi a7, zero, 16
	mul a7, a7, s10
	add a7, a7, s11
	addi a7, a7, 256
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
	addi t0, s9, 0
	addi a5, zero, 18
	mul a5, a5, s10
	add a5, a5, s11
	addi a5, a5, 256
	addi a6, zero, 19
	mul a6, a6, s10
	add a6, a6, s11
	addi a6, a6, 256
	addi a2, zero, 21
	mul a2, a2, s10
	add a2, a2, s11
	addi a2, a2, 256
	addi a3, zero, 17
	mul a3, a3, s10
	add a3, a3, s11
	addi a3, a3, 256
	addi a4, zero, 20
	mul a4, a4, s10
	add a4, a4, s11
	addi a4, a4, 256
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
	addi a0, a7, 0
218:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 218b
219:
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
	beqz t5, 220f
222:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
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
	bnez t5, 222b
	j 221f
220:
221:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 223f
225:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 24(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
	ld a7, 24(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 32(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
	ld a7, 32(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 40(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
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
	bnez t5, 225b
	j 224f
223:
224:
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
	bnez a1, 219b
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
226:
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
	bnez t5, 226b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
227:
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
	bnez t5, 227b
	addi t1, zero, 21
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 0
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t4, zero, 0
	addi t3, s9, 0
228:
	ld t5, 0(t1)
	ld t6, 0(t2)
	xor t5, t5, t6
	or t4, t4, t5
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 228b
	addi t5, zero, 0
	sltu t5, t5, t4
	xori t5, t5, 1
	sd t5, 152(s11)
	ld t5, 160(s11)
	ld t6, 152(s11)
	and t5, t5, t6
	sd t5, 160(s11)
	addi t0, zero, 22
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 0
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
229:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 229b
	addi a2, zero, 4
	mul a2, a2, s10
	add a2, a2, s11
	addi a2, a2, 256
	addi a3, zero, 22
	mul a3, a3, s10
	add a3, a3, s11
	addi a3, a3, 256
	addi s8, s9, 0
230:
	ld a6, 0(a2)
	addi t0, a3, 0
	addi t1, zero, 5
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s8, 0
	addi t4, zero, 0
231:
	ld t5, 0(t1)
	mul t6, a6, t5
	mulhu t5, a6, t5
	ld a4, 0(t0)
	add t6, t6, a4
	sltu a4, t6, a4
	add t5, t5, a4
	add t6, t6, t4
	sltu a4, t6, t4
	add t5, t5, a4
	sd t6, 0(t0)
	addi t4, t5, 0
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 231b
	addi a2, a2, 8
	addi a3, a3, 8
	addi s8, s8, -1
	bnez s8, 230b
	addi t1, zero, 22
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 2
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t4, zero, 0
	addi t3, s9, 0
232:
	ld t5, 0(t1)
	ld t6, 0(t2)
	xor t5, t5, t6
	or t4, t4, t5
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 232b
	addi t5, zero, 0
	sltu t5, t5, t4
	xori t5, t5, 1
	sd t5, 152(s11)
	ld t5, 160(s11)
	ld t6, 152(s11)
	and t5, t5, t6
	sd t5, 160(s11)
	addi t0, zero, 23
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 8
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 4
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
233:
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
	bnez t3, 233b
	sd t4, 152(s11)
	ld t5, 160(s11)
	ld t6, 152(s11)
	and t5, t5, t6
	sd t5, 160(s11)
	addi t0, zero, 20
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 0
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 8
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	ld t4, 152(s11)
	addi t5, zero, 0
	sub t4, t5, t4
	addi t3, s9, 0
234:
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
	bnez t3, 234b
	addi t0, zero, 17
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 5
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
235:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 235b
	addi a7, zero, 16
	mul a7, a7, s10
	add a7, a7, s11
	addi a7, a7, 256
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
	addi t0, s9, 0
	addi a5, zero, 18
	mul a5, a5, s10
	add a5, a5, s11
	addi a5, a5, 256
	addi a6, zero, 19
	mul a6, a6, s10
	add a6, a6, s11
	addi a6, a6, 256
	addi a2, zero, 21
	mul a2, a2, s10
	add a2, a2, s11
	addi a2, a2, 256
	addi a3, zero, 17
	mul a3, a3, s10
	add a3, a3, s11
	addi a3, a3, 256
	addi a4, zero, 20
	mul a4, a4, s10
	add a4, a4, s11
	addi a4, a4, 256
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
	addi a0, a7, 0
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
	beqz t5, 238f
240:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
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
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 24(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
	ld a7, 24(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 32(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
	ld a7, 32(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 40(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
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
	slli s2, t0, 3
	sub a0, a0, s2
	addi a0, a0, 8
	addi a1, a1, -1
	bnez a1, 237b
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
	addi t0, zero, 17
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 1
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
246:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 246b
	addi a7, zero, 16
	mul a7, a7, s10
	add a7, a7, s11
	addi a7, a7, 256
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
	addi t0, s9, 0
	addi a5, zero, 18
	mul a5, a5, s10
	add a5, a5, s11
	addi a5, a5, 256
	addi a6, zero, 19
	mul a6, a6, s10
	add a6, a6, s11
	addi a6, a6, 256
	addi a2, zero, 22
	mul a2, a2, s10
	add a2, a2, s11
	addi a2, a2, 256
	addi a3, zero, 17
	mul a3, a3, s10
	add a3, a3, s11
	addi a3, a3, 256
	addi a4, zero, 17
	mul a4, a4, s10
	add a4, a4, s11
	addi a4, a4, 256
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
	addi a0, a7, 0
247:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 247b
248:
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
	beqz t5, 249f
251:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
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
	bnez t5, 251b
	j 250f
249:
250:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 252f
254:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 24(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
	ld a7, 24(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 32(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
	ld a7, 32(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mul s2, t6, a6
	mulhu s3, t6, a6
	ld a6, 40(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mul s2, t2, a7
	mulhu s3, t2, a7
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
	bnez t5, 254b
	j 253f
252:
253:
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
	bnez a1, 248b
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
255:
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
	bnez t5, 255b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
256:
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
	bnez t5, 256b
	addi t1, zero, 21
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 22
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t4, zero, 0
	addi t3, s9, 0
257:
	ld t5, 0(t1)
	ld t6, 0(t2)
	xor t5, t5, t6
	or t4, t4, t5
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 257b
	addi t5, zero, 0
	sltu t5, t5, t4
	xori t5, t5, 1
	sd t5, 152(s11)
	ld t5, 160(s11)
	ld t6, 152(s11)
	and t5, t5, t6
	sd t5, 160(s11)
	addi t0, zero, 10
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 4
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
258:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 258b
	addi t0, zero, 10
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld t5, 0(t0)
	andi t5, t5, -2
	sd t5, 0(t0)
	addi t0, zero, 11
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 5
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
259:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 259b
	addi t0, zero, 11
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld t5, 0(t0)
	andi t5, t5, -2
	sd t5, 0(t0)
	addi t0, zero, 23
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 6
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 10
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
260:
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
	bnez t3, 260b
	sd t4, 152(s11)
	ld t5, 160(s11)
	ld t6, 152(s11)
	and t5, t5, t6
	sd t5, 160(s11)
	addi t0, zero, 16
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 3
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
	addi t0, zero, 17
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 6
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
262:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 262b
	addi t0, zero, 18
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 0
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
263:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 263b
	addi s7, zero, 33
264:
	addi t0, zero, 16
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld t5, 0(t0)
	andi t5, t5, 1
	sd t5, 136(s11)
	addi t0, zero, 19
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 0
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 17
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	ld t4, 136(s11)
	addi t5, zero, 0
	sub t4, t5, t4
	addi t3, s9, 0
265:
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
	bnez t3, 265b
	addi t0, zero, 20
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 0
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 19
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
266:
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
	bnez t3, 266b
	addi t0, zero, 21
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 18
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 20
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
267:
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
	bnez t3, 267b
	addi t0, zero, 22
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 21
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 10
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
268:
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
	bnez t3, 268b
	sd t4, 144(s11)
	addi t0, zero, 18
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 22
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 21
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	ld t4, 144(s11)
	addi t5, zero, 0
	sub t4, t5, t4
	addi t3, s9, 0
269:
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
	bnez t3, 269b
	addi t0, zero, 20
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 0
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 17
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
270:
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
	bnez t3, 270b
	addi t0, zero, 21
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 17
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 20
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
271:
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
	bnez t3, 271b
	addi t0, zero, 22
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 21
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 10
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
272:
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
	bnez t3, 272b
	sd t4, 144(s11)
	addi t0, zero, 17
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 22
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 21
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	ld t4, 144(s11)
	addi t5, zero, 0
	sub t4, t5, t4
	addi t3, s9, 0
273:
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
	bnez t3, 273b
	addi t4, zero, 0
	addi t0, zero, 16
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	slli t5, s9, 3
	add t5, t0, t5
	sd t4, 0(t5)
	addi t3, s9, 0
274:
	ld t5, 0(t0)
	ld t6, 8(t0)
	slli t6, t6, 63
	srli t5, t5, 1
	or t5, t5, t6
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t3, t3, -1
	bnez t3, 274b
	addi s7, s7, -1
	bnez s7, 264b
	addi t1, zero, 18
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 1
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t4, zero, 0
	addi t3, s9, 0
275:
	ld t5, 0(t1)
	ld t6, 0(t2)
	xor t5, t5, t6
	or t4, t4, t5
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 275b
	addi t5, zero, 0
	sltu t5, t5, t4
	xori t5, t5, 1
	sd t5, 152(s11)
	ld t5, 160(s11)
	ld t6, 152(s11)
	and t5, t5, t6
	sd t5, 160(s11)
	addi t0, zero, 23
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 7
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 11
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
276:
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
	bnez t3, 276b
	sd t4, 152(s11)
	ld t5, 160(s11)
	ld t6, 152(s11)
	and t5, t5, t6
	sd t5, 160(s11)
	addi t0, zero, 16
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 3
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
277:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 277b
	addi t0, zero, 17
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 7
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
278:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 278b
	addi t0, zero, 18
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 0
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
279:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 279b
	addi s7, zero, 33
280:
	addi t0, zero, 16
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld t5, 0(t0)
	andi t5, t5, 1
	sd t5, 136(s11)
	addi t0, zero, 19
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 0
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 17
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	ld t4, 136(s11)
	addi t5, zero, 0
	sub t4, t5, t4
	addi t3, s9, 0
281:
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
	bnez t3, 281b
	addi t0, zero, 20
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 0
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 19
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
282:
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
	bnez t3, 282b
	addi t0, zero, 21
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 18
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 20
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
283:
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
	bnez t3, 283b
	addi t0, zero, 22
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 21
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 11
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
284:
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
	bnez t3, 284b
	sd t4, 144(s11)
	addi t0, zero, 18
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 22
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 21
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	ld t4, 144(s11)
	addi t5, zero, 0
	sub t4, t5, t4
	addi t3, s9, 0
285:
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
	bnez t3, 285b
	addi t0, zero, 20
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 0
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 17
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
286:
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
	bnez t3, 286b
	addi t0, zero, 21
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 17
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 20
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
287:
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
	bnez t3, 287b
	addi t0, zero, 22
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 21
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 11
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
288:
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
	bnez t3, 288b
	sd t4, 144(s11)
	addi t0, zero, 17
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 22
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 21
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	ld t4, 144(s11)
	addi t5, zero, 0
	sub t4, t5, t4
	addi t3, s9, 0
289:
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
	bnez t3, 289b
	addi t4, zero, 0
	addi t0, zero, 16
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	slli t5, s9, 3
	add t5, t0, t5
	sd t4, 0(t5)
	addi t3, s9, 0
290:
	ld t5, 0(t0)
	ld t6, 8(t0)
	slli t6, t6, 63
	srli t5, t5, 1
	or t5, t5, t6
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t3, t3, -1
	bnez t3, 290b
	addi s7, s7, -1
	bnez s7, 280b
	addi t1, zero, 18
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 1
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t4, zero, 0
	addi t3, s9, 0
291:
	ld t5, 0(t1)
	ld t6, 0(t2)
	xor t5, t5, t6
	or t4, t4, t5
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 291b
	addi t5, zero, 0
	sltu t5, t5, t4
	xori t5, t5, 1
	sd t5, 152(s11)
	ld t5, 160(s11)
	ld t6, 152(s11)
	and t5, t5, t6
	sd t5, 160(s11)
	ld a0, 160(s11)
26:
	ld s0, 0(s11)
	ld s1, 8(s11)
	ld s2, 16(s11)
	ld s3, 24(s11)
	ld s4, 32(s11)
	ld s5, 40(s11)
	ld s6, 48(s11)
	ld s7, 56(s11)
	ld s8, 64(s11)
	ld s9, 72(s11)
	ld s10, 80(s11)
	ld s11, 88(s11)
	ret
	.option pop

vg_rsa_recover_primes_det:
	.option push
	.option arch, +m, +c
	addi t0, sp, 0
	ld t0, 16(t0)
	sd s0, 0(t0)
	sd s1, 8(t0)
	sd s2, 16(t0)
	sd s3, 24(t0)
	sd s4, 32(t0)
	sd s5, 40(t0)
	sd s6, 48(t0)
	sd s7, 56(t0)
	sd s8, 64(t0)
	sd s9, 72(t0)
	sd s10, 80(t0)
	sd s11, 88(t0)
	addi s11, t0, 0
	addi s3, a0, 0
	addi s4, a2, 0
	addi s1, a4, 0
	addi s2, a5, 0
	addi s5, a6, 0
	addi s6, a7, 0
	addi t0, sp, 0
	ld a0, 0(t0)
	ld a1, 8(t0)
	addi s7, s1, 0
	addi s8, s2, 0
	add t4, s7, s8
	addi t4, t4, -1
	lbu s0, 0(t4)
	andi s0, s0, 1
	xori s0, s0, 1
	lbu t4, 0(s7)
	beqz t4, 20f
	j 21f
20:
	addi s0, zero, 1
21:
	addi t5, s8, -64
	beqz t5, 22f
	j 23f
22:
	srli t4, t4, 7
	xori t4, t4, 1
	or s0, s0, t4
23:
	beqz s0, 24f
	addi t0, s3, 0
	addi t3, s2, 0
	addi t5, zero, 0
26:
	sb t5, 0(t0)
	addi t0, t0, 1
	addi t3, t3, -1
	bnez t3, 26b
	addi t0, s4, 0
	addi t3, s2, 0
	addi t5, zero, 0
27:
	sb t5, 0(t0)
	addi t0, t0, 1
	addi t3, t3, -1
	bnez t3, 27b
	addi a0, zero, 0
	j 25f
24:
	addi s9, s2, 7
	srli s9, s9, 3
	addi s9, s9, 1
	addi s10, s9, 2
	slli s10, s10, 3
	addi t3, zero, 63
	mul t3, t3, s10
	srli t3, t3, 3
	addi t0, s11, 256
	addi t5, zero, 0
28:
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t3, t3, -1
	bnez t3, 28b
	addi t1, s1, 0
	addi t3, s2, 0
	addi t0, zero, 40
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	add t0, t0, t3
	addi t0, t0, -1
29:
	lbu t5, 0(t1)
	sb t5, 0(t0)
	addi t1, t1, 1
	addi t0, t0, -1
	addi t3, t3, -1
	bnez t3, 29b
	slli s9, s9, 1
	addi s9, s9, 2
	slli s10, s10, 1
	addi t1, s5, 0
	addi t3, s6, 0
	addi t0, zero, 1
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	add t0, t0, t3
	addi t0, t0, -1
210:
	lbu t5, 0(t1)
	sb t5, 0(t0)
	addi t1, t1, 1
	addi t0, t0, -1
	addi t3, t3, -1
	bnez t3, 210b
	addi t1, a0, 0
	addi t3, a1, 0
	addi t0, zero, 2
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	add t0, t0, t3
	addi t0, t0, -1
211:
	lbu t5, 0(t1)
	sb t5, 0(t0)
	addi t1, t1, 1
	addi t0, t0, -1
	addi t3, t3, -1
	bnez t3, 211b
	addi t0, zero, 4
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	slli t5, s9, 3
	add t0, t0, t5
	addi t0, t0, -8
	addi t5, zero, 1
	slli t5, t5, 63
	sd t5, 0(t0)
	slli s7, s6, 3
212:
	addi t0, zero, 1
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld t5, 0(t0)
	andi t5, t5, 1
	sd t5, 136(s11)
	addi t0, zero, 5
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 0
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 2
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	ld t4, 136(s11)
	addi t5, zero, 0
	sub t4, t5, t4
	addi t3, s9, 0
213:
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
	bnez t3, 213b
	addi t0, zero, 6
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 0
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 5
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
214:
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
	bnez t3, 214b
	addi t0, zero, 7
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 3
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 6
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
215:
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
	bnez t3, 215b
	addi t0, zero, 8
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 7
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 4
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
216:
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
	bnez t3, 216b
	sd t4, 144(s11)
	addi t0, zero, 3
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 8
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 7
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	ld t4, 144(s11)
	addi t5, zero, 0
	sub t4, t5, t4
	addi t3, s9, 0
217:
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
	bnez t3, 217b
	addi t0, zero, 6
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 0
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 2
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
218:
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
	bnez t3, 218b
	addi t0, zero, 7
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 2
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 6
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
219:
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
	bnez t3, 219b
	addi t0, zero, 8
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 7
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 4
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
220:
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
	bnez t3, 220b
	sd t4, 144(s11)
	addi t0, zero, 2
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 8
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 7
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	ld t4, 144(s11)
	addi t5, zero, 0
	sub t4, t5, t4
	addi t3, s9, 0
221:
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
	bnez t3, 221b
	addi t4, zero, 0
	addi t0, zero, 1
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	slli t5, s9, 3
	add t5, t0, t5
	sd t4, 0(t5)
	addi t3, s9, 0
222:
	ld t5, 0(t0)
	ld t6, 8(t0)
	slli t6, t6, 63
	srli t5, t5, 1
	or t5, t5, t6
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t3, t3, -1
	bnez t3, 222b
	addi s7, s7, -1
	bnez s7, 212b
	addi t0, zero, 10
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t5, zero, 1
	sd t5, 0(t0)
	addi t0, zero, 9
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 3
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 10
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
223:
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
	bnez t3, 223b
	sd t4, 152(s11)
	addi t0, zero, 16
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 9
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 10
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
224:
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
	bnez t3, 224b
	sd t4, 160(s11)
	addi t0, zero, 11
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 9
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
225:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 225b
	addi s9, s9, -2
	srli s9, s9, 1
	srli s10, s10, 1
	addi t0, zero, 41
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t5, zero, 1
	sd t5, 0(t0)
	addi t0, zero, 43
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 40
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 41
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
226:
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
	bnez t3, 226b
	addi t0, zero, 44
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 18
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
227:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 227b
	slli s7, s9, 6
228:
	addi t0, zero, 43
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld t5, 0(t0)
	andi t5, t5, 1
	sd t5, 168(s11)
	addi t0, zero, 44
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld t5, 0(t0)
	andi t5, t5, 1
	sd t5, 176(s11)
	ld t5, 168(s11)
	ld t6, 176(s11)
	xori t5, t5, 1
	xori t6, t6, 1
	sd t5, 184(s11)
	and t6, t6, t5
	sd t6, 192(s11)
	addi t0, zero, 43
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld a4, 184(s11)
	addi t4, zero, 0
	sub a4, t4, a4
	slli t5, s9, 3
	add t5, t0, t5
	sd t4, 0(t5)
	addi t3, s9, 0
229:
	ld t5, 0(t0)
	ld t6, 8(t0)
	srli t1, t5, 1
	slli t6, t6, 63
	or t1, t1, t6
	xor t1, t1, t5
	and t1, t1, a4
	xor t5, t5, t1
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t3, t3, -1
	bnez t3, 229b
	addi t0, zero, 44
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld a4, 192(s11)
	addi t4, zero, 0
	sub a4, t4, a4
	slli t5, s9, 3
	add t5, t0, t5
	sd t4, 0(t5)
	addi t3, s9, 0
230:
	ld t5, 0(t0)
	ld t6, 8(t0)
	srli t1, t5, 1
	slli t6, t6, 63
	or t1, t1, t6
	xor t1, t1, t5
	and t1, t1, a4
	xor t5, t5, t1
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t3, t3, -1
	bnez t3, 230b
	slli s9, s9, 1
	addi s9, s9, 2
	slli s10, s10, 1
	addi t0, zero, 11
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld a4, 192(s11)
	addi t4, zero, 0
	sub a4, t4, a4
	addi t3, s9, 0
231:
	ld t5, 0(t0)
	slli t6, t5, 1
	or t6, t6, t4
	srli t4, t5, 63
	xor t6, t6, t5
	and t6, t6, a4
	xor t5, t5, t6
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t3, t3, -1
	bnez t3, 231b
	addi s9, s9, -2
	srli s9, s9, 1
	srli s10, s10, 1
	addi s7, s7, -1
	bnez s7, 228b
	addi t0, zero, 0
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 44
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
232:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 232b
	addi t0, zero, 8
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 43
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
233:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 233b
	add s8, s9, s9
	addi t0, zero, 2
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 8
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s8, 0
234:
	lwu t5, 0(t1)
	sw t5, 0(t0)
	addi t0, t0, 4
	addi t1, t1, 4
	addi t3, t3, -1
	bnez t3, 234b
	addi t1, zero, 2
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	slli t3, s8, 2
	add t1, t1, t3
	addi t5, zero, 0
	sw t5, 0(t1)
	addi t0, zero, 7
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t3, s8, 1
	addi t5, zero, 0
235:
	sw t5, 0(t0)
	addi t0, t0, 4
	addi t3, t3, -1
	bnez t3, 235b
	addi t0, zero, 7
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t5, zero, 1
	sw t5, 0(t0)
	addi t1, zero, 2
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 7
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s8, 1
	addi t4, zero, 0
236:
	lwu t5, 0(t1)
	lwu t6, 0(t2)
	xor t5, t5, t6
	or t4, t4, t5
	addi t1, t1, 4
	addi t2, t2, 4
	addi t3, t3, -1
	bnez t3, 236b
	addi t5, zero, 0
	sub t5, t5, t4
	srli t5, t5, 63
	xori t5, t5, 1
	slli t5, t5, 1
	addi t0, zero, 2
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	lwu t6, 0(t0)
	or t6, t6, t5
	sw t6, 0(t0)
	addi a4, zero, 2
	mul a4, a4, s10
	add a4, a4, s11
	addi a4, a4, 256
	lwu t5, 0(a4)
	addi t6, t5, 0
	mul a5, t5, t6
	addi t4, zero, 2
	sub a5, t4, a5
	mul t6, t6, a5
	mul a5, t5, t6
	addi t4, zero, 2
	sub a5, t4, a5
	mul t6, t6, a5
	mul a5, t5, t6
	addi t4, zero, 2
	sub a5, t4, a5
	mul t6, t6, a5
	mul a5, t5, t6
	addi t4, zero, 2
	sub a5, t4, a5
	mul t6, t6, a5
	addi a5, zero, 0
	sub t1, a5, t6
	addi a4, zero, 9
	mul a4, a4, s10
	add a4, a4, s11
	addi a4, a4, 256
	sd t1, 40(a4)
	addi t0, zero, 4
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 2
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s8, 1
237:
	lwu t5, 0(t1)
	sw t5, 0(t0)
	addi t0, t0, 4
	addi t1, t1, 4
	addi t3, t3, -1
	bnez t3, 237b
	addi t0, zero, 0
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	lwu a5, 0(t0)
	andi a5, a5, 1
	xori a5, a5, 1
	addi t0, zero, 5
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 0
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 2
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s8, 0
	addi t4, zero, 0
238:
	lwu t5, 0(t2)
	mul t5, a5, t5
	lwu t6, 0(t1)
	add t5, t5, t6
	add t5, t5, t4
	sw t5, 0(t0)
	srli t4, t5, 32
	addi t0, t0, 4
	addi t1, t1, 4
	addi t2, t2, 4
	addi t3, t3, -1
	bnez t3, 238b
	sw t4, 0(t0)
	addi t0, zero, 6
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t3, s8, 1
	addi t5, zero, 0
239:
	sw t5, 0(t0)
	addi t0, t0, 4
	addi t3, t3, -1
	bnez t3, 239b
	addi t0, zero, 9
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t5, zero, 1
	sd t5, 0(t0)
	addi s7, s8, 1
	add t5, s7, s7
	add s7, s7, t5
240:
	addi t0, zero, 4
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	lwu a4, 0(t0)
	addi t0, zero, 5
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	lwu t0, 0(t0)
	addi t6, zero, 9
	mul t6, t6, s10
	add t6, t6, s11
	addi t6, t6, 256
	ld t6, 0(t6)
	addi t1, zero, 1
	addi t2, zero, 0
	addi t3, zero, 0
	addi t4, zero, 1
	andi t5, t0, 1
	addi a5, zero, 0
	sub a5, a5, t5
	srli a7, t6, 63
	addi a7, a7, -1
	and a7, a7, a5
	xor t5, a4, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t0, t0, t5
	xor t5, t1, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t3, t3, t5
	xor t5, t2, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t4, t4, t5
	xor t6, t6, a7
	sub t6, t6, a7
	addi t6, t6, 2
	and t5, t0, a7
	add a4, a4, t5
	srli t0, t0, 1
	and t5, t3, a7
	add t1, t1, t5
	add t1, t1, t1
	and t5, t4, a7
	add t2, t2, t5
	add t2, t2, t2
	andi t5, t0, 1
	addi a5, zero, 0
	sub a5, a5, t5
	srli a7, t6, 63
	addi a7, a7, -1
	and a7, a7, a5
	xor t5, a4, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t0, t0, t5
	xor t5, t1, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t3, t3, t5
	xor t5, t2, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t4, t4, t5
	xor t6, t6, a7
	sub t6, t6, a7
	addi t6, t6, 2
	and t5, t0, a7
	add a4, a4, t5
	srli t0, t0, 1
	and t5, t3, a7
	add t1, t1, t5
	add t1, t1, t1
	and t5, t4, a7
	add t2, t2, t5
	add t2, t2, t2
	andi t5, t0, 1
	addi a5, zero, 0
	sub a5, a5, t5
	srli a7, t6, 63
	addi a7, a7, -1
	and a7, a7, a5
	xor t5, a4, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t0, t0, t5
	xor t5, t1, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t3, t3, t5
	xor t5, t2, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t4, t4, t5
	xor t6, t6, a7
	sub t6, t6, a7
	addi t6, t6, 2
	and t5, t0, a7
	add a4, a4, t5
	srli t0, t0, 1
	and t5, t3, a7
	add t1, t1, t5
	add t1, t1, t1
	and t5, t4, a7
	add t2, t2, t5
	add t2, t2, t2
	andi t5, t0, 1
	addi a5, zero, 0
	sub a5, a5, t5
	srli a7, t6, 63
	addi a7, a7, -1
	and a7, a7, a5
	xor t5, a4, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t0, t0, t5
	xor t5, t1, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t3, t3, t5
	xor t5, t2, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t4, t4, t5
	xor t6, t6, a7
	sub t6, t6, a7
	addi t6, t6, 2
	and t5, t0, a7
	add a4, a4, t5
	srli t0, t0, 1
	and t5, t3, a7
	add t1, t1, t5
	add t1, t1, t1
	and t5, t4, a7
	add t2, t2, t5
	add t2, t2, t2
	andi t5, t0, 1
	addi a5, zero, 0
	sub a5, a5, t5
	srli a7, t6, 63
	addi a7, a7, -1
	and a7, a7, a5
	xor t5, a4, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t0, t0, t5
	xor t5, t1, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t3, t3, t5
	xor t5, t2, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t4, t4, t5
	xor t6, t6, a7
	sub t6, t6, a7
	addi t6, t6, 2
	and t5, t0, a7
	add a4, a4, t5
	srli t0, t0, 1
	and t5, t3, a7
	add t1, t1, t5
	add t1, t1, t1
	and t5, t4, a7
	add t2, t2, t5
	add t2, t2, t2
	andi t5, t0, 1
	addi a5, zero, 0
	sub a5, a5, t5
	srli a7, t6, 63
	addi a7, a7, -1
	and a7, a7, a5
	xor t5, a4, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t0, t0, t5
	xor t5, t1, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t3, t3, t5
	xor t5, t2, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t4, t4, t5
	xor t6, t6, a7
	sub t6, t6, a7
	addi t6, t6, 2
	and t5, t0, a7
	add a4, a4, t5
	srli t0, t0, 1
	and t5, t3, a7
	add t1, t1, t5
	add t1, t1, t1
	and t5, t4, a7
	add t2, t2, t5
	add t2, t2, t2
	andi t5, t0, 1
	addi a5, zero, 0
	sub a5, a5, t5
	srli a7, t6, 63
	addi a7, a7, -1
	and a7, a7, a5
	xor t5, a4, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t0, t0, t5
	xor t5, t1, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t3, t3, t5
	xor t5, t2, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t4, t4, t5
	xor t6, t6, a7
	sub t6, t6, a7
	addi t6, t6, 2
	and t5, t0, a7
	add a4, a4, t5
	srli t0, t0, 1
	and t5, t3, a7
	add t1, t1, t5
	add t1, t1, t1
	and t5, t4, a7
	add t2, t2, t5
	add t2, t2, t2
	andi t5, t0, 1
	addi a5, zero, 0
	sub a5, a5, t5
	srli a7, t6, 63
	addi a7, a7, -1
	and a7, a7, a5
	xor t5, a4, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t0, t0, t5
	xor t5, t1, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t3, t3, t5
	xor t5, t2, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t4, t4, t5
	xor t6, t6, a7
	sub t6, t6, a7
	addi t6, t6, 2
	and t5, t0, a7
	add a4, a4, t5
	srli t0, t0, 1
	and t5, t3, a7
	add t1, t1, t5
	add t1, t1, t1
	and t5, t4, a7
	add t2, t2, t5
	add t2, t2, t2
	andi t5, t0, 1
	addi a5, zero, 0
	sub a5, a5, t5
	srli a7, t6, 63
	addi a7, a7, -1
	and a7, a7, a5
	xor t5, a4, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t0, t0, t5
	xor t5, t1, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t3, t3, t5
	xor t5, t2, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t4, t4, t5
	xor t6, t6, a7
	sub t6, t6, a7
	addi t6, t6, 2
	and t5, t0, a7
	add a4, a4, t5
	srli t0, t0, 1
	and t5, t3, a7
	add t1, t1, t5
	add t1, t1, t1
	and t5, t4, a7
	add t2, t2, t5
	add t2, t2, t2
	andi t5, t0, 1
	addi a5, zero, 0
	sub a5, a5, t5
	srli a7, t6, 63
	addi a7, a7, -1
	and a7, a7, a5
	xor t5, a4, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t0, t0, t5
	xor t5, t1, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t3, t3, t5
	xor t5, t2, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t4, t4, t5
	xor t6, t6, a7
	sub t6, t6, a7
	addi t6, t6, 2
	and t5, t0, a7
	add a4, a4, t5
	srli t0, t0, 1
	and t5, t3, a7
	add t1, t1, t5
	add t1, t1, t1
	and t5, t4, a7
	add t2, t2, t5
	add t2, t2, t2
	andi t5, t0, 1
	addi a5, zero, 0
	sub a5, a5, t5
	srli a7, t6, 63
	addi a7, a7, -1
	and a7, a7, a5
	xor t5, a4, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t0, t0, t5
	xor t5, t1, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t3, t3, t5
	xor t5, t2, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t4, t4, t5
	xor t6, t6, a7
	sub t6, t6, a7
	addi t6, t6, 2
	and t5, t0, a7
	add a4, a4, t5
	srli t0, t0, 1
	and t5, t3, a7
	add t1, t1, t5
	add t1, t1, t1
	and t5, t4, a7
	add t2, t2, t5
	add t2, t2, t2
	andi t5, t0, 1
	addi a5, zero, 0
	sub a5, a5, t5
	srli a7, t6, 63
	addi a7, a7, -1
	and a7, a7, a5
	xor t5, a4, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t0, t0, t5
	xor t5, t1, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t3, t3, t5
	xor t5, t2, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t4, t4, t5
	xor t6, t6, a7
	sub t6, t6, a7
	addi t6, t6, 2
	and t5, t0, a7
	add a4, a4, t5
	srli t0, t0, 1
	and t5, t3, a7
	add t1, t1, t5
	add t1, t1, t1
	and t5, t4, a7
	add t2, t2, t5
	add t2, t2, t2
	andi t5, t0, 1
	addi a5, zero, 0
	sub a5, a5, t5
	srli a7, t6, 63
	addi a7, a7, -1
	and a7, a7, a5
	xor t5, a4, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t0, t0, t5
	xor t5, t1, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t3, t3, t5
	xor t5, t2, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t4, t4, t5
	xor t6, t6, a7
	sub t6, t6, a7
	addi t6, t6, 2
	and t5, t0, a7
	add a4, a4, t5
	srli t0, t0, 1
	and t5, t3, a7
	add t1, t1, t5
	add t1, t1, t1
	and t5, t4, a7
	add t2, t2, t5
	add t2, t2, t2
	andi t5, t0, 1
	addi a5, zero, 0
	sub a5, a5, t5
	srli a7, t6, 63
	addi a7, a7, -1
	and a7, a7, a5
	xor t5, a4, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t0, t0, t5
	xor t5, t1, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t3, t3, t5
	xor t5, t2, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t4, t4, t5
	xor t6, t6, a7
	sub t6, t6, a7
	addi t6, t6, 2
	and t5, t0, a7
	add a4, a4, t5
	srli t0, t0, 1
	and t5, t3, a7
	add t1, t1, t5
	add t1, t1, t1
	and t5, t4, a7
	add t2, t2, t5
	add t2, t2, t2
	andi t5, t0, 1
	addi a5, zero, 0
	sub a5, a5, t5
	srli a7, t6, 63
	addi a7, a7, -1
	and a7, a7, a5
	xor t5, a4, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t0, t0, t5
	xor t5, t1, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t3, t3, t5
	xor t5, t2, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t4, t4, t5
	xor t6, t6, a7
	sub t6, t6, a7
	addi t6, t6, 2
	and t5, t0, a7
	add a4, a4, t5
	srli t0, t0, 1
	and t5, t3, a7
	add t1, t1, t5
	add t1, t1, t1
	and t5, t4, a7
	add t2, t2, t5
	add t2, t2, t2
	andi t5, t0, 1
	addi a5, zero, 0
	sub a5, a5, t5
	srli a7, t6, 63
	addi a7, a7, -1
	and a7, a7, a5
	xor t5, a4, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t0, t0, t5
	xor t5, t1, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t3, t3, t5
	xor t5, t2, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t4, t4, t5
	xor t6, t6, a7
	sub t6, t6, a7
	addi t6, t6, 2
	and t5, t0, a7
	add a4, a4, t5
	srli t0, t0, 1
	and t5, t3, a7
	add t1, t1, t5
	add t1, t1, t1
	and t5, t4, a7
	add t2, t2, t5
	add t2, t2, t2
	andi t5, t0, 1
	addi a5, zero, 0
	sub a5, a5, t5
	srli a7, t6, 63
	addi a7, a7, -1
	and a7, a7, a5
	xor t5, a4, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t0, t0, t5
	xor t5, t1, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t3, t3, t5
	xor t5, t2, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t4, t4, t5
	xor t6, t6, a7
	sub t6, t6, a7
	addi t6, t6, 2
	and t5, t0, a7
	add a4, a4, t5
	srli t0, t0, 1
	and t5, t3, a7
	add t1, t1, t5
	add t1, t1, t1
	and t5, t4, a7
	add t2, t2, t5
	add t2, t2, t2
	andi t5, t0, 1
	addi a5, zero, 0
	sub a5, a5, t5
	srli a7, t6, 63
	addi a7, a7, -1
	and a7, a7, a5
	xor t5, a4, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t0, t0, t5
	xor t5, t1, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t3, t3, t5
	xor t5, t2, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t4, t4, t5
	xor t6, t6, a7
	sub t6, t6, a7
	addi t6, t6, 2
	and t5, t0, a7
	add a4, a4, t5
	srli t0, t0, 1
	and t5, t3, a7
	add t1, t1, t5
	add t1, t1, t1
	and t5, t4, a7
	add t2, t2, t5
	add t2, t2, t2
	andi t5, t0, 1
	addi a5, zero, 0
	sub a5, a5, t5
	srli a7, t6, 63
	addi a7, a7, -1
	and a7, a7, a5
	xor t5, a4, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t0, t0, t5
	xor t5, t1, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t3, t3, t5
	xor t5, t2, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t4, t4, t5
	xor t6, t6, a7
	sub t6, t6, a7
	addi t6, t6, 2
	and t5, t0, a7
	add a4, a4, t5
	srli t0, t0, 1
	and t5, t3, a7
	add t1, t1, t5
	add t1, t1, t1
	and t5, t4, a7
	add t2, t2, t5
	add t2, t2, t2
	andi t5, t0, 1
	addi a5, zero, 0
	sub a5, a5, t5
	srli a7, t6, 63
	addi a7, a7, -1
	and a7, a7, a5
	xor t5, a4, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t0, t0, t5
	xor t5, t1, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t3, t3, t5
	xor t5, t2, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t4, t4, t5
	xor t6, t6, a7
	sub t6, t6, a7
	addi t6, t6, 2
	and t5, t0, a7
	add a4, a4, t5
	srli t0, t0, 1
	and t5, t3, a7
	add t1, t1, t5
	add t1, t1, t1
	and t5, t4, a7
	add t2, t2, t5
	add t2, t2, t2
	andi t5, t0, 1
	addi a5, zero, 0
	sub a5, a5, t5
	srli a7, t6, 63
	addi a7, a7, -1
	and a7, a7, a5
	xor t5, a4, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t0, t0, t5
	xor t5, t1, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t3, t3, t5
	xor t5, t2, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t4, t4, t5
	xor t6, t6, a7
	sub t6, t6, a7
	addi t6, t6, 2
	and t5, t0, a7
	add a4, a4, t5
	srli t0, t0, 1
	and t5, t3, a7
	add t1, t1, t5
	add t1, t1, t1
	and t5, t4, a7
	add t2, t2, t5
	add t2, t2, t2
	andi t5, t0, 1
	addi a5, zero, 0
	sub a5, a5, t5
	srli a7, t6, 63
	addi a7, a7, -1
	and a7, a7, a5
	xor t5, a4, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t0, t0, t5
	xor t5, t1, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t3, t3, t5
	xor t5, t2, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t4, t4, t5
	xor t6, t6, a7
	sub t6, t6, a7
	addi t6, t6, 2
	and t5, t0, a7
	add a4, a4, t5
	srli t0, t0, 1
	and t5, t3, a7
	add t1, t1, t5
	add t1, t1, t1
	and t5, t4, a7
	add t2, t2, t5
	add t2, t2, t2
	andi t5, t0, 1
	addi a5, zero, 0
	sub a5, a5, t5
	srli a7, t6, 63
	addi a7, a7, -1
	and a7, a7, a5
	xor t5, a4, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t0, t0, t5
	xor t5, t1, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t3, t3, t5
	xor t5, t2, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t4, t4, t5
	xor t6, t6, a7
	sub t6, t6, a7
	addi t6, t6, 2
	and t5, t0, a7
	add a4, a4, t5
	srli t0, t0, 1
	and t5, t3, a7
	add t1, t1, t5
	add t1, t1, t1
	and t5, t4, a7
	add t2, t2, t5
	add t2, t2, t2
	andi t5, t0, 1
	addi a5, zero, 0
	sub a5, a5, t5
	srli a7, t6, 63
	addi a7, a7, -1
	and a7, a7, a5
	xor t5, a4, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t0, t0, t5
	xor t5, t1, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t3, t3, t5
	xor t5, t2, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t4, t4, t5
	xor t6, t6, a7
	sub t6, t6, a7
	addi t6, t6, 2
	and t5, t0, a7
	add a4, a4, t5
	srli t0, t0, 1
	and t5, t3, a7
	add t1, t1, t5
	add t1, t1, t1
	and t5, t4, a7
	add t2, t2, t5
	add t2, t2, t2
	andi t5, t0, 1
	addi a5, zero, 0
	sub a5, a5, t5
	srli a7, t6, 63
	addi a7, a7, -1
	and a7, a7, a5
	xor t5, a4, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t0, t0, t5
	xor t5, t1, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t3, t3, t5
	xor t5, t2, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t4, t4, t5
	xor t6, t6, a7
	sub t6, t6, a7
	addi t6, t6, 2
	and t5, t0, a7
	add a4, a4, t5
	srli t0, t0, 1
	and t5, t3, a7
	add t1, t1, t5
	add t1, t1, t1
	and t5, t4, a7
	add t2, t2, t5
	add t2, t2, t2
	andi t5, t0, 1
	addi a5, zero, 0
	sub a5, a5, t5
	srli a7, t6, 63
	addi a7, a7, -1
	and a7, a7, a5
	xor t5, a4, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t0, t0, t5
	xor t5, t1, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t3, t3, t5
	xor t5, t2, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t4, t4, t5
	xor t6, t6, a7
	sub t6, t6, a7
	addi t6, t6, 2
	and t5, t0, a7
	add a4, a4, t5
	srli t0, t0, 1
	and t5, t3, a7
	add t1, t1, t5
	add t1, t1, t1
	and t5, t4, a7
	add t2, t2, t5
	add t2, t2, t2
	andi t5, t0, 1
	addi a5, zero, 0
	sub a5, a5, t5
	srli a7, t6, 63
	addi a7, a7, -1
	and a7, a7, a5
	xor t5, a4, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t0, t0, t5
	xor t5, t1, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t3, t3, t5
	xor t5, t2, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t4, t4, t5
	xor t6, t6, a7
	sub t6, t6, a7
	addi t6, t6, 2
	and t5, t0, a7
	add a4, a4, t5
	srli t0, t0, 1
	and t5, t3, a7
	add t1, t1, t5
	add t1, t1, t1
	and t5, t4, a7
	add t2, t2, t5
	add t2, t2, t2
	andi t5, t0, 1
	addi a5, zero, 0
	sub a5, a5, t5
	srli a7, t6, 63
	addi a7, a7, -1
	and a7, a7, a5
	xor t5, a4, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t0, t0, t5
	xor t5, t1, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t3, t3, t5
	xor t5, t2, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t4, t4, t5
	xor t6, t6, a7
	sub t6, t6, a7
	addi t6, t6, 2
	and t5, t0, a7
	add a4, a4, t5
	srli t0, t0, 1
	and t5, t3, a7
	add t1, t1, t5
	add t1, t1, t1
	and t5, t4, a7
	add t2, t2, t5
	add t2, t2, t2
	andi t5, t0, 1
	addi a5, zero, 0
	sub a5, a5, t5
	srli a7, t6, 63
	addi a7, a7, -1
	and a7, a7, a5
	xor t5, a4, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t0, t0, t5
	xor t5, t1, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t3, t3, t5
	xor t5, t2, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t4, t4, t5
	xor t6, t6, a7
	sub t6, t6, a7
	addi t6, t6, 2
	and t5, t0, a7
	add a4, a4, t5
	srli t0, t0, 1
	and t5, t3, a7
	add t1, t1, t5
	add t1, t1, t1
	and t5, t4, a7
	add t2, t2, t5
	add t2, t2, t2
	andi t5, t0, 1
	addi a5, zero, 0
	sub a5, a5, t5
	srli a7, t6, 63
	addi a7, a7, -1
	and a7, a7, a5
	xor t5, a4, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t0, t0, t5
	xor t5, t1, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t3, t3, t5
	xor t5, t2, a7
	sub t5, t5, a7
	and t5, t5, a5
	add t4, t4, t5
	xor t6, t6, a7
	sub t6, t6, a7
	addi t6, t6, 2
	and t5, t0, a7
	add a4, a4, t5
	srli t0, t0, 1
	and t5, t3, a7
	add t1, t1, t5
	add t1, t1, t1
	and t5, t4, a7
	add t2, t2, t5
	add t2, t2, t2
	addi a4, zero, 9
	mul a4, a4, s10
	add a4, a4, s11
	addi a4, a4, 256
	sd t6, 0(a4)
	sd t1, 8(a4)
	sd t2, 16(a4)
	sd t3, 24(a4)
	sd t4, 32(a4)
	addi t0, zero, 11
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 4
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 5
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi a5, zero, 9
	mul a5, a5, s10
	add a5, a5, s11
	addi a5, a5, 256
	ld a5, 8(a5)
	addi a7, zero, 9
	mul a7, a7, s10
	add a7, a7, s11
	addi a7, a7, 256
	ld a7, 16(a7)
	addi t3, s8, 0
	addi t4, zero, 0
241:
	lwu t5, 0(t1)
	mul t5, a5, t5
	lwu t6, 0(t2)
	mul t6, a7, t6
	add t5, t5, t6
	add t5, t5, t4
	sw t5, 0(t0)
	srai t4, t5, 32
	addi t0, t0, 4
	addi t1, t1, 4
	addi t2, t2, 4
	addi t3, t3, -1
	bnez t3, 241b
	lwu t5, 0(t1)
	addiw t5, t5, 0
	mul t5, a5, t5
	lwu t6, 0(t2)
	addiw t6, t6, 0
	mul t6, a7, t6
	add t5, t5, t6
	add t5, t5, t4
	sw t5, 0(t0)
	srai t4, t5, 32
	sw t4, 4(t0)
	addi t0, zero, 12
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 4
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 5
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi a5, zero, 9
	mul a5, a5, s10
	add a5, a5, s11
	addi a5, a5, 256
	ld a5, 24(a5)
	addi a7, zero, 9
	mul a7, a7, s10
	add a7, a7, s11
	addi a7, a7, 256
	ld a7, 32(a7)
	addi t3, s8, 0
	addi t4, zero, 0
242:
	lwu t5, 0(t1)
	mul t5, a5, t5
	lwu t6, 0(t2)
	mul t6, a7, t6
	add t5, t5, t6
	add t5, t5, t4
	sw t5, 0(t0)
	srai t4, t5, 32
	addi t0, t0, 4
	addi t1, t1, 4
	addi t2, t2, 4
	addi t3, t3, -1
	bnez t3, 242b
	lwu t5, 0(t1)
	addiw t5, t5, 0
	mul t5, a5, t5
	lwu t6, 0(t2)
	addiw t6, t6, 0
	mul t6, a7, t6
	add t5, t5, t6
	add t5, t5, t4
	sw t5, 0(t0)
	srai t4, t5, 32
	sw t4, 4(t0)
	addi t0, zero, 4
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 11
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s8, 1
243:
	lwu t5, 0(t1)
	lwu t6, 4(t1)
	srli t5, t5, 30
	slli t6, t6, 2
	add t5, t5, t6
	sw t5, 0(t0)
	addi t0, t0, 4
	addi t1, t1, 4
	addi t3, t3, -1
	bnez t3, 243b
	addi t0, zero, 5
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 12
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s8, 1
244:
	lwu t5, 0(t1)
	lwu t6, 4(t1)
	srli t5, t5, 30
	slli t6, t6, 2
	add t5, t5, t6
	sw t5, 0(t0)
	addi t0, t0, 4
	addi t1, t1, 4
	addi t3, t3, -1
	bnez t3, 244b
	addi s7, s7, -1
	bnez s7, 240b
	addi t0, zero, 1
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	add t3, s9, s9
	addi t3, t3, 2
	addi t5, zero, 0
245:
	sw t5, 0(t0)
	addi t0, t0, 4
	addi t3, t3, -1
	bnez t3, 245b
	addi t0, zero, 11
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 1
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 4
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s8, 1
	addi t4, zero, 0
246:
	lwu t5, 0(t1)
	lwu t6, 0(t2)
	sub t5, t5, t6
	sub t5, t5, t4
	sw t5, 0(t0)
	srli t4, t5, 63
	addi t0, t0, 4
	addi t1, t1, 4
	addi t2, t2, 4
	addi t3, t3, -1
	bnez t3, 246b
	addi t1, zero, 4
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	slli t3, s8, 2
	add t1, t1, t3
	lwu t4, 0(t1)
	srli t4, t4, 31
	addi t5, zero, 0
	sub t4, t5, t4
	addi t0, zero, 1
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 4
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 11
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s8, 1
247:
	lwu t5, 0(t1)
	lwu t6, 0(t2)
	xor t6, t6, t5
	and t6, t6, t4
	xor t6, t6, t5
	sw t6, 0(t0)
	addi t0, t0, 4
	addi t1, t1, 4
	addi t2, t2, 4
	addi t3, t3, -1
	bnez t3, 247b
	addi t1, zero, 8
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 41
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t4, zero, 0
	addi t3, s9, 0
248:
	ld t5, 0(t1)
	ld t6, 0(t2)
	xor t5, t5, t6
	or t4, t4, t5
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 248b
	addi t5, zero, 0
	sltu t5, t5, t4
	xori t5, t5, 1
	sd t5, 96(s11)
	addi t0, zero, 3
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 1
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 41
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	ld t4, 96(s11)
	addi t5, zero, 0
	sub t4, t5, t4
	addi t3, s9, 0
249:
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
	bnez t3, 249b
	addi t0, zero, 34
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 3
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
250:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 250b
	addi t0, zero, 28
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 40
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
251:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 251b
	slli s9, s9, 1
	addi s9, s9, 2
	slli s10, s10, 1
	addi a2, zero, 17
	mul a2, a2, s10
	add a2, a2, s11
	addi a2, a2, 256
	addi a3, zero, 12
	mul a3, a3, s10
	add a3, a3, s11
	addi a3, a3, 256
	addi s8, s9, 0
252:
	ld a6, 0(a2)
	addi t0, a3, 0
	addi t1, zero, 11
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s8, 0
	addi t4, zero, 0
253:
	ld t5, 0(t1)
	mul t6, a6, t5
	mulhu t5, a6, t5
	ld a4, 0(t0)
	add t6, t6, a4
	sltu a4, t6, a4
	add t5, t5, a4
	add t6, t6, t4
	sltu a4, t6, t4
	add t5, t5, a4
	sd t6, 0(t0)
	addi t4, t5, 0
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 253b
	addi a2, a2, 8
	addi a3, a3, 8
	addi s8, s8, -1
	bnez s8, 252b
	addi s8, s9, -2
	srli s8, s8, 1
	addi t0, zero, 13
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t3, s9, 1
	addi t5, zero, 0
254:
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t3, t3, -1
	bnez t3, 254b
	slli s7, s9, 6
	addi a4, zero, -1
255:
	addi t2, zero, 12
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t5, s7, -1
	srli t5, t5, 6
	slli t5, t5, 3
	add t2, t2, t5
	ld t5, 0(t2)
	srli t3, t5, 63
	addi t0, zero, 13
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 14
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	andi t4, a4, 1
	addi t2, s8, 1
	andi t2, t2, 3
	beqz t2, 256f
258:
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
	bnez t2, 258b
	j 257f
256:
257:
	addi t2, s8, 1
	srli t2, t2, 2
	beqz t2, 259f
261:
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
	bnez t2, 261b
	j 260f
259:
260:
	srli t5, t6, 63
	addi a4, t5, -1
	andi a5, a4, 1
	addi t2, zero, 12
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
	bnez s7, 255b
	addi t0, zero, 13
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 14
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	xori a4, a4, -1
	addi t4, zero, 0
	addi t3, s8, 1
262:
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
	bnez t3, 262b
	addi t0, zero, 16
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 12
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 14
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
263:
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
	bnez t3, 263b
	sd t4, 200(s11)
	addi s9, s9, -2
	srli s9, s9, 1
	srli s10, s10, 1
	addi t0, zero, 51
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 42
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 41
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
264:
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
	bnez t3, 264b
	addi t0, zero, 52
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 24
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 51
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
265:
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
	bnez t3, 265b
	addi t0, zero, 53
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 40
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 26
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
266:
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
	bnez t3, 266b
	addi t0, zero, 54
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t3, s9, 1
	addi t5, zero, 0
267:
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t3, t3, -1
	bnez t3, 267b
	slli s7, s9, 6
	addi a4, zero, -1
268:
	addi t2, zero, 53
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t5, s7, -1
	srli t5, t5, 6
	slli t5, t5, 3
	add t2, t2, t5
	ld t5, 0(t2)
	srli t3, t5, 63
	addi t0, zero, 54
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 52
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	andi t4, a4, 1
	addi t2, s9, 1
	andi t2, t2, 3
	beqz t2, 269f
271:
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
	bnez t2, 271b
	j 270f
269:
270:
	addi t2, s9, 1
	srli t2, t2, 2
	beqz t2, 272f
274:
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
	bnez t2, 274b
	j 273f
272:
273:
	srli t5, t6, 63
	addi a4, t5, -1
	andi a5, a4, 1
	addi t2, zero, 53
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
	bnez s7, 268b
	addi t0, zero, 54
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 52
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	xori a4, a4, -1
	addi t4, zero, 0
	addi t3, s9, 1
275:
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
	bnez t3, 275b
	addi t1, zero, 54
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 42
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t4, zero, 0
	addi t3, s9, 0
276:
	ld t5, 0(t1)
	ld t6, 0(t2)
	xor t5, t5, t6
	or t4, t4, t5
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 276b
	addi t5, zero, 0
	sltu t5, t5, t4
	xori t5, t5, 1
	sd t5, 208(s11)
	addi t0, zero, 53
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 53
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 51
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
277:
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
	bnez t3, 277b
	addi t0, zero, 36
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 53
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
278:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 278b
	slli s9, s9, 1
	addi s9, s9, 2
	slli s10, s10, 1
	addi a2, zero, 18
	mul a2, a2, s10
	add a2, a2, s11
	addi a2, a2, 256
	addi a3, zero, 19
	mul a3, a3, s10
	add a3, a3, s11
	addi a3, a3, 256
	addi s8, s9, 0
279:
	ld a6, 0(a2)
	addi t0, a3, 0
	addi t1, zero, 18
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s8, 0
	addi t4, zero, 0
280:
	ld t5, 0(t1)
	mul t6, a6, t5
	mulhu t5, a6, t5
	ld a4, 0(t0)
	add t6, t6, a4
	sltu a4, t6, a4
	add t5, t5, a4
	add t6, t6, t4
	sltu a4, t6, t4
	add t5, t5, a4
	sd t6, 0(t0)
	addi t4, t5, 0
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 280b
	addi a2, a2, 8
	addi a3, a3, 8
	addi s8, s8, -1
	bnez s8, 279b
	addi t4, zero, 0
	addi t0, zero, 14
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t3, s9, 0
281:
	ld t5, 0(t0)
	slli t6, t5, 1
	or t6, t6, t4
	sd t6, 0(t0)
	srli t4, t5, 63
	addi t0, t0, 8
	addi t3, t3, -1
	bnez t3, 281b
	addi t4, zero, 0
	addi t0, zero, 14
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t3, s9, 0
282:
	ld t5, 0(t0)
	slli t6, t5, 1
	or t6, t6, t4
	sd t6, 0(t0)
	srli t4, t5, 63
	addi t0, t0, 8
	addi t3, t3, -1
	bnez t3, 282b
	addi t0, zero, 13
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 19
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 14
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
283:
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
	bnez t3, 283b
	sd t4, 216(s11)
	addi t0, zero, 16
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 13
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 10
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
284:
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
	bnez t3, 284b
	sd t4, 224(s11)
	addi s9, s9, -2
	srli s9, s9, 1
	srli s10, s10, 1
	slli s7, s9, 6
	addi s7, s7, 64
285:
	slli s9, s9, 1
	addi s9, s9, 2
	slli s10, s10, 1
	addi t4, zero, 0
	addi t0, zero, 13
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t3, s9, 0
286:
	ld t5, 0(t0)
	slli t6, t5, 2
	or t6, t6, t4
	srli t4, t5, 62
	sd t6, 0(t0)
	addi t0, t0, 8
	addi t3, t3, -1
	bnez t3, 286b
	addi s9, s9, -2
	srli s9, s9, 1
	srli s10, s10, 1
	addi t0, zero, 56
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t3, s9, 0
287:
	ld t5, 0(t0)
	slli t6, t5, 2
	or t6, t6, t4
	srli t4, t5, 62
	sd t6, 0(t0)
	addi t0, t0, 8
	addi t3, t3, -1
	bnez t3, 287b
	addi t0, zero, 59
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 56
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 57
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t4, zero, 0
	addi a4, zero, 1
	addi t3, s9, 0
288:
	ld t6, 0(t2)
	slli t5, t6, 2
	or t5, t5, a4
	srli a4, t6, 62
	ld t6, 0(t1)
	sltu a5, t6, t5
	sub t6, t6, t5
	sltu t5, t6, t4
	sub t6, t6, t4
	or t4, a5, t5
	sd t6, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 288b
	sd t4, 232(s11)
	addi t0, zero, 56
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 59
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 56
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	ld t4, 232(s11)
	addi t5, zero, 0
	sub t4, t5, t4
	addi t3, s9, 0
289:
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
	bnez t3, 289b
	ld t5, 232(s11)
	xori t4, t5, 1
	addi t0, zero, 57
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t3, s9, 0
290:
	ld t5, 0(t0)
	slli t6, t5, 1
	or t6, t6, t4
	sd t6, 0(t0)
	srli t4, t5, 63
	addi t0, t0, 8
	addi t3, t3, -1
	bnez t3, 290b
	addi s7, s7, -1
	bnez s7, 285b
	addi t1, zero, 56
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 42
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t4, zero, 0
	addi t3, s9, 0
291:
	ld t5, 0(t1)
	ld t6, 0(t2)
	xor t5, t5, t6
	or t4, t4, t5
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 291b
	addi t5, zero, 0
	sltu t5, t5, t4
	xori t5, t5, 1
	sd t5, 240(s11)
	addi t0, zero, 62
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 42
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 57
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
292:
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
	bnez t3, 292b
	addi t0, zero, 60
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 53
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 62
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
293:
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
	bnez t3, 293b
	addi t4, zero, 0
	addi t0, zero, 60
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	slli t5, s9, 3
	add t5, t0, t5
	sd t4, 0(t5)
	addi t3, s9, 0
294:
	ld t5, 0(t0)
	ld t6, 8(t0)
	slli t6, t6, 63
	srli t5, t5, 1
	or t5, t5, t6
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t3, t3, -1
	bnez t3, 294b
	addi t0, zero, 61
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 53
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 57
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
295:
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
	bnez t3, 295b
	addi t4, zero, 0
	addi t0, zero, 61
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	slli t5, s9, 3
	add t5, t0, t5
	sd t4, 0(t5)
	addi t3, s9, 0
296:
	ld t5, 0(t0)
	ld t6, 8(t0)
	slli t6, t6, 63
	srli t5, t5, 1
	or t5, t5, t6
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t3, t3, -1
	bnez t3, 296b
	ld t5, 152(s11)
	xori t5, t5, 1
	ld t6, 160(s11)
	xori t6, t6, 1
	and t5, t5, t6
	ld t6, 200(s11)
	and t5, t5, t6
	ld t6, 208(s11)
	and t5, t5, t6
	ld t6, 216(s11)
	xori t6, t6, 1
	and t5, t5, t6
	ld t6, 224(s11)
	xori t6, t6, 1
	and t5, t5, t6
	ld t6, 240(s11)
	and t5, t5, t6
	sd t5, 248(s11)
	ld t4, 248(s11)
	addi t5, zero, 0
	sub t4, t5, t4
	addi t1, zero, 60
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	add t1, t1, s2
	addi t1, t1, -1
	addi t0, s3, 0
	addi t3, s2, 0
297:
	lbu t5, 0(t1)
	and t5, t5, t4
	sb t5, 0(t0)
	addi t0, t0, 1
	addi t1, t1, -1
	addi t3, t3, -1
	bnez t3, 297b
	addi t1, zero, 61
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	add t1, t1, s2
	addi t1, t1, -1
	addi t0, s4, 0
	addi t3, s2, 0
298:
	lbu t5, 0(t1)
	and t5, t5, t4
	sb t5, 0(t0)
	addi t0, t0, 1
	addi t1, t1, -1
	addi t3, t3, -1
	bnez t3, 298b
	ld a0, 248(s11)
25:
	ld s0, 0(s11)
	ld s1, 8(s11)
	ld s2, 16(s11)
	ld s3, 24(s11)
	ld s4, 32(s11)
	ld s5, 40(s11)
	ld s6, 48(s11)
	ld s7, 56(s11)
	ld s8, 64(s11)
	ld s9, 72(s11)
	ld s10, 80(s11)
	ld s11, 88(s11)
	ret
	.option pop
