// The functions of `src/internal/vg_dsa_sign_prevalidated.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_dsa_sign_prevalidated:
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
225:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 225b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
226:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 226b
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
227:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 227b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
228:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 228b
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
	beqz s0, 229f
	addi t3, zero, 4
	bltu t0, t3, 231f
	slli t3, t0, 3
	add t3, t3, a7
	addi t3, t3, -8
	ld s0, 0(t3)
	addi a1, zero, 0
	addi t5, zero, 63
233:
	srli s1, s0, 63
	xori s1, s1, 1
	sll s0, s0, s1
	add a1, a1, s1
	addi t5, t5, -1
	bnez t5, 233b
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
234:
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
	bnez t5, 234b
	sd s4, 16(a6)
	addi t3, a2, 0
	addi t5, t0, 0
	addi s0, zero, 0
235:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 235b
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
236:
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
237:
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
	bnez t5, 237b
	ld a0, 0(t3)
	sub s3, a0, s0
	sub s3, s3, s4
	srli a0, t6, 1
	slli a3, s3, 63
	or a0, a0, a3
	sd a0, 0(t3)
	addi a1, a1, -1
	bnez a1, 236b
	addi t3, a2, 0
	addi t4, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
	ld s2, 0(a2)
238:
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
	bnez t5, 238b
	srli s2, s2, 63
	sd s2, 0(t3)
	sltu s4, s2, s4
	xori s4, s4, 1
	sub s1, a4, s4
	addi t3, a2, 0
	addi t4, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
239:
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
	bnez t5, 239b
	ld s2, 0(t3)
	sub s2, s2, s4
	sd s2, 0(t3)
	j 232f
231:
	addi t3, a2, 0
	addi t5, t0, 0
	addi s0, zero, 0
240:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 240b
	slli t3, t0, 3
	add t3, t3, a2
	addi t3, t3, -8
	addi s0, zero, 1
	sd s0, 0(t3)
	addi a1, t0, 64
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
	addi s7, zero, 6
245:
	addi a3, a2, 0
	addi a4, a2, 0
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
	addi a0, a7, 0
246:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 246b
247:
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
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 250b
	j 249f
248:
249:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 251f
253:
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
	bnez t5, 253b
	j 252f
251:
252:
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
	bnez a1, 247b
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
	addi s7, s7, -1
	bnez s7, 245b
232:
	j 230f
229:
	addi t3, a2, 0
	addi t5, t0, 0
	addi s0, zero, 0
256:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 256b
	addi s0, zero, 1
	sd s0, 0(a2)
	slli a1, t0, 7
257:
	addi t3, a5, 0
	addi t4, a2, 0
	addi t5, t0, 0
	addi s4, zero, 0
258:
	ld s2, 0(t4)
	slli s3, s2, 1
	add s3, s3, s4
	srli s4, s2, 63
	sd s3, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 258b
	sd s4, 0(t3)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
259:
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
	bnez t5, 259b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
260:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 260b
	addi a1, a1, -1
	bnez a1, 257b
230:
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
261:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 261b
	addi a0, zero, -1
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
262:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 262b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
263:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 263b
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
264:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 264b
	ld s10, 16(s6)
	slli s10, s10, 32
	srli s10, s10, 48
	call {vg_bignum_pow_win}
	ld ra, 32(s6)
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
265:
	lbu s0, 0(t3)
	sb s0, 0(t4)
	addi t4, t4, 1
	addi t3, t3, -1
	addi t5, t5, -1
	bnez t5, 265b
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
266:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 266b
	addi a2, a7, 0
	add a2, a2, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
267:
	lbu s7, 0(s9)
	slli s7, s7, 56
	addi s9, s9, 1
	addi s8, zero, 8
268:
	srli s4, s7, 63
	slli s7, s7, 1
	addi t3, a5, 0
	addi t4, a2, 0
	addi t5, t0, 0
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
	addi s8, s8, -1
	bnez s8, 268b
	addi s10, s10, -1
	bnez s10, 267b
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
272:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
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
	addi t5, t0, 0
	addi s0, zero, 0
273:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 273b
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
274:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 274b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
275:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 275b
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
281:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 281b
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
282:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 282b
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
	beqz s0, 283f
	addi t3, zero, 4
	bltu t0, t3, 285f
	slli t3, t0, 3
	add t3, t3, a7
	addi t3, t3, -8
	ld s0, 0(t3)
	addi a1, zero, 0
	addi t5, zero, 63
287:
	srli s1, s0, 63
	xori s1, s1, 1
	sll s0, s0, s1
	add a1, a1, s1
	addi t5, t5, -1
	bnez t5, 287b
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
288:
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
	bnez t5, 288b
	sd s4, 16(a6)
	addi t3, a2, 0
	addi t5, t0, 0
	addi s0, zero, 0
289:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 289b
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
290:
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
291:
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
	bnez t5, 291b
	ld a0, 0(t3)
	sub s3, a0, s0
	sub s3, s3, s4
	srli a0, t6, 1
	slli a3, s3, 63
	or a0, a0, a3
	sd a0, 0(t3)
	addi a1, a1, -1
	bnez a1, 290b
	addi t3, a2, 0
	addi t4, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
	ld s2, 0(a2)
292:
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
	bnez t5, 292b
	srli s2, s2, 63
	sd s2, 0(t3)
	sltu s4, s2, s4
	xori s4, s4, 1
	sub s1, a4, s4
	addi t3, a2, 0
	addi t4, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
293:
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
	bnez t5, 293b
	ld s2, 0(t3)
	sub s2, s2, s4
	sd s2, 0(t3)
	j 286f
285:
	addi t3, a2, 0
	addi t5, t0, 0
	addi s0, zero, 0
294:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 294b
	slli t3, t0, 3
	add t3, t3, a2
	addi t3, t3, -8
	addi s0, zero, 1
	sd s0, 0(t3)
	addi a1, t0, 64
295:
	addi t3, a5, 0
	addi t4, a2, 0
	addi t5, t0, 0
	addi s4, zero, 0
296:
	ld s2, 0(t4)
	slli s3, s2, 1
	add s3, s3, s4
	srli s4, s2, 63
	sd s3, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 296b
	sd s4, 0(t3)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
297:
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
	bnez t5, 297b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
298:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 298b
	addi a1, a1, -1
	bnez a1, 295b
	addi s7, zero, 6
299:
	addi a3, a2, 0
	addi a4, a2, 0
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
	addi a0, a7, 0
2100:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2100b
2101:
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
	beqz t5, 2102f
2104:
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
	bnez t5, 2104b
	j 2103f
2102:
2103:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2105f
2107:
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
	bnez t5, 2107b
	j 2106f
2105:
2106:
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
	bnez a1, 2101b
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
2108:
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
	bnez t5, 2108b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2109:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2109b
	addi s7, s7, -1
	bnez s7, 299b
286:
	j 284f
283:
	addi t3, a2, 0
	addi t5, t0, 0
	addi s0, zero, 0
2110:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2110b
	addi s0, zero, 1
	sd s0, 0(a2)
	slli a1, t0, 7
2111:
	addi t3, a5, 0
	addi t4, a2, 0
	addi t5, t0, 0
	addi s4, zero, 0
2112:
	ld s2, 0(t4)
	slli s3, s2, 1
	add s3, s3, s4
	srli s4, s2, 63
	sd s3, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2112b
	sd s4, 0(t3)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2113:
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
	bnez t5, 2113b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2114:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2114b
	addi a1, a1, -1
	bnez a1, 2111b
284:
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
2115:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2115b
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
2116:
	ld s2, 0(t3)
	sltu s0, s2, s4
	sub s2, s2, s4
	addi s4, s0, 0
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2116b
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
2117:
	lbu s0, 0(t3)
	sb s0, 0(t4)
	addi t4, t4, 1
	addi t3, t3, -1
	addi t5, t5, -1
	bnez t5, 2117b
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
2118:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2118b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
2119:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 2119b
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
2120:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2120b
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
	beqz a0, 2121f
	j 2122f
2121:
	addi s8, t3, 0
2122:
	ld s7, 8(s6)
	beqz s8, 2123f
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
2125:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2125b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
2126:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 2126b
	sub a7, a7, s5
	sub a7, a7, s5
	sub a7, a7, s5
	sub a7, a7, s5
	sub a7, a7, s5
	sub a7, a7, s5
	j 2124f
2123:
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t5, t0, 0
	addi s0, zero, 0
2127:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2127b
2124:
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
2128:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2128b
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
2129:
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
	bnez t5, 2129b
	sd s4, 0(t3)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2130:
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
	bnez t5, 2130b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2131:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2131b
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
2132:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2132b
	addi a2, a7, 0
	add a2, a2, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
2133:
	lbu s7, 0(s9)
	slli s7, s7, 56
	addi s9, s9, 1
	addi s8, zero, 8
2134:
	srli s4, s7, 63
	slli s7, s7, 1
	addi t3, a5, 0
	addi t4, a2, 0
	addi t5, t0, 0
2135:
	ld s2, 0(t4)
	slli s3, s2, 1
	add s3, s3, s4
	srli s4, s2, 63
	sd s3, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2135b
	sd s4, 0(t3)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2136:
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
	bnez t5, 2136b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2137:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2137b
	addi s8, s8, -1
	bnez s8, 2134b
	addi s10, s10, -1
	bnez s10, 2133b
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t4, a7, 0
	add t4, t4, s5
	addi t5, t0, 2
2138:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2138b
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
2139:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2139b
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
	bnez t5, 2144b
	j 2143f
2142:
2143:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2145f
2147:
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
	bnez t5, 2154b
	j 2153f
2152:
2153:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2155f
2157:
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
2160:
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
	bnez t5, 2160b
	sd s4, 0(t3)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2161:
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
	bnez t5, 2161b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2162:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2162b
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
2163:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2163b
2164:
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
	beqz t5, 2165f
2167:
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
	bnez t5, 2167b
	j 2166f
2165:
2166:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2168f
2170:
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
	bnez t5, 2170b
	j 2169f
2168:
2169:
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
	bnez a1, 2164b
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
2171:
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
	bnez t5, 2171b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
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
	beqz t5, 2175f
2177:
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
	bnez t5, 2177b
	j 2176f
2175:
2176:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2178f
2180:
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
	slli s2, t0, 3
	sub a0, a0, s2
	addi a0, a0, 8
	addi a1, a1, -1
	bnez a1, 2174b
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
2183:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2183b
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
2184:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2184b
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
2185:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2185b
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
2186:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2186b
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
2187:
	lbu s0, 0(t3)
	sb s0, 0(t4)
	addi t4, t4, 1
	addi t3, t3, -1
	addi t5, t5, -1
	bnez t5, 2187b
	add s7, s7, s8
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s8
	addi t3, t3, -1
	addi t4, s7, 0
	addi t5, s8, 0
2188:
	lbu s0, 0(t3)
	sb s0, 0(t4)
	addi t4, t4, 1
	addi t3, t3, -1
	addi t5, t5, -1
	bnez t5, 2188b
	andi a0, a4, 1
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
