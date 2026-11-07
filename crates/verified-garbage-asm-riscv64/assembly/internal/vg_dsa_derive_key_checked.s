// The functions of `src/internal/vg_dsa_derive_key_checked.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_dsa_derive_key_checked:
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
	addi t3, a2, 0
	addi t5, t0, 0
	addi s0, zero, 0
229:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 229b
	addi s0, zero, 1
	sd s0, 0(a2)
	slli a1, t0, 7
230:
	addi t3, a5, 0
	addi t4, a2, 0
	addi t5, t0, 0
	addi s4, zero, 0
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
	addi a1, a1, -1
	bnez a1, 230b
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
234:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 234b
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
235:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 235b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
236:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 236b
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
237:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 237b
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
238:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 238b
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
239:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 239b
240:
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
	beqz t5, 241f
243:
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
	bnez t5, 243b
	j 242f
241:
242:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 244f
246:
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
	bnez t5, 246b
	j 245f
244:
245:
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
	bnez a1, 240b
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
247:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 247b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
248:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 248b
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
249:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 249b
250:
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
	beqz t5, 251f
253:
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
	bnez t5, 253b
	j 252f
251:
252:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 254f
256:
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
	bnez t5, 256b
	j 255f
254:
255:
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
	bnez a1, 250b
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
257:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 257b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
258:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 258b
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
259:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 259b
	addi s7, zero, 2
260:
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
	addi a0, a7, 0
261:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 261b
262:
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
	beqz t5, 263f
265:
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
	bnez t5, 265b
	j 264f
263:
264:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 266f
268:
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
	bnez t5, 268b
	j 267f
266:
267:
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
	bnez a1, 262b
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
269:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 269b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
270:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 270b
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
	addi s7, s7, 1
	addi t2, s7, -16
	bnez t2, 260b
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
273:
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
274:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 274b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
275:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 276f
278:
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
	bnez t5, 278b
	j 277f
276:
277:
	beqz t6, 279f
281:
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
	bnez t6, 281b
	j 280f
279:
280:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 275b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
282:
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
	bnez t5, 282b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
283:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 284f
286:
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
	bnez t5, 286b
	j 285f
284:
285:
	beqz t6, 287f
289:
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
	bnez t6, 289b
	j 288f
287:
288:
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
	bnez t2, 283b
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
292:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 292b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
293:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 294f
296:
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
	bnez t5, 296b
	j 295f
294:
295:
	beqz t6, 297f
299:
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
	bnez t6, 299b
	j 298f
297:
298:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 293b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2100:
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
	bnez t5, 2100b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2101:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2102f
2104:
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
	bnez t5, 2104b
	j 2103f
2102:
2103:
	beqz t6, 2105f
2107:
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
	bnez t6, 2107b
	j 2106f
2105:
2106:
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
	bnez t2, 2101b
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
2110:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2110b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2111:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2112f
2114:
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
	bnez t5, 2114b
	j 2113f
2112:
2113:
	beqz t6, 2115f
2117:
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
	bnez t6, 2117b
	j 2116f
2115:
2116:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2111b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2118:
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
	bnez t5, 2118b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2119:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2120f
2122:
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
	bnez t5, 2122b
	j 2121f
2120:
2121:
	beqz t6, 2123f
2125:
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
	bnez t6, 2125b
	j 2124f
2123:
2124:
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
	bnez t2, 2119b
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
2126:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2126b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2127:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2127b
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
2128:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2128b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2129:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2130f
2132:
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
	bnez t5, 2132b
	j 2131f
2130:
2131:
	beqz t6, 2133f
2135:
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
	bnez t6, 2135b
	j 2134f
2133:
2134:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2129b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2136:
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
	bnez t5, 2136b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2137:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2138f
2140:
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
	bnez t5, 2140b
	j 2139f
2138:
2139:
	beqz t6, 2141f
2143:
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
	bnez t6, 2143b
	j 2142f
2141:
2142:
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
	bnez t2, 2137b
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
	slli t3, t0, 3
	sub a5, a5, t3
	srli a1, s7, 60
	slli t3, s5, 3
	add t3, a7, t3
	slli s4, s5, 2
	add s4, s4, s5
	add s4, a7, s4
	addi t5, t0, 0
2146:
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
	bnez t5, 2146b
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
2147:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2147b
2148:
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
	beqz t5, 2149f
2151:
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
	bnez t5, 2151b
	j 2150f
2149:
2150:
	addi t5, t0, -1
	srli t5, t5, 2
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
	bnez t5, 2154b
	j 2153f
2152:
2153:
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
	bnez a1, 2148b
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
2155:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2155b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2156:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2156b
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
2157:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2157b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2158:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2159f
2161:
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
	bnez t5, 2161b
	j 2160f
2159:
2160:
	beqz t6, 2162f
2164:
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
	bnez t6, 2164b
	j 2163f
2162:
2163:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2158b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2165:
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
	bnez t5, 2165b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2166:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2167f
2169:
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
	bnez t5, 2169b
	j 2168f
2167:
2168:
	beqz t6, 2170f
2172:
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
	bnez t6, 2172b
	j 2171f
2170:
2171:
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
	bnez t2, 2166b
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
2173:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2173b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2174:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2174b
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
2175:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2175b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2176:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2177f
2179:
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
	bnez t5, 2179b
	j 2178f
2177:
2178:
	beqz t6, 2180f
2182:
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
	bnez t6, 2182b
	j 2181f
2180:
2181:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2176b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2183:
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
	bnez t5, 2183b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2184:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2185f
2187:
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
	bnez t5, 2187b
	j 2186f
2185:
2186:
	beqz t6, 2188f
2190:
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
	bnez t6, 2190b
	j 2189f
2188:
2189:
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
	bnez t2, 2184b
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
2191:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2191b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2192:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2192b
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
2193:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2193b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2194:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2195f
2197:
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
	bnez t5, 2197b
	j 2196f
2195:
2196:
	beqz t6, 2198f
2200:
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
	bnez t6, 2200b
	j 2199f
2198:
2199:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2194b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2201:
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
	bnez t5, 2201b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2202:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2203f
2205:
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
	bnez t5, 2205b
	j 2204f
2203:
2204:
	beqz t6, 2206f
2208:
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
	bnez t6, 2208b
	j 2207f
2206:
2207:
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
	bnez t2, 2202b
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
2209:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2209b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2210:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2210b
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
2211:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2211b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2212:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2213f
2215:
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
	bnez t5, 2215b
	j 2214f
2213:
2214:
	beqz t6, 2216f
2218:
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
	bnez t6, 2218b
	j 2217f
2216:
2217:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2212b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2219:
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
	bnez t5, 2219b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2220:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2221f
2223:
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
	bnez t5, 2223b
	j 2222f
2221:
2222:
	beqz t6, 2224f
2226:
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
	bnez t6, 2226b
	j 2225f
2224:
2225:
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
	bnez t2, 2220b
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
2227:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2227b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2228:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2228b
	slli t3, t0, 3
	sub a5, a5, t3
	srli a1, s7, 60
	slli t3, s5, 3
	add t3, a7, t3
	slli s4, s5, 2
	add s4, s4, s5
	add s4, a7, s4
	addi t5, t0, 0
2229:
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
	bnez t5, 2229b
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
	slli s7, s7, 4
	addi s10, s10, -1
	bnez s10, 273b
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
2250:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2250b
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
2251:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2251b
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
2252:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2252b
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
2253:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2253b
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
2254:
	lbu s0, 0(t3)
	sb s0, 0(t4)
	addi t4, t4, 1
	addi t3, t3, -1
	addi t5, t5, -1
	bnez t5, 2254b
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
2255:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2255b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
2256:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 2256b
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
2257:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2257b
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
2259:
	ld s0, 0(t3)
	ld s1, 0(t4)
	xor s0, s0, s1
	or t2, t2, s0
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2259b
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
2260:
	lbu s0, 0(t3)
	and s0, s0, a4
	sb s0, 0(t4)
	addi t3, t3, 1
	addi t4, t4, 1
	addi t5, t5, -1
	bnez t5, 2260b
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
2261:
	lbu s0, 0(t3)
	and s0, s0, a4
	sb s0, 0(t4)
	addi t3, t3, 1
	addi t4, t4, 1
	addi t5, t5, -1
	bnez t5, 2261b
	addi t3, ra, 0
	ld t5, 16(s6)
	slli t5, t5, 32
	srli t5, t5, 48
2262:
	lbu s0, 0(t3)
	and s0, s0, a4
	sb s0, 0(t4)
	addi t3, t3, 1
	addi t4, t4, 1
	addi t5, t5, -1
	bnez t5, 2262b
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
