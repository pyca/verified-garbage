// The functions of `src/internal/vg_ffdh_parameter_candidate.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ffdh_parameter_candidate:
	.option push
	.option arch, +m, +c
	addi t3, sp, 0
	ld t3, 0(t3)
	slli t4, t3, 3
	add t4, a7, t4
	addi t4, t4, -104
	sd s0, 0(t4)
	sd s1, 8(t4)
	sd s2, 16(t4)
	sd s3, 24(t4)
	sd s4, 32(t4)
	sd s5, 40(t4)
	sd s6, 48(t4)
	sd s7, 56(t4)
	sd s8, 64(t4)
	sd s9, 72(t4)
	sd s10, 80(t4)
	sd s11, 88(t4)
	sd ra, 96(t4)
	addi s6, a7, 0
	sd t3, 0(s6)
	sd a0, 16(s6)
	sd a1, 24(s6)
	sd a1, 152(s6)
	sd a2, 32(s6)
	sd a3, 40(s6)
	slli a4, a4, 32
	srli a4, a4, 32
	sd a4, 128(s6)
	sd a5, 136(s6)
	sd a6, 144(s6)
	ld t3, 16(s6)
	ld t4, 24(s6)
	addi t5, zero, 0
20:
	sb t5, 0(t3)
	addi t3, t3, 1
	addi t4, t4, -1
	bnez t4, 20b
	ld t3, 144(s6)
	ld t4, 24(s6)
	sltu t5, t3, t4
	xori t5, t5, 1
	beqz t5, 21f
	ld t3, 40(s6)
	sd t3, 248(s6)
	addi t4, t3, 7
	srli t4, t4, 3
	sd t4, 216(s6)
	addi t4, t3, 63
	srli t4, t4, 6
	sd t4, 48(s6)
	addi t0, t4, 0
	slli s5, t4, 3
	addi s5, s5, 16
	sd s5, 224(s6)
	addi a7, s6, 256
	addi t5, a7, 0
	sd t5, 64(s6)
	add t5, t5, s5
	sd t5, 72(s6)
	add t5, t5, s5
	sd t5, 80(s6)
	add t5, t5, s5
	sd t5, 88(s6)
	add t5, t5, s5
	sd t5, 96(s6)
	add t5, t5, s5
	sd t5, 104(s6)
	add t5, t5, s5
	sd t5, 112(s6)
	add t5, t5, s5
	sd t5, 120(s6)
	add t5, t5, s5
	addi t5, t3, -2048
	addi t5, t5, -1
	srli t5, t5, 63
	slli t5, t5, 6
	addi t6, zero, 128
	sub t5, t6, t5
	sd t5, 168(s6)
	ld t3, 248(s6)
	ld t4, 48(s6)
	slli t4, t4, 6
	sub t3, t3, t4
	addi t3, t3, 64
	addi t5, zero, 0
23:
	add t5, t5, t5
	addi t5, t5, 1
	addi t3, t3, -1
	bnez t3, 23b
	sd t5, 192(s6)
	ld s7, 136(s6)
	ld s8, 24(s6)
	addi t3, a7, 0
	addi t5, t0, 0
	addi s0, zero, 0
24:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 24b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
25:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 25b
	slli t3, t0, 3
	add t3, a7, t3
	addi t3, t3, -8
	ld t4, 192(s6)
	ld t5, 0(t3)
	and t5, t5, t4
	srli t4, t4, 1
	addi t4, t4, 1
	or t5, t5, t4
	sd t5, 0(t3)
	ld t5, 0(a7)
	ori t5, t5, 1
	sd t5, 0(a7)
	ld t3, 128(s6)
	addi t3, t3, -2
	beqz t3, 26f
	addi s1, zero, 10
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
28:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
29:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 29b
	addi t4, t4, -1
	bnez t4, 28b
	ori s0, s0, 4
	xori s0, s0, 7
	sd s0, 200(s6)
	j 27f
26:
	addi s1, zero, 24
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
210:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
211:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 211b
	addi t4, t4, -1
	bnez t4, 210b
	xori s0, s0, 11
	sd s0, 200(s6)
27:
	ld t3, 200(s6)
	beqz t3, 212f
	ld t3, 32(s6)
	ld t4, 152(s6)
	sd t4, 0(t3)
	addi a0, zero, 2
	j 213f
212:
	ld a4, 200(s6)
	addi s1, zero, 3
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
214:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
215:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 215b
	addi t4, t4, -1
	bnez t4, 214b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 5
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
216:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
217:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 217b
	addi t4, t4, -1
	bnez t4, 216b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 7
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
218:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
219:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 219b
	addi t4, t4, -1
	bnez t4, 218b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 11
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
220:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
221:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 221b
	addi t4, t4, -1
	bnez t4, 220b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 13
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
222:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
223:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 223b
	addi t4, t4, -1
	bnez t4, 222b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 17
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
224:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
225:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 225b
	addi t4, t4, -1
	bnez t4, 224b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 19
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
226:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
227:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 227b
	addi t4, t4, -1
	bnez t4, 226b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 23
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
228:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
229:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 229b
	addi t4, t4, -1
	bnez t4, 228b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 29
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
230:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
231:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 231b
	addi t4, t4, -1
	bnez t4, 230b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 31
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
232:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
233:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 233b
	addi t4, t4, -1
	bnez t4, 232b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 37
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
234:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
235:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 235b
	addi t4, t4, -1
	bnez t4, 234b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 41
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
236:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
237:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 237b
	addi t4, t4, -1
	bnez t4, 236b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 43
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
238:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
239:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 239b
	addi t4, t4, -1
	bnez t4, 238b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 47
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
240:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
241:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 241b
	addi t4, t4, -1
	bnez t4, 240b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 53
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
242:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
243:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 243b
	addi t4, t4, -1
	bnez t4, 242b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 59
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
244:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
245:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 245b
	addi t4, t4, -1
	bnez t4, 244b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 61
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
246:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
247:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 247b
	addi t4, t4, -1
	bnez t4, 246b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 67
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
248:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
249:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 249b
	addi t4, t4, -1
	bnez t4, 248b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 71
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
250:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
251:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 251b
	addi t4, t4, -1
	bnez t4, 250b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 73
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
252:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
253:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 253b
	addi t4, t4, -1
	bnez t4, 252b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 79
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
254:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
255:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 255b
	addi t4, t4, -1
	bnez t4, 254b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 83
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
256:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
257:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 257b
	addi t4, t4, -1
	bnez t4, 256b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 89
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
258:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
259:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 259b
	addi t4, t4, -1
	bnez t4, 258b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 97
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
260:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
261:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 261b
	addi t4, t4, -1
	bnez t4, 260b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 101
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
262:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
263:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 263b
	addi t4, t4, -1
	bnez t4, 262b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 103
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
264:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
265:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 265b
	addi t4, t4, -1
	bnez t4, 264b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 107
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
266:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
267:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 267b
	addi t4, t4, -1
	bnez t4, 266b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 109
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
268:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
269:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 269b
	addi t4, t4, -1
	bnez t4, 268b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 113
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
270:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
271:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 271b
	addi t4, t4, -1
	bnez t4, 270b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 127
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
272:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
273:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 273b
	addi t4, t4, -1
	bnez t4, 272b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 131
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
274:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
275:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 275b
	addi t4, t4, -1
	bnez t4, 274b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 137
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
276:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
277:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 277b
	addi t4, t4, -1
	bnez t4, 276b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 139
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
278:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
279:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 279b
	addi t4, t4, -1
	bnez t4, 278b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 149
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
280:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
281:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 281b
	addi t4, t4, -1
	bnez t4, 280b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 151
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
282:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
283:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 283b
	addi t4, t4, -1
	bnez t4, 282b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 157
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
284:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
285:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 285b
	addi t4, t4, -1
	bnez t4, 284b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 163
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
286:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
287:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 287b
	addi t4, t4, -1
	bnez t4, 286b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 167
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
288:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
289:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 289b
	addi t4, t4, -1
	bnez t4, 288b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 173
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
290:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
291:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 291b
	addi t4, t4, -1
	bnez t4, 290b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 179
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
292:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
293:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 293b
	addi t4, t4, -1
	bnez t4, 292b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 181
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
294:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
295:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 295b
	addi t4, t4, -1
	bnez t4, 294b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 191
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
296:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
297:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 297b
	addi t4, t4, -1
	bnez t4, 296b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 193
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
298:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
299:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 299b
	addi t4, t4, -1
	bnez t4, 298b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 197
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2100:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2101:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2101b
	addi t4, t4, -1
	bnez t4, 2100b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 199
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2102:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2103:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2103b
	addi t4, t4, -1
	bnez t4, 2102b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 211
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2104:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2105:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2105b
	addi t4, t4, -1
	bnez t4, 2104b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 223
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2106:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2107:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2107b
	addi t4, t4, -1
	bnez t4, 2106b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 227
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2108:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2109:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2109b
	addi t4, t4, -1
	bnez t4, 2108b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 229
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2110:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2111:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2111b
	addi t4, t4, -1
	bnez t4, 2110b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 233
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2112:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2113:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2113b
	addi t4, t4, -1
	bnez t4, 2112b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 239
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2114:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2115:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2115b
	addi t4, t4, -1
	bnez t4, 2114b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 241
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2116:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2117:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2117b
	addi t4, t4, -1
	bnez t4, 2116b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 251
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2118:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2119:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2119b
	addi t4, t4, -1
	bnez t4, 2118b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	sd a4, 200(s6)
	addi t3, a7, 0
	addi t4, t0, -1
2120:
	ld t5, 0(t3)
	ld t6, 8(t3)
	srli t5, t5, 1
	slli t6, t6, 63
	or t5, t5, t6
	sd t5, 0(t3)
	addi t3, t3, 8
	addi t4, t4, -1
	bnez t4, 2120b
	ld t5, 0(t3)
	srli t5, t5, 1
	sd t5, 0(t3)
	ld t4, 200(s6)
	ld t5, 0(a7)
	andi t5, t5, 1
	xori t5, t5, 1
	or t4, t4, t5
	sd t4, 200(s6)
	ld a4, 200(s6)
	addi s1, zero, 3
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2121:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2122:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2122b
	addi t4, t4, -1
	bnez t4, 2121b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 5
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2123:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2124:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2124b
	addi t4, t4, -1
	bnez t4, 2123b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 7
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2125:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2126:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2126b
	addi t4, t4, -1
	bnez t4, 2125b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 11
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2127:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2128:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2128b
	addi t4, t4, -1
	bnez t4, 2127b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 13
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2129:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2130:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2130b
	addi t4, t4, -1
	bnez t4, 2129b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 17
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2131:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2132:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2132b
	addi t4, t4, -1
	bnez t4, 2131b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 19
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2133:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2134:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2134b
	addi t4, t4, -1
	bnez t4, 2133b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 23
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2135:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2136:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2136b
	addi t4, t4, -1
	bnez t4, 2135b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 29
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2137:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2138:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2138b
	addi t4, t4, -1
	bnez t4, 2137b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 31
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2139:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2140:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2140b
	addi t4, t4, -1
	bnez t4, 2139b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 37
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2141:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2142:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2142b
	addi t4, t4, -1
	bnez t4, 2141b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 41
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2143:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2144:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2144b
	addi t4, t4, -1
	bnez t4, 2143b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 43
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2145:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2146:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2146b
	addi t4, t4, -1
	bnez t4, 2145b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 47
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2147:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2148:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2148b
	addi t4, t4, -1
	bnez t4, 2147b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 53
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2149:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2150:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2150b
	addi t4, t4, -1
	bnez t4, 2149b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 59
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2151:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2152:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2152b
	addi t4, t4, -1
	bnez t4, 2151b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 61
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2153:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2154:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2154b
	addi t4, t4, -1
	bnez t4, 2153b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 67
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2155:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2156:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2156b
	addi t4, t4, -1
	bnez t4, 2155b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 71
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2157:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2158:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2158b
	addi t4, t4, -1
	bnez t4, 2157b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 73
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2159:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2160:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2160b
	addi t4, t4, -1
	bnez t4, 2159b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 79
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2161:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2162:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2162b
	addi t4, t4, -1
	bnez t4, 2161b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 83
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2163:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2164:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2164b
	addi t4, t4, -1
	bnez t4, 2163b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 89
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2165:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2166:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2166b
	addi t4, t4, -1
	bnez t4, 2165b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 97
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2167:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2168:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2168b
	addi t4, t4, -1
	bnez t4, 2167b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 101
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2169:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2170:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2170b
	addi t4, t4, -1
	bnez t4, 2169b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 103
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2171:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2172:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2172b
	addi t4, t4, -1
	bnez t4, 2171b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 107
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2173:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2174:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2174b
	addi t4, t4, -1
	bnez t4, 2173b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 109
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2175:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2176:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2176b
	addi t4, t4, -1
	bnez t4, 2175b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 113
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2177:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2178:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2178b
	addi t4, t4, -1
	bnez t4, 2177b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 127
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2179:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2180:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2180b
	addi t4, t4, -1
	bnez t4, 2179b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 131
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2181:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2182:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2182b
	addi t4, t4, -1
	bnez t4, 2181b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 137
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2183:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2184:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2184b
	addi t4, t4, -1
	bnez t4, 2183b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 139
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2185:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2186:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2186b
	addi t4, t4, -1
	bnez t4, 2185b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 149
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2187:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2188:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2188b
	addi t4, t4, -1
	bnez t4, 2187b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 151
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2189:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2190:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2190b
	addi t4, t4, -1
	bnez t4, 2189b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 157
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2191:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2192:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2192b
	addi t4, t4, -1
	bnez t4, 2191b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 163
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2193:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2194:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2194b
	addi t4, t4, -1
	bnez t4, 2193b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 167
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2195:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2196:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2196b
	addi t4, t4, -1
	bnez t4, 2195b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 173
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2197:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2198:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2198b
	addi t4, t4, -1
	bnez t4, 2197b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 179
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2199:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2200:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2200b
	addi t4, t4, -1
	bnez t4, 2199b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 181
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2201:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2202:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2202b
	addi t4, t4, -1
	bnez t4, 2201b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 191
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2203:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2204:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2204b
	addi t4, t4, -1
	bnez t4, 2203b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 193
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2205:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2206:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2206b
	addi t4, t4, -1
	bnez t4, 2205b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 197
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2207:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2208:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2208b
	addi t4, t4, -1
	bnez t4, 2207b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 199
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2209:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2210:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2210b
	addi t4, t4, -1
	bnez t4, 2209b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 211
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2211:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2212:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2212b
	addi t4, t4, -1
	bnez t4, 2211b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 223
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2213:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2214:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2214b
	addi t4, t4, -1
	bnez t4, 2213b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 227
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2215:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2216:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2216b
	addi t4, t4, -1
	bnez t4, 2215b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 229
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2217:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2218:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2218b
	addi t4, t4, -1
	bnez t4, 2217b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 233
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2219:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2220:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2220b
	addi t4, t4, -1
	bnez t4, 2219b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 239
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2221:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2222:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2222b
	addi t4, t4, -1
	bnez t4, 2221b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 241
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2223:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2224:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2224b
	addi t4, t4, -1
	bnez t4, 2223b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	addi s1, zero, 251
	slli t3, t0, 3
	add t3, a7, t3
	addi t4, t0, 0
	addi s0, zero, 0
2225:
	addi t3, t3, -8
	ld s2, 0(t3)
	addi t5, zero, 64
2226:
	srli s3, s2, 63
	slli s2, s2, 1
	add s0, s0, s0
	add s0, s0, s3
	sub s3, s0, s1
	sltu s4, s0, s1
	addi s4, s4, -1
	xor s3, s3, s0
	and s3, s3, s4
	xor s0, s0, s3
	addi t5, t5, -1
	bnez t5, 2226b
	addi t4, t4, -1
	bnez t4, 2225b
	addi t2, zero, 1
	sltu t2, s0, t2
	or a4, a4, t2
	sd a4, 200(s6)
	ld t3, 200(s6)
	beqz t3, 2227f
	ld t3, 32(s6)
	ld t4, 152(s6)
	sd t4, 0(t3)
	addi a0, zero, 2
	j 2228f
2227:
	ld t3, 40(s6)
	addi t3, t3, -1
	sd t3, 248(s6)
	addi t4, t3, 7
	srli t4, t4, 3
	sd t4, 216(s6)
	addi t4, t3, 63
	srli t4, t4, 6
	sd t4, 48(s6)
	addi t0, t4, 0
	slli s5, t4, 3
	addi s5, s5, 16
	sd s5, 224(s6)
	addi a7, s6, 256
	addi t5, a7, 0
	sd t5, 64(s6)
	add t5, t5, s5
	sd t5, 72(s6)
	add t5, t5, s5
	sd t5, 80(s6)
	add t5, t5, s5
	sd t5, 88(s6)
	add t5, t5, s5
	sd t5, 96(s6)
	add t5, t5, s5
	sd t5, 104(s6)
	add t5, t5, s5
	sd t5, 112(s6)
	add t5, t5, s5
	sd t5, 120(s6)
	add t5, t5, s5
	addi t5, t3, -2048
	addi t5, t5, -1
	srli t5, t5, 63
	slli t5, t5, 6
	addi t6, zero, 128
	sub t5, t6, t5
	sd t5, 168(s6)
	ld t3, 248(s6)
	ld t4, 48(s6)
	slli t4, t4, 6
	sub t3, t3, t4
	addi t3, t3, 64
	addi t5, zero, 0
2229:
	add t5, t5, t5
	addi t5, t5, 1
	addi t3, t3, -1
	bnez t3, 2229b
	sd t5, 192(s6)
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
2230:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2230b
	addi s0, zero, 1
	sd s0, 0(a2)
	slli a1, t0, 7
2231:
	addi t3, a5, 0
	addi t4, a2, 0
	addi t5, t0, 0
	addi s4, zero, 0
2232:
	ld s2, 0(t4)
	slli s3, s2, 1
	add s3, s3, s4
	srli s4, s2, 63
	sd s3, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2232b
	sd s4, 0(t3)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2233:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2233b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2234:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2234b
	addi a1, a1, -1
	bnez a1, 2231b
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
	sd t1, 56(s6)
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
2235:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2235b
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
2236:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2236b
2237:
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
	beqz t5, 2238f
2240:
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
	bnez t5, 2240b
	j 2239f
2238:
2239:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2241f
2243:
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
	bnez t5, 2243b
	j 2242f
2241:
2242:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	addi a1, a1, -1
	bnez a1, 2237b
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2244:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2244b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2245:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2245b
	addi a5, a7, 0
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
	add a6, a6, s5
	addi t2, a7, 0
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	addi a7, t2, 0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2246:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2246b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi a7, s6, 256
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
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2247:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2247b
	addi t3, a7, 0
	addi t5, t0, 0
	addi s0, zero, 0
	addi s1, zero, 1
2248:
	ld s2, 0(t3)
	xor s2, s2, s1
	addi s1, zero, 0
	addi t2, zero, 0
	sltu t2, t2, s0
	addi t2, t2, -1
	and s2, s2, t2
	or s0, s0, s2
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2248b
	addi t2, zero, 0
	sub t2, t2, s0
	and s0, s0, t2
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
	add t3, t3, s5
	add t3, t3, s5
	slli t2, t0, 3
	add t3, t3, t2
	sd s0, 0(t3)
	addi s3, zero, -1
	addi t3, a7, 0
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
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	ld s0, 0(t3)
	addi t3, t3, 8
	addi t5, t0, -1
2249:
	ld s1, 0(t3)
	slli s2, s1, 63
	srli s4, s0, 1
	or s4, s4, s2
	xor s4, s4, s0
	and s4, s4, s3
	xor s4, s4, s0
	sd s4, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi s0, s1, 0
	addi t5, t5, -1
	bnez t5, 2249b
	srli s4, s0, 1
	xor s4, s4, s0
	and s4, s4, s3
	xor s4, s4, s0
	sd s4, 0(t4)
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
	add t3, t3, s5
	add t3, t3, s5
	slli t2, t0, 3
	add t3, t3, t2
	ld t3, 0(t3)
	lui t4, 14
	addi t4, t4, -547
	slli t5, t4, 16
	or t4, t4, t5
	slli t5, t4, 32
	or t4, t4, t5
	and t3, t3, t4
	addi t2, zero, 0
	sltu s3, t2, t3
	sub s3, t2, s3
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
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	ld s0, 0(t3)
	addi t3, t3, 8
	addi t5, t0, -1
2250:
	ld s1, 0(t3)
	slli s2, s1, 63
	srli s4, s0, 1
	or s4, s4, s2
	xor s4, s4, s0
	and s4, s4, s3
	xor s4, s4, s0
	sd s4, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi s0, s1, 0
	addi t5, t5, -1
	bnez t5, 2250b
	srli s4, s0, 1
	xor s4, s4, s0
	and s4, s4, s3
	xor s4, s4, s0
	sd s4, 0(t4)
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
	add t3, t3, s5
	add t3, t3, s5
	slli t2, t0, 3
	add t3, t3, t2
	ld t3, 0(t3)
	lui t4, 10
	addi t4, t4, -1639
	slli t5, t4, 16
	or t4, t4, t5
	slli t5, t4, 32
	or t4, t4, t5
	and t3, t3, t4
	addi t2, zero, 0
	sltu s3, t2, t3
	sub s3, t2, s3
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
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	ld s0, 0(t3)
	addi t3, t3, 8
	addi t5, t0, -1
2251:
	ld s1, 0(t3)
	slli s2, s1, 63
	srli s4, s0, 1
	or s4, s4, s2
	xor s4, s4, s0
	and s4, s4, s3
	xor s4, s4, s0
	sd s4, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi s0, s1, 0
	addi t5, t5, -1
	bnez t5, 2251b
	srli s4, s0, 1
	xor s4, s4, s0
	and s4, s4, s3
	xor s4, s4, s0
	sd s4, 0(t4)
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
	add t3, t3, s5
	add t3, t3, s5
	slli t2, t0, 3
	add t3, t3, t2
	ld t3, 0(t3)
	lui t4, 1
	addi t4, t4, 273
	slli t5, t4, 16
	or t4, t4, t5
	slli t5, t4, 32
	or t4, t4, t5
	and t3, t3, t4
	addi t2, zero, 0
	sltu s3, t2, t3
	sub s3, t2, s3
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
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	ld s0, 0(t3)
	addi t3, t3, 8
	addi t5, t0, -1
2252:
	ld s1, 0(t3)
	slli s2, s1, 63
	srli s4, s0, 1
	or s4, s4, s2
	xor s4, s4, s0
	and s4, s4, s3
	xor s4, s4, s0
	sd s4, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi s0, s1, 0
	addi t5, t5, -1
	bnez t5, 2252b
	srli s4, s0, 1
	xor s4, s4, s0
	and s4, s4, s3
	xor s4, s4, s0
	sd s4, 0(t4)
	addi t2, zero, 0
	sd t2, 176(s6)
	addi t2, zero, 4
	sd t2, 160(s6)
2253:
	ld t2, 144(s6)
	ld t3, 152(s6)
	sub t2, t2, t3
	ld t3, 216(s6)
	sltu t4, t2, t3
	bnez t4, 2254f
	ld s7, 136(s6)
	ld t2, 152(s6)
	add s7, s7, t2
	ld s8, 216(s6)
	add t2, t2, s8
	sd t2, 152(s6)
	addi a7, a7, 0
	add a7, a7, s5
	add a7, a7, s5
	add a7, a7, s5
	add a7, a7, s5
	addi t3, a7, 0
	addi t5, t0, 0
	addi s0, zero, 0
2256:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2256b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
2257:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 2257b
	addi a7, s6, 256
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	slli t2, t0, 3
	add t3, t3, t2
	addi t3, t3, -8
	ld t4, 192(s6)
	ld t2, 0(t3)
	and t2, t2, t4
	sd t2, 0(t3)
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	ld a3, 0(t3)
	srli a3, a3, 1
	addi t3, t3, 8
	addi t5, t0, -1
2258:
	ld t2, 0(t3)
	or a3, a3, t2
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2258b
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t4, a7, 0
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	addi t5, t0, 0
2259:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2259b
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	ld t2, 0(t3)
	ori t2, t2, 1
	sd t2, 0(t3)
	slli t4, t0, 3
	add t3, t3, t4
	addi t2, zero, 0
	sd t2, 0(t3)
	addi a5, a7, 0
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
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2260:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2260b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	beqz a3, 2261f
	beqz s4, 2263f
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
2265:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2265b
2266:
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
	beqz t5, 2267f
2269:
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
	bnez t5, 2269b
	j 2268f
2267:
2268:
	addi t5, t0, -1
	srli t5, t5, 2
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
	bnez t5, 2272b
	j 2271f
2270:
2271:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	addi a1, a1, -1
	bnez a1, 2266b
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2273:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2273b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2274:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2274b
	addi a0, s6, 0
	ld a1, 0(s6)
	call {vg_miller_rabin_round}
	slli a0, a0, 32
	srli a0, a0, 32
	addi a7, s6, 256
	ld t0, 48(s6)
	ld t1, 56(s6)
	beqz a0, 2275f
	ld t2, 176(s6)
	ld t3, 168(s6)
	addi t2, t2, 1
	sd t2, 176(s6)
	sltu t3, t2, t3
	xori t3, t3, 1
	addi t4, zero, 3
	mul t3, t3, t4
	addi t4, zero, 4
	sub t3, t4, t3
	sd t3, 160(s6)
	j 2276f
2275:
	addi t2, zero, 2
	sd t2, 160(s6)
2276:
	j 2264f
2263:
2264:
	j 2262f
2261:
2262:
	j 2255f
2254:
	addi t2, zero, 0
	sd t2, 160(s6)
2255:
	ld t2, 160(s6)
	addi t2, t2, -4
	beqz t2, 2253b
	ld t3, 160(s6)
	addi t3, t3, -1
	beqz t3, 2277f
	ld t3, 160(s6)
	beqz t3, 2279f
	ld t3, 32(s6)
	ld t4, 152(s6)
	sd t4, 0(t3)
	addi a0, zero, 2
	j 2280f
2279:
	ld t3, 32(s6)
	addi t4, zero, 0
	sd t4, 0(t3)
	addi a0, zero, 0
2280:
	j 2278f
2277:
	ld t3, 40(s6)
	sd t3, 248(s6)
	addi t4, t3, 7
	srli t4, t4, 3
	sd t4, 216(s6)
	addi t4, t3, 63
	srli t4, t4, 6
	sd t4, 48(s6)
	addi t0, t4, 0
	slli s5, t4, 3
	addi s5, s5, 16
	sd s5, 224(s6)
	addi a7, s6, 256
	addi t5, a7, 0
	sd t5, 64(s6)
	add t5, t5, s5
	sd t5, 72(s6)
	add t5, t5, s5
	sd t5, 80(s6)
	add t5, t5, s5
	sd t5, 88(s6)
	add t5, t5, s5
	sd t5, 96(s6)
	add t5, t5, s5
	sd t5, 104(s6)
	add t5, t5, s5
	sd t5, 112(s6)
	add t5, t5, s5
	sd t5, 120(s6)
	add t5, t5, s5
	addi t5, t3, -2048
	addi t5, t5, -1
	srli t5, t5, 63
	slli t5, t5, 6
	addi t6, zero, 128
	sub t5, t6, t5
	sd t5, 168(s6)
	ld t3, 248(s6)
	ld t4, 48(s6)
	slli t4, t4, 6
	sub t3, t3, t4
	addi t3, t3, 64
	addi t5, zero, 0
2281:
	add t5, t5, t5
	addi t5, t5, 1
	addi t3, t3, -1
	bnez t3, 2281b
	sd t5, 192(s6)
	ld s7, 136(s6)
	ld s8, 24(s6)
	addi t3, a7, 0
	addi t5, t0, 0
	addi s0, zero, 0
2282:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2282b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
2283:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 2283b
	slli t3, t0, 3
	add t3, a7, t3
	addi t3, t3, -8
	ld t4, 192(s6)
	ld t5, 0(t3)
	and t5, t5, t4
	srli t4, t4, 1
	addi t4, t4, 1
	or t5, t5, t4
	sd t5, 0(t3)
	ld t5, 0(a7)
	ori t5, t5, 1
	sd t5, 0(a7)
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
2284:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2284b
	addi s0, zero, 1
	sd s0, 0(a2)
	slli a1, t0, 7
2285:
	addi t3, a5, 0
	addi t4, a2, 0
	addi t5, t0, 0
	addi s4, zero, 0
2286:
	ld s2, 0(t4)
	slli s3, s2, 1
	add s3, s3, s4
	srli s4, s2, 63
	sd s3, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2286b
	sd s4, 0(t3)
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
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2288:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2288b
	addi a1, a1, -1
	bnez a1, 2285b
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
	sd t1, 56(s6)
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
2289:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2289b
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
2290:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2290b
2291:
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
	beqz t5, 2292f
2294:
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
	bnez t5, 2294b
	j 2293f
2292:
2293:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2295f
2297:
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
	bnez t5, 2297b
	j 2296f
2295:
2296:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	addi a1, a1, -1
	bnez a1, 2291b
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2298:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2298b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2299:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2299b
	addi a5, a7, 0
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
	add a6, a6, s5
	addi t2, a7, 0
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	addi a7, t2, 0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2300:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2300b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi a7, s6, 256
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
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2301:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2301b
	addi t3, a7, 0
	addi t5, t0, 0
	addi s0, zero, 0
	addi s1, zero, 1
2302:
	ld s2, 0(t3)
	xor s2, s2, s1
	addi s1, zero, 0
	addi t2, zero, 0
	sltu t2, t2, s0
	addi t2, t2, -1
	and s2, s2, t2
	or s0, s0, s2
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2302b
	addi t2, zero, 0
	sub t2, t2, s0
	and s0, s0, t2
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
	add t3, t3, s5
	add t3, t3, s5
	slli t2, t0, 3
	add t3, t3, t2
	sd s0, 0(t3)
	addi s3, zero, -1
	addi t3, a7, 0
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
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	ld s0, 0(t3)
	addi t3, t3, 8
	addi t5, t0, -1
2303:
	ld s1, 0(t3)
	slli s2, s1, 63
	srli s4, s0, 1
	or s4, s4, s2
	xor s4, s4, s0
	and s4, s4, s3
	xor s4, s4, s0
	sd s4, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi s0, s1, 0
	addi t5, t5, -1
	bnez t5, 2303b
	srli s4, s0, 1
	xor s4, s4, s0
	and s4, s4, s3
	xor s4, s4, s0
	sd s4, 0(t4)
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
	add t3, t3, s5
	add t3, t3, s5
	slli t2, t0, 3
	add t3, t3, t2
	ld t3, 0(t3)
	lui t4, 14
	addi t4, t4, -547
	slli t5, t4, 16
	or t4, t4, t5
	slli t5, t4, 32
	or t4, t4, t5
	and t3, t3, t4
	addi t2, zero, 0
	sltu s3, t2, t3
	sub s3, t2, s3
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
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	ld s0, 0(t3)
	addi t3, t3, 8
	addi t5, t0, -1
2304:
	ld s1, 0(t3)
	slli s2, s1, 63
	srli s4, s0, 1
	or s4, s4, s2
	xor s4, s4, s0
	and s4, s4, s3
	xor s4, s4, s0
	sd s4, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi s0, s1, 0
	addi t5, t5, -1
	bnez t5, 2304b
	srli s4, s0, 1
	xor s4, s4, s0
	and s4, s4, s3
	xor s4, s4, s0
	sd s4, 0(t4)
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
	add t3, t3, s5
	add t3, t3, s5
	slli t2, t0, 3
	add t3, t3, t2
	ld t3, 0(t3)
	lui t4, 10
	addi t4, t4, -1639
	slli t5, t4, 16
	or t4, t4, t5
	slli t5, t4, 32
	or t4, t4, t5
	and t3, t3, t4
	addi t2, zero, 0
	sltu s3, t2, t3
	sub s3, t2, s3
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
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	ld s0, 0(t3)
	addi t3, t3, 8
	addi t5, t0, -1
2305:
	ld s1, 0(t3)
	slli s2, s1, 63
	srli s4, s0, 1
	or s4, s4, s2
	xor s4, s4, s0
	and s4, s4, s3
	xor s4, s4, s0
	sd s4, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi s0, s1, 0
	addi t5, t5, -1
	bnez t5, 2305b
	srli s4, s0, 1
	xor s4, s4, s0
	and s4, s4, s3
	xor s4, s4, s0
	sd s4, 0(t4)
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
	add t3, t3, s5
	add t3, t3, s5
	slli t2, t0, 3
	add t3, t3, t2
	ld t3, 0(t3)
	lui t4, 1
	addi t4, t4, 273
	slli t5, t4, 16
	or t4, t4, t5
	slli t5, t4, 32
	or t4, t4, t5
	and t3, t3, t4
	addi t2, zero, 0
	sltu s3, t2, t3
	sub s3, t2, s3
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
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	ld s0, 0(t3)
	addi t3, t3, 8
	addi t5, t0, -1
2306:
	ld s1, 0(t3)
	slli s2, s1, 63
	srli s4, s0, 1
	or s4, s4, s2
	xor s4, s4, s0
	and s4, s4, s3
	xor s4, s4, s0
	sd s4, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi s0, s1, 0
	addi t5, t5, -1
	bnez t5, 2306b
	srli s4, s0, 1
	xor s4, s4, s0
	and s4, s4, s3
	xor s4, s4, s0
	sd s4, 0(t4)
	addi t2, zero, 0
	sd t2, 176(s6)
	addi t2, zero, 4
	sd t2, 160(s6)
2307:
	ld t2, 144(s6)
	ld t3, 152(s6)
	sub t2, t2, t3
	ld t3, 216(s6)
	sltu t4, t2, t3
	bnez t4, 2308f
	ld s7, 136(s6)
	ld t2, 152(s6)
	add s7, s7, t2
	ld s8, 216(s6)
	add t2, t2, s8
	sd t2, 152(s6)
	addi a7, a7, 0
	add a7, a7, s5
	add a7, a7, s5
	add a7, a7, s5
	add a7, a7, s5
	addi t3, a7, 0
	addi t5, t0, 0
	addi s0, zero, 0
2310:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2310b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
2311:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 2311b
	addi a7, s6, 256
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	slli t2, t0, 3
	add t3, t3, t2
	addi t3, t3, -8
	ld t4, 192(s6)
	ld t2, 0(t3)
	and t2, t2, t4
	sd t2, 0(t3)
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	ld a3, 0(t3)
	srli a3, a3, 1
	addi t3, t3, 8
	addi t5, t0, -1
2312:
	ld t2, 0(t3)
	or a3, a3, t2
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2312b
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t4, a7, 0
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	addi t5, t0, 0
2313:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2313b
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	ld t2, 0(t3)
	ori t2, t2, 1
	sd t2, 0(t3)
	slli t4, t0, 3
	add t3, t3, t4
	addi t2, zero, 0
	sd t2, 0(t3)
	addi a5, a7, 0
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
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2314:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2314b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	beqz a3, 2315f
	beqz s4, 2317f
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
2319:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2319b
2320:
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
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2323b
	j 2322f
2321:
2322:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2324f
2326:
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
	bnez t5, 2326b
	j 2325f
2324:
2325:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	addi a1, a1, -1
	bnez a1, 2320b
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2327:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2327b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2328:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2328b
	addi a0, s6, 0
	ld a1, 0(s6)
	call {vg_miller_rabin_round}
	slli a0, a0, 32
	srli a0, a0, 32
	addi a7, s6, 256
	ld t0, 48(s6)
	ld t1, 56(s6)
	beqz a0, 2329f
	ld t2, 176(s6)
	ld t3, 168(s6)
	addi t2, t2, 1
	sd t2, 176(s6)
	sltu t3, t2, t3
	xori t3, t3, 1
	addi t4, zero, 3
	mul t3, t3, t4
	addi t4, zero, 4
	sub t3, t4, t3
	sd t3, 160(s6)
	j 2330f
2329:
	addi t2, zero, 2
	sd t2, 160(s6)
2330:
	j 2318f
2317:
2318:
	j 2316f
2315:
2316:
	j 2309f
2308:
	addi t2, zero, 0
	sd t2, 160(s6)
2309:
	ld t2, 160(s6)
	addi t2, t2, -4
	beqz t2, 2307b
	ld t3, 160(s6)
	beqz t3, 2331f
	addi t3, t3, -1
	beqz t3, 2333f
	ld t3, 32(s6)
	ld t4, 152(s6)
	sd t4, 0(t3)
	addi a0, zero, 2
	j 2334f
2333:
	ld t3, 16(s6)
	ld t4, 24(s6)
	add t5, a7, t4
	addi t5, t5, -1
2335:
	lbu t6, 0(t5)
	sb t6, 0(t3)
	addi t3, t3, 1
	addi t5, t5, -1
	addi t4, t4, -1
	bnez t4, 2335b
	ld t3, 32(s6)
	ld t4, 152(s6)
	sd t4, 0(t3)
	addi a0, zero, 1
2334:
	j 2332f
2331:
	ld t3, 32(s6)
	addi t4, zero, 0
	sd t4, 0(t3)
	addi a0, zero, 0
2332:
2278:
2228:
213:
	j 22f
21:
	ld t3, 32(s6)
	addi t4, zero, 0
	sd t4, 0(t3)
	addi a0, zero, 0
22:
	ld t3, 0(s6)
	slli t3, t3, 3
	add t3, s6, t3
	addi t3, t3, -104
	ld s0, 0(t3)
	ld s1, 8(t3)
	ld s2, 16(t3)
	ld s3, 24(t3)
	ld s4, 32(t3)
	ld s5, 40(t3)
	ld s6, 48(t3)
	ld s7, 56(t3)
	ld s8, 64(t3)
	ld s9, 72(t3)
	ld s10, 80(t3)
	ld s11, 88(t3)
	ld ra, 96(t3)
	ret
	.option pop
