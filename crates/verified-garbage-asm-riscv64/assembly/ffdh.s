// The functions of `src/ffdh.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ffdh_parameter_generation_init:
	.option push
	.option arch, +m, +c
	slli a2, a2, 32
	srli a2, a2, 32
	addi t2, zero, 512
	sltu t0, a1, t2
	lui t2, 2
	sltu t1, t2, a1
	or t0, t0, t1
	addi t2, zero, 2
	sltu t1, a2, t2
	addi t2, zero, 3
	sltu t3, a2, t2
	sub t1, t3, t1
	addi t2, zero, 5
	sltu t3, a2, t2
	addi t2, zero, 6
	sltu t4, a2, t2
	sub t3, t4, t3
	or t1, t1, t3
	xori t1, t1, 1
	or t0, t0, t1
	beqz t0, 20f
	addi t2, zero, 0
	sd t2, 0(a0)
	sd t2, 8(a0)
	sd t2, 16(a0)
	sd t2, 24(a0)
	addi a0, zero, 0
	j 21f
20:
	mul t0, a1, a1
	slli t0, t0, 6
	addi t1, a1, 7
	srli t1, t1, 3
	slli t2, t1, 15
	add t2, t2, t1
	slli t3, t1, 9
	sd t0, 0(a0)
	sd t1, 8(a0)
	sd t2, 16(a0)
	sd t3, 24(a0)
	addi a0, zero, 1
21:
	ret
	.option pop

vg_ffdh_key_generation_init:
	.option push
	.option arch, +m, +c
	addi t2, zero, 64
	sltu t0, a1, t2
	addi t2, zero, 1024
	sltu t1, t2, a1
	or t0, t0, t1
	beqz t0, 20f
	addi t2, zero, 0
	sd t2, 0(a0)
	sd t2, 8(a0)
	sd t2, 16(a0)
	sd t2, 24(a0)
	addi a0, zero, 0
	j 21f
20:
	addi t2, zero, 128
	sd t2, 0(a0)
	sd t2, 8(a0)
	sd a1, 16(a0)
	sd a1, 24(a0)
	addi a0, zero, 1
21:
	ret
	.option pop

vg_ffdh_check_public:
	.option push
	.option arch, +m, +c
	addi t0, a5, 0
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
	sd a0, 0(s6)
	sd a1, 8(s6)
	sd a3, 16(s6)
	addi s7, a0, 0
	addi s8, a2, 0
	addi a1, a2, 0
	addi s10, a0, 0
	addi s11, a1, 0
	addi t0, a1, 7
	srli t0, t0, 3
	slli s5, t0, 3
	addi s5, s5, 16
	addi a7, s6, 256
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
	addi a0, zero, 0
	j 27f
26:
	ld a6, 16(s6)
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
28:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 28b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
29:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 29b
	add t3, a7, s5
	addi t3, t3, -16
	addi s0, zero, 0
	sd s0, 0(t3)
	addi a7, s6, 256
	addi s7, a1, 0
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t5, t0, 0
	addi s0, zero, 0
210:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 210b
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
211:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 211b
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
	add t3, t3, s5
	addi t4, a7, 0
	addi t5, t0, 0
212:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 212b
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	ld s0, 0(t3)
	xori s0, s0, 1
	sd s0, 0(t3)
	addi s9, zero, -1
	addi s4, zero, -1
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
	addi s1, zero, 0
213:
	ld s2, 0(t3)
	ld s3, 0(t4)
	xor s2, s2, s3
	or s1, s1, s2
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 213b
	addi s2, zero, 0
	sltu s1, s2, s1
	addi s1, s1, -1
	and s4, s4, s1
	xor s4, s4, s9
	and s9, s9, s4
	addi s4, zero, -1
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
	addi s1, zero, 0
214:
	ld s2, 0(t3)
	ld s3, 0(t4)
	xor s2, s2, s3
	or s1, s1, s2
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 214b
	addi s2, zero, 0
	sltu s1, s2, s1
	addi s1, s1, -1
	and s4, s4, s1
	xori s4, s4, -1
	and s9, s9, s4
	addi s4, zero, -1
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
	addi t5, t0, 0
	addi s1, zero, 0
215:
	ld s2, 0(t3)
	ld s3, 0(t4)
	xor s2, s2, s3
	or s1, s1, s2
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 215b
	addi s2, zero, 0
	sltu s1, s2, s1
	addi s1, s1, -1
	and s4, s4, s1
	xori s4, s4, -1
	and s9, s9, s4
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
216:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 216b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	and s9, s9, s4
	beqz s9, 217f
	ld t3, 8(s6)
	slli t2, s11, 1
	add t2, t2, s11
	sub t3, t3, t2
	beqz t3, 219f
	addi a0, zero, 1
	j 220f
219:
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
221:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 221b
	slli t3, t0, 3
	add t3, t3, a2
	addi t3, t3, -8
	addi s0, zero, 1
	sd s0, 0(t3)
	addi a1, t0, 64
222:
	addi t3, a5, 0
	addi t4, a2, 0
	addi t5, t0, 0
	addi s4, zero, 0
223:
	ld s2, 0(t4)
	slli s3, s2, 1
	add s3, s3, s4
	srli s4, s2, 63
	sd s3, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 223b
	sd s4, 0(t3)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
224:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 224b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
225:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 225b
	addi a1, a1, -1
	bnez a1, 222b
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
	addi a0, a7, 0
226:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 226b
227:
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
	beqz t5, 228f
230:
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
	bnez t5, 230b
	j 229f
228:
229:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 231f
233:
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
	bnez t5, 233b
	j 232f
231:
232:
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
	bnez a1, 227b
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
234:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 234b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
235:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 235b
	addi a3, a2, 0
	addi a4, a2, 0
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
	bnez t5, 250b
	j 249f
248:
249:
	addi t5, t0, -1
	srli t5, t5, 2
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
	addi a3, a2, 0
	addi a4, a2, 0
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
	addi a0, a7, 0
256:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 256b
257:
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
	beqz t5, 258f
260:
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
	bnez t5, 260b
	j 259f
258:
259:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 261f
263:
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
	bnez t5, 263b
	j 262f
261:
262:
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
	bnez a1, 257b
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
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
265:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 265b
	addi a3, a2, 0
	addi a4, a2, 0
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
	addi a0, a7, 0
266:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 266b
267:
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
	beqz t5, 268f
270:
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
	bnez t5, 270b
	j 269f
268:
269:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 271f
273:
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
	bnez t5, 273b
	j 272f
271:
272:
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
	bnez a1, 267b
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
274:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 274b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
275:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 275b
	addi a3, a2, 0
	addi a4, a2, 0
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
	addi a0, a7, 0
276:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 276b
277:
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
	beqz t5, 278f
280:
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
	bnez t5, 280b
	j 279f
278:
279:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 281f
283:
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
	bnez t5, 283b
	j 282f
281:
282:
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
	bnez a1, 277b
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
284:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 284b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
285:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 285b
	ld t3, 0(s6)
	add t3, t3, s11
	add t3, t3, s11
	addi a4, s11, 0
	addi t5, a4, 0
	addi t4, zero, 0
	addi s1, a4, -1
	addi s2, zero, 0
	addi s3, zero, 0
286:
	lbu t6, 0(t3)
	addi t2, zero, 0
	sub s4, t2, t6
	or s4, s4, t6
	srli s4, s4, 63
	sub s4, t2, s4
	or s4, s4, s3
	xor s4, s4, s3
	xor s0, s1, t4
	and s0, s0, s4
	xor s1, s1, s0
	xor s0, s2, t6
	and s0, s0, s4
	xor s2, s2, s0
	or s3, s3, s4
	addi t3, t3, 1
	addi t4, t4, 1
	addi t5, t5, -1
	bnez t5, 286b
	ld s9, 0(s6)
	add s9, s9, s11
	add s9, s9, s11
	add s9, s9, s1
	sub s10, s11, s1
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
287:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 287b
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
288:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 288b
289:
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
	beqz t5, 290f
292:
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
	bnez t5, 292b
	j 291f
290:
291:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 293f
295:
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
	bnez t5, 295b
	j 294f
293:
294:
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
	bnez a1, 289b
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
296:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 296b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
297:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 297b
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
298:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 298b
299:
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
	beqz t5, 2100f
2102:
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
	bnez t5, 2102b
	j 2101f
2100:
2101:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2103f
2105:
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
	bnez t5, 2105b
	j 2104f
2103:
2104:
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
	bnez a1, 299b
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
2106:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2106b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2107:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2107b
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
2108:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2108b
	addi s7, zero, 2
2109:
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
2120:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2120b
	addi s7, s7, 1
	addi t2, s7, -16
	bnez t2, 2109b
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
2121:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2121b
2122:
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
2123:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2123b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2124:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2125f
2127:
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
	bnez t5, 2127b
	j 2126f
2125:
2126:
	beqz t6, 2128f
2130:
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
	bnez t6, 2130b
	j 2129f
2128:
2129:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2124b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2131:
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
	bnez t5, 2131b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2132:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2133f
2135:
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
	bnez t5, 2135b
	j 2134f
2133:
2134:
	beqz t6, 2136f
2138:
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
	bnez t6, 2138b
	j 2137f
2136:
2137:
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
	bnez t2, 2132b
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
2139:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2139b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2140:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2140b
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
2141:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2141b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2142:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2143f
2145:
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
	bnez t5, 2145b
	j 2144f
2143:
2144:
	beqz t6, 2146f
2148:
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
	bnez t6, 2148b
	j 2147f
2146:
2147:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2142b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2149:
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
	bnez t5, 2149b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2150:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2151f
2153:
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
	bnez t5, 2153b
	j 2152f
2151:
2152:
	beqz t6, 2154f
2156:
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
	bnez t6, 2156b
	j 2155f
2154:
2155:
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
	bnez t2, 2150b
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
2157:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2157b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2158:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2158b
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
2159:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2159b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2160:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2161f
2163:
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
	bnez t5, 2163b
	j 2162f
2161:
2162:
	beqz t6, 2164f
2166:
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
	bnez t6, 2166b
	j 2165f
2164:
2165:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2160b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2167:
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
	bnez t5, 2167b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2168:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2169f
2171:
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
	bnez t5, 2171b
	j 2170f
2169:
2170:
	beqz t6, 2172f
2174:
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
	bnez t6, 2174b
	j 2173f
2172:
2173:
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
	bnez t2, 2168b
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
2175:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2175b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2176:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2176b
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
2177:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2177b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2178:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2179f
2181:
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
	bnez t5, 2181b
	j 2180f
2179:
2180:
	beqz t6, 2182f
2184:
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
	bnez t6, 2184b
	j 2183f
2182:
2183:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2178b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2185:
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
	bnez t5, 2185b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2186:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2187f
2189:
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
	bnez t5, 2189b
	j 2188f
2187:
2188:
	beqz t6, 2190f
2192:
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
	bnez t6, 2192b
	j 2191f
2190:
2191:
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
	bnez t2, 2186b
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
2193:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2193b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2194:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2194b
	slli t3, t0, 3
	sub a5, a5, t3
	srli a1, s7, 60
	slli t3, s5, 3
	add t3, a7, t3
	slli s4, s5, 2
	add s4, s4, s5
	add s4, a7, s4
	addi t5, t0, 0
2195:
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
	bnez t5, 2195b
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
2196:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2196b
2197:
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
	beqz t5, 2198f
2200:
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
	bnez t5, 2200b
	j 2199f
2198:
2199:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2201f
2203:
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
	bnez t5, 2203b
	j 2202f
2201:
2202:
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
	bnez a1, 2197b
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
2204:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2204b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2205:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2205b
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
2206:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2206b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2207:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2208f
2210:
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
	bnez t5, 2210b
	j 2209f
2208:
2209:
	beqz t6, 2211f
2213:
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
	bnez t6, 2213b
	j 2212f
2211:
2212:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2207b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2214:
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
	bnez t5, 2214b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2215:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2216f
2218:
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
	bnez t5, 2218b
	j 2217f
2216:
2217:
	beqz t6, 2219f
2221:
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
	bnez t6, 2221b
	j 2220f
2219:
2220:
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
	bnez t2, 2215b
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
2224:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2224b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2225:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2226f
2228:
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
	bnez t5, 2228b
	j 2227f
2226:
2227:
	beqz t6, 2229f
2231:
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
	bnez t6, 2231b
	j 2230f
2229:
2230:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2225b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2232:
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
	bnez t5, 2232b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2233:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2234f
2236:
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
	bnez t5, 2236b
	j 2235f
2234:
2235:
	beqz t6, 2237f
2239:
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
	bnez t6, 2239b
	j 2238f
2237:
2238:
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
	bnez t2, 2233b
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
2240:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2240b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2241:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2241b
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
2242:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2242b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2243:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2244f
2246:
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
	bnez t5, 2246b
	j 2245f
2244:
2245:
	beqz t6, 2247f
2249:
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
	bnez t6, 2249b
	j 2248f
2247:
2248:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2243b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2250:
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
	bnez t5, 2250b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2251:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2252f
2254:
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
	bnez t5, 2254b
	j 2253f
2252:
2253:
	beqz t6, 2255f
2257:
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
	bnez t6, 2257b
	j 2256f
2255:
2256:
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
	bnez t2, 2251b
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
2260:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2260b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2261:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2262f
2264:
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
	bnez t5, 2264b
	j 2263f
2262:
2263:
	beqz t6, 2265f
2267:
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
	bnez t6, 2267b
	j 2266f
2265:
2266:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2261b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2268:
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
	bnez t5, 2268b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2269:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2270f
2272:
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
	bnez t5, 2272b
	j 2271f
2270:
2271:
	beqz t6, 2273f
2275:
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
	bnez t6, 2275b
	j 2274f
2273:
2274:
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
	bnez t2, 2269b
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
	slli t3, t0, 3
	sub a5, a5, t3
	srli a1, s7, 60
	slli t3, s5, 3
	add t3, a7, t3
	slli s4, s5, 2
	add s4, s4, s5
	add s4, a7, s4
	addi t5, t0, 0
2278:
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
	bnez t5, 2278b
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
2279:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2279b
2280:
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
	beqz t5, 2281f
2283:
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
	bnez t5, 2283b
	j 2282f
2281:
2282:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2284f
2286:
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
	bnez t5, 2286b
	j 2285f
2284:
2285:
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
	bnez a1, 2280b
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
	slli s7, s7, 4
	addi s10, s10, -1
	bnez s10, 2122b
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
2289:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2289b
2290:
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
	beqz t5, 2291f
2293:
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
	bnez t5, 2293b
	j 2292f
2291:
2292:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2294f
2296:
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
	bnez t5, 2296b
	j 2295f
2294:
2295:
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
	bnez a1, 2290b
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
2297:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2297b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2298:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2298b
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
2299:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2299b
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
	addi s4, zero, -1
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
	addi s1, zero, 0
2300:
	ld s2, 0(t3)
	ld s3, 0(t4)
	xor s2, s2, s3
	or s1, s1, s2
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2300b
	addi s2, zero, 0
	sltu s1, s2, s1
	addi s1, s1, -1
	and s4, s4, s1
	addi a0, zero, 1
	and a0, a0, s4
220:
	j 218f
217:
	addi a0, zero, 0
218:
27:
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

vg_ffdh_check_domain:
	.option push
	.option arch, +m, +c
	lla t5, {VG_FFDH_VETTED_GROUPS_RISCV}
	addi a5, zero, 0
	addi t3, a2, -256
	beqz t3, 20f
	addi t4, zero, 1
	j 21f
20:
	addi t0, t5, 8
	addi t2, a1, 0
	addi t4, zero, 0
22:
	sub t1, a1, t2
	add t1, a0, t1
	lbu t3, 0(t1)
	lbu t1, 0(t0)
	xor t3, t3, t1
	or t4, t4, t3
	addi t0, t0, 1
	addi t2, t2, -1
	bnez t2, 22b
21:
	addi t6, zero, 0
	sltu t6, t6, t4
	addi t6, t6, -1
	andi t6, t6, 225
	or a5, a5, t6
	addi t5, t5, 388
	addi t5, t5, 388
	addi t3, a2, -256
	beqz t3, 23f
	addi t4, zero, 1
	j 24f
23:
	addi t0, t5, 8
	addi t2, a1, 0
	addi t4, zero, 0
25:
	sub t1, a1, t2
	add t1, a0, t1
	lbu t3, 0(t1)
	lbu t1, 0(t0)
	xor t3, t3, t1
	or t4, t4, t3
	addi t0, t0, 1
	addi t2, t2, -1
	bnez t2, 25b
24:
	addi t6, zero, 0
	sltu t6, t6, t4
	addi t6, t6, -1
	andi t6, t6, 225
	or a5, a5, t6
	addi t5, t5, 388
	addi t5, t5, 388
	addi t3, a2, -384
	beqz t3, 26f
	addi t4, zero, 1
	j 27f
26:
	addi t0, t5, 8
	addi t2, a1, 0
	addi t4, zero, 0
28:
	sub t1, a1, t2
	add t1, a0, t1
	lbu t3, 0(t1)
	lbu t1, 0(t0)
	xor t3, t3, t1
	or t4, t4, t3
	addi t0, t0, 1
	addi t2, t2, -1
	bnez t2, 28b
27:
	addi t6, zero, 0
	sltu t6, t6, t4
	addi t6, t6, -1
	andi t6, t6, 275
	or a5, a5, t6
	addi t5, t5, 580
	addi t5, t5, 580
	addi t3, a2, -384
	beqz t3, 29f
	addi t4, zero, 1
	j 210f
29:
	addi t0, t5, 8
	addi t2, a1, 0
	addi t4, zero, 0
211:
	sub t1, a1, t2
	add t1, a0, t1
	lbu t3, 0(t1)
	lbu t1, 0(t0)
	xor t3, t3, t1
	or t4, t4, t3
	addi t0, t0, 1
	addi t2, t2, -1
	bnez t2, 211b
210:
	addi t6, zero, 0
	sltu t6, t6, t4
	addi t6, t6, -1
	andi t6, t6, 275
	or a5, a5, t6
	addi t5, t5, 580
	addi t5, t5, 580
	addi t3, a2, -512
	beqz t3, 212f
	addi t4, zero, 1
	j 213f
212:
	addi t0, t5, 8
	addi t2, a1, 0
	addi t4, zero, 0
214:
	sub t1, a1, t2
	add t1, a0, t1
	lbu t3, 0(t1)
	lbu t1, 0(t0)
	xor t3, t3, t1
	or t4, t4, t3
	addi t0, t0, 1
	addi t2, t2, -1
	bnez t2, 214b
213:
	addi t6, zero, 0
	sltu t6, t6, t4
	addi t6, t6, -1
	andi t6, t6, 325
	or a5, a5, t6
	addi t5, t5, 772
	addi t5, t5, 772
	addi t3, a2, -512
	beqz t3, 215f
	addi t4, zero, 1
	j 216f
215:
	addi t0, t5, 8
	addi t2, a1, 0
	addi t4, zero, 0
217:
	sub t1, a1, t2
	add t1, a0, t1
	lbu t3, 0(t1)
	lbu t1, 0(t0)
	xor t3, t3, t1
	or t4, t4, t3
	addi t0, t0, 1
	addi t2, t2, -1
	bnez t2, 217b
216:
	addi t6, zero, 0
	sltu t6, t6, t4
	addi t6, t6, -1
	andi t6, t6, 325
	or a5, a5, t6
	addi t5, t5, 772
	addi t5, t5, 772
	addi t3, a2, -768
	beqz t3, 218f
	addi t4, zero, 1
	j 219f
218:
	addi t0, t5, 8
	addi t2, a1, 0
	addi t4, zero, 0
220:
	sub t1, a1, t2
	add t1, a0, t1
	lbu t3, 0(t1)
	lbu t1, 0(t0)
	xor t3, t3, t1
	or t4, t4, t3
	addi t0, t0, 1
	addi t2, t2, -1
	bnez t2, 220b
219:
	addi t6, zero, 0
	sltu t6, t6, t4
	addi t6, t6, -1
	andi t6, t6, 375
	or a5, a5, t6
	addi t5, t5, 1156
	addi t5, t5, 1156
	addi t3, a2, -768
	beqz t3, 221f
	addi t4, zero, 1
	j 222f
221:
	addi t0, t5, 8
	addi t2, a1, 0
	addi t4, zero, 0
223:
	sub t1, a1, t2
	add t1, a0, t1
	lbu t3, 0(t1)
	lbu t1, 0(t0)
	xor t3, t3, t1
	or t4, t4, t3
	addi t0, t0, 1
	addi t2, t2, -1
	bnez t2, 223b
222:
	addi t6, zero, 0
	sltu t6, t6, t4
	addi t6, t6, -1
	andi t6, t6, 375
	or a5, a5, t6
	addi t5, t5, 1156
	addi t5, t5, 1156
	addi t3, a2, -1024
	beqz t3, 224f
	addi t4, zero, 1
	j 225f
224:
	addi t0, t5, 8
	addi t2, a1, 0
	addi t4, zero, 0
226:
	sub t1, a1, t2
	add t1, a0, t1
	lbu t3, 0(t1)
	lbu t1, 0(t0)
	xor t3, t3, t1
	or t4, t4, t3
	addi t0, t0, 1
	addi t2, t2, -1
	bnez t2, 226b
225:
	addi t6, zero, 0
	sltu t6, t6, t4
	addi t6, t6, -1
	andi t6, t6, 400
	or a5, a5, t6
	addi t5, t5, 1540
	addi t5, t5, 1540
	addi t3, a2, -1024
	beqz t3, 227f
	addi t4, zero, 1
	j 228f
227:
	addi t0, t5, 8
	addi t2, a1, 0
	addi t4, zero, 0
229:
	sub t1, a1, t2
	add t1, a0, t1
	lbu t3, 0(t1)
	lbu t1, 0(t0)
	xor t3, t3, t1
	or t4, t4, t3
	addi t0, t0, 1
	addi t2, t2, -1
	bnez t2, 229b
228:
	addi t6, zero, 0
	sltu t6, t6, t4
	addi t6, t6, -1
	andi t6, t6, 400
	or a5, a5, t6
	addi t5, t5, 1540
	addi t5, t5, 1540
	bnez a5, 230f
	addi t0, a3, 0
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
	sd a0, 0(s6)
	sd a1, 8(s6)
	addi s7, a0, 0
	addi s8, a2, 0
	addi a1, a2, 0
	addi s10, a0, 0
	addi s11, a1, 0
	addi t0, a1, 7
	srli t0, t0, 3
	slli s5, t0, 3
	addi s5, s5, 16
	addi a7, s6, 256
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
	add t4, s7, s8
	addi t4, t4, -1
	lbu s0, 0(t4)
	andi s0, s0, 1
	xori s0, s0, 1
	lbu t4, 0(s7)
	beqz t4, 234f
	j 235f
234:
	addi s0, zero, 1
235:
	addi t5, s8, -64
	beqz t5, 236f
	j 237f
236:
	srli t4, t4, 7
	xori t4, t4, 1
	or s0, s0, t4
237:
	beqz s0, 238f
	addi a0, zero, 0
	j 239f
238:
	ld t3, 8(s6)
	slli t2, s11, 1
	add t2, t2, s11
	sub t3, t3, t2
	beqz t3, 240f
	ld a6, 0(s6)
	add a6, a6, s11
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
242:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 242b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
243:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 243b
	add t3, a7, s5
	addi t3, t3, -16
	addi s0, zero, 0
	sd s0, 0(t3)
	addi a7, s6, 256
	addi s7, a1, 0
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t5, t0, 0
	addi s0, zero, 0
244:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 244b
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
245:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 245b
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
	add t3, t3, s5
	addi t4, a7, 0
	addi t5, t0, 0
246:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 246b
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	ld s0, 0(t3)
	xori s0, s0, 1
	sd s0, 0(t3)
	addi s9, zero, -1
	addi s4, zero, -1
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
	addi s1, zero, 0
247:
	ld s2, 0(t3)
	ld s3, 0(t4)
	xor s2, s2, s3
	or s1, s1, s2
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 247b
	addi s2, zero, 0
	sltu s1, s2, s1
	addi s1, s1, -1
	and s4, s4, s1
	xor s4, s4, s9
	and s9, s9, s4
	addi s4, zero, -1
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
	addi s1, zero, 0
248:
	ld s2, 0(t3)
	ld s3, 0(t4)
	xor s2, s2, s3
	or s1, s1, s2
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 248b
	addi s2, zero, 0
	sltu s1, s2, s1
	addi s1, s1, -1
	and s4, s4, s1
	xori s4, s4, -1
	and s9, s9, s4
	addi s4, zero, -1
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
	addi t5, t0, 0
	addi s1, zero, 0
249:
	ld s2, 0(t3)
	ld s3, 0(t4)
	xor s2, s2, s3
	or s1, s1, s2
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 249b
	addi s2, zero, 0
	sltu s1, s2, s1
	addi s1, s1, -1
	and s4, s4, s1
	xori s4, s4, -1
	and s9, s9, s4
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
	and s9, s9, s4
	addi a0, zero, 1
	and a0, a0, s9
	j 241f
240:
	ld a6, 0(s6)
	add a6, a6, s11
	add a6, a6, s11
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
251:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 251b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
252:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 252b
	add t3, a7, s5
	addi t3, t3, -16
	addi s0, zero, 0
	sd s0, 0(t3)
	addi a7, s6, 256
	addi s7, a1, 0
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t5, t0, 0
	addi s0, zero, 0
253:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 253b
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
	add t3, t3, s5
	addi t4, a7, 0
	addi t5, t0, 0
255:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 255b
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	ld s0, 0(t3)
	xori s0, s0, 1
	sd s0, 0(t3)
	addi s9, zero, -1
	addi s4, zero, -1
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
	addi s1, zero, 0
256:
	ld s2, 0(t3)
	ld s3, 0(t4)
	xor s2, s2, s3
	or s1, s1, s2
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 256b
	addi s2, zero, 0
	sltu s1, s2, s1
	addi s1, s1, -1
	and s4, s4, s1
	xor s4, s4, s9
	and s9, s9, s4
	addi s4, zero, -1
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
	addi s1, zero, 0
257:
	ld s2, 0(t3)
	ld s3, 0(t4)
	xor s2, s2, s3
	or s1, s1, s2
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 257b
	addi s2, zero, 0
	sltu s1, s2, s1
	addi s1, s1, -1
	and s4, s4, s1
	xori s4, s4, -1
	and s9, s9, s4
	addi s4, zero, -1
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
	addi t5, t0, 0
	addi s1, zero, 0
258:
	ld s2, 0(t3)
	ld s3, 0(t4)
	xor s2, s2, s3
	or s1, s1, s2
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 258b
	addi s2, zero, 0
	sltu s1, s2, s1
	addi s1, s1, -1
	and s4, s4, s1
	xori s4, s4, -1
	and s9, s9, s4
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
	and s9, s9, s4
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	ld t4, 0(t3)
	andi t4, t4, 1
	addi t5, zero, 0
	sub t4, t5, t4
	and s9, s9, t4
	beqz s9, 260f
	ld s7, 0(s6)
	add s7, s7, s11
	add s7, s7, s11
	addi s8, s11, 0
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
	ld s9, 0(s6)
	addi s10, s11, 0
	addi t3, a7, 0
	add t3, t3, s5
	addi t5, t0, 0
	addi s0, zero, 0
264:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 264b
	addi a2, a7, 0
	add a2, a2, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
265:
	lbu s7, 0(s9)
	slli s7, s7, 56
	addi s9, s9, 1
	addi s8, zero, 8
266:
	srli s4, s7, 63
	slli s7, s7, 1
	addi t3, a5, 0
	addi t4, a2, 0
	addi t5, t0, 0
267:
	ld s2, 0(t4)
	slli s3, s2, 1
	add s3, s3, s4
	srli s4, s2, 63
	sd s3, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 267b
	sd s4, 0(t3)
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
	addi s8, s8, -1
	bnez s8, 266b
	addi s10, s10, -1
	bnez s10, 265b
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
	addi s4, zero, -1
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
	addi s1, zero, 0
271:
	ld s2, 0(t3)
	ld s3, 0(t4)
	xor s2, s2, s3
	or s1, s1, s2
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 271b
	addi s2, zero, 0
	sltu s1, s2, s1
	addi s1, s1, -1
	and s4, s4, s1
	addi s10, s4, 0
	ld s7, 0(s6)
	addi s8, s11, 0
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
	ld a6, 0(s6)
	add a6, a6, s11
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
	add t3, a7, s5
	addi t3, t3, -16
	addi s0, zero, 0
	sd s0, 0(t3)
	addi a7, s6, 256
	addi s7, a1, 0
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
	add t3, t3, s5
	addi t4, a7, 0
	addi t5, t0, 0
278:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 278b
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	ld s0, 0(t3)
	xori s0, s0, 1
	sd s0, 0(t3)
	addi s9, zero, -1
	addi s4, zero, -1
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
	addi s1, zero, 0
279:
	ld s2, 0(t3)
	ld s3, 0(t4)
	xor s2, s2, s3
	or s1, s1, s2
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 279b
	addi s2, zero, 0
	sltu s1, s2, s1
	addi s1, s1, -1
	and s4, s4, s1
	xor s4, s4, s9
	and s9, s9, s4
	addi s4, zero, -1
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
	addi s1, zero, 0
280:
	ld s2, 0(t3)
	ld s3, 0(t4)
	xor s2, s2, s3
	or s1, s1, s2
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 280b
	addi s2, zero, 0
	sltu s1, s2, s1
	addi s1, s1, -1
	and s4, s4, s1
	xori s4, s4, -1
	and s9, s9, s4
	addi s4, zero, -1
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
	addi t5, t0, 0
	addi s1, zero, 0
281:
	ld s2, 0(t3)
	ld s3, 0(t4)
	xor s2, s2, s3
	or s1, s1, s2
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 281b
	addi s2, zero, 0
	sltu s1, s2, s1
	addi s1, s1, -1
	and s4, s4, s1
	xori s4, s4, -1
	and s9, s9, s4
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
	and s9, s9, s4
	and s9, s9, s10
	beqz s9, 283f
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
285:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 285b
	slli t3, t0, 3
	add t3, t3, a2
	addi t3, t3, -8
	addi s0, zero, 1
	sd s0, 0(t3)
	addi a1, t0, 64
286:
	addi t3, a5, 0
	addi t4, a2, 0
	addi t5, t0, 0
	addi s4, zero, 0
287:
	ld s2, 0(t4)
	slli s3, s2, 1
	add s3, s3, s4
	srli s4, s2, 63
	sd s3, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 287b
	sd s4, 0(t3)
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
	addi a1, a1, -1
	bnez a1, 286b
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
	addi a0, a7, 0
290:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 290b
291:
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
	beqz t5, 292f
294:
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
	bnez t5, 294b
	j 293f
292:
293:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 295f
297:
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
	bnez t5, 297b
	j 296f
295:
296:
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
	bnez a1, 291b
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
	bnez t5, 2104b
	j 2103f
2102:
2103:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2105f
2107:
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
	addi a3, a2, 0
	addi a4, a2, 0
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
	addi a3, a2, 0
	addi a4, a2, 0
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
	addi a3, a2, 0
	addi a4, a2, 0
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
	addi a3, a2, 0
	addi a4, a2, 0
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
	ld t3, 0(s6)
	add t3, t3, s11
	add t3, t3, s11
	addi a4, s11, 0
	addi t5, a4, 0
	addi t4, zero, 0
	addi s1, a4, -1
	addi s2, zero, 0
	addi s3, zero, 0
2150:
	lbu t6, 0(t3)
	addi t2, zero, 0
	sub s4, t2, t6
	or s4, s4, t6
	srli s4, s4, 63
	sub s4, t2, s4
	or s4, s4, s3
	xor s4, s4, s3
	xor s0, s1, t4
	and s0, s0, s4
	xor s1, s1, s0
	xor s0, s2, t6
	and s0, s0, s4
	xor s2, s2, s0
	or s3, s3, s4
	addi t3, t3, 1
	addi t4, t4, 1
	addi t5, t5, -1
	bnez t5, 2150b
	ld s9, 0(s6)
	add s9, s9, s11
	add s9, s9, s11
	add s9, s9, s1
	sub s10, s11, s1
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
2151:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2151b
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
2152:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2152b
2153:
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
	beqz t5, 2154f
2156:
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
	bnez t5, 2156b
	j 2155f
2154:
2155:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2157f
2159:
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
	bnez t5, 2159b
	j 2158f
2157:
2158:
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
	bnez a1, 2153b
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
2160:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2160b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2161:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2161b
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
2162:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2162b
2163:
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
	beqz t5, 2164f
2166:
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
	bnez t5, 2166b
	j 2165f
2164:
2165:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2167f
2169:
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
	bnez t5, 2169b
	j 2168f
2167:
2168:
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
	bnez a1, 2163b
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
2170:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2170b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
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
	addi s7, zero, 2
2173:
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
	bnez t5, 2178b
	j 2177f
2176:
2177:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2179f
2181:
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
2184:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2184b
	addi s7, s7, 1
	addi t2, s7, -16
	bnez t2, 2173b
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
2186:
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
2187:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2187b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2188:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2189f
2191:
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
	bnez t5, 2191b
	j 2190f
2189:
2190:
	beqz t6, 2192f
2194:
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
	bnez t6, 2194b
	j 2193f
2192:
2193:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2188b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2195:
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
	bnez t5, 2195b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2196:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2197f
2199:
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
	bnez t5, 2199b
	j 2198f
2197:
2198:
	beqz t6, 2200f
2202:
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
	bnez t6, 2202b
	j 2201f
2200:
2201:
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
	bnez t2, 2196b
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
2203:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2203b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2204:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2204b
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
2205:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2205b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2206:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2207f
2209:
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
	bnez t5, 2209b
	j 2208f
2207:
2208:
	beqz t6, 2210f
2212:
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
	bnez t6, 2212b
	j 2211f
2210:
2211:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2206b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2213:
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
	bnez t5, 2213b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2214:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2215f
2217:
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
	bnez t5, 2217b
	j 2216f
2215:
2216:
	beqz t6, 2218f
2220:
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
	bnez t6, 2220b
	j 2219f
2218:
2219:
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
	bnez t2, 2214b
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
2221:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2221b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2222:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2222b
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
2223:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2223b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2224:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2225f
2227:
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
	bnez t5, 2227b
	j 2226f
2225:
2226:
	beqz t6, 2228f
2230:
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
	bnez t6, 2230b
	j 2229f
2228:
2229:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2224b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2231:
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
	bnez t5, 2231b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2232:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2233f
2235:
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
	bnez t5, 2235b
	j 2234f
2233:
2234:
	beqz t6, 2236f
2238:
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
	bnez t6, 2238b
	j 2237f
2236:
2237:
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
	bnez t2, 2232b
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
2239:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2239b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2240:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2240b
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
2241:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2241b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2242:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2243f
2245:
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
	bnez t5, 2245b
	j 2244f
2243:
2244:
	beqz t6, 2246f
2248:
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
	bnez t6, 2248b
	j 2247f
2246:
2247:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2242b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2249:
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
	bnez t5, 2249b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2250:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2251f
2253:
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
	bnez t5, 2253b
	j 2252f
2251:
2252:
	beqz t6, 2254f
2256:
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
	bnez t6, 2256b
	j 2255f
2254:
2255:
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
	bnez t2, 2250b
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
2257:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2257b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2258:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2258b
	slli t3, t0, 3
	sub a5, a5, t3
	srli a1, s7, 60
	slli t3, s5, 3
	add t3, a7, t3
	slli s4, s5, 2
	add s4, s4, s5
	add s4, a7, s4
	addi t5, t0, 0
2259:
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
	bnez t5, 2259b
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
2270:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2270b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2271:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2272f
2274:
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
	bnez t5, 2274b
	j 2273f
2272:
2273:
	beqz t6, 2275f
2277:
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
	bnez t6, 2277b
	j 2276f
2275:
2276:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2271b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2278:
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
	bnez t5, 2278b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2279:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2280f
2282:
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
	bnez t5, 2282b
	j 2281f
2280:
2281:
	beqz t6, 2283f
2285:
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
	bnez t6, 2285b
	j 2284f
2283:
2284:
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
	bnez t2, 2279b
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
2286:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2286b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2287:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2287b
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
2288:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2288b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2289:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2290f
2292:
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
	bnez t5, 2292b
	j 2291f
2290:
2291:
	beqz t6, 2293f
2295:
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
	bnez t6, 2295b
	j 2294f
2293:
2294:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2289b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2296:
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
	bnez t5, 2296b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2297:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2298f
2300:
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
	bnez t5, 2300b
	j 2299f
2298:
2299:
	beqz t6, 2301f
2303:
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
	bnez t6, 2303b
	j 2302f
2301:
2302:
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
	bnez t2, 2297b
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
2304:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2304b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2305:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2305b
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
2306:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2306b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2307:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2308f
2310:
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
	bnez t5, 2310b
	j 2309f
2308:
2309:
	beqz t6, 2311f
2313:
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
	bnez t6, 2313b
	j 2312f
2311:
2312:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2307b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2314:
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
	bnez t5, 2314b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2315:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2316f
2318:
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
	bnez t5, 2318b
	j 2317f
2316:
2317:
	beqz t6, 2319f
2321:
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
	bnez t6, 2321b
	j 2320f
2319:
2320:
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
	bnez t2, 2315b
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
2324:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2324b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2325:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2326f
2328:
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
	bnez t5, 2328b
	j 2327f
2326:
2327:
	beqz t6, 2329f
2331:
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
	bnez t6, 2331b
	j 2330f
2329:
2330:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2325b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2332:
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
	bnez t5, 2332b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2333:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2334f
2336:
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
	bnez t5, 2336b
	j 2335f
2334:
2335:
	beqz t6, 2337f
2339:
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
	bnez t6, 2339b
	j 2338f
2337:
2338:
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
	bnez t2, 2333b
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
2340:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2340b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2341:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2341b
	slli t3, t0, 3
	sub a5, a5, t3
	srli a1, s7, 60
	slli t3, s5, 3
	add t3, a7, t3
	slli s4, s5, 2
	add s4, s4, s5
	add s4, a7, s4
	addi t5, t0, 0
2342:
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
	bnez t5, 2342b
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
2343:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2343b
2344:
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
	beqz t5, 2345f
2347:
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
	bnez t5, 2347b
	j 2346f
2345:
2346:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2348f
2350:
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
	bnez t5, 2350b
	j 2349f
2348:
2349:
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
	bnez a1, 2344b
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
2351:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2351b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2352:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2352b
	slli s7, s7, 4
	addi s10, s10, -1
	bnez s10, 2186b
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
2353:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2353b
2354:
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
	beqz t5, 2355f
2357:
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
	bnez t5, 2357b
	j 2356f
2355:
2356:
	addi t5, t0, -1
	srli t5, t5, 2
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
	bnez t5, 2360b
	j 2359f
2358:
2359:
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
	bnez a1, 2354b
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
2361:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2361b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2362:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2362b
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
2363:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2363b
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
	addi s4, zero, -1
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
	addi s1, zero, 0
2364:
	ld s2, 0(t3)
	ld s3, 0(t4)
	xor s2, s2, s3
	or s1, s1, s2
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2364b
	addi s2, zero, 0
	sltu s1, s2, s1
	addi s1, s1, -1
	and s4, s4, s1
	addi a0, zero, 1
	and a0, a0, s4
	j 284f
283:
	addi a0, zero, 0
284:
	j 261f
260:
	addi a0, zero, 0
261:
241:
239:
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
	j 231f
230:
	addi a0, zero, 1
231:
	ret
	.option pop

vg_ffdh_exchange:
	.option push
	.option arch, +m, +c
	addi t0, sp, 8
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
	sd a0, 0(s6)
	sd a5, 8(s6)
	sd a6, 16(s6)
	sd a7, 24(s6)
	addi s7, a2, 0
	addi s8, a4, 0
	addi a1, a4, 0
	addi s10, a0, 0
	addi s11, a1, 0
	addi t0, a1, 7
	srli t0, t0, 3
	slli s5, t0, 3
	addi s5, s5, 16
	addi a7, s6, 256
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
	addi a0, zero, 0
	j 27f
26:
	ld a6, 24(s6)
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
28:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 28b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
29:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 29b
	add t3, a7, s5
	addi t3, t3, -16
	addi s0, zero, 0
	sd s0, 0(t3)
	addi a7, s6, 256
	addi s7, a1, 0
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
	addi a0, a7, 0
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
	beqz t5, 217f
219:
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
	slli s2, t0, 3
	sub a0, a0, s2
	addi a0, a0, 8
	addi a1, a1, -1
	bnez a1, 216b
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
	addi a0, a7, 0
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
	beqz t5, 227f
229:
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
	slli s2, t0, 3
	sub a0, a0, s2
	addi a0, a0, 8
	addi a1, a1, -1
	bnez a1, 226b
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
	addi a0, a7, 0
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
	beqz t5, 237f
239:
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
	slli s2, t0, 3
	sub a0, a0, s2
	addi a0, a0, 8
	addi a1, a1, -1
	bnez a1, 236b
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
	addi a0, a7, 0
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
	beqz t5, 247f
249:
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
	slli s2, t0, 3
	sub a0, a0, s2
	addi a0, a0, 8
	addi a1, a1, -1
	bnez a1, 246b
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
	addi a0, a7, 0
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
	beqz t5, 257f
259:
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
	slli s2, t0, 3
	sub a0, a0, s2
	addi a0, a0, 8
	addi a1, a1, -1
	bnez a1, 256b
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
	addi a0, a7, 0
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
	slli s2, t0, 3
	sub a0, a0, s2
	addi a0, a0, 8
	addi a1, a1, -1
	bnez a1, 266b
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
	ld s9, 8(s6)
	ld s10, 16(s6)
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
276:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 276b
277:
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
	beqz t5, 278f
280:
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
	bnez t5, 280b
	j 279f
278:
279:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 281f
283:
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
	bnez t5, 283b
	j 282f
281:
282:
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
	bnez a1, 277b
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
284:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 284b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
285:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 285b
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
286:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 286b
287:
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
	beqz t5, 288f
290:
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
	bnez t5, 290b
	j 289f
288:
289:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 291f
293:
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
	bnez t5, 293b
	j 292f
291:
292:
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
	bnez a1, 287b
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
294:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 294b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
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
	addi s7, zero, 2
297:
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
298:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 298b
299:
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
	beqz t5, 2100f
2102:
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
	bnez t5, 2102b
	j 2101f
2100:
2101:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2103f
2105:
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
	bnez t5, 2105b
	j 2104f
2103:
2104:
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
	bnez a1, 299b
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
2106:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2106b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2107:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2107b
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
2108:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2108b
	addi s7, s7, 1
	addi t2, s7, -16
	bnez t2, 297b
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
2110:
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
2111:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2111b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2112:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2113f
2115:
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
	bnez t5, 2115b
	j 2114f
2113:
2114:
	beqz t6, 2116f
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
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2118b
	j 2117f
2116:
2117:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2112b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2119:
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
	bnez t5, 2119b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2120:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2121f
2123:
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
	bnez t5, 2123b
	j 2122f
2121:
2122:
	beqz t6, 2124f
2126:
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
	bnez t6, 2126b
	j 2125f
2124:
2125:
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
	bnez t2, 2120b
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
2127:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2127b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2128:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2128b
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
2129:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2129b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2130:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2131f
2133:
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
	bnez t5, 2133b
	j 2132f
2131:
2132:
	beqz t6, 2134f
2136:
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
	bnez t6, 2136b
	j 2135f
2134:
2135:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2130b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2137:
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
	bnez t5, 2137b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2138:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2139f
2141:
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
	bnez t5, 2141b
	j 2140f
2139:
2140:
	beqz t6, 2142f
2144:
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
	bnez t6, 2144b
	j 2143f
2142:
2143:
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
	bnez t2, 2138b
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
2145:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2145b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2146:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2146b
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
2147:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2147b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2148:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2149f
2151:
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
	bnez t5, 2151b
	j 2150f
2149:
2150:
	beqz t6, 2152f
2154:
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
	bnez t6, 2154b
	j 2153f
2152:
2153:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2148b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2155:
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
	bnez t5, 2155b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2156:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2157f
2159:
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
	bnez t5, 2159b
	j 2158f
2157:
2158:
	beqz t6, 2160f
2162:
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
	bnez t6, 2162b
	j 2161f
2160:
2161:
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
	bnez t2, 2156b
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
2163:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2163b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2164:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2164b
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
2165:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2165b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2166:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
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
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2166b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2173:
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
	bnez t5, 2173b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2174:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2175f
2177:
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
	bnez t5, 2177b
	j 2176f
2175:
2176:
	beqz t6, 2178f
2180:
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
	bnez t6, 2180b
	j 2179f
2178:
2179:
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
	bnez t2, 2174b
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
	slli t3, t0, 3
	sub a5, a5, t3
	srli a1, s7, 60
	slli t3, s5, 3
	add t3, a7, t3
	slli s4, s5, 2
	add s4, s4, s5
	add s4, a7, s4
	addi t5, t0, 0
2183:
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
	bnez t5, 2183b
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
	bnez t5, 2188b
	j 2187f
2186:
2187:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2189f
2191:
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
2194:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2194b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2195:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2196f
2198:
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
	bnez t5, 2198b
	j 2197f
2196:
2197:
	beqz t6, 2199f
2201:
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
	bnez t6, 2201b
	j 2200f
2199:
2200:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2195b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2202:
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
	bnez t5, 2202b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2203:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2204f
2206:
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
	bnez t5, 2206b
	j 2205f
2204:
2205:
	beqz t6, 2207f
2209:
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
	bnez t6, 2209b
	j 2208f
2207:
2208:
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
	bnez t2, 2203b
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
2210:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2210b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2211:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2211b
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
2212:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2212b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2213:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2214f
2216:
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
	bnez t5, 2216b
	j 2215f
2214:
2215:
	beqz t6, 2217f
2219:
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
	bnez t6, 2219b
	j 2218f
2217:
2218:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2213b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2220:
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
	bnez t5, 2220b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2221:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2222f
2224:
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
	bnez t5, 2224b
	j 2223f
2222:
2223:
	beqz t6, 2225f
2227:
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
	bnez t6, 2227b
	j 2226f
2225:
2226:
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
	bnez t2, 2221b
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
2230:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2230b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2231:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2232f
2234:
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
	bnez t5, 2234b
	j 2233f
2232:
2233:
	beqz t6, 2235f
2237:
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
	bnez t6, 2237b
	j 2236f
2235:
2236:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2231b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2238:
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
	bnez t5, 2238b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2239:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2240f
2242:
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
	bnez t5, 2242b
	j 2241f
2240:
2241:
	beqz t6, 2243f
2245:
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
	bnez t6, 2245b
	j 2244f
2243:
2244:
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
	bnez t2, 2239b
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
2248:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2248b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2249:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2250f
2252:
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
	bnez t5, 2252b
	j 2251f
2250:
2251:
	beqz t6, 2253f
2255:
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
	bnez t6, 2255b
	j 2254f
2253:
2254:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2249b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2256:
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
	bnez t5, 2256b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2257:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2258f
2260:
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
	bnez t5, 2260b
	j 2259f
2258:
2259:
	beqz t6, 2261f
2263:
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
	bnez t6, 2263b
	j 2262f
2261:
2262:
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
	bnez t2, 2257b
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
2264:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2264b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2265:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2265b
	slli t3, t0, 3
	sub a5, a5, t3
	srli a1, s7, 60
	slli t3, s5, 3
	add t3, a7, t3
	slli s4, s5, 2
	add s4, s4, s5
	add s4, a7, s4
	addi t5, t0, 0
2266:
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
	bnez t5, 2266b
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
2267:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2267b
2268:
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
	beqz t5, 2269f
2271:
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
	bnez t5, 2271b
	j 2270f
2269:
2270:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2272f
2274:
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
	bnez t5, 2274b
	j 2273f
2272:
2273:
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
	bnez a1, 2268b
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
2275:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2275b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2276:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2276b
	slli s7, s7, 4
	addi s10, s10, -1
	bnez s10, 2110b
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
2277:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2277b
2278:
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
	beqz t5, 2279f
2281:
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
	bnez t5, 2281b
	j 2280f
2279:
2280:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2282f
2284:
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
	bnez t5, 2284b
	j 2283f
2282:
2283:
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
	bnez a1, 2278b
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
2285:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2285b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2286:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2286b
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t5, t0, 0
	addi s0, zero, 0
2287:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2287b
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
2288:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2288b
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
	add t3, t3, s5
	addi t4, a7, 0
	addi t5, t0, 0
2289:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2289b
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	ld s0, 0(t3)
	xori s0, s0, 1
	sd s0, 0(t3)
	addi s9, zero, -1
	addi s4, zero, -1
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
	addi s1, zero, 0
2290:
	ld s2, 0(t3)
	ld s3, 0(t4)
	xor s2, s2, s3
	or s1, s1, s2
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2290b
	addi s2, zero, 0
	sltu s1, s2, s1
	addi s1, s1, -1
	and s4, s4, s1
	xor s4, s4, s9
	and s9, s9, s4
	addi s4, zero, -1
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
	addi s1, zero, 0
2291:
	ld s2, 0(t3)
	ld s3, 0(t4)
	xor s2, s2, s3
	or s1, s1, s2
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2291b
	addi s2, zero, 0
	sltu s1, s2, s1
	addi s1, s1, -1
	and s4, s4, s1
	xori s4, s4, -1
	and s9, s9, s4
	addi s4, zero, -1
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
	addi t5, t0, 0
	addi s1, zero, 0
2292:
	ld s2, 0(t3)
	ld s3, 0(t4)
	xor s2, s2, s3
	or s1, s1, s2
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2292b
	addi s2, zero, 0
	sltu s1, s2, s1
	addi s1, s1, -1
	and s4, s4, s1
	xori s4, s4, -1
	and s9, s9, s4
	ld s10, 0(s6)
	addi t4, a7, 0
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s11
	addi t4, t4, -1
	addi t3, s10, 0
	addi t5, s11, 0
2293:
	lbu s0, 0(t4)
	and s0, s0, s9
	sb s0, 0(t3)
	addi t3, t3, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 2293b
	addi a0, zero, 1
	and a0, a0, s9
27:
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

vg_ffdh_derive_public:
	.option push
	.option arch, +m, +c
	addi t0, a7, 0
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
	sd a0, 0(s6)
	sd a5, 8(s6)
	sd a6, 16(s6)
	add t2, a2, a4
	sd t2, 24(s6)
	addi s7, a2, 0
	addi s8, a4, 0
	addi a1, a4, 0
	addi s10, a0, 0
	addi s11, a1, 0
	addi t0, a1, 7
	srli t0, t0, 3
	slli s5, t0, 3
	addi s5, s5, 16
	addi a7, s6, 256
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
	addi a0, zero, 0
	j 27f
26:
	addi s11, a6, 0
	addi a6, a5, 0
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
28:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 28b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
29:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 29b
	add t3, a7, s5
	addi t3, t3, -16
	addi s0, zero, 0
	sd s0, 0(t3)
	addi a7, s6, 256
	addi s7, a1, 0
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add t2, a4, a4
	add t2, t2, a4
	sub t2, a3, t2
	beqz t2, 210f
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t4, a7, 0
	addi t5, t0, 0
212:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 212b
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	ld s0, 0(t3)
	xori s0, s0, 1
	sd s0, 0(t3)
	addi a7, a7, 0
	add a7, a7, s5
	add a7, a7, s5
	add a7, a7, s5
	add a7, a7, s5
	add a7, a7, s5
	add a7, a7, s5
	j 211f
210:
	addi a7, a7, 0
	add a7, a7, s5
	add s7, a4, a4
	add s7, s7, a2
	addi s8, a4, 0
	addi t3, a7, 0
	addi t5, t0, 0
	addi s0, zero, 0
213:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 213b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
214:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 214b
211:
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
215:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 215b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi a7, s6, 256
	addi s9, s4, 0
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t5, t0, 0
	addi s0, zero, 0
216:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 216b
	addi s4, zero, -1
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
	addi s1, zero, 0
217:
	ld s2, 0(t3)
	ld s3, 0(t4)
	xor s2, s2, s3
	or s1, s1, s2
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 217b
	addi s2, zero, 0
	sltu s1, s2, s1
	addi s1, s1, -1
	and s4, s4, s1
	xori s4, s4, -1
	and s9, s9, s4
	addi s7, a2, 0
	addi s8, a4, 0
	addi s11, a4, 0
	addi s0, zero, 0
	beqz s9, 218f
	ld a6, 24(s6)
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
220:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 220b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
221:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 221b
	add t3, a7, s5
	addi t3, t3, -16
	addi s0, zero, 0
	sd s0, 0(t3)
	addi a7, s6, 256
	addi s7, a1, 0
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
222:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 222b
	slli t3, t0, 3
	add t3, t3, a2
	addi t3, t3, -8
	addi s0, zero, 1
	sd s0, 0(t3)
	addi a1, t0, 64
223:
	addi t3, a5, 0
	addi t4, a2, 0
	addi t5, t0, 0
	addi s4, zero, 0
224:
	ld s2, 0(t4)
	slli s3, s2, 1
	add s3, s3, s4
	srli s4, s2, 63
	sd s3, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 224b
	sd s4, 0(t3)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
225:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 225b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
226:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 226b
	addi a1, a1, -1
	bnez a1, 223b
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
	addi a0, a7, 0
227:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 227b
228:
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
	beqz t5, 229f
231:
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
	bnez t5, 231b
	j 230f
229:
230:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 232f
234:
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
	bnez t5, 234b
	j 233f
232:
233:
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
	bnez a1, 228b
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
235:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 235b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
236:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 236b
	addi a3, a2, 0
	addi a4, a2, 0
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
	addi a3, a2, 0
	addi a4, a2, 0
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
	bnez t5, 261b
	j 260f
259:
260:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 262f
264:
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
	addi a3, a2, 0
	addi a4, a2, 0
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
	addi a0, a7, 0
267:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 267b
268:
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
	beqz t5, 269f
271:
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
	bnez t5, 271b
	j 270f
269:
270:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 272f
274:
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
	bnez t5, 274b
	j 273f
272:
273:
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
	bnez a1, 268b
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
275:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 275b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
276:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 276b
	addi a3, a2, 0
	addi a4, a2, 0
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
	addi a0, a7, 0
277:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 277b
278:
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
	beqz t5, 279f
281:
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
	bnez t5, 281b
	j 280f
279:
280:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 282f
284:
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
	bnez t5, 284b
	j 283f
282:
283:
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
	bnez a1, 278b
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
285:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 285b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
286:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 286b
	ld s9, 8(s6)
	ld s10, 16(s6)
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
287:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 287b
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
288:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 288b
289:
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
	beqz t5, 290f
292:
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
	bnez t5, 292b
	j 291f
290:
291:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 293f
295:
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
	bnez t5, 295b
	j 294f
293:
294:
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
	bnez a1, 289b
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
296:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 296b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
297:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 297b
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
298:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 298b
299:
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
	beqz t5, 2100f
2102:
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
	bnez t5, 2102b
	j 2101f
2100:
2101:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2103f
2105:
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
	bnez t5, 2105b
	j 2104f
2103:
2104:
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
	bnez a1, 299b
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
2106:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2106b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2107:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2107b
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
2108:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2108b
	addi s7, zero, 2
2109:
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
2120:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2120b
	addi s7, s7, 1
	addi t2, s7, -16
	bnez t2, 2109b
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
2121:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2121b
2122:
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
2123:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2123b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2124:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2125f
2127:
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
	bnez t5, 2127b
	j 2126f
2125:
2126:
	beqz t6, 2128f
2130:
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
	bnez t6, 2130b
	j 2129f
2128:
2129:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2124b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2131:
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
	bnez t5, 2131b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2132:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2133f
2135:
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
	bnez t5, 2135b
	j 2134f
2133:
2134:
	beqz t6, 2136f
2138:
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
	bnez t6, 2138b
	j 2137f
2136:
2137:
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
	bnez t2, 2132b
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
2139:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2139b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2140:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2140b
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
2141:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2141b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2142:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2143f
2145:
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
	bnez t5, 2145b
	j 2144f
2143:
2144:
	beqz t6, 2146f
2148:
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
	bnez t6, 2148b
	j 2147f
2146:
2147:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2142b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2149:
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
	bnez t5, 2149b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2150:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2151f
2153:
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
	bnez t5, 2153b
	j 2152f
2151:
2152:
	beqz t6, 2154f
2156:
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
	bnez t6, 2156b
	j 2155f
2154:
2155:
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
	bnez t2, 2150b
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
2157:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2157b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2158:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2158b
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
2159:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2159b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2160:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2161f
2163:
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
	bnez t5, 2163b
	j 2162f
2161:
2162:
	beqz t6, 2164f
2166:
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
	bnez t6, 2166b
	j 2165f
2164:
2165:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2160b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2167:
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
	bnez t5, 2167b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2168:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2169f
2171:
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
	bnez t5, 2171b
	j 2170f
2169:
2170:
	beqz t6, 2172f
2174:
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
	bnez t6, 2174b
	j 2173f
2172:
2173:
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
	bnez t2, 2168b
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
2175:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2175b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2176:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2176b
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
2177:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2177b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2178:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2179f
2181:
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
	bnez t5, 2181b
	j 2180f
2179:
2180:
	beqz t6, 2182f
2184:
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
	bnez t6, 2184b
	j 2183f
2182:
2183:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2178b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2185:
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
	bnez t5, 2185b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2186:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2187f
2189:
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
	bnez t5, 2189b
	j 2188f
2187:
2188:
	beqz t6, 2190f
2192:
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
	bnez t6, 2192b
	j 2191f
2190:
2191:
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
	bnez t2, 2186b
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
2193:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2193b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2194:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2194b
	slli t3, t0, 3
	sub a5, a5, t3
	srli a1, s7, 60
	slli t3, s5, 3
	add t3, a7, t3
	slli s4, s5, 2
	add s4, s4, s5
	add s4, a7, s4
	addi t5, t0, 0
2195:
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
	bnez t5, 2195b
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
2196:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2196b
2197:
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
	beqz t5, 2198f
2200:
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
	bnez t5, 2200b
	j 2199f
2198:
2199:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2201f
2203:
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
	bnez t5, 2203b
	j 2202f
2201:
2202:
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
	bnez a1, 2197b
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
2204:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2204b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2205:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2205b
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
2206:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2206b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2207:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2208f
2210:
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
	bnez t5, 2210b
	j 2209f
2208:
2209:
	beqz t6, 2211f
2213:
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
	bnez t6, 2213b
	j 2212f
2211:
2212:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2207b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2214:
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
	bnez t5, 2214b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2215:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2216f
2218:
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
	bnez t5, 2218b
	j 2217f
2216:
2217:
	beqz t6, 2219f
2221:
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
	bnez t6, 2221b
	j 2220f
2219:
2220:
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
	bnez t2, 2215b
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
2224:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2224b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2225:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2226f
2228:
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
	bnez t5, 2228b
	j 2227f
2226:
2227:
	beqz t6, 2229f
2231:
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
	bnez t6, 2231b
	j 2230f
2229:
2230:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2225b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2232:
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
	bnez t5, 2232b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2233:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2234f
2236:
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
	bnez t5, 2236b
	j 2235f
2234:
2235:
	beqz t6, 2237f
2239:
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
	bnez t6, 2239b
	j 2238f
2237:
2238:
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
	bnez t2, 2233b
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
2240:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2240b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2241:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2241b
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
2242:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2242b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2243:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2244f
2246:
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
	bnez t5, 2246b
	j 2245f
2244:
2245:
	beqz t6, 2247f
2249:
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
	bnez t6, 2249b
	j 2248f
2247:
2248:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2243b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2250:
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
	bnez t5, 2250b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2251:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2252f
2254:
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
	bnez t5, 2254b
	j 2253f
2252:
2253:
	beqz t6, 2255f
2257:
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
	bnez t6, 2257b
	j 2256f
2255:
2256:
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
	bnez t2, 2251b
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
2260:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2260b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2261:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2262f
2264:
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
	bnez t5, 2264b
	j 2263f
2262:
2263:
	beqz t6, 2265f
2267:
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
	bnez t6, 2267b
	j 2266f
2265:
2266:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2261b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2268:
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
	bnez t5, 2268b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2269:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2270f
2272:
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
	bnez t5, 2272b
	j 2271f
2270:
2271:
	beqz t6, 2273f
2275:
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
	bnez t6, 2275b
	j 2274f
2273:
2274:
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
	bnez t2, 2269b
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
	slli t3, t0, 3
	sub a5, a5, t3
	srli a1, s7, 60
	slli t3, s5, 3
	add t3, a7, t3
	slli s4, s5, 2
	add s4, s4, s5
	add s4, a7, s4
	addi t5, t0, 0
2278:
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
	bnez t5, 2278b
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
2279:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2279b
2280:
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
	beqz t5, 2281f
2283:
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
	bnez t5, 2283b
	j 2282f
2281:
2282:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2284f
2286:
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
	bnez t5, 2286b
	j 2285f
2284:
2285:
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
	bnez a1, 2280b
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
	slli s7, s7, 4
	addi s10, s10, -1
	bnez s10, 2122b
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
2289:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2289b
2290:
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
	beqz t5, 2291f
2293:
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
	bnez t5, 2293b
	j 2292f
2291:
2292:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2294f
2296:
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
	bnez t5, 2296b
	j 2295f
2294:
2295:
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
	bnez a1, 2290b
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
2297:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2297b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2298:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2298b
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t5, t0, 0
	addi s0, zero, 0
2299:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2299b
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
2300:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2300b
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
	add t3, t3, s5
	addi t4, a7, 0
	addi t5, t0, 0
2301:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2301b
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	ld s0, 0(t3)
	xori s0, s0, 1
	sd s0, 0(t3)
	addi s9, zero, -1
	addi s4, zero, -1
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
	addi s1, zero, 0
2302:
	ld s2, 0(t3)
	ld s3, 0(t4)
	xor s2, s2, s3
	or s1, s1, s2
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2302b
	addi s2, zero, 0
	sltu s1, s2, s1
	addi s1, s1, -1
	and s4, s4, s1
	xor s4, s4, s9
	and s9, s9, s4
	addi s4, zero, -1
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
	addi s1, zero, 0
2303:
	ld s2, 0(t3)
	ld s3, 0(t4)
	xor s2, s2, s3
	or s1, s1, s2
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2303b
	addi s2, zero, 0
	sltu s1, s2, s1
	addi s1, s1, -1
	and s4, s4, s1
	xori s4, s4, -1
	and s9, s9, s4
	addi s4, zero, -1
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
	addi t5, t0, 0
	addi s1, zero, 0
2304:
	ld s2, 0(t3)
	ld s3, 0(t4)
	xor s2, s2, s3
	or s1, s1, s2
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2304b
	addi s2, zero, 0
	sltu s1, s2, s1
	addi s1, s1, -1
	and s4, s4, s1
	xori s4, s4, -1
	and s9, s9, s4
	ld s10, 0(s6)
	addi t4, a7, 0
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s11
	addi t4, t4, -1
	addi t3, s10, 0
	addi t5, s11, 0
2305:
	lbu s0, 0(t4)
	and s0, s0, s9
	sb s0, 0(t3)
	addi t3, t3, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 2305b
	addi a0, zero, 1
	and a0, a0, s9
	slli a0, a0, 1
	addi t2, zero, 3
	sub a0, t2, a0
	j 219f
218:
	addi t4, a7, 0
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s11
	addi t4, t4, -1
	addi t3, s10, 0
	addi t5, s11, 0
2306:
	lbu s0, 0(t4)
	and s0, s0, s9
	sb s0, 0(t3)
	addi t3, t3, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 2306b
	addi a0, zero, 1
	and a0, a0, s9
	addi a0, zero, 2
219:
27:
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

vg_ffdh_check_private:
	.option push
	.option arch, +m, +c
	addi t0, a7, 0
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
	sd a3, 32(s6)
	addi a4, a2, 0
	addi a3, a1, 0
	addi a2, a0, 0
	sd a5, 8(s6)
	sd a6, 16(s6)
	add t2, a2, a4
	sd t2, 24(s6)
	addi s7, a2, 0
	addi s8, a4, 0
	addi a1, a4, 0
	addi s10, a0, 0
	addi s11, a1, 0
	addi t0, a1, 7
	srli t0, t0, 3
	slli s5, t0, 3
	addi s5, s5, 16
	addi a7, s6, 256
	addi t2, zero, 24
	mul t2, t2, s5
	add s10, t2, a7
	sd s10, 0(s6)
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
	addi a0, zero, 0
	j 27f
26:
	addi s11, a6, 0
	addi a6, a5, 0
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
28:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 28b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
29:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 29b
	add t3, a7, s5
	addi t3, t3, -16
	addi s0, zero, 0
	sd s0, 0(t3)
	addi a7, s6, 256
	addi s7, a1, 0
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add t2, a4, a4
	add t2, t2, a4
	sub t2, a3, t2
	beqz t2, 210f
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t4, a7, 0
	addi t5, t0, 0
212:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 212b
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	ld s0, 0(t3)
	xori s0, s0, 1
	sd s0, 0(t3)
	addi a7, a7, 0
	add a7, a7, s5
	add a7, a7, s5
	add a7, a7, s5
	add a7, a7, s5
	add a7, a7, s5
	add a7, a7, s5
	j 211f
210:
	addi a7, a7, 0
	add a7, a7, s5
	add s7, a4, a4
	add s7, s7, a2
	addi s8, a4, 0
	addi t3, a7, 0
	addi t5, t0, 0
	addi s0, zero, 0
213:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 213b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
214:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 214b
211:
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
215:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 215b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi a7, s6, 256
	addi s9, s4, 0
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t5, t0, 0
	addi s0, zero, 0
216:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 216b
	addi s4, zero, -1
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
	addi s1, zero, 0
217:
	ld s2, 0(t3)
	ld s3, 0(t4)
	xor s2, s2, s3
	or s1, s1, s2
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 217b
	addi s2, zero, 0
	sltu s1, s2, s1
	addi s1, s1, -1
	and s4, s4, s1
	xori s4, s4, -1
	and s9, s9, s4
	addi s7, a2, 0
	addi s8, a4, 0
	addi s11, a4, 0
	addi s0, zero, 0
	beqz s9, 218f
	ld a6, 24(s6)
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
220:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 220b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
221:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 221b
	add t3, a7, s5
	addi t3, t3, -16
	addi s0, zero, 0
	sd s0, 0(t3)
	addi a7, s6, 256
	addi s7, a1, 0
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
222:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 222b
	slli t3, t0, 3
	add t3, t3, a2
	addi t3, t3, -8
	addi s0, zero, 1
	sd s0, 0(t3)
	addi a1, t0, 64
223:
	addi t3, a5, 0
	addi t4, a2, 0
	addi t5, t0, 0
	addi s4, zero, 0
224:
	ld s2, 0(t4)
	slli s3, s2, 1
	add s3, s3, s4
	srli s4, s2, 63
	sd s3, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 224b
	sd s4, 0(t3)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
225:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 225b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
226:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 226b
	addi a1, a1, -1
	bnez a1, 223b
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
	addi a0, a7, 0
227:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 227b
228:
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
	beqz t5, 229f
231:
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
	bnez t5, 231b
	j 230f
229:
230:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 232f
234:
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
	bnez t5, 234b
	j 233f
232:
233:
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
	bnez a1, 228b
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
235:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 235b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
236:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 236b
	addi a3, a2, 0
	addi a4, a2, 0
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
	addi a3, a2, 0
	addi a4, a2, 0
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
	bnez t5, 261b
	j 260f
259:
260:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 262f
264:
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
	addi a3, a2, 0
	addi a4, a2, 0
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
	addi a0, a7, 0
267:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 267b
268:
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
	beqz t5, 269f
271:
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
	bnez t5, 271b
	j 270f
269:
270:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 272f
274:
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
	bnez t5, 274b
	j 273f
272:
273:
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
	bnez a1, 268b
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
275:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 275b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
276:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 276b
	addi a3, a2, 0
	addi a4, a2, 0
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
	addi a0, a7, 0
277:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 277b
278:
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
	beqz t5, 279f
281:
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
	bnez t5, 281b
	j 280f
279:
280:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 282f
284:
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
	bnez t5, 284b
	j 283f
282:
283:
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
	bnez a1, 278b
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
285:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 285b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
286:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 286b
	ld s9, 8(s6)
	ld s10, 16(s6)
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
287:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 287b
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
288:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 288b
289:
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
	beqz t5, 290f
292:
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
	bnez t5, 292b
	j 291f
290:
291:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 293f
295:
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
	bnez t5, 295b
	j 294f
293:
294:
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
	bnez a1, 289b
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
296:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 296b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
297:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 297b
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
298:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 298b
299:
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
	beqz t5, 2100f
2102:
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
	bnez t5, 2102b
	j 2101f
2100:
2101:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2103f
2105:
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
	bnez t5, 2105b
	j 2104f
2103:
2104:
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
	bnez a1, 299b
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
2106:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2106b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2107:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2107b
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
2108:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2108b
	addi s7, zero, 2
2109:
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
2120:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2120b
	addi s7, s7, 1
	addi t2, s7, -16
	bnez t2, 2109b
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
2121:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2121b
2122:
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
2123:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2123b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2124:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2125f
2127:
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
	bnez t5, 2127b
	j 2126f
2125:
2126:
	beqz t6, 2128f
2130:
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
	bnez t6, 2130b
	j 2129f
2128:
2129:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2124b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2131:
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
	bnez t5, 2131b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2132:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2133f
2135:
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
	bnez t5, 2135b
	j 2134f
2133:
2134:
	beqz t6, 2136f
2138:
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
	bnez t6, 2138b
	j 2137f
2136:
2137:
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
	bnez t2, 2132b
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
2139:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2139b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2140:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2140b
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
2141:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2141b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2142:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2143f
2145:
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
	bnez t5, 2145b
	j 2144f
2143:
2144:
	beqz t6, 2146f
2148:
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
	bnez t6, 2148b
	j 2147f
2146:
2147:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2142b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2149:
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
	bnez t5, 2149b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2150:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2151f
2153:
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
	bnez t5, 2153b
	j 2152f
2151:
2152:
	beqz t6, 2154f
2156:
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
	bnez t6, 2156b
	j 2155f
2154:
2155:
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
	bnez t2, 2150b
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
2157:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2157b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2158:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2158b
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
2159:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2159b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2160:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2161f
2163:
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
	bnez t5, 2163b
	j 2162f
2161:
2162:
	beqz t6, 2164f
2166:
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
	bnez t6, 2166b
	j 2165f
2164:
2165:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2160b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2167:
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
	bnez t5, 2167b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2168:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2169f
2171:
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
	bnez t5, 2171b
	j 2170f
2169:
2170:
	beqz t6, 2172f
2174:
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
	bnez t6, 2174b
	j 2173f
2172:
2173:
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
	bnez t2, 2168b
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
2175:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2175b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2176:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2176b
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
2177:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2177b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2178:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2179f
2181:
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
	bnez t5, 2181b
	j 2180f
2179:
2180:
	beqz t6, 2182f
2184:
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
	bnez t6, 2184b
	j 2183f
2182:
2183:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2178b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2185:
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
	bnez t5, 2185b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2186:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2187f
2189:
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
	bnez t5, 2189b
	j 2188f
2187:
2188:
	beqz t6, 2190f
2192:
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
	bnez t6, 2192b
	j 2191f
2190:
2191:
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
	bnez t2, 2186b
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
2193:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2193b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2194:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2194b
	slli t3, t0, 3
	sub a5, a5, t3
	srli a1, s7, 60
	slli t3, s5, 3
	add t3, a7, t3
	slli s4, s5, 2
	add s4, s4, s5
	add s4, a7, s4
	addi t5, t0, 0
2195:
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
	bnez t5, 2195b
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
2196:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2196b
2197:
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
	beqz t5, 2198f
2200:
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
	bnez t5, 2200b
	j 2199f
2198:
2199:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2201f
2203:
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
	bnez t5, 2203b
	j 2202f
2201:
2202:
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
	bnez a1, 2197b
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
2204:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2204b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2205:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2205b
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
2206:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2206b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2207:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2208f
2210:
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
	bnez t5, 2210b
	j 2209f
2208:
2209:
	beqz t6, 2211f
2213:
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
	bnez t6, 2213b
	j 2212f
2211:
2212:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2207b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2214:
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
	bnez t5, 2214b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2215:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2216f
2218:
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
	bnez t5, 2218b
	j 2217f
2216:
2217:
	beqz t6, 2219f
2221:
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
	bnez t6, 2221b
	j 2220f
2219:
2220:
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
	bnez t2, 2215b
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
2224:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2224b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2225:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2226f
2228:
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
	bnez t5, 2228b
	j 2227f
2226:
2227:
	beqz t6, 2229f
2231:
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
	bnez t6, 2231b
	j 2230f
2229:
2230:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2225b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2232:
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
	bnez t5, 2232b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2233:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2234f
2236:
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
	bnez t5, 2236b
	j 2235f
2234:
2235:
	beqz t6, 2237f
2239:
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
	bnez t6, 2239b
	j 2238f
2237:
2238:
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
	bnez t2, 2233b
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
2240:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2240b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2241:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2241b
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
2242:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2242b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2243:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2244f
2246:
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
	bnez t5, 2246b
	j 2245f
2244:
2245:
	beqz t6, 2247f
2249:
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
	bnez t6, 2249b
	j 2248f
2247:
2248:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2243b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2250:
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
	bnez t5, 2250b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2251:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2252f
2254:
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
	bnez t5, 2254b
	j 2253f
2252:
2253:
	beqz t6, 2255f
2257:
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
	bnez t6, 2257b
	j 2256f
2255:
2256:
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
	bnez t2, 2251b
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
2260:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2260b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2261:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2262f
2264:
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
	bnez t5, 2264b
	j 2263f
2262:
2263:
	beqz t6, 2265f
2267:
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
	bnez t6, 2267b
	j 2266f
2265:
2266:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2261b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2268:
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
	bnez t5, 2268b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2269:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2270f
2272:
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
	bnez t5, 2272b
	j 2271f
2270:
2271:
	beqz t6, 2273f
2275:
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
	bnez t6, 2275b
	j 2274f
2273:
2274:
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
	bnez t2, 2269b
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
	slli t3, t0, 3
	sub a5, a5, t3
	srli a1, s7, 60
	slli t3, s5, 3
	add t3, a7, t3
	slli s4, s5, 2
	add s4, s4, s5
	add s4, a7, s4
	addi t5, t0, 0
2278:
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
	bnez t5, 2278b
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
2279:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2279b
2280:
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
	beqz t5, 2281f
2283:
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
	bnez t5, 2283b
	j 2282f
2281:
2282:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2284f
2286:
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
	bnez t5, 2286b
	j 2285f
2284:
2285:
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
	bnez a1, 2280b
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
	slli s7, s7, 4
	addi s10, s10, -1
	bnez s10, 2122b
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
2289:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2289b
2290:
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
	beqz t5, 2291f
2293:
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
	bnez t5, 2293b
	j 2292f
2291:
2292:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2294f
2296:
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
	bnez t5, 2296b
	j 2295f
2294:
2295:
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
	bnez a1, 2290b
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
2297:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2297b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2298:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2298b
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t5, t0, 0
	addi s0, zero, 0
2299:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2299b
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
2300:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2300b
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
	add t3, t3, s5
	addi t4, a7, 0
	addi t5, t0, 0
2301:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2301b
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	ld s0, 0(t3)
	xori s0, s0, 1
	sd s0, 0(t3)
	addi s9, zero, -1
	addi s4, zero, -1
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
	addi s1, zero, 0
2302:
	ld s2, 0(t3)
	ld s3, 0(t4)
	xor s2, s2, s3
	or s1, s1, s2
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2302b
	addi s2, zero, 0
	sltu s1, s2, s1
	addi s1, s1, -1
	and s4, s4, s1
	xor s4, s4, s9
	and s9, s9, s4
	addi s4, zero, -1
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
	addi s1, zero, 0
2303:
	ld s2, 0(t3)
	ld s3, 0(t4)
	xor s2, s2, s3
	or s1, s1, s2
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2303b
	addi s2, zero, 0
	sltu s1, s2, s1
	addi s1, s1, -1
	and s4, s4, s1
	xori s4, s4, -1
	and s9, s9, s4
	addi s4, zero, -1
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
	addi t5, t0, 0
	addi s1, zero, 0
2304:
	ld s2, 0(t3)
	ld s3, 0(t4)
	xor s2, s2, s3
	or s1, s1, s2
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2304b
	addi s2, zero, 0
	sltu s1, s2, s1
	addi s1, s1, -1
	and s4, s4, s1
	xori s4, s4, -1
	and s9, s9, s4
	ld s7, 32(s6)
	addi a7, a7, 0
	add a7, a7, s5
	add a7, a7, s5
	add a7, a7, s5
	add a7, a7, s5
	add a7, a7, s5
	add a7, a7, s5
	add a7, a7, s5
	add a7, a7, s5
	addi s8, s11, 0
	addi t3, a7, 0
	addi t5, t0, 0
	addi s0, zero, 0
2305:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2305b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
2306:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 2306b
	addi a7, s6, 256
	addi s4, zero, -1
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
	add t4, t4, s5
	addi t5, t0, 0
	addi s1, zero, 0
2307:
	ld s2, 0(t3)
	ld s3, 0(t4)
	xor s2, s2, s3
	or s1, s1, s2
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2307b
	addi s2, zero, 0
	sltu s1, s2, s1
	addi s1, s1, -1
	and s4, s4, s1
	and s9, s9, s4
	addi a0, zero, 1
	and a0, a0, s9
	j 219f
218:
	addi a0, zero, 2
219:
27:
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

vg_ffdh_generate_key_precompute:
	.option push
	.option arch, +m, +c
	addi t0, a5, 0
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
	sd a0, 0(s6)
	sd a2, 8(s6)
	sd a4, 16(s6)
	add t2, a2, a4
	sd t2, 24(s6)
	addi a0, a2, 0
	addi a1, a3, 0
	addi a2, a4, 0
	lla t5, {VG_FFDH_VETTED_GROUPS_RISCV}
	addi a5, zero, 0
	addi t3, a2, -256
	beqz t3, 20f
	addi t4, zero, 1
	j 21f
20:
	addi t0, t5, 8
	addi t2, a1, 0
	addi t4, zero, 0
22:
	sub t1, a1, t2
	add t1, a0, t1
	lbu t3, 0(t1)
	lbu t1, 0(t0)
	xor t3, t3, t1
	or t4, t4, t3
	addi t0, t0, 1
	addi t2, t2, -1
	bnez t2, 22b
21:
	addi t6, zero, 0
	sltu t6, t6, t4
	addi t6, t6, -1
	andi t6, t6, 225
	or a5, a5, t6
	addi t5, t5, 388
	addi t5, t5, 388
	addi t3, a2, -256
	beqz t3, 23f
	addi t4, zero, 1
	j 24f
23:
	addi t0, t5, 8
	addi t2, a1, 0
	addi t4, zero, 0
25:
	sub t1, a1, t2
	add t1, a0, t1
	lbu t3, 0(t1)
	lbu t1, 0(t0)
	xor t3, t3, t1
	or t4, t4, t3
	addi t0, t0, 1
	addi t2, t2, -1
	bnez t2, 25b
24:
	addi t6, zero, 0
	sltu t6, t6, t4
	addi t6, t6, -1
	andi t6, t6, 225
	or a5, a5, t6
	addi t5, t5, 388
	addi t5, t5, 388
	addi t3, a2, -384
	beqz t3, 26f
	addi t4, zero, 1
	j 27f
26:
	addi t0, t5, 8
	addi t2, a1, 0
	addi t4, zero, 0
28:
	sub t1, a1, t2
	add t1, a0, t1
	lbu t3, 0(t1)
	lbu t1, 0(t0)
	xor t3, t3, t1
	or t4, t4, t3
	addi t0, t0, 1
	addi t2, t2, -1
	bnez t2, 28b
27:
	addi t6, zero, 0
	sltu t6, t6, t4
	addi t6, t6, -1
	andi t6, t6, 275
	or a5, a5, t6
	addi t5, t5, 580
	addi t5, t5, 580
	addi t3, a2, -384
	beqz t3, 29f
	addi t4, zero, 1
	j 210f
29:
	addi t0, t5, 8
	addi t2, a1, 0
	addi t4, zero, 0
211:
	sub t1, a1, t2
	add t1, a0, t1
	lbu t3, 0(t1)
	lbu t1, 0(t0)
	xor t3, t3, t1
	or t4, t4, t3
	addi t0, t0, 1
	addi t2, t2, -1
	bnez t2, 211b
210:
	addi t6, zero, 0
	sltu t6, t6, t4
	addi t6, t6, -1
	andi t6, t6, 275
	or a5, a5, t6
	addi t5, t5, 580
	addi t5, t5, 580
	addi t3, a2, -512
	beqz t3, 212f
	addi t4, zero, 1
	j 213f
212:
	addi t0, t5, 8
	addi t2, a1, 0
	addi t4, zero, 0
214:
	sub t1, a1, t2
	add t1, a0, t1
	lbu t3, 0(t1)
	lbu t1, 0(t0)
	xor t3, t3, t1
	or t4, t4, t3
	addi t0, t0, 1
	addi t2, t2, -1
	bnez t2, 214b
213:
	addi t6, zero, 0
	sltu t6, t6, t4
	addi t6, t6, -1
	andi t6, t6, 325
	or a5, a5, t6
	addi t5, t5, 772
	addi t5, t5, 772
	addi t3, a2, -512
	beqz t3, 215f
	addi t4, zero, 1
	j 216f
215:
	addi t0, t5, 8
	addi t2, a1, 0
	addi t4, zero, 0
217:
	sub t1, a1, t2
	add t1, a0, t1
	lbu t3, 0(t1)
	lbu t1, 0(t0)
	xor t3, t3, t1
	or t4, t4, t3
	addi t0, t0, 1
	addi t2, t2, -1
	bnez t2, 217b
216:
	addi t6, zero, 0
	sltu t6, t6, t4
	addi t6, t6, -1
	andi t6, t6, 325
	or a5, a5, t6
	addi t5, t5, 772
	addi t5, t5, 772
	addi t3, a2, -768
	beqz t3, 218f
	addi t4, zero, 1
	j 219f
218:
	addi t0, t5, 8
	addi t2, a1, 0
	addi t4, zero, 0
220:
	sub t1, a1, t2
	add t1, a0, t1
	lbu t3, 0(t1)
	lbu t1, 0(t0)
	xor t3, t3, t1
	or t4, t4, t3
	addi t0, t0, 1
	addi t2, t2, -1
	bnez t2, 220b
219:
	addi t6, zero, 0
	sltu t6, t6, t4
	addi t6, t6, -1
	andi t6, t6, 375
	or a5, a5, t6
	addi t5, t5, 1156
	addi t5, t5, 1156
	addi t3, a2, -768
	beqz t3, 221f
	addi t4, zero, 1
	j 222f
221:
	addi t0, t5, 8
	addi t2, a1, 0
	addi t4, zero, 0
223:
	sub t1, a1, t2
	add t1, a0, t1
	lbu t3, 0(t1)
	lbu t1, 0(t0)
	xor t3, t3, t1
	or t4, t4, t3
	addi t0, t0, 1
	addi t2, t2, -1
	bnez t2, 223b
222:
	addi t6, zero, 0
	sltu t6, t6, t4
	addi t6, t6, -1
	andi t6, t6, 375
	or a5, a5, t6
	addi t5, t5, 1156
	addi t5, t5, 1156
	addi t3, a2, -1024
	beqz t3, 224f
	addi t4, zero, 1
	j 225f
224:
	addi t0, t5, 8
	addi t2, a1, 0
	addi t4, zero, 0
226:
	sub t1, a1, t2
	add t1, a0, t1
	lbu t3, 0(t1)
	lbu t1, 0(t0)
	xor t3, t3, t1
	or t4, t4, t3
	addi t0, t0, 1
	addi t2, t2, -1
	bnez t2, 226b
225:
	addi t6, zero, 0
	sltu t6, t6, t4
	addi t6, t6, -1
	andi t6, t6, 400
	or a5, a5, t6
	addi t5, t5, 1540
	addi t5, t5, 1540
	addi t3, a2, -1024
	beqz t3, 227f
	addi t4, zero, 1
	j 228f
227:
	addi t0, t5, 8
	addi t2, a1, 0
	addi t4, zero, 0
229:
	sub t1, a1, t2
	add t1, a0, t1
	lbu t3, 0(t1)
	lbu t1, 0(t0)
	xor t3, t3, t1
	or t4, t4, t3
	addi t0, t0, 1
	addi t2, t2, -1
	bnez t2, 229b
228:
	addi t6, zero, 0
	sltu t6, t6, t4
	addi t6, t6, -1
	andi t6, t6, 400
	or a5, a5, t6
	addi t5, t5, 1540
	addi t5, t5, 1540
	addi a2, a0, 0
	addi s7, a0, 0
	addi s8, a4, 0
	addi a1, a4, 0
	ld a0, 0(s6)
	addi s10, a0, 0
	addi s11, a1, 0
	addi t0, a1, 7
	srli t0, t0, 3
	slli s5, t0, 3
	addi s5, s5, 16
	addi a7, s6, 256
	addi t3, a7, 0
	addi t5, t0, 0
	addi s0, zero, 0
230:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 230b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
231:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 231b
	add t4, s7, s8
	addi t4, t4, -1
	lbu s0, 0(t4)
	andi s0, s0, 1
	xori s0, s0, 1
	lbu t4, 0(s7)
	beqz t4, 232f
	j 233f
232:
	addi s0, zero, 1
233:
	addi t5, s8, -64
	beqz t5, 234f
	j 235f
234:
	srli t4, t4, 7
	xori t4, t4, 1
	or s0, s0, t4
235:
	beqz s0, 236f
	addi a0, zero, 0
	j 237f
236:
	add t2, a4, a4
	add t2, t2, a4
	sub t2, a3, t2
	beqz t2, 238f
	addi t3, a2, 0
	j 239f
238:
	add t3, a4, a4
	add t3, t3, a2
239:
	addi t5, a4, 0
	addi t4, zero, 0
	addi s1, a4, -1
	addi s2, zero, 0
	addi s3, zero, 0
240:
	lbu t6, 0(t3)
	addi t2, zero, 0
	sub s4, t2, t6
	or s4, s4, t6
	srli s4, s4, 63
	sub s4, t2, s4
	or s4, s4, s3
	xor s4, s4, s3
	xor s0, s1, t4
	and s0, s0, s4
	xor s1, s1, s0
	xor s0, s2, t6
	and s0, s0, s4
	xor s2, s2, s0
	or s3, s3, s4
	addi t3, t3, 1
	addi t4, t4, 1
	addi t5, t5, -1
	bnez t5, 240b
	addi t2, zero, 0
	addi t3, zero, 0
	sltu t3, t3, s2
	add t2, t2, t3
	addi t3, zero, 1
	sltu t3, t3, s2
	add t2, t2, t3
	addi t3, zero, 3
	sltu t3, t3, s2
	add t2, t2, t3
	addi t3, zero, 7
	sltu t3, t3, s2
	add t2, t2, t3
	addi t3, zero, 15
	sltu t3, t3, s2
	add t2, t2, t3
	addi t3, zero, 31
	sltu t3, t3, s2
	add t2, t2, t3
	addi t3, zero, 63
	sltu t3, t3, s2
	add t2, t2, t3
	addi t3, zero, 127
	sltu t3, t3, s2
	add t2, t2, t3
	sub s3, a4, s1
	slli s3, s3, 3
	addi s3, s3, -8
	add s3, s3, t2
	sltu t3, a5, s3
	beqz a5, 241f
	beqz t3, 243f
	addi s9, a5, 0
	j 244f
243:
	addi s9, s3, 0
244:
	j 242f
241:
	addi s9, s3, 0
242:
	addi t3, s9, 7
	srli t3, t3, 3
	addi t4, s9, 4
	lui t5, 13
	addi t5, t5, -819
	mul t4, t4, t5
	srli t4, t4, 18
	sd s9, 0(s10)
	sd t3, 8(s10)
	sd t4, 16(s10)
	addi s9, t4, 0
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
245:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 245b
	slli t3, t0, 3
	add t3, t3, a2
	addi t3, t3, -8
	addi s0, zero, 1
	sd s0, 0(t3)
	addi a1, t0, 64
246:
	addi t3, a5, 0
	addi t4, a2, 0
	addi t5, t0, 0
	addi s4, zero, 0
247:
	ld s2, 0(t4)
	slli s3, s2, 1
	add s3, s3, s4
	srli s4, s2, 63
	sd s3, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 247b
	sd s4, 0(t3)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
248:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 248b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
249:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 249b
	addi a1, a1, -1
	bnez a1, 246b
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
	addi a0, a7, 0
250:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 250b
251:
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
	beqz t5, 252f
254:
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
	bnez t5, 254b
	j 253f
252:
253:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 255f
257:
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
	bnez t5, 257b
	j 256f
255:
256:
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
	bnez a1, 251b
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
258:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 258b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
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
	addi a3, a2, 0
	addi a4, a2, 0
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
	addi a0, a7, 0
260:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 260b
261:
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
	beqz t5, 262f
264:
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
	bnez t5, 264b
	j 263f
262:
263:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 265f
267:
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
	bnez t5, 267b
	j 266f
265:
266:
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
	bnez a1, 261b
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
	addi a3, a2, 0
	addi a4, a2, 0
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
	addi a3, a2, 0
	addi a4, a2, 0
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
	addi a3, a2, 0
	addi a4, a2, 0
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
	addi a0, a7, 0
290:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 290b
291:
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
	beqz t5, 292f
294:
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
	bnez t5, 294b
	j 293f
292:
293:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 295f
297:
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
	bnez t5, 297b
	j 296f
295:
296:
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
	bnez a1, 291b
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
	bnez t5, 2104b
	j 2103f
2102:
2103:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2105f
2107:
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
	addi t2, zero, 0
	mul t2, t2, t0
	slli t2, t2, 3
	add t3, s10, t2
	addi t3, t3, 24
	addi t4, a7, 0
	addi t5, t0, 0
2110:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2110b
	addi t2, zero, 1
	mul t2, t2, t0
	slli t2, t2, 3
	add t3, s10, t2
	addi t3, t3, 24
	addi t4, a7, 0
	add t4, t4, s5
	addi t5, t0, 0
2111:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2111b
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
2112:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2112b
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
	addi a0, a7, 0
2113:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2113b
2114:
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
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2117b
	j 2116f
2115:
2116:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2118f
2120:
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
	bnez t5, 2120b
	j 2119f
2118:
2119:
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
	bnez a1, 2114b
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
2121:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2121b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2122:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2122b
	addi t2, zero, 2
	mul t2, t2, t0
	slli t2, t2, 3
	add t3, s10, t2
	addi t3, t3, 24
	addi t4, a7, 0
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	addi t5, t0, 0
2123:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2123b
	add a6, s7, s11
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
2124:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2124b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
2125:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 2125b
	add t3, a7, s5
	addi t3, t3, -16
	addi s0, zero, 0
	sd s0, 0(t3)
	addi a7, s6, 256
	addi s7, a1, 0
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
	bnez t5, 2130b
	j 2129f
2128:
2129:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2131f
2133:
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
	addi t2, zero, 3
	mul t2, t2, t0
	slli t2, t2, 3
	add t3, s10, t2
	addi t3, t3, 24
	addi t4, a7, 0
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	addi t5, t0, 0
2136:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2136b
	addi s4, zero, -1
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
	addi s7, zero, 2
2138:
	addi s8, s9, 0
2139:
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
	addi s8, s8, -1
	bnez s8, 2139b
	addi t2, s7, 2
	mul t2, t2, t0
	slli t2, t2, 3
	add t3, s10, t2
	addi t3, t3, 24
	addi t4, a7, 0
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	addi t5, t0, 0
2150:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2150b
	addi s8, zero, 1
2151:
	addi t2, s8, 2
	mul t2, t2, t0
	slli t2, t2, 3
	add t4, s10, t2
	addi t4, t4, 24
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t5, t0, 0
2152:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2152b
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
2153:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2153b
2154:
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
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2157b
	j 2156f
2155:
2156:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2158f
2160:
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
	bnez t5, 2160b
	j 2159f
2158:
2159:
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
	bnez a1, 2154b
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
	add t2, s8, s7
	addi t2, t2, 2
	mul t2, t2, t0
	slli t2, t2, 3
	add t3, s10, t2
	addi t3, t3, 24
	addi t4, a7, 0
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	addi t5, t0, 0
2163:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2163b
	addi s8, s8, 1
	sub t2, s8, s7
	bnez t2, 2151b
	add s7, s7, s7
	addi t2, s7, -32
	bnez t2, 2138b
	addi a0, zero, 1
237:
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

vg_ffdh_generate_key_cached:
	.option push
	.option arch, +m, +c
	addi t0, sp, 8
	ld t0, 0(t0)
	addi t1, sp, 24
	ld t1, 0(t1)
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
	ld t2, 0(t1)
	ld t3, 8(t1)
	ld t4, 16(t1)
	sd t1, 32(s6)
	sd t2, 40(s6)
	sd t3, 48(s6)
	sd t4, 56(s6)
	sd a2, 0(s6)
	sd a0, 8(s6)
	sd a6, 16(s6)
	add t2, a4, a6
	sd t2, 24(s6)
	addi t1, a7, 0
	addi a3, a5, 0
	addi a5, a0, 0
	addi a0, a2, 0
	addi a2, a4, 0
	addi a4, a6, 0
	addi s7, a2, 0
	addi s8, a4, 0
	addi a1, a4, 0
	addi s10, a0, 0
	addi s11, a1, 0
	addi t0, a1, 7
	srli t0, t0, 3
	slli s5, t0, 3
	addi s5, s5, 16
	addi a7, s6, 256
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
	addi a0, zero, 0
	j 27f
26:
	ld t2, 48(s6)
	slli t2, t2, 3
	ld t3, 40(s6)
	sub t2, t2, t3
	addi s2, zero, 255
	srl s2, s2, t2
	ld s1, 48(s6)
	sub s1, a4, s1
	addi t5, a4, 0
	addi t4, zero, 0
	addi a0, a5, 0
28:
	lbu t6, 0(t1)
	addi t2, zero, 0
	sub s4, t4, s1
	srli s4, s4, 63
	sub s4, t2, s4
	xor s0, t4, s1
	addi s0, s0, -1
	srli s0, s0, 63
	sub s0, t2, s0
	addi s3, zero, 255
	xor a1, s3, s2
	and a1, a1, s0
	xor a1, a1, s3
	or a1, a1, s4
	xor a1, a1, s4
	and t6, t6, a1
	sb t6, 0(a0)
	addi t1, t1, 1
	addi a0, a0, 1
	addi t4, t4, 1
	addi t5, t5, -1
	bnez t5, 28b
	addi s0, zero, 0
	addi s11, a6, 0
	addi a6, a5, 0
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
29:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 29b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
210:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 210b
	add t3, a7, s5
	addi t3, t3, -16
	addi s0, zero, 0
	sd s0, 0(t3)
	addi a7, s6, 256
	addi s7, a1, 0
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add t2, a4, a4
	add t2, t2, a4
	sub t2, a3, t2
	beqz t2, 211f
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t4, a7, 0
	addi t5, t0, 0
213:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 213b
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	ld s0, 0(t3)
	xori s0, s0, 1
	sd s0, 0(t3)
	addi a7, a7, 0
	add a7, a7, s5
	add a7, a7, s5
	add a7, a7, s5
	add a7, a7, s5
	add a7, a7, s5
	add a7, a7, s5
	j 212f
211:
	addi a7, a7, 0
	add a7, a7, s5
	add s7, a4, a4
	add s7, s7, a2
	addi s8, a4, 0
	addi t3, a7, 0
	addi t5, t0, 0
	addi s0, zero, 0
214:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 214b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
215:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 215b
212:
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
216:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 216b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi a7, s6, 256
	addi s9, s4, 0
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t5, t0, 0
	addi s0, zero, 0
217:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 217b
	addi s4, zero, -1
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
	addi s1, zero, 0
218:
	ld s2, 0(t3)
	ld s3, 0(t4)
	xor s2, s2, s3
	or s1, s1, s2
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 218b
	addi s2, zero, 0
	sltu s1, s2, s1
	addi s1, s1, -1
	and s4, s4, s1
	xori s4, s4, -1
	and s9, s9, s4
	addi s7, a2, 0
	addi s8, a4, 0
	addi s11, a4, 0
	addi s0, zero, 0
	beqz s9, 219f
	ld s10, 32(s6)
	ld s8, 8(s6)
	ld s7, 56(s6)
	addi t2, zero, 1
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
	mul t2, t2, t0
	slli t2, t2, 3
	add t4, s10, t2
	addi t4, t4, 24
	addi t3, a7, 0
	add t3, t3, s5
	addi t5, t0, 0
221:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 221b
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
222:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 222b
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
	addi s9, s7, 0
233:
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
234:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 234b
235:
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
	beqz t5, 236f
238:
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
	bnez t5, 238b
	j 237f
236:
237:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 239f
241:
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
	bnez t5, 241b
	j 240f
239:
240:
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
	bnez a1, 235b
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
242:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 242b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
243:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 243b
	addi a1, zero, 0
	addi t6, s9, -1
	slli t2, s11, 3
	bltu t6, t2, 244f
	addi t5, zero, 0
	j 245f
244:
	srli t2, t6, 3
	sub t2, s11, t2
	addi t2, t2, -1
	add t2, s8, t2
	lbu t5, 0(t2)
	andi t2, t6, 7
	srl t5, t5, t2
	andi t5, t5, 1
245:
	or a1, a1, t5
	add t6, t6, s7
	slli t2, s11, 3
	bltu t6, t2, 246f
	addi t5, zero, 0
	j 247f
246:
	srli t2, t6, 3
	sub t2, s11, t2
	addi t2, t2, -1
	add t2, s8, t2
	lbu t5, 0(t2)
	andi t2, t6, 7
	srl t5, t5, t2
	andi t5, t5, 1
247:
	slli t5, t5, 1
	or a1, a1, t5
	add t6, t6, s7
	slli t2, s11, 3
	bltu t6, t2, 248f
	addi t5, zero, 0
	j 249f
248:
	srli t2, t6, 3
	sub t2, s11, t2
	addi t2, t2, -1
	add t2, s8, t2
	lbu t5, 0(t2)
	andi t2, t6, 7
	srl t5, t5, t2
	andi t5, t5, 1
249:
	slli t5, t5, 2
	or a1, a1, t5
	add t6, t6, s7
	slli t2, s11, 3
	bltu t6, t2, 250f
	addi t5, zero, 0
	j 251f
250:
	srli t2, t6, 3
	sub t2, s11, t2
	addi t2, t2, -1
	add t2, s8, t2
	lbu t5, 0(t2)
	andi t2, t6, 7
	srl t5, t5, t2
	andi t5, t5, 1
251:
	slli t5, t5, 3
	or a1, a1, t5
	add t6, t6, s7
	slli t2, s11, 3
	bltu t6, t2, 252f
	addi t5, zero, 0
	j 253f
252:
	srli t2, t6, 3
	sub t2, s11, t2
	addi t2, t2, -1
	add t2, s8, t2
	lbu t5, 0(t2)
	andi t2, t6, 7
	srl t5, t5, t2
	andi t5, t5, 1
253:
	slli t5, t5, 4
	or a1, a1, t5
	add t6, t6, s7
	addi t3, a7, 0
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
	addi a3, zero, 0
255:
	addi t2, a3, 2
	mul t2, t2, t0
	slli t2, t2, 3
	add t4, s10, t2
	addi t4, t4, 24
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t5, t0, 0
256:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 256b
	xor t2, a3, a1
	addi t2, t2, -1
	srli t2, t2, 63
	addi t3, zero, 0
	sub s4, t3, t2
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
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
	addi a3, a3, 1
	addi t2, a3, 2
	mul t2, t2, t0
	slli t2, t2, 3
	add t4, s10, t2
	addi t4, t4, 24
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t5, t0, 0
258:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 258b
	xor t2, a3, a1
	addi t2, t2, -1
	srli t2, t2, 63
	addi t3, zero, 0
	sub s4, t3, t2
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
	addi a2, a7, 0
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
	addi a3, a3, 1
	addi t2, a3, -32
	bnez t2, 255b
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
260:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 260b
261:
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
	beqz t5, 262f
264:
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
	bnez t5, 264b
	j 263f
262:
263:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 265f
267:
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
	bnez t5, 267b
	j 266f
265:
266:
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
	bnez a1, 261b
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
	addi s9, s9, -1
	bnez s9, 233b
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
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t5, t0, 0
	addi s0, zero, 0
280:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 280b
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
	add t3, t3, s5
	addi t4, a7, 0
	addi t5, t0, 0
282:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 282b
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	ld s0, 0(t3)
	xori s0, s0, 1
	sd s0, 0(t3)
	addi s9, zero, -1
	addi s4, zero, -1
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
	addi s1, zero, 0
283:
	ld s2, 0(t3)
	ld s3, 0(t4)
	xor s2, s2, s3
	or s1, s1, s2
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 283b
	addi s2, zero, 0
	sltu s1, s2, s1
	addi s1, s1, -1
	and s4, s4, s1
	xor s4, s4, s9
	and s9, s9, s4
	addi s4, zero, -1
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
	addi s1, zero, 0
284:
	ld s2, 0(t3)
	ld s3, 0(t4)
	xor s2, s2, s3
	or s1, s1, s2
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 284b
	addi s2, zero, 0
	sltu s1, s2, s1
	addi s1, s1, -1
	and s4, s4, s1
	xori s4, s4, -1
	and s9, s9, s4
	addi s4, zero, -1
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
	addi t5, t0, 0
	addi s1, zero, 0
285:
	ld s2, 0(t3)
	ld s3, 0(t4)
	xor s2, s2, s3
	or s1, s1, s2
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 285b
	addi s2, zero, 0
	sltu s1, s2, s1
	addi s1, s1, -1
	and s4, s4, s1
	xori s4, s4, -1
	and s9, s9, s4
	ld s10, 0(s6)
	addi t4, a7, 0
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s11
	addi t4, t4, -1
	addi t3, s10, 0
	addi t5, s11, 0
286:
	lbu s0, 0(t4)
	and s0, s0, s9
	sb s0, 0(t3)
	addi t3, t3, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 286b
	addi a0, zero, 1
	and a0, a0, s9
	slli a0, a0, 1
	addi t2, zero, 3
	sub a0, t2, a0
	j 220f
219:
	addi t4, a7, 0
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s11
	addi t4, t4, -1
	addi t3, s10, 0
	addi t5, s11, 0
287:
	lbu s0, 0(t4)
	and s0, s0, s9
	sb s0, 0(t3)
	addi t3, t3, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 287b
	addi a0, zero, 1
	and a0, a0, s9
	addi a0, zero, 2
220:
	addi t2, a0, -1
	addi t3, zero, 0
	sub s4, t3, t2
	or s4, s4, t2
	srli s4, s4, 63
	addi s4, s4, -1
	ld a1, 8(s6)
	ld t5, 16(s6)
288:
	lbu t6, 0(a1)
	and t6, t6, s4
	sb t6, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 288b
27:
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

vg_ffdh_generate_key_search_cached:
	.option push
	.option arch, +m, +c
	addi t1, sp, 0
	ld t2, 32(t1)
	ld t3, 0(t1)
	ld t4, 8(t1)
	ld t5, 16(t1)
	ld t6, 24(t1)
	sd s0, 32(t2)
	addi s0, t2, 0
	sd a0, 40(s0)
	sd a2, 48(s0)
	sd a5, 56(s0)
	sd a6, 64(s0)
	sd a4, 120(s0)
	sd t3, 72(s0)
	sd t4, 80(s0)
	addi t1, zero, 0
	sd t1, 88(s0)
	sd t5, 96(s0)
	sd t6, 104(s0)
	addi sp, sp, -16
	sd ra, 8(sp)
20:
	ld t0, 0(s0)
	beqz t0, 21f
	ld t0, 8(s0)
	beqz t0, 23f
	ld t0, 80(s0)
	ld t1, 16(s0)
	bltu t0, t1, 25f
	addi sp, sp, -48
	addi t3, sp, 104
	ld t4, 0(t3)
	ld t5, 8(t3)
	ld a0, 40(s0)
	ld a1, 16(s0)
	ld a2, 48(s0)
	ld a3, 16(s0)
	ld a4, 56(s0)
	ld a5, 64(s0)
	ld a6, 16(s0)
	ld a7, 72(s0)
	ld t0, 96(s0)
	ld t1, 104(s0)
	addi t2, sp, 0
	sd a1, 0(t2)
	sd t0, 8(t2)
	sd t1, 16(t2)
	sd t4, 24(t2)
	sd t5, 32(t2)
	call {vg_ffdh_generate_key_cached}
	addi sp, sp, 48
	slli t0, a0, 32
	srli t0, t0, 32
	ld t1, 16(s0)
	ld t2, 72(s0)
	ld t3, 80(s0)
	ld t4, 88(s0)
	add t2, t2, t1
	sub t3, t3, t1
	add t4, t4, t1
	sd t2, 72(s0)
	sd t3, 80(s0)
	sd t4, 88(s0)
	addi t1, t0, -1
	beqz t1, 27f
	addi t1, t0, -2
	beqz t1, 29f
	addi t1, t0, -3
	beqz t1, 211f
	addi t0, zero, 0
	addi t1, zero, 3
	sd t0, 0(s0)
	sd t0, 8(s0)
	sd t0, 24(s0)
	sd t1, 112(s0)
	ld t0, 40(s0)
	ld t1, 16(s0)
	addi t2, zero, 0
213:
	sb t2, 0(t0)
	addi t0, t0, 1
	addi t1, t1, -1
	bnez t1, 213b
	ld t0, 48(s0)
	ld t1, 16(s0)
	addi t2, zero, 0
214:
	sb t2, 0(t0)
	addi t0, t0, 1
	addi t1, t1, -1
	bnez t1, 214b
	j 212f
211:
	ld t1, 0(s0)
	addi t1, t1, -1
	addi t2, zero, 128
	addi t3, zero, 4
	sd t1, 0(s0)
	sd t2, 8(s0)
	sd t3, 112(s0)
212:
	j 210f
29:
	ld t1, 8(s0)
	addi t1, t1, -1
	addi t2, zero, 4
	sd t1, 8(s0)
	sd t2, 112(s0)
210:
	j 28f
27:
	addi t0, zero, 0
	addi t1, zero, 1
	sd t0, 0(s0)
	sd t0, 8(s0)
	sd t0, 24(s0)
	sd t1, 112(s0)
28:
	j 26f
25:
	ld t1, 16(s0)
	addi t2, zero, 0
	sd t1, 24(s0)
	sd t2, 112(s0)
	ld t0, 40(s0)
	ld t1, 16(s0)
	addi t2, zero, 0
215:
	sb t2, 0(t0)
	addi t0, t0, 1
	addi t1, t1, -1
	bnez t1, 215b
	ld t0, 48(s0)
	ld t1, 16(s0)
	addi t2, zero, 0
216:
	sb t2, 0(t0)
	addi t0, t0, 1
	addi t1, t1, -1
	bnez t1, 216b
26:
	j 24f
23:
	addi t0, zero, 0
	addi t1, zero, 3
	sd t0, 0(s0)
	sd t0, 8(s0)
	sd t0, 24(s0)
	sd t1, 112(s0)
	ld t0, 40(s0)
	ld t1, 16(s0)
	addi t2, zero, 0
217:
	sb t2, 0(t0)
	addi t0, t0, 1
	addi t1, t1, -1
	bnez t1, 217b
	ld t0, 48(s0)
	ld t1, 16(s0)
	addi t2, zero, 0
218:
	sb t2, 0(t0)
	addi t0, t0, 1
	addi t1, t1, -1
	bnez t1, 218b
24:
	j 22f
21:
	addi t0, zero, 0
	addi t1, zero, 3
	sd t0, 0(s0)
	sd t0, 8(s0)
	sd t0, 24(s0)
	sd t1, 112(s0)
	ld t0, 40(s0)
	ld t1, 16(s0)
	addi t2, zero, 0
219:
	sb t2, 0(t0)
	addi t0, t0, 1
	addi t1, t1, -1
	bnez t1, 219b
	ld t0, 48(s0)
	ld t1, 16(s0)
	addi t2, zero, 0
220:
	sb t2, 0(t0)
	addi t0, t0, 1
	addi t1, t1, -1
	bnez t1, 220b
22:
	ld t0, 112(s0)
	addi t0, t0, -4
	beqz t0, 20b
	ld ra, 8(sp)
	addi sp, sp, 16
	ld t0, 120(s0)
	ld t1, 88(s0)
	ld a0, 112(s0)
	sd t1, 0(t0)
	ld s0, 32(s0)
	ret
	.option pop

vg_ffdh_generate_parameters:
	.option push
	.option arch, +m, +c
	addi t1, sp, 0
	ld t2, 8(t1)
	ld t3, 0(t1)
	sd s0, 32(t2)
	addi s0, t2, 0
	sd a0, 40(s0)
	sd a1, 48(s0)
	sd a2, 56(s0)
	sd a3, 64(s0)
	slli t4, a4, 32
	srli t4, t4, 32
	sd t4, 72(s0)
	sd a5, 80(s0)
	sd a6, 88(s0)
	addi t1, zero, 0
	sd t1, 96(s0)
	sd a7, 104(s0)
	sd t3, 120(s0)
	addi sp, sp, -16
	sd ra, 8(sp)
20:
	ld t0, 0(s0)
	beqz t0, 21f
	addi sp, sp, -16
	ld a0, 40(s0)
	ld a1, 48(s0)
	ld a2, 56(s0)
	ld a3, 64(s0)
	ld a4, 72(s0)
	ld a5, 80(s0)
	ld a6, 88(s0)
	ld a7, 104(s0)
	ld t0, 120(s0)
	addi t1, sp, 0
	sd t0, 0(t1)
	call {vg_ffdh_parameter_candidate_sieved}
	addi sp, sp, 16
	slli t0, a0, 32
	srli t0, t0, 32
	ld t2, 56(s0)
	ld t2, 0(t2)
	addi t1, t0, -1
	beqz t1, 23f
	addi t1, t0, -2
	beqz t1, 25f
	ld t0, 88(s0)
	ld t1, 16(s0)
	bltu t0, t1, 27f
	addi t4, zero, 0
	addi t5, zero, 3
	sd t4, 0(s0)
	sd t4, 24(s0)
	sd t5, 112(s0)
	ld t0, 40(s0)
	ld t1, 48(s0)
	addi t2, zero, 0
29:
	sb t2, 0(t0)
	addi t0, t0, 1
	addi t1, t1, -1
	bnez t1, 29b
	j 28f
27:
	ld t0, 88(s0)
	ld t1, 48(s0)
	ld t2, 16(s0)
	slli t1, t1, 8
	sltu t4, t0, t1
	addi t4, t4, -1
	xor t3, t0, t1
	and t3, t3, t4
	xor t3, t3, t1
	add t3, t3, t3
	sltu t4, t3, t2
	addi t4, t4, -1
	xor t5, t3, t2
	and t5, t5, t4
	xor t5, t5, t3
	addi t6, zero, 0
	sd t5, 24(s0)
	sd t6, 112(s0)
28:
	j 26f
25:
	ld t3, 96(s0)
	ld t4, 80(s0)
	ld t5, 88(s0)
	ld t6, 0(s0)
	add t3, t3, t2
	add t4, t4, t2
	sub t5, t5, t2
	addi t6, t6, -1
	addi t1, zero, 4
	sd t3, 96(s0)
	sd t4, 80(s0)
	sd t5, 88(s0)
	sd t6, 0(s0)
	sd t1, 112(s0)
26:
	j 24f
23:
	ld t3, 96(s0)
	add t3, t3, t2
	sd t3, 96(s0)
	addi t4, zero, 0
	addi t5, zero, 1
	sd t4, 0(s0)
	sd t4, 24(s0)
	sd t5, 112(s0)
24:
	j 22f
21:
	addi t4, zero, 0
	addi t5, zero, 3
	sd t4, 0(s0)
	sd t4, 24(s0)
	sd t5, 112(s0)
	ld t0, 40(s0)
	ld t1, 48(s0)
	addi t2, zero, 0
210:
	sb t2, 0(t0)
	addi t0, t0, 1
	addi t1, t1, -1
	bnez t1, 210b
22:
	ld t0, 112(s0)
	addi t0, t0, -4
	beqz t0, 20b
	ld ra, 8(sp)
	addi sp, sp, 16
	ld t0, 56(s0)
	ld t1, 96(s0)
	ld a0, 112(s0)
	sd t1, 0(t0)
	ld s0, 32(s0)
	ret
	.option pop
