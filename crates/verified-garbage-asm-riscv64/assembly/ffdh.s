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

vg_ffdh_check_public:
	.option push
	.option arch, +m, +c
	addi t2, a5, 0
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
	bnez t5, 230b
	j 229f
228:
229:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 231f
233:
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
	bnez t5, 240b
	j 239f
238:
239:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 241f
243:
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
	bnez t5, 260b
	j 259f
258:
259:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 261f
263:
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
	bnez t5, 270b
	j 269f
268:
269:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 271f
273:
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
	bnez t5, 280b
	j 279f
278:
279:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 281f
283:
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
	call {vg_bignum_pow_win}
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
288:
	ld s2, 0(t3)
	ld s3, 0(t4)
	xor s2, s2, s3
	or s1, s1, s2
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 288b
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
	addi t2, a3, 0
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
	bnez t5, 294b
	j 293f
292:
293:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 295f
297:
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
	bnez t5, 2114b
	j 2113f
2112:
2113:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2115f
2117:
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
	bnez t5, 2124b
	j 2123f
2122:
2123:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2125f
2127:
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
	bnez t5, 2134b
	j 2133f
2132:
2133:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2135f
2137:
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
	call {vg_bignum_pow_win}
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
2152:
	ld s2, 0(t3)
	ld s3, 0(t4)
	xor s2, s2, s3
	or s1, s1, s2
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2152b
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
	ld ra, 216(s6)
	ld s6, 224(s6)
	j 231f
230:
	addi a0, zero, 1
231:
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

vg_ffdh_exchange:
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
	bnez t5, 219b
	j 218f
217:
218:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 220f
222:
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
	bnez t5, 229b
	j 228f
227:
228:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 230f
232:
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
	bnez t5, 239b
	j 238f
237:
238:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 240f
242:
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
	bnez t5, 249b
	j 248f
247:
248:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 250f
252:
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
	bnez t5, 259b
	j 258f
257:
258:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 260f
262:
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
	bnez t5, 269b
	j 268f
267:
268:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 270f
272:
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
	call {vg_bignum_pow_win}
	addi t3, a7, 0
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
277:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 277b
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
278:
	ld s2, 0(t3)
	ld s3, 0(t4)
	xor s2, s2, s3
	or s1, s1, s2
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 278b
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
281:
	lbu s0, 0(t4)
	and s0, s0, s9
	sb s0, 0(t3)
	addi t3, t3, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 281b
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

vg_ffdh_derive_public:
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
	bnez t5, 231b
	j 230f
229:
230:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 232f
234:
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
	bnez t5, 241b
	j 240f
239:
240:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 242f
244:
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
	bnez t5, 251b
	j 250f
249:
250:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 252f
254:
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
	bnez t5, 271b
	j 270f
269:
270:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 272f
274:
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
	bnez t5, 281b
	j 280f
279:
280:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 282f
284:
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
	call {vg_bignum_pow_win}
	addi t3, a7, 0
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
	addi t5, t0, 0
	addi s0, zero, 0
288:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 288b
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
289:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 289b
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
290:
	ld s2, 0(t3)
	ld s3, 0(t4)
	xor s2, s2, s3
	or s1, s1, s2
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 290b
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
291:
	ld s2, 0(t3)
	ld s3, 0(t4)
	xor s2, s2, s3
	or s1, s1, s2
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 291b
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
292:
	ld s2, 0(t3)
	ld s3, 0(t4)
	xor s2, s2, s3
	or s1, s1, s2
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 292b
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
293:
	lbu s0, 0(t4)
	and s0, s0, s9
	sb s0, 0(t3)
	addi t3, t3, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 293b
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
294:
	lbu s0, 0(t4)
	and s0, s0, s9
	sb s0, 0(t3)
	addi t3, t3, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 294b
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

vg_ffdh_check_private:
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
	bnez t5, 231b
	j 230f
229:
230:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 232f
234:
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
	bnez t5, 241b
	j 240f
239:
240:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 242f
244:
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
	bnez t5, 251b
	j 250f
249:
250:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 252f
254:
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
	bnez t5, 271b
	j 270f
269:
270:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 272f
274:
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
	bnez t5, 281b
	j 280f
279:
280:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 282f
284:
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
	call {vg_bignum_pow_win}
	addi t3, a7, 0
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
	addi t5, t0, 0
	addi s0, zero, 0
288:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 288b
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
289:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 289b
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
290:
	ld s2, 0(t3)
	ld s3, 0(t4)
	xor s2, s2, s3
	or s1, s1, s2
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 290b
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
291:
	ld s2, 0(t3)
	ld s3, 0(t4)
	xor s2, s2, s3
	or s1, s1, s2
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 291b
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
292:
	ld s2, 0(t3)
	ld s3, 0(t4)
	xor s2, s2, s3
	or s1, s1, s2
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 292b
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
293:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 293b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
294:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 294b
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
295:
	ld s2, 0(t3)
	ld s3, 0(t4)
	xor s2, s2, s3
	or s1, s1, s2
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 295b
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
	bnez t5, 254b
	j 253f
252:
253:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 255f
257:
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
	bnez t5, 264b
	j 263f
262:
263:
	addi t5, t0, -1
	srli t5, t5, 2
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
	bnez t5, 274b
	j 273f
272:
273:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 275f
277:
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
	bnez t5, 284b
	j 283f
282:
283:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 285f
287:
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
	bnez t5, 294b
	j 293f
292:
293:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 295f
297:
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
	bnez t5, 2117b
	j 2116f
2115:
2116:
	addi t5, t0, -1
	srli t5, t5, 2
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
	bnez t5, 2157b
	j 2156f
2155:
2156:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2158f
2160:
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
	addi t0, zero, 0
	addi sp, sp, -64
	addi t1, sp, 0
	sd t0, 0(t1)
	sd t0, 8(t1)
	sd t0, 16(t1)
	sd t0, 24(t1)
	sd t0, 32(t1)
	sd t0, 40(t1)
	sd t0, 48(t1)
	sd t0, 56(t1)
	addi sp, sp, 64
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
	addi t0, zero, 0
	addi sp, sp, -128
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
	addi sp, sp, 128
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
