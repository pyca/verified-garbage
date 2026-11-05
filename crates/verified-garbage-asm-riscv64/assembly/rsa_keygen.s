// The functions of `src/rsa_keygen.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_keygen_key:
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
	addi s0, a0, 0
	addi s1, a2, 0
	addi s2, a4, 0
	addi s3, a6, 0
	addi a1, a5, 0
	addi t0, sp, 0
	ld s4, 0(t0)
	ld s5, 16(t0)
	ld s6, 32(t0)
	ld a0, 48(t0)
	ld a7, 56(t0)
	slli t6, a1, 1
	addi s9, t6, 7
	srli s9, s9, 3
	addi s10, s9, 2
	slli s10, s10, 3
	addi t3, zero, 56
	mul t3, t3, s10
	srli t3, t3, 3
	addi t0, s11, 256
	addi t5, zero, 0
20:
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t3, t3, -1
	bnez t3, 20b
	addi t1, s2, 0
	addi t3, a1, 0
	addi t0, zero, 22
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	add t0, t0, t3
	addi t0, t0, -1
21:
	lbu t5, 0(t1)
	sb t5, 0(t0)
	addi t1, t1, 1
	addi t0, t0, -1
	addi t3, t3, -1
	bnez t3, 21b
	addi t1, s3, 0
	addi t3, a1, 0
	addi t0, zero, 23
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	add t0, t0, t3
	addi t0, t0, -1
22:
	lbu t5, 0(t1)
	sb t5, 0(t0)
	addi t1, t1, 1
	addi t0, t0, -1
	addi t3, t3, -1
	bnez t3, 22b
	addi t1, a0, 0
	addi t3, a7, 0
	addi t0, zero, 21
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	add t0, t0, t3
	addi t0, t0, -1
23:
	lbu t5, 0(t1)
	sb t5, 0(t0)
	addi t1, t1, 1
	addi t0, t0, -1
	addi t3, t3, -1
	bnez t3, 23b
	addi t0, zero, 15
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t5, zero, 1
	sd t5, 0(t0)
	addi t0, zero, 16
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t5, zero, 2
	sd t5, 0(t0)
	addi t0, zero, 17
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t5, zero, 3
	sd t5, 0(t0)
	addi t0, zero, 19
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t5, zero, 1
	sd t5, 0(t0)
	addi t0, zero, 19
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	add t0, t0, a1
	addi t5, zero, 1
	sd t5, 0(t0)
	addi t0, zero, 20
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t5, zero, 1
	slli t5, t5, 33
	sd t5, 0(t0)
	addi t4, zero, 1
	addi t0, zero, 18
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	slli t5, s9, 3
	add t5, t0, t5
	sd t4, 0(t5)
	addi t3, s9, 0
24:
	ld t5, 0(t0)
	ld t6, 8(t0)
	slli t6, t6, 63
	srli t5, t5, 1
	or t5, t5, t6
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t3, t3, -1
	bnez t3, 24b
	addi t0, zero, 28
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 22
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 23
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
25:
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
	bnez t3, 25b
	sd t4, 152(s11)
	addi t0, zero, 24
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 22
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 23
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	ld t4, 152(s11)
	addi t5, zero, 0
	sub t4, t5, t4
	addi t3, s9, 0
26:
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
	bnez t3, 26b
	addi t0, zero, 25
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 23
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 22
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	ld t4, 152(s11)
	addi t5, zero, 0
	sub t4, t5, t4
	addi t3, s9, 0
27:
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
	bnez t3, 27b
	addi t0, zero, 28
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 24
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 15
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
28:
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
	bnez t3, 28b
	sd t4, 152(s11)
	addi t0, zero, 26
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 28
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 10
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	ld t4, 152(s11)
	addi t5, zero, 0
	sub t4, t5, t4
	addi t3, s9, 0
29:
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
	bnez t3, 29b
	addi t0, zero, 28
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 25
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 15
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
210:
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
	bnez t3, 210b
	sd t4, 152(s11)
	addi t0, zero, 27
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 28
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 10
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	ld t4, 152(s11)
	addi t5, zero, 0
	sub t4, t5, t4
	addi t3, s9, 0
211:
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
	bnez t3, 211b
	addi t0, zero, 32
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 10
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
212:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 212b
	addi a2, zero, 26
	mul a2, a2, s10
	add a2, a2, s11
	addi a2, a2, 256
	addi a3, zero, 32
	mul a3, a3, s10
	add a3, a3, s11
	addi a3, a3, 256
	addi s8, s9, 0
213:
	ld a6, 0(a2)
	addi t0, a3, 0
	addi t1, zero, 27
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s8, 0
	addi t4, zero, 0
214:
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
	bnez t3, 214b
	addi a2, a2, 8
	addi a3, a3, 8
	addi s8, s8, -1
	bnez s8, 213b
	addi t0, zero, 30
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 26
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
	addi t0, zero, 31
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 27
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
	slli s7, a1, 3
217:
	addi t0, zero, 30
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld t5, 0(t0)
	andi t5, t5, 1
	sd t5, 152(s11)
	addi t0, zero, 31
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld t5, 0(t0)
	andi t5, t5, 1
	sd t5, 160(s11)
	ld t5, 160(s11)
	xori t5, t5, 1
	sd t5, 160(s11)
	ld t5, 152(s11)
	xori t5, t5, 1
	ld t6, 160(s11)
	and t5, t5, t6
	sd t5, 168(s11)
	addi t0, zero, 28
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 30
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
	addi t4, zero, 0
	addi t0, zero, 28
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	slli t5, s9, 3
	add t5, t0, t5
	sd t4, 0(t5)
	addi t3, s9, 0
219:
	ld t5, 0(t0)
	ld t6, 8(t0)
	slli t6, t6, 63
	srli t5, t5, 1
	or t5, t5, t6
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t3, t3, -1
	bnez t3, 219b
	addi t0, zero, 30
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 30
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 28
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	ld t4, 168(s11)
	addi t5, zero, 0
	sub t4, t5, t4
	addi t3, s9, 0
220:
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
	bnez t3, 220b
	addi t0, zero, 28
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 31
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
221:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 221b
	addi t4, zero, 0
	addi t0, zero, 28
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
	addi t0, zero, 31
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 31
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 28
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	ld t4, 168(s11)
	addi t5, zero, 0
	sub t4, t5, t4
	addi t3, s9, 0
223:
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
	bnez t3, 223b
	addi t0, zero, 28
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 32
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
224:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 224b
	addi t4, zero, 0
	addi t0, zero, 28
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	slli t5, s9, 3
	add t5, t0, t5
	sd t4, 0(t5)
	addi t3, s9, 0
225:
	ld t5, 0(t0)
	ld t6, 8(t0)
	slli t6, t6, 63
	srli t5, t5, 1
	or t5, t5, t6
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t3, t3, -1
	bnez t3, 225b
	addi t0, zero, 32
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 32
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 28
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	ld t4, 168(s11)
	addi t5, zero, 0
	sub t4, t5, t4
	addi t3, s9, 0
226:
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
	bnez t3, 226b
	addi s7, s7, -1
	bnez s7, 217b
	addi t0, zero, 31
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld t5, 0(t0)
	andi t5, t5, 1
	sd t5, 152(s11)
	ld t5, 152(s11)
	xori t5, t5, 1
	sd t5, 152(s11)
	addi t0, zero, 33
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 30
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 31
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	ld t4, 152(s11)
	addi t5, zero, 0
	sub t4, t5, t4
	addi t3, s9, 0
227:
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
	bnez t3, 227b
	addi t0, zero, 34
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 31
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 30
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	ld t4, 152(s11)
	addi t5, zero, 0
	sub t4, t5, t4
	addi t3, s9, 0
228:
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
	bnez t3, 228b
	addi t0, zero, 28
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 34
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 16
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
229:
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
	bnez t3, 229b
	sd t4, 160(s11)
	addi t0, zero, 29
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 34
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 17
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	ld t4, 160(s11)
	addi t5, zero, 0
	sub t4, t5, t4
	addi t3, s9, 0
230:
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
	bnez t3, 230b
	addi t0, zero, 0
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 33
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
231:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 231b
	addi t0, zero, 8
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 29
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
	srli s8, a1, 2
	addi t0, zero, 2
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 8
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s8, 0
233:
	lwu t5, 0(t1)
	sw t5, 0(t0)
	addi t0, t0, 4
	addi t1, t1, 4
	addi t3, t3, -1
	bnez t3, 233b
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
234:
	sw t5, 0(t0)
	addi t0, t0, 4
	addi t3, t3, -1
	bnez t3, 234b
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
235:
	lwu t5, 0(t1)
	lwu t6, 0(t2)
	xor t5, t5, t6
	or t4, t4, t5
	addi t1, t1, 4
	addi t2, t2, 4
	addi t3, t3, -1
	bnez t3, 235b
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
236:
	lwu t5, 0(t1)
	sw t5, 0(t0)
	addi t0, t0, 4
	addi t1, t1, 4
	addi t3, t3, -1
	bnez t3, 236b
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
237:
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
	bnez t3, 237b
	sw t4, 0(t0)
	addi t0, zero, 6
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t3, s8, 1
	addi t5, zero, 0
238:
	sw t5, 0(t0)
	addi t0, t0, 4
	addi t3, t3, -1
	bnez t3, 238b
	addi t0, zero, 9
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t5, zero, 1
	sd t5, 0(t0)
	addi s7, s8, 1
	add t5, s7, s7
	add s7, s7, t5
239:
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
240:
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
	bnez t3, 240b
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
	addi t0, zero, 4
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 11
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s8, 1
242:
	lwu t5, 0(t1)
	lwu t6, 4(t1)
	srli t5, t5, 30
	slli t6, t6, 2
	add t5, t5, t6
	sw t5, 0(t0)
	addi t0, t0, 4
	addi t1, t1, 4
	addi t3, t3, -1
	bnez t3, 242b
	addi t0, zero, 5
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 12
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
244:
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
	bnez t3, 244b
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
245:
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
	bnez t3, 245b
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
246:
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
	bnez t3, 246b
	lwu t5, 0(t0)
	add t5, t5, t4
	sw t5, 0(t0)
	srli a5, t5, 31
	andi a5, a5, 1
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
	addi t3, s8, 1
	addi t4, zero, 0
247:
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
	bnez t3, 247b
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
248:
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
	bnez t3, 248b
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
249:
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
	bnez t3, 249b
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
250:
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
	bnez t3, 250b
	lwu t5, 0(t0)
	add t5, t5, t4
	sw t5, 0(t0)
	srli a5, t5, 31
	andi a5, a5, 1
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
	addi t3, s8, 1
	addi t4, zero, 0
251:
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
	bnez t3, 251b
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
	addi s7, s7, -1
	bnez s7, 239b
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
254:
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
	bnez t3, 254b
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
255:
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
	bnez t3, 255b
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
	addi s7, s8, 1
	add t5, s7, s7
	add s7, s7, t5
	add s7, s7, s7
258:
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
259:
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
	bnez t3, 259b
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
	addi s7, s7, -1
	bnez s7, 258b
	addi t0, zero, 1
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	add t3, s9, s9
	addi t3, t3, 2
	addi t5, zero, 0
262:
	sw t5, 0(t0)
	addi t0, t0, 4
	addi t3, t3, -1
	bnez t3, 262b
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
263:
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
	bnez t3, 263b
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
264:
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
	bnez t3, 264b
	addi t0, zero, 3
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	add t3, s9, s9
	addi t3, t3, 2
	addi t5, zero, 0
265:
	sw t5, 0(t0)
	addi t0, t0, 4
	addi t3, t3, -1
	bnez t3, 265b
	addi t0, zero, 3
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 6
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s8, 1
266:
	lwu t5, 0(t1)
	sw t5, 0(t0)
	addi t0, t0, 4
	addi t1, t1, 4
	addi t3, t3, -1
	bnez t3, 266b
	addi t0, zero, 35
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 1
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 15
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	ld t4, 160(s11)
	addi t5, zero, 0
	sub t4, t5, t4
	addi t3, s9, 0
267:
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
	bnez t3, 267b
	addi t0, zero, 36
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 32
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
268:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 268b
	addi t0, zero, 37
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 35
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
269:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 269b
	addi t0, zero, 38
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t3, s9, 1
	addi t5, zero, 0
270:
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t3, t3, -1
	bnez t3, 270b
	slli s7, s9, 6
	addi a4, zero, -1
271:
	addi t2, zero, 36
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t5, s7, -1
	srli t5, t5, 6
	slli t5, t5, 3
	add t2, t2, t5
	ld t5, 0(t2)
	srli t3, t5, 63
	addi t0, zero, 38
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 37
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	andi t4, a4, 1
	addi t2, s9, 1
	andi t2, t2, 3
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
	addi t0, t0, 8
	addi t1, t1, 8
	addi t2, t2, -1
	bnez t2, 274b
	j 273f
272:
273:
	addi t2, s9, 1
	srli t2, t2, 2
	beqz t2, 275f
277:
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
	bnez t2, 277b
	j 276f
275:
276:
	srli t5, t6, 63
	addi a4, t5, -1
	andi a5, a4, 1
	addi t2, zero, 36
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
	bnez s7, 271b
	addi t0, zero, 38
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 37
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	xori a4, a4, -1
	addi t4, zero, 0
	addi t3, s9, 1
278:
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
	bnez t3, 278b
	addi t0, zero, 21
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld t5, 0(t0)
	andi t5, t5, 1
	sd t5, 176(s11)
	addi t1, zero, 21
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 15
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t4, zero, 0
	addi t3, s9, 0
279:
	ld t5, 0(t1)
	ld t6, 0(t2)
	xor t5, t5, t6
	or t4, t4, t5
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 279b
	addi t5, zero, 0
	sltu t5, t5, t4
	xori t5, t5, 1
	sd t5, 184(s11)
	addi t0, zero, 28
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 21
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 17
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
280:
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
	bnez t3, 280b
	sd t4, 192(s11)
	ld t5, 192(s11)
	xori t5, t5, 1
	ld t6, 176(s11)
	and t5, t5, t6
	sd t5, 152(s11)
	addi t0, zero, 40
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 17
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 21
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	ld t4, 152(s11)
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
	addi t0, zero, 41
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 36
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
282:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 282b
	addi t0, zero, 37
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 40
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
283:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 283b
	addi t0, zero, 42
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t3, s9, 1
	addi t5, zero, 0
284:
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t3, t3, -1
	bnez t3, 284b
	slli s7, s9, 6
	addi a4, zero, -1
285:
	addi t2, zero, 41
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t5, s7, -1
	srli t5, t5, 6
	slli t5, t5, 3
	add t2, t2, t5
	ld t5, 0(t2)
	srli t3, t5, 63
	addi t0, zero, 42
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 37
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	andi t4, a4, 1
	addi t2, s9, 1
	andi t2, t2, 3
	beqz t2, 286f
288:
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
	bnez t2, 288b
	j 287f
286:
287:
	addi t2, s9, 1
	srli t2, t2, 2
	beqz t2, 289f
291:
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
	bnez t2, 291b
	j 290f
289:
290:
	srli t5, t6, 63
	addi a4, t5, -1
	andi a5, a4, 1
	addi t2, zero, 41
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
	bnez s7, 285b
	addi t0, zero, 42
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 37
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	xori a4, a4, -1
	addi t4, zero, 0
	addi t3, s9, 1
292:
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
	bnez t3, 292b
	addi t0, zero, 0
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 42
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
293:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 293b
	addi t0, zero, 8
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 40
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
	addi s8, zero, 2
	addi t0, zero, 2
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 8
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s8, 0
295:
	lwu t5, 0(t1)
	sw t5, 0(t0)
	addi t0, t0, 4
	addi t1, t1, 4
	addi t3, t3, -1
	bnez t3, 295b
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
296:
	sw t5, 0(t0)
	addi t0, t0, 4
	addi t3, t3, -1
	bnez t3, 296b
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
297:
	lwu t5, 0(t1)
	lwu t6, 0(t2)
	xor t5, t5, t6
	or t4, t4, t5
	addi t1, t1, 4
	addi t2, t2, 4
	addi t3, t3, -1
	bnez t3, 297b
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
298:
	lwu t5, 0(t1)
	sw t5, 0(t0)
	addi t0, t0, 4
	addi t1, t1, 4
	addi t3, t3, -1
	bnez t3, 298b
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
299:
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
	bnez t3, 299b
	sw t4, 0(t0)
	addi t0, zero, 6
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t3, s8, 1
	addi t5, zero, 0
2100:
	sw t5, 0(t0)
	addi t0, t0, 4
	addi t3, t3, -1
	bnez t3, 2100b
	addi t0, zero, 9
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t5, zero, 1
	sd t5, 0(t0)
	addi s7, s8, 1
	add t5, s7, s7
	add s7, s7, t5
2101:
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
2102:
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
	bnez t3, 2102b
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
2103:
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
	bnez t3, 2103b
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
2104:
	lwu t5, 0(t1)
	lwu t6, 4(t1)
	srli t5, t5, 30
	slli t6, t6, 2
	add t5, t5, t6
	sw t5, 0(t0)
	addi t0, t0, 4
	addi t1, t1, 4
	addi t3, t3, -1
	bnez t3, 2104b
	addi t0, zero, 5
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 12
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s8, 1
2105:
	lwu t5, 0(t1)
	lwu t6, 4(t1)
	srli t5, t5, 30
	slli t6, t6, 2
	add t5, t5, t6
	sw t5, 0(t0)
	addi t0, t0, 4
	addi t1, t1, 4
	addi t3, t3, -1
	bnez t3, 2105b
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
2106:
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
	bnez t3, 2106b
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
2107:
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
	bnez t3, 2107b
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
2108:
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
	bnez t3, 2108b
	lwu t5, 0(t0)
	add t5, t5, t4
	sw t5, 0(t0)
	srli a5, t5, 31
	andi a5, a5, 1
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
	addi t3, s8, 1
	addi t4, zero, 0
2109:
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
	bnez t3, 2109b
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
2110:
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
	bnez t3, 2110b
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
2111:
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
	bnez t3, 2111b
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
2112:
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
	bnez t3, 2112b
	lwu t5, 0(t0)
	add t5, t5, t4
	sw t5, 0(t0)
	srli a5, t5, 31
	andi a5, a5, 1
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
	addi t3, s8, 1
	addi t4, zero, 0
2113:
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
	bnez t3, 2113b
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
2114:
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
	bnez t3, 2114b
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
2115:
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
	bnez t3, 2115b
	addi s7, s7, -1
	bnez s7, 2101b
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
2116:
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
	bnez t3, 2116b
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
2117:
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
	bnez t3, 2117b
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
2118:
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
	bnez t3, 2118b
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
2119:
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
	bnez t3, 2119b
	addi s7, s8, 1
	add t5, s7, s7
	add s7, s7, t5
	add s7, s7, s7
2120:
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
2121:
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
	bnez t3, 2121b
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
2122:
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
	bnez t3, 2122b
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
2123:
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
	bnez t3, 2123b
	addi s7, s7, -1
	bnez s7, 2120b
	addi t0, zero, 1
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	add t3, s9, s9
	addi t3, t3, 2
	addi t5, zero, 0
2124:
	sw t5, 0(t0)
	addi t0, t0, 4
	addi t3, t3, -1
	bnez t3, 2124b
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
2125:
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
	bnez t3, 2125b
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
2126:
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
	bnez t3, 2126b
	addi t0, zero, 3
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	add t3, s9, s9
	addi t3, t3, 2
	addi t5, zero, 0
2127:
	sw t5, 0(t0)
	addi t0, t0, 4
	addi t3, t3, -1
	bnez t3, 2127b
	addi t0, zero, 3
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 6
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s8, 1
2128:
	lwu t5, 0(t1)
	sw t5, 0(t0)
	addi t0, t0, 4
	addi t1, t1, 4
	addi t3, t3, -1
	bnez t3, 2128b
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
2129:
	ld t5, 0(t1)
	ld t6, 0(t2)
	xor t5, t5, t6
	or t4, t4, t5
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 2129b
	addi t5, zero, 0
	sltu t5, t5, t4
	xori t5, t5, 1
	sd t5, 160(s11)
	addi t0, zero, 43
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 40
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 3
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
2130:
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
	bnez t3, 2130b
	addi t0, zero, 44
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 10
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
2131:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 2131b
	addi a2, zero, 41
	mul a2, a2, s10
	add a2, a2, s11
	addi a2, a2, 256
	addi a3, zero, 44
	mul a3, a3, s10
	add a3, a3, s11
	addi a3, a3, 256
	addi s8, s9, 0
2132:
	ld a6, 0(a2)
	addi t0, a3, 0
	addi t1, zero, 43
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s8, 0
	addi t4, zero, 0
2133:
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
	bnez t3, 2133b
	addi a2, a2, 8
	addi a3, a3, 8
	addi s8, s8, -1
	bnez s8, 2132b
	addi t0, zero, 45
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 10
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
2134:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 2134b
	addi a2, zero, 42
	mul a2, a2, s10
	add a2, a2, s11
	addi a2, a2, 256
	addi a3, zero, 45
	mul a3, a3, s10
	add a3, a3, s11
	addi a3, a3, 256
	addi s8, s9, 0
2135:
	ld a6, 0(a2)
	addi t0, a3, 0
	addi t1, zero, 43
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s8, 0
	addi t4, zero, 0
2136:
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
	bnez t3, 2136b
	addi a2, a2, 8
	addi a3, a3, 8
	addi s8, s8, -1
	bnez s8, 2135b
	addi t0, zero, 46
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 10
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 15
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
2137:
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
	bnez t3, 2137b
	addi t0, zero, 55
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 45
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 46
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
2138:
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
	bnez t3, 2138b
	addi t0, zero, 38
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t3, s9, 1
	addi t5, zero, 0
2139:
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t3, t3, -1
	bnez t3, 2139b
	slli s7, s9, 6
	addi a4, zero, -1
2140:
	addi t2, zero, 55
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t5, s7, -1
	srli t5, t5, 6
	slli t5, t5, 3
	add t2, t2, t5
	ld t5, 0(t2)
	srli t3, t5, 63
	addi t0, zero, 38
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 37
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	andi t4, a4, 1
	addi t2, s9, 1
	andi t2, t2, 3
	beqz t2, 2141f
2143:
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
	bnez t2, 2143b
	j 2142f
2141:
2142:
	addi t2, s9, 1
	srli t2, t2, 2
	beqz t2, 2144f
2146:
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
	bnez t2, 2146b
	j 2145f
2144:
2145:
	srli t5, t6, 63
	addi a4, t5, -1
	andi a5, a4, 1
	addi t2, zero, 55
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
	bnez s7, 2140b
	addi t0, zero, 38
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 37
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	xori a4, a4, -1
	addi t4, zero, 0
	addi t3, s9, 1
2147:
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
	bnez t3, 2147b
	addi t0, zero, 46
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 10
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 55
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
2148:
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
	bnez t3, 2148b
	addi t0, zero, 47
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 44
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 46
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
2149:
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
	bnez t3, 2149b
	addi t0, zero, 28
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 36
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 16
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
2150:
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
	bnez t3, 2150b
	sd t4, 168(s11)
	ld t5, 168(s11)
	xori t5, t5, 1
	ld t6, 160(s11)
	and t5, t5, t6
	sd t5, 200(s11)
	addi t1, zero, 36
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 15
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t4, zero, 0
	addi t3, s9, 0
2151:
	ld t5, 0(t1)
	ld t6, 0(t2)
	xor t5, t5, t6
	or t4, t4, t5
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 2151b
	addi t5, zero, 0
	sltu t5, t5, t4
	xori t5, t5, 1
	sd t5, 152(s11)
	ld t5, 152(s11)
	xori t5, t5, 1
	sd t5, 208(s11)
	ld t5, 200(s11)
	ld t6, 208(s11)
	xor t6, t6, t5
	ld t4, 184(s11)
	and t6, t6, t4
	xor t5, t5, t6
	sd t5, 200(s11)
	addi t0, zero, 29
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 47
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 15
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	ld t4, 184(s11)
	addi t5, zero, 0
	sub t4, t5, t4
	addi t3, s9, 0
2152:
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
	bnez t3, 2152b
	ld t5, 176(s11)
	bnez t5, 2153f
	addi t0, zero, 36
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld t5, 0(t0)
	andi t5, t5, 1
	sd t5, 152(s11)
	addi t0, zero, 28
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 36
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 17
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
2155:
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
	bnez t3, 2155b
	sd t4, 160(s11)
	ld t5, 160(s11)
	xori t5, t5, 1
	ld t6, 152(s11)
	and t5, t5, t6
	sd t5, 168(s11)
	addi t0, zero, 48
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 17
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 36
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	ld t4, 168(s11)
	addi t5, zero, 0
	sub t4, t5, t4
	addi t3, s9, 0
2156:
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
	bnez t3, 2156b
	addi t0, zero, 0
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 21
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
2157:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 2157b
	addi t0, zero, 8
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 48
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
2158:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 2158b
	srli s8, a1, 1
	addi t0, zero, 2
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 8
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s8, 0
2159:
	lwu t5, 0(t1)
	sw t5, 0(t0)
	addi t0, t0, 4
	addi t1, t1, 4
	addi t3, t3, -1
	bnez t3, 2159b
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
2160:
	sw t5, 0(t0)
	addi t0, t0, 4
	addi t3, t3, -1
	bnez t3, 2160b
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
2161:
	lwu t5, 0(t1)
	lwu t6, 0(t2)
	xor t5, t5, t6
	or t4, t4, t5
	addi t1, t1, 4
	addi t2, t2, 4
	addi t3, t3, -1
	bnez t3, 2161b
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
2162:
	lwu t5, 0(t1)
	sw t5, 0(t0)
	addi t0, t0, 4
	addi t1, t1, 4
	addi t3, t3, -1
	bnez t3, 2162b
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
2163:
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
	bnez t3, 2163b
	sw t4, 0(t0)
	addi t0, zero, 6
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t3, s8, 1
	addi t5, zero, 0
2164:
	sw t5, 0(t0)
	addi t0, t0, 4
	addi t3, t3, -1
	bnez t3, 2164b
	addi t0, zero, 9
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t5, zero, 1
	sd t5, 0(t0)
	addi s7, s8, 1
	add t5, s7, s7
	add s7, s7, t5
2165:
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
2166:
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
	bnez t3, 2166b
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
2167:
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
	bnez t3, 2167b
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
2168:
	lwu t5, 0(t1)
	lwu t6, 4(t1)
	srli t5, t5, 30
	slli t6, t6, 2
	add t5, t5, t6
	sw t5, 0(t0)
	addi t0, t0, 4
	addi t1, t1, 4
	addi t3, t3, -1
	bnez t3, 2168b
	addi t0, zero, 5
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 12
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s8, 1
2169:
	lwu t5, 0(t1)
	lwu t6, 4(t1)
	srli t5, t5, 30
	slli t6, t6, 2
	add t5, t5, t6
	sw t5, 0(t0)
	addi t0, t0, 4
	addi t1, t1, 4
	addi t3, t3, -1
	bnez t3, 2169b
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
2170:
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
	bnez t3, 2170b
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
2171:
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
	bnez t3, 2171b
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
2172:
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
	bnez t3, 2172b
	lwu t5, 0(t0)
	add t5, t5, t4
	sw t5, 0(t0)
	srli a5, t5, 31
	andi a5, a5, 1
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
	addi t3, s8, 1
	addi t4, zero, 0
2173:
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
	bnez t3, 2173b
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
2174:
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
	bnez t3, 2174b
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
2175:
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
	bnez t3, 2175b
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
2176:
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
	bnez t3, 2176b
	lwu t5, 0(t0)
	add t5, t5, t4
	sw t5, 0(t0)
	srli a5, t5, 31
	andi a5, a5, 1
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
	addi t3, s8, 1
	addi t4, zero, 0
2177:
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
	bnez t3, 2177b
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
2178:
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
	bnez t3, 2178b
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
2179:
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
	bnez t3, 2179b
	addi s7, s7, -1
	bnez s7, 2165b
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
2180:
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
	bnez t3, 2180b
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
2181:
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
	bnez t3, 2181b
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
2182:
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
	bnez t3, 2182b
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
2183:
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
	bnez t3, 2183b
	addi s7, s8, 1
	add t5, s7, s7
	add s7, s7, t5
	add s7, s7, s7
2184:
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
2185:
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
	bnez t3, 2185b
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
2186:
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
	bnez t3, 2186b
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
2187:
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
	bnez t3, 2187b
	addi s7, s7, -1
	bnez s7, 2184b
	addi t0, zero, 1
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	add t3, s9, s9
	addi t3, t3, 2
	addi t5, zero, 0
2188:
	sw t5, 0(t0)
	addi t0, t0, 4
	addi t3, t3, -1
	bnez t3, 2188b
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
2189:
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
	bnez t3, 2189b
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
2190:
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
	bnez t3, 2190b
	addi t0, zero, 3
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	add t3, s9, s9
	addi t3, t3, 2
	addi t5, zero, 0
2191:
	sw t5, 0(t0)
	addi t0, t0, 4
	addi t3, t3, -1
	bnez t3, 2191b
	addi t0, zero, 3
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 6
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s8, 1
2192:
	lwu t5, 0(t1)
	sw t5, 0(t0)
	addi t0, t0, 4
	addi t1, t1, 4
	addi t3, t3, -1
	bnez t3, 2192b
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
2193:
	ld t5, 0(t1)
	ld t6, 0(t2)
	xor t5, t5, t6
	or t4, t4, t5
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 2193b
	addi t5, zero, 0
	sltu t5, t5, t4
	xori t5, t5, 1
	sd t5, 152(s11)
	ld t5, 168(s11)
	ld t6, 152(s11)
	and t5, t5, t6
	sd t5, 160(s11)
	ld t5, 160(s11)
	ld t6, 200(s11)
	xor t6, t6, t5
	ld t4, 176(s11)
	and t6, t6, t4
	xor t5, t5, t6
	sd t5, 200(s11)
	addi t0, zero, 49
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 3
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 29
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	ld t4, 176(s11)
	addi t5, zero, 0
	sub t4, t5, t4
	addi t3, s9, 0
2194:
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
	bnez t3, 2194b
	j 2154f
2153:
	addi t0, zero, 49
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 29
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
2195:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 2195b
2154:
	addi t0, zero, 28
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 49
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 19
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
2196:
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
	bnez t3, 2196b
	sd t4, 152(s11)
	ld t5, 152(s11)
	ld t6, 200(s11)
	and t5, t5, t6
	sd t5, 208(s11)
	addi t0, zero, 24
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld t5, 0(t0)
	andi t5, t5, 1
	sd t5, 152(s11)
	addi t0, zero, 28
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 24
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 17
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
2197:
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
	bnez t3, 2197b
	sd t4, 160(s11)
	ld t5, 160(s11)
	xori t5, t5, 1
	ld t6, 152(s11)
	and t5, t5, t6
	sd t5, 168(s11)
	addi t0, zero, 54
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 17
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 24
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	ld t4, 168(s11)
	addi t5, zero, 0
	sub t4, t5, t4
	addi t3, s9, 0
2198:
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
	bnez t3, 2198b
	addi t0, zero, 0
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 25
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
2199:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 2199b
	addi t0, zero, 8
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 54
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
2200:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 2200b
	srli s8, a1, 2
	addi t0, zero, 2
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 8
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s8, 0
2201:
	lwu t5, 0(t1)
	sw t5, 0(t0)
	addi t0, t0, 4
	addi t1, t1, 4
	addi t3, t3, -1
	bnez t3, 2201b
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
2202:
	sw t5, 0(t0)
	addi t0, t0, 4
	addi t3, t3, -1
	bnez t3, 2202b
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
2203:
	lwu t5, 0(t1)
	lwu t6, 0(t2)
	xor t5, t5, t6
	or t4, t4, t5
	addi t1, t1, 4
	addi t2, t2, 4
	addi t3, t3, -1
	bnez t3, 2203b
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
2204:
	lwu t5, 0(t1)
	sw t5, 0(t0)
	addi t0, t0, 4
	addi t1, t1, 4
	addi t3, t3, -1
	bnez t3, 2204b
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
2205:
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
	bnez t3, 2205b
	sw t4, 0(t0)
	addi t0, zero, 6
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t3, s8, 1
	addi t5, zero, 0
2206:
	sw t5, 0(t0)
	addi t0, t0, 4
	addi t3, t3, -1
	bnez t3, 2206b
	addi t0, zero, 9
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t5, zero, 1
	sd t5, 0(t0)
	addi s7, s8, 1
	add t5, s7, s7
	add s7, s7, t5
2207:
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
2208:
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
	bnez t3, 2208b
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
2209:
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
	bnez t3, 2209b
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
2210:
	lwu t5, 0(t1)
	lwu t6, 4(t1)
	srli t5, t5, 30
	slli t6, t6, 2
	add t5, t5, t6
	sw t5, 0(t0)
	addi t0, t0, 4
	addi t1, t1, 4
	addi t3, t3, -1
	bnez t3, 2210b
	addi t0, zero, 5
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 12
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s8, 1
2211:
	lwu t5, 0(t1)
	lwu t6, 4(t1)
	srli t5, t5, 30
	slli t6, t6, 2
	add t5, t5, t6
	sw t5, 0(t0)
	addi t0, t0, 4
	addi t1, t1, 4
	addi t3, t3, -1
	bnez t3, 2211b
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
2212:
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
	bnez t3, 2212b
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
2213:
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
	bnez t3, 2213b
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
2214:
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
	bnez t3, 2214b
	lwu t5, 0(t0)
	add t5, t5, t4
	sw t5, 0(t0)
	srli a5, t5, 31
	andi a5, a5, 1
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
	addi t3, s8, 1
	addi t4, zero, 0
2215:
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
	bnez t3, 2215b
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
2216:
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
	bnez t3, 2216b
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
2217:
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
	bnez t3, 2217b
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
2218:
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
	bnez t3, 2218b
	lwu t5, 0(t0)
	add t5, t5, t4
	sw t5, 0(t0)
	srli a5, t5, 31
	andi a5, a5, 1
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
	addi t3, s8, 1
	addi t4, zero, 0
2219:
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
	bnez t3, 2219b
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
2220:
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
	bnez t3, 2220b
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
2221:
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
	bnez t3, 2221b
	addi s7, s7, -1
	bnez s7, 2207b
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
2222:
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
	bnez t3, 2222b
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
2223:
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
	bnez t3, 2223b
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
2224:
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
	bnez t3, 2224b
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
2225:
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
	bnez t3, 2225b
	addi s7, s8, 1
	add t5, s7, s7
	add s7, s7, t5
	add s7, s7, s7
2226:
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
2227:
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
	bnez t3, 2227b
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
2228:
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
	bnez t3, 2228b
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
2229:
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
	bnez t3, 2229b
	addi s7, s7, -1
	bnez s7, 2226b
	addi t0, zero, 1
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	add t3, s9, s9
	addi t3, t3, 2
	addi t5, zero, 0
2230:
	sw t5, 0(t0)
	addi t0, t0, 4
	addi t3, t3, -1
	bnez t3, 2230b
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
2231:
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
	bnez t3, 2231b
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
2232:
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
	bnez t3, 2232b
	addi t0, zero, 3
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	add t3, s9, s9
	addi t3, t3, 2
	addi t5, zero, 0
2233:
	sw t5, 0(t0)
	addi t0, t0, 4
	addi t3, t3, -1
	bnez t3, 2233b
	addi t0, zero, 3
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 6
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s8, 1
2234:
	lwu t5, 0(t1)
	sw t5, 0(t0)
	addi t0, t0, 4
	addi t1, t1, 4
	addi t3, t3, -1
	bnez t3, 2234b
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
2235:
	ld t5, 0(t1)
	ld t6, 0(t2)
	xor t5, t5, t6
	or t4, t4, t5
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 2235b
	addi t5, zero, 0
	sltu t5, t5, t4
	xori t5, t5, 1
	sd t5, 160(s11)
	addi t0, zero, 52
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 3
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
2236:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 2236b
	addi t1, zero, 26
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 10
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t4, zero, 0
	addi t3, s9, 0
2237:
	ld t5, 0(t1)
	ld t6, 0(t2)
	xor t5, t5, t6
	or t4, t4, t5
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 2237b
	addi t5, zero, 0
	sltu t5, t5, t4
	xori t5, t5, 1
	sd t5, 168(s11)
	addi t0, zero, 29
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 26
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 15
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	ld t4, 168(s11)
	addi t5, zero, 0
	sub t4, t5, t4
	addi t3, s9, 0
2238:
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
	bnez t3, 2238b
	addi t0, zero, 41
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 49
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
2239:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 2239b
	addi t0, zero, 37
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 29
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
2240:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 2240b
	addi t0, zero, 50
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t3, s9, 1
	addi t5, zero, 0
2241:
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t3, t3, -1
	bnez t3, 2241b
	slli s7, s9, 6
	addi a4, zero, -1
2242:
	addi t2, zero, 41
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t5, s7, -1
	srli t5, t5, 6
	slli t5, t5, 3
	add t2, t2, t5
	ld t5, 0(t2)
	srli t3, t5, 63
	addi t0, zero, 50
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 37
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	andi t4, a4, 1
	addi t2, s9, 1
	andi t2, t2, 3
	beqz t2, 2243f
2245:
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
	bnez t2, 2245b
	j 2244f
2243:
2244:
	addi t2, s9, 1
	srli t2, t2, 2
	beqz t2, 2246f
2248:
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
	bnez t2, 2248b
	j 2247f
2246:
2247:
	srli t5, t6, 63
	addi a4, t5, -1
	andi a5, a4, 1
	addi t2, zero, 41
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
	bnez s7, 2242b
	addi t0, zero, 50
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 37
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	xori a4, a4, -1
	addi t4, zero, 0
	addi t3, s9, 1
2249:
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
	bnez t3, 2249b
	addi t1, zero, 27
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 10
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t4, zero, 0
	addi t3, s9, 0
2250:
	ld t5, 0(t1)
	ld t6, 0(t2)
	xor t5, t5, t6
	or t4, t4, t5
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 2250b
	addi t5, zero, 0
	sltu t5, t5, t4
	xori t5, t5, 1
	sd t5, 168(s11)
	addi t0, zero, 29
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 27
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 15
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	ld t4, 168(s11)
	addi t5, zero, 0
	sub t4, t5, t4
	addi t3, s9, 0
2251:
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
	bnez t3, 2251b
	addi t0, zero, 41
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 49
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
2252:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 2252b
	addi t0, zero, 37
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 29
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
2253:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 2253b
	addi t0, zero, 51
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t3, s9, 1
	addi t5, zero, 0
2254:
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t3, t3, -1
	bnez t3, 2254b
	slli s7, s9, 6
	addi a4, zero, -1
2255:
	addi t2, zero, 41
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t5, s7, -1
	srli t5, t5, 6
	slli t5, t5, 3
	add t2, t2, t5
	ld t5, 0(t2)
	srli t3, t5, 63
	addi t0, zero, 51
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 37
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	andi t4, a4, 1
	addi t2, s9, 1
	andi t2, t2, 3
	beqz t2, 2256f
2258:
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
	bnez t2, 2258b
	j 2257f
2256:
2257:
	addi t2, s9, 1
	srli t2, t2, 2
	beqz t2, 2259f
2261:
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
	bnez t2, 2261b
	j 2260f
2259:
2260:
	srli t5, t6, 63
	addi a4, t5, -1
	andi a5, a4, 1
	addi t2, zero, 41
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
	bnez s7, 2255b
	addi t0, zero, 51
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 37
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	xori a4, a4, -1
	addi t4, zero, 0
	addi t3, s9, 1
2262:
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
	bnez t3, 2262b
	addi t0, zero, 53
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 10
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
2263:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 2263b
	addi a2, zero, 24
	mul a2, a2, s10
	add a2, a2, s11
	addi a2, a2, 256
	addi a3, zero, 53
	mul a3, a3, s10
	add a3, a3, s11
	addi a3, a3, 256
	addi s8, s9, 0
2264:
	ld a6, 0(a2)
	addi t0, a3, 0
	addi t1, zero, 25
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s8, 0
	addi t4, zero, 0
2265:
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
	bnez t3, 2265b
	addi a2, a2, 8
	addi a3, a3, 8
	addi s8, s8, -1
	bnez s8, 2264b
	addi t0, zero, 28
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 53
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 18
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
2266:
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
	bnez t3, 2266b
	sd t4, 168(s11)
	ld t5, 168(s11)
	xori t5, t5, 1
	ld t6, 200(s11)
	and t5, t5, t6
	sd t5, 216(s11)
	ld t5, 216(s11)
	ld t6, 160(s11)
	and t5, t5, t6
	sd t5, 216(s11)
	ld t5, 216(s11)
	ld t6, 152(s11)
	and t5, t5, t6
	sd t5, 216(s11)
	addi t0, zero, 25
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld t5, 0(t0)
	andi t5, t5, 1
	sd t5, 168(s11)
	ld t5, 216(s11)
	ld t6, 168(s11)
	and t5, t5, t6
	sd t5, 216(s11)
	ld t5, 216(s11)
	ld t6, 176(s11)
	and t5, t5, t6
	sd t5, 216(s11)
	addi t0, zero, 28
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 21
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t2, zero, 20
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi t3, s9, 0
	addi t4, zero, 0
2267:
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
	bnez t3, 2267b
	sd t4, 168(s11)
	ld t5, 192(s11)
	xori t5, t5, 1
	ld t6, 168(s11)
	and t5, t5, t6
	sd t5, 184(s11)
	ld t5, 216(s11)
	ld t6, 184(s11)
	and t5, t5, t6
	sd t5, 216(s11)
	ld t5, 208(s11)
	xori t5, t5, 1
	ld t6, 216(s11)
	and t5, t5, t6
	sd t5, 216(s11)
	slli a5, a1, 1
	ld t4, 216(s11)
	addi t5, zero, 0
	sub t4, t5, t4
	addi t1, zero, 53
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	add t1, t1, a5
	addi t1, t1, -1
	addi t0, s0, 0
	addi t3, a5, 0
2268:
	lbu t5, 0(t1)
	and t5, t5, t4
	sb t5, 0(t0)
	addi t0, t0, 1
	addi t1, t1, -1
	addi t3, t3, -1
	bnez t3, 2268b
	ld t4, 216(s11)
	addi t5, zero, 0
	sub t4, t5, t4
	addi t1, zero, 49
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	add t1, t1, a5
	addi t1, t1, -1
	addi t0, s1, 0
	addi t3, a5, 0
2269:
	lbu t5, 0(t1)
	and t5, t5, t4
	sb t5, 0(t0)
	addi t0, t0, 1
	addi t1, t1, -1
	addi t3, t3, -1
	bnez t3, 2269b
	ld t4, 216(s11)
	addi t5, zero, 0
	sub t4, t5, t4
	addi t1, zero, 24
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	add t1, t1, a1
	addi t1, t1, -1
	addi t0, s2, 0
	addi t3, a1, 0
2270:
	lbu t5, 0(t1)
	and t5, t5, t4
	sb t5, 0(t0)
	addi t0, t0, 1
	addi t1, t1, -1
	addi t3, t3, -1
	bnez t3, 2270b
	ld t4, 216(s11)
	addi t5, zero, 0
	sub t4, t5, t4
	addi t1, zero, 25
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	add t1, t1, a1
	addi t1, t1, -1
	addi t0, s3, 0
	addi t3, a1, 0
2271:
	lbu t5, 0(t1)
	and t5, t5, t4
	sb t5, 0(t0)
	addi t0, t0, 1
	addi t1, t1, -1
	addi t3, t3, -1
	bnez t3, 2271b
	ld t4, 216(s11)
	addi t5, zero, 0
	sub t4, t5, t4
	addi t1, zero, 50
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	add t1, t1, a1
	addi t1, t1, -1
	addi t0, s4, 0
	addi t3, a1, 0
2272:
	lbu t5, 0(t1)
	and t5, t5, t4
	sb t5, 0(t0)
	addi t0, t0, 1
	addi t1, t1, -1
	addi t3, t3, -1
	bnez t3, 2272b
	ld t4, 216(s11)
	addi t5, zero, 0
	sub t4, t5, t4
	addi t1, zero, 51
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	add t1, t1, a1
	addi t1, t1, -1
	addi t0, s5, 0
	addi t3, a1, 0
2273:
	lbu t5, 0(t1)
	and t5, t5, t4
	sb t5, 0(t0)
	addi t0, t0, 1
	addi t1, t1, -1
	addi t3, t3, -1
	bnez t3, 2273b
	ld t4, 216(s11)
	addi t5, zero, 0
	sub t4, t5, t4
	addi t1, zero, 52
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	add t1, t1, a1
	addi t1, t1, -1
	addi t0, s6, 0
	addi t3, a1, 0
2274:
	lbu t5, 0(t1)
	and t5, t5, t4
	sb t5, 0(t0)
	addi t0, t0, 1
	addi t1, t1, -1
	addi t3, t3, -1
	bnez t3, 2274b
	ld a0, 208(s11)
	slli a0, a0, 1
	ld t5, 216(s11)
	add a0, a0, t5
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

vg_rsa_prime_search_init:
	.option push
	.option arch, +m, +c
	addi t0, zero, 32
	sltu t1, a1, t0
	addi t0, zero, 513
	sltu t2, a1, t0
	sub t3, t2, t1
	andi t1, a1, 7
	addi t0, zero, 1
	sltu t1, t1, t0
	and t3, t3, t1
	sltu t1, a3, t0
	addi t0, zero, 9
	sltu t2, a3, t0
	sub t1, t2, t1
	and t3, t3, t1
	beqz t3, 20f
	addi t4, zero, 0
	addi t5, a3, -1
	beqz t5, 22f
24:
	lbu t6, 0(a2)
	or t4, t4, t6
	addi a2, a2, 1
	addi t5, t5, -1
	bnez t5, 24b
	j 23f
22:
23:
	lbu t6, 0(a2)
	addi t0, zero, 3
	xor t6, t6, t0
	or t4, t4, t6
	addi t0, zero, 1
	sltu t0, t4, t0
	slli t1, a1, 3
	slli t2, a1, 5
	add t1, t1, t2
	slli t2, a1, 4
	slli t5, a1, 3
	add t2, t2, t5
	mul t2, t2, t0
	add t1, t1, t2
	sd t1, 0(a0)
	sd a1, 8(a0)
	slli t2, a1, 15
	add t2, t2, a1
	sd t2, 16(a0)
	slli t2, a1, 5
	sd t2, 24(a0)
	addi a0, zero, 1
	j 21f
20:
	addi t0, zero, 0
	sd t0, 0(a0)
	sd t0, 8(a0)
	sd t0, 16(a0)
	sd t0, 24(a0)
	addi a0, zero, 0
21:
	ret
	.option pop

vg_rsa_keygen_candidate:
	.option push
	.option arch, +m, +c
	addi sp, sp, -192
	addi t2, sp, 0
	sd s0, 0(t2)
	sd s1, 8(t2)
	sd s2, 16(t2)
	sd s3, 24(t2)
	sd s4, 32(t2)
	sd s5, 40(t2)
	sd s6, 48(t2)
	sd s7, 56(t2)
	sd s8, 64(t2)
	sd s9, 72(t2)
	sd s10, 80(t2)
	sd s11, 88(t2)
	sd ra, 96(t2)
	addi s11, t2, 0
	sd a0, 104(s11)
	sd a1, 112(s11)
	sd a2, 120(s11)
	sd a3, 128(s11)
	sd a4, 136(s11)
	sd a5, 144(s11)
	sd a6, 152(s11)
	sd a7, 160(s11)
	ld t3, 192(s11)
	sd t3, 168(s11)
	ld s6, 200(s11)
	ld t3, 208(s11)
	sd t3, 184(s11)
	addi t3, zero, 0
	sd t3, 176(s11)
	ld t3, 104(s11)
	ld t5, 112(s11)
	addi t2, zero, 0
20:
	sb t2, 0(t3)
	addi t3, t3, 1
	addi t5, t5, -1
	bnez t5, 20b
	ld t3, 168(s11)
	ld t4, 112(s11)
	sltu t2, t3, t4
	xori t2, t2, 1
	beqz t2, 21f
	ld t2, 184(s11)
	sd t2, 0(s6)
	ld t2, 112(s11)
	srli t0, t2, 3
	sd t0, 48(s6)
	addi s5, t0, 2
	slli s5, s5, 3
	sd s5, 224(s6)
	addi a7, s6, 256
	addi t2, a7, 0
	sd t2, 64(s6)
	addi t2, a7, 0
	add t2, t2, s5
	sd t2, 72(s6)
	addi t2, a7, 0
	add t2, t2, s5
	add t2, t2, s5
	sd t2, 80(s6)
	addi t2, a7, 0
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	sd t2, 88(s6)
	addi t2, a7, 0
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	sd t2, 96(s6)
	addi t2, a7, 0
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	sd t2, 104(s6)
	addi t2, a7, 0
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	sd t2, 112(s6)
	addi t2, a7, 0
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	sd t2, 120(s6)
	addi t3, a7, 0
	addi t5, zero, 35
	mul t5, t5, s5
	srli t5, t5, 3
	addi t2, zero, 0
23:
	sd t2, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 23b
	ld s7, 160(s11)
	ld s8, 112(s11)
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
	ld t2, 0(a7)
	ori t2, t2, 1
	sd t2, 0(a7)
	slli t3, t0, 3
	add t3, t3, a7
	addi t3, t3, -8
	ld t2, 0(t3)
	addi t4, zero, 3
	slli t4, t4, 62
	or t2, t2, t4
	sd t2, 0(t3)
	ld t2, 112(s11)
	sd t2, 176(s11)
	ld t2, 152(s11)
	beqz t2, 26f
	addi t2, a7, 0
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	addi a7, t2, 0
	ld s7, 144(s11)
	ld s8, 112(s11)
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
	addi a7, s6, 256
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
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
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
210:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 210b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi a7, s6, 256
	addi s9, s4, 0
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
	add a6, a6, s5
	addi t2, a7, 0
	addi a7, t2, 0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
211:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 211b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi a7, s6, 256
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
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi s4, s9, 0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
212:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 212b
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
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	slli t4, t0, 3
	add t3, t3, t4
	addi t3, t3, -16
	addi t2, zero, 1
	slli t2, t2, 28
	sd t2, 0(t3)
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
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
	add t2, t2, s5
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
	addi a7, s6, 256
	andi s9, s4, 1
	xori s9, s9, 1
	j 27f
26:
	addi s9, zero, 0
27:
	bnez s9, 214f
	addi t2, zero, 0
	ld t3, 128(s11)
	ld t5, 136(s11)
216:
	slli t2, t2, 8
	lbu t4, 0(t3)
	add t2, t2, t4
	addi t3, t3, 1
	addi t5, t5, -1
	bnez t5, 216b
	addi s10, t2, 0
	andi t2, s10, 1
	beqz t2, 217f
	addi t2, s10, -1
	beqz t2, 219f
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
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t4, a7, 0
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
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	ld t2, 0(t3)
	addi t2, t2, -1
	sd t2, 0(t3)
	slli t4, t0, 3
	add t3, t3, t4
	addi a6, t0, 0
	addi a1, zero, 0
222:
	addi t3, t3, -8
	ld a2, 0(t3)
	addi t5, zero, 64
223:
	srli a3, a1, 63
	srli a4, a2, 63
	slli a1, a1, 1
	add a1, a1, a4
	slli a2, a2, 1
	sltu a4, a1, s10
	xori a4, a4, 1
	or a4, a4, a3
	addi a5, zero, 0
	sub a4, a5, a4
	sub a5, a1, s10
	xor a5, a5, a1
	and a5, a5, a4
	xor a1, a1, a5
	addi t5, t5, -1
	bnez t5, 223b
	addi a6, a6, -1
	bnez a6, 222b
	addi t5, zero, 128
224:
	sltu a3, a1, s10
	addi t2, zero, 0
	sub a3, t2, a3
	andi a4, a1, 1
	sub a4, t2, a4
	sub a5, a1, s10
	sub a2, s10, a1
	xor a2, a2, a5
	and a2, a2, a3
	xor a5, a5, a2
	xor a2, a1, s10
	and a2, a2, a3
	xor a2, a2, s10
	xor a5, a5, a1
	and a5, a5, a4
	xor a1, a1, a5
	xor a2, a2, s10
	and a2, a2, a4
	xor s10, s10, a2
	srli a1, a1, 1
	addi t5, t5, -1
	bnez t5, 224b
	addi s9, s10, -1
	j 220f
219:
	addi s9, zero, 0
220:
	j 218f
217:
	addi s9, zero, 1
218:
	bnez s9, 225f
	ld t2, 160(s11)
	sd t2, 136(s6)
	ld t2, 168(s11)
	sd t2, 144(s6)
	ld t2, 176(s11)
	sd t2, 152(s6)
	ld t2, 112(s11)
	sd t2, 216(s6)
	addi s0, zero, 27
	addi t4, zero, 5
	sltu t3, t0, t4
	addi t3, t3, -1
	addi t4, zero, 8
	xor t4, t4, s0
	and t4, t4, t3
	xor s0, s0, t4
	addi t4, zero, 6
	sltu t3, t0, t4
	addi t3, t3, -1
	addi t4, zero, 7
	xor t4, t4, s0
	and t4, t4, t3
	xor s0, s0, t4
	addi t4, zero, 7
	sltu t3, t0, t4
	addi t3, t3, -1
	addi t4, zero, 6
	xor t4, t4, s0
	and t4, t4, t3
	xor s0, s0, t4
	addi t4, zero, 8
	sltu t3, t0, t4
	addi t3, t3, -1
	addi t4, zero, 5
	xor t4, t4, s0
	and t4, t4, t3
	xor s0, s0, t4
	addi t4, zero, 22
	sltu t3, t0, t4
	addi t3, t3, -1
	addi t4, zero, 4
	xor t4, t4, s0
	and t4, t4, t3
	xor s0, s0, t4
	addi t4, zero, 59
	sltu t3, t0, t4
	addi t3, t3, -1
	addi t4, zero, 3
	xor t4, t4, s0
	and t4, t4, t3
	xor s0, s0, t4
	sd s0, 168(s6)
	addi t2, zero, 16
	sltu t2, t2, t0
	slli t2, t2, 9
	addi t2, t2, 512
	sd t2, 128(s6)
	lla s9, {VG_RSA_KEYGEN_TRIAL32}
	ld s10, 128(s6)
227:
	ld s1, 0(s9)
	srli s2, s1, 32
	slli s1, s1, 32
	srli s1, s1, 32
	addi s0, zero, 0
	addi t3, a7, 0
	slli t5, t0, 1
228:
	lwu t2, 0(t3)
	add t2, t2, s0
	mul t4, t2, s2
	slli t4, t4, 32
	srli t4, t4, 32
	mul t4, t4, s1
	add t4, t4, t2
	srli s0, t4, 32
	addi t3, t3, 4
	addi t5, t5, -1
	bnez t5, 228b
	addi t2, zero, 1
	sltu t4, s0, t2
	xor t6, s0, s1
	sltu t6, t6, t2
	or a4, t4, t6
	addi s9, s9, 8
	addi s10, s10, -1
	addi t2, a4, -1
	and s10, s10, t2
	bnez s10, 227b
	bnez a4, 229f
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
231:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 231b
	slli t3, t0, 3
	add t3, t3, a2
	addi t3, t3, -8
	addi s0, zero, 1
	sd s0, 0(t3)
	addi a1, t0, 64
232:
	addi t3, a5, 0
	addi t4, a2, 0
	addi t5, t0, 0
	addi s4, zero, 0
233:
	ld s2, 0(t4)
	slli s3, s2, 1
	add s3, s3, s4
	srli s4, s2, 63
	sd s3, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 233b
	sd s4, 0(t3)
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
	addi a1, a1, -1
	bnez a1, 232b
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
	addi a3, a2, 0
	addi a4, a2, 0
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
296:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 296b
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
297:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 297b
298:
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
	beqz t5, 299f
2101:
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
	bnez t5, 2101b
	j 2100f
299:
2100:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2102f
2104:
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
	bnez t5, 2104b
	j 2103f
2102:
2103:
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
	bnez a1, 298b
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
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2106:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2106b
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
	addi t3, a7, 0
	addi t5, t0, 0
	addi s0, zero, 0
	addi s1, zero, 1
2109:
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
	bnez t5, 2109b
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
2110:
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
	bnez t5, 2110b
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
2111:
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
	bnez t5, 2111b
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
2112:
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
	bnez t5, 2112b
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
2113:
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
	bnez t5, 2113b
	srli s4, s0, 1
	xor s4, s4, s0
	and s4, s4, s3
	xor s4, s4, s0
	sd s4, 0(t4)
	addi t2, zero, 1
	sd t2, 176(s6)
	addi t2, zero, 0
	sd t2, 16(s6)
	addi t2, zero, 4
	sd t2, 160(s6)
2114:
	ld t2, 144(s6)
	ld t3, 152(s6)
	sub t2, t2, t3
	ld t3, 216(s6)
	sltu t4, t2, t3
	bnez t4, 2115f
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
2117:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2117b
	add t4, a7, s8
	addi t4, t4, -1
	addi a0, s7, 0
	addi t5, s8, 0
2118:
	lbu s0, 0(a0)
	sb s0, 0(t4)
	addi a0, a0, 1
	addi t4, t4, -1
	addi t5, t5, -1
	bnez t5, 2118b
	addi a7, s6, 256
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	ld a3, 0(t3)
	srli a3, a3, 1
	addi t3, t3, 8
	addi t5, t0, -1
2119:
	ld t2, 0(t3)
	or a3, a3, t2
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2119b
	addi t2, zero, 0
	sltu s9, t2, a3
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
2120:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2120b
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
	and s9, s9, s4
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
2122:
	ld s0, 0(t4)
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi t5, t5, -1
	bnez t5, 2122b
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	ld t2, 0(t3)
	ori t2, t2, 2
	sd t2, 0(t3)
	slli t4, t0, 3
	add t3, t3, t4
	addi t3, t3, -8
	addi t4, zero, -1
	srli t4, t4, 1
	ld t2, 0(t3)
	and t2, t2, t4
	sd t2, 0(t3)
	addi t2, zero, 0
	sub s4, t2, s9
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
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
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2124:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2124b
	ld t2, 16(s6)
	add t2, t2, s9
	sd t2, 16(s6)
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
2125:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2125b
2126:
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
	beqz t5, 2127f
2129:
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
	bnez t5, 2129b
	j 2128f
2127:
2128:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2130f
2132:
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
	bnez t5, 2132b
	j 2131f
2130:
2131:
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
	bnez a1, 2126b
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
2133:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2133b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2134:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2134b
	addi a0, s6, 0
	ld a1, 0(s6)
	call {vg_miller_rabin_round}
	slli a0, a0, 32
	srli a0, a0, 32
	addi a7, s6, 256
	ld t0, 48(s6)
	ld t1, 56(s6)
	beqz a0, 2135f
	ld t2, 176(s6)
	addi t2, t2, 1
	sd t2, 176(s6)
	addi t3, zero, 17
	sltu t5, t2, t3
	xori t5, t5, 1
	ld t2, 16(s6)
	ld t3, 168(s6)
	sltu t4, t2, t3
	xori t4, t4, 1
	and t4, t4, t5
	addi t3, zero, 3
	mul t4, t4, t3
	addi t3, zero, 4
	sub t4, t3, t4
	sd t4, 160(s6)
	j 2136f
2135:
	addi t2, zero, 2
	sd t2, 160(s6)
2136:
	j 2116f
2115:
	addi t2, zero, 0
	sd t2, 160(s6)
2116:
	ld t2, 160(s6)
	addi t2, t2, -4
	beqz t2, 2114b
	ld t2, 152(s6)
	sd t2, 176(s11)
	ld t2, 160(s6)
	beqz t2, 2137f
	addi t2, t2, -1
	beqz t2, 2139f
	ld t2, 176(s11)
	ld t3, 120(s11)
	sd t2, 0(t3)
	addi a0, zero, 3
	j 2140f
2139:
	ld t5, 112(s11)
	add t3, a7, t5
	addi t3, t3, -1
	ld t4, 104(s11)
2141:
	lbu t2, 0(t3)
	sb t2, 0(t4)
	addi t4, t4, 1
	addi t3, t3, -1
	addi t5, t5, -1
	bnez t5, 2141b
	ld t2, 176(s11)
	ld t3, 120(s11)
	sd t2, 0(t3)
	addi a0, zero, 1
2140:
	j 2138f
2137:
	addi t2, zero, 0
	sd t2, 176(s11)
	ld t2, 176(s11)
	ld t3, 120(s11)
	sd t2, 0(t3)
	addi a0, zero, 0
2138:
	j 230f
229:
	ld t2, 176(s11)
	ld t3, 120(s11)
	sd t2, 0(t3)
	addi a0, zero, 3
230:
	j 226f
225:
	ld t2, 176(s11)
	ld t3, 120(s11)
	sd t2, 0(t3)
	addi a0, zero, 3
226:
	j 215f
214:
	ld t2, 176(s11)
	ld t3, 120(s11)
	sd t2, 0(t3)
	addi a0, zero, 2
215:
	j 22f
21:
	addi t2, zero, 0
	sd t2, 176(s11)
	ld t2, 176(s11)
	ld t3, 120(s11)
	sd t2, 0(t3)
	addi a0, zero, 0
22:
	addi t2, sp, 0
	ld ra, 96(t2)
	ld s0, 0(t2)
	ld s1, 8(t2)
	ld s2, 16(t2)
	ld s3, 24(t2)
	ld s4, 32(t2)
	ld s5, 40(t2)
	ld s6, 48(t2)
	ld s7, 56(t2)
	ld s8, 64(t2)
	ld s9, 72(t2)
	ld s10, 80(t2)
	ld s11, 88(t2)
	addi sp, sp, 192
	ret
	.option pop

vg_rsa_prime_search:
	.option push
	.option arch, +m, +c
	addi sp, sp, -160
	addi t6, sp, 0
	ld t0, 160(t6)
	ld t1, 168(t6)
	ld t2, 176(t6)
	ld t3, 184(t6)
	ld t4, 0(t3)
	sd s0, 32(t6)
	addi s0, t6, 0
	sd a0, 40(s0)
	sd a1, 48(s0)
	sd a2, 56(s0)
	sd a3, 64(s0)
	sd a4, 72(s0)
	sd a5, 80(s0)
	sd a6, 88(s0)
	sd a7, 96(s0)
	sd t0, 104(s0)
	sd t1, 112(s0)
	sd t2, 120(s0)
	sd t3, 144(s0)
	sd t4, 0(s0)
	sd a1, 8(s0)
	slli t4, a1, 15
	add t4, t4, a1
	sd t4, 16(s0)
	addi t5, zero, 0
	sd t5, 24(s0)
	sd t5, 128(s0)
	addi sp, sp, -16
	sd ra, 8(sp)
20:
	ld t1, 0(s0)
	beqz t1, 21f
	addi sp, sp, -32
	ld a0, 40(s0)
	ld a1, 48(s0)
	ld a2, 56(s0)
	ld a3, 64(s0)
	ld a4, 72(s0)
	ld a5, 80(s0)
	ld a6, 88(s0)
	ld a7, 96(s0)
	ld t1, 104(s0)
	ld t2, 112(s0)
	ld t3, 120(s0)
	addi t0, sp, 0
	sd t1, 0(t0)
	sd t2, 8(t0)
	sd t3, 16(t0)
	call {vg_rsa_keygen_candidate}
	addi sp, sp, 32
	slli t1, a0, 32
	srli t1, t1, 32
	ld t3, 56(s0)
	ld t2, 0(t3)
	addi t4, t1, -1
	beqz t4, 23f
	beqz t1, 25f
	beqz t2, 27f
	ld t3, 96(s0)
	ld t4, 104(s0)
	ld t5, 128(s0)
	add t3, t3, t2
	sub t4, t4, t2
	add t5, t5, t2
	addi t6, zero, 4
	sd t3, 96(s0)
	sd t4, 104(s0)
	sd t5, 128(s0)
	sd t6, 136(s0)
	addi t5, t1, -2
	beqz t5, 29f
	ld t3, 0(s0)
	addi t3, t3, -1
	sd t3, 0(s0)
	j 210f
29:
210:
	j 28f
27:
	addi t2, zero, 0
	addi t3, zero, 3
	sd t2, 0(s0)
	sd t2, 24(s0)
	sd t3, 136(s0)
	ld a1, 40(s0)
	ld a2, 48(s0)
	addi a3, zero, 0
211:
	sb a3, 0(a1)
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 211b
28:
	j 26f
25:
	ld t2, 104(s0)
	ld t3, 16(s0)
	sltu t4, t2, t3
	beqz t4, 212f
	ld t4, 8(s0)
	slli t4, t4, 4
	sltu t0, t2, t4
	addi t5, zero, 0
	sub t0, t5, t0
	xor t5, t2, t4
	and t5, t5, t0
	xor t5, t5, t2
	add t5, t5, t5
	sltu t0, t5, t3
	addi t6, zero, 0
	sub t0, t6, t0
	xor t6, t5, t3
	and t6, t6, t0
	xor t6, t6, t3
	addi t4, zero, 0
	sd t6, 24(s0)
	sd t4, 136(s0)
	j 213f
212:
	addi t2, zero, 0
	addi t3, zero, 3
	sd t2, 0(s0)
	sd t2, 24(s0)
	sd t3, 136(s0)
	ld a1, 40(s0)
	ld a2, 48(s0)
	addi a3, zero, 0
214:
	sb a3, 0(a1)
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 214b
213:
26:
	j 24f
23:
	ld t3, 128(s0)
	add t3, t3, t2
	sd t3, 128(s0)
	addi t2, zero, 0
	addi t3, zero, 1
	sd t2, 0(s0)
	sd t2, 24(s0)
	sd t3, 136(s0)
24:
	j 22f
21:
	addi t2, zero, 0
	addi t3, zero, 3
	sd t2, 0(s0)
	sd t2, 24(s0)
	sd t3, 136(s0)
	ld a1, 40(s0)
	ld a2, 48(s0)
	addi a3, zero, 0
215:
	sb a3, 0(a1)
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 215b
22:
	ld t1, 136(s0)
	addi t1, t1, -4
	beqz t1, 20b
	ld ra, 8(sp)
	addi sp, sp, 16
	ld t0, 144(s0)
	ld t1, 0(s0)
	ld t2, 8(s0)
	ld t3, 16(s0)
	ld t4, 24(s0)
	ld t5, 56(s0)
	ld t6, 128(s0)
	ld a0, 136(s0)
	ld s0, 32(s0)
	sd t1, 0(t0)
	sd t2, 8(t0)
	sd t3, 16(t0)
	sd t4, 24(t0)
	sd t6, 0(t5)
	addi sp, sp, 160
	ret
	.option pop
