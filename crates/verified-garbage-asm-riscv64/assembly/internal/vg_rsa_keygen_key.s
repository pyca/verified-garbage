// The functions of `src/internal/vg_rsa_keygen_key.rs` of `verified-garbage-asm-riscv64`, as text: generated from
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
	addi t3, s8, 1
	srli t3, t3, 1
233:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 233b
	addi t1, zero, 2
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s8, 1
	srli t3, t3, 1
	slli t3, t3, 3
	add t1, t1, t3
	addi t5, zero, 0
	sd t5, 0(t1)
	addi a4, zero, 2
	mul a4, a4, s10
	add a4, a4, s11
	addi a4, a4, 256
	ld t5, 0(a4)
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
	srli t3, t3, 1
	addi t3, t3, 1
234:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 234b
	addi t0, zero, 0
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld a5, 0(t0)
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
	addi t3, s8, 1
	srli t3, t3, 1
	addi t4, zero, 0
235:
	ld t5, 0(t2)
	mul t6, a5, t5
	mulhu t5, a5, t5
	ld a4, 0(t1)
	add t6, t6, a4
	sltu a4, t6, a4
	add t5, t5, a4
	add t6, t6, t4
	sltu a4, t6, t4
	add t4, t5, a4
	sd t6, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 235b
	sd t4, 0(t0)
	addi t0, zero, 6
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t3, s8, 1
	srli t3, t3, 1
	addi t3, t3, 1
	addi t5, zero, 0
236:
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t3, t3, -1
	bnez t3, 236b
	addi t0, zero, 7
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t3, s8, 1
	srli t3, t3, 1
	addi t3, t3, 1
	addi t5, zero, 0
237:
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t3, t3, -1
	bnez t3, 237b
	addi t0, zero, 7
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t5, zero, 1
	sd t5, 0(t0)
	addi t0, zero, 9
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	sd t5, 0(t0)
	addi t3, s8, 1
	srli t3, t3, 1
	add s7, t3, t3
	add s7, s7, t3
	addi s7, s7, 2
238:
	addi t0, zero, 4
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld a4, 0(t0)
	addi t0, zero, 5
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld t0, 0(t0)
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
	sd s0, 0(t0)
	sd s1, 8(t0)
	sd s2, 16(t0)
	sd s3, 24(t0)
	sd s4, 32(t0)
	sd s5, 40(t0)
	addi t0, zero, 12
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	sd s6, 0(t0)
	sd a0, 8(t0)
	sd a1, 16(t0)
	sd a2, 24(t0)
	sd a3, 32(t0)
	sd a6, 40(t0)
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
	addi s1, zero, 9
	mul s1, s1, s10
	add s1, s1, s11
	addi s1, s1, 256
	ld s1, 24(s1)
	addi s2, zero, 9
	mul s2, s2, s10
	add s2, s2, s11
	addi s2, s2, 256
	ld s2, 32(s2)
	srai s3, a5, 63
	srai s4, a7, 63
	srai s5, s1, 63
	addi t0, zero, 4
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 5
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t4, zero, 0
	addi a4, zero, 0
	addi a0, zero, 0
	addi a1, zero, 0
	srai s6, s2, 63
	ld t5, 0(t0)
	ld t6, 0(t1)
	mul t2, a5, t5
	add t4, t4, t2
	sltu t2, t4, t2
	add a4, a4, t2
	mulhu t2, a5, t5
	add a4, a4, t2
	and t2, s3, t5
	sub a4, a4, t2
	mul t2, a7, t6
	add t4, t4, t2
	sltu t2, t4, t2
	add a4, a4, t2
	mulhu t2, a7, t6
	add a4, a4, t2
	and t2, s4, t6
	sub a4, a4, t2
	mul t2, s1, t5
	add a0, a0, t2
	sltu t2, a0, t2
	add a1, a1, t2
	mulhu t2, s1, t5
	add a1, a1, t2
	and t2, s5, t5
	sub a1, a1, t2
	mul t2, s2, t6
	add a0, a0, t2
	sltu t2, a0, t2
	add a1, a1, t2
	mulhu t2, s2, t6
	add a1, a1, t2
	and t2, s6, t6
	sub a1, a1, t2
	srli a2, t4, 59
	addi t4, a4, 0
	srai a4, a4, 63
	srli a3, a0, 59
	addi a0, a1, 0
	srai a1, a1, 63
	addi t3, s8, 1
	srli t3, t3, 1
239:
	ld t5, 8(t0)
	ld t6, 8(t1)
	mul t2, a5, t5
	add t4, t4, t2
	sltu t2, t4, t2
	add a4, a4, t2
	mulhu t2, a5, t5
	add a4, a4, t2
	and t2, s3, t5
	sub a4, a4, t2
	mul t2, a7, t6
	add t4, t4, t2
	sltu t2, t4, t2
	add a4, a4, t2
	mulhu t2, a7, t6
	add a4, a4, t2
	and t2, s4, t6
	sub a4, a4, t2
	mul t2, s1, t5
	add a0, a0, t2
	sltu t2, a0, t2
	add a1, a1, t2
	mulhu t2, s1, t5
	add a1, a1, t2
	and t2, s5, t5
	sub a1, a1, t2
	mul t2, s2, t6
	add a0, a0, t2
	sltu t2, a0, t2
	add a1, a1, t2
	mulhu t2, s2, t6
	add a1, a1, t2
	and t2, s6, t6
	sub a1, a1, t2
	slli t2, t4, 5
	add t2, a2, t2
	sd t2, 0(t0)
	slli t2, a0, 5
	add t2, a3, t2
	sd t2, 0(t1)
	srli a2, t4, 59
	addi t4, a4, 0
	srai a4, a4, 63
	srli a3, a0, 59
	addi a0, a1, 0
	srai a1, a1, 63
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 239b
	slli t2, a2, 59
	srai t2, t2, 59
	sd t2, 0(t0)
	slli t2, a3, 59
	srai t2, t2, 59
	sd t2, 0(t1)
	addi t0, zero, 11
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld s0, 0(t0)
	ld s1, 8(t0)
	ld s2, 16(t0)
	ld s3, 24(t0)
	ld s4, 32(t0)
	ld s5, 40(t0)
	addi t0, zero, 12
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld s6, 0(t0)
	ld a0, 8(t0)
	ld a1, 16(t0)
	ld a2, 24(t0)
	ld a3, 32(t0)
	ld a6, 40(t0)
	addi t0, zero, 11
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	sd s0, 0(t0)
	sd s1, 8(t0)
	sd s2, 16(t0)
	sd s3, 24(t0)
	sd s4, 32(t0)
	sd s5, 40(t0)
	addi t0, zero, 12
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	sd s6, 0(t0)
	sd a0, 8(t0)
	sd a1, 16(t0)
	sd a2, 24(t0)
	sd a3, 32(t0)
	sd a6, 40(t0)
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
	addi s1, zero, 9
	mul s1, s1, s10
	add s1, s1, s11
	addi s1, s1, 256
	ld s1, 24(s1)
	addi s2, zero, 9
	mul s2, s2, s10
	add s2, s2, s11
	addi s2, s2, 256
	ld s2, 32(s2)
	srai s3, a5, 63
	srai s4, a7, 63
	srai s5, s1, 63
	addi t0, zero, 6
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 7
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t4, zero, 0
	addi a4, zero, 0
	addi a0, zero, 0
	addi a1, zero, 0
	addi t2, zero, 2
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi a6, zero, 0
	addi s0, zero, 0
	ld t5, 0(t0)
	ld t6, 0(t1)
	mul s6, a5, t5
	add t4, t4, s6
	sltu s6, t4, s6
	add a4, a4, s6
	mulhu s6, a5, t5
	add a4, a4, s6
	and s6, s3, t5
	sub a4, a4, s6
	mul s6, a7, t6
	add t4, t4, s6
	sltu s6, t4, s6
	add a4, a4, s6
	mulhu s6, a7, t6
	add a4, a4, s6
	and s6, s4, t6
	sub a4, a4, s6
	mul s6, s1, t5
	add a0, a0, s6
	sltu s6, a0, s6
	add a1, a1, s6
	mulhu s6, s1, t5
	add a1, a1, s6
	and s6, s5, t5
	sub a1, a1, s6
	mul s6, s2, t6
	add a0, a0, s6
	sltu s6, a0, s6
	add a1, a1, s6
	mulhu s6, s2, t6
	add a1, a1, s6
	srai s6, s2, 63
	and s6, s6, t6
	sub a1, a1, s6
	addi t5, zero, 9
	mul t5, t5, s10
	add t5, t5, s11
	addi t5, t5, 256
	ld t5, 40(t5)
	mul a2, t4, t5
	mul a3, a0, t5
	ld t5, 0(t2)
	mul s6, a2, t5
	add s6, s6, t4
	sltu t4, s6, t4
	mulhu t6, a2, t5
	add t6, t6, t4
	add t4, s6, a6
	sltu s6, t4, a6
	add a6, t6, s6
	mul s6, a3, t5
	add s6, s6, a0
	sltu a0, s6, a0
	mulhu t6, a3, t5
	add t6, t6, a0
	add a0, s6, s0
	sltu s6, a0, s0
	add s0, t6, s6
	addi t4, a4, 0
	srai a4, a4, 63
	addi a0, a1, 0
	srai a1, a1, 63
	addi t3, s8, 1
	srli t3, t3, 1
	addi t3, t3, -1
	beqz t3, 240f
242:
	ld t5, 8(t0)
	ld t6, 8(t1)
	mul s6, a5, t5
	add t4, t4, s6
	sltu s6, t4, s6
	add a4, a4, s6
	mulhu s6, a5, t5
	add a4, a4, s6
	and s6, s3, t5
	sub a4, a4, s6
	mul s6, a7, t6
	add t4, t4, s6
	sltu s6, t4, s6
	add a4, a4, s6
	mulhu s6, a7, t6
	add a4, a4, s6
	and s6, s4, t6
	sub a4, a4, s6
	mul s6, s1, t5
	add a0, a0, s6
	sltu s6, a0, s6
	add a1, a1, s6
	mulhu s6, s1, t5
	add a1, a1, s6
	and s6, s5, t5
	sub a1, a1, s6
	mul s6, s2, t6
	add a0, a0, s6
	sltu s6, a0, s6
	add a1, a1, s6
	mulhu s6, s2, t6
	add a1, a1, s6
	srai s6, s2, 63
	and s6, s6, t6
	sub a1, a1, s6
	ld t5, 8(t2)
	mul s6, a2, t5
	add s6, s6, t4
	sltu t4, s6, t4
	mulhu t6, a2, t5
	add t6, t6, t4
	add t4, s6, a6
	sltu s6, t4, a6
	add a6, t6, s6
	sd t4, 0(t0)
	mul s6, a3, t5
	add s6, s6, a0
	sltu a0, s6, a0
	mulhu t6, a3, t5
	add t6, t6, a0
	add a0, s6, s0
	sltu s6, a0, s0
	add s0, t6, s6
	sd a0, 0(t1)
	addi t4, a4, 0
	srai a4, a4, 63
	addi a0, a1, 0
	srai a1, a1, 63
	addi t0, t0, 8
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 242b
	j 241f
240:
241:
	ld t5, 8(t0)
	ld t6, 8(t1)
	mul s6, a5, t5
	add t4, t4, s6
	sltu s6, t4, s6
	add a4, a4, s6
	mulhu s6, a5, t5
	add a4, a4, s6
	and s6, s3, t5
	sub a4, a4, s6
	mul s6, a7, t6
	add t4, t4, s6
	sltu s6, t4, s6
	add a4, a4, s6
	mulhu s6, a7, t6
	add a4, a4, s6
	and s6, s4, t6
	sub a4, a4, s6
	mul s6, s1, t5
	add a0, a0, s6
	sltu s6, a0, s6
	add a1, a1, s6
	mulhu s6, s1, t5
	add a1, a1, s6
	and s6, s5, t5
	sub a1, a1, s6
	mul s6, s2, t6
	add a0, a0, s6
	sltu s6, a0, s6
	add a1, a1, s6
	mulhu s6, s2, t6
	add a1, a1, s6
	srai s6, s2, 63
	and s6, s6, t6
	sub a1, a1, s6
	srai t5, t4, 63
	add t4, t4, a6
	sltu t6, t4, a6
	sd t4, 0(t0)
	add t5, t5, t6
	sd t5, 8(t0)
	srai t5, a0, 63
	add a0, a0, s0
	sltu t6, a0, s0
	sd a0, 0(t1)
	add t5, t5, t6
	sd t5, 8(t1)
	addi t0, zero, 11
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld s0, 0(t0)
	ld s1, 8(t0)
	ld s2, 16(t0)
	ld s3, 24(t0)
	ld s4, 32(t0)
	ld s5, 40(t0)
	addi t0, zero, 12
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld s6, 0(t0)
	ld a0, 8(t0)
	ld a1, 16(t0)
	ld a2, 24(t0)
	ld a3, 32(t0)
	ld a6, 40(t0)
	addi s7, s7, -1
	bnez s7, 238b
	addi a5, zero, 1
	addi t0, zero, 13
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
	srli t3, t3, 1
	addi t3, t3, 1
	addi t4, zero, 0
243:
	ld t5, 0(t2)
	mul t6, a5, t5
	mulhu t5, a5, t5
	ld a4, 0(t1)
	add t6, t6, a4
	sltu a4, t6, a4
	add t5, t5, a4
	add t6, t6, t4
	sltu a4, t6, t4
	add t4, t5, a4
	sd t6, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 243b
	addi t1, zero, 6
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s8, 1
	srli t3, t3, 1
	slli t3, t3, 3
	add t1, t1, t3
	ld t4, 0(t1)
	srai t4, t4, 63
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
	srli t3, t3, 1
	addi t3, t3, 1
244:
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
	bnez t3, 244b
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
	srli t3, t3, 1
	addi t3, t3, 1
	addi t4, zero, 0
245:
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
	bnez t3, 245b
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
	srli t3, t3, 1
	addi t3, t3, 1
	addi t5, zero, 0
	sub t4, t5, t4
246:
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
	bnez t3, 246b
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
	srli t3, t3, 1
	addi t3, t3, 1
	addi t4, zero, 0
247:
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
	bnez t3, 247b
	addi t1, zero, 4
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s8, 1
	srli t3, t3, 1
	slli t3, t3, 3
	add t1, t1, t3
	ld t4, 0(t1)
	srai t4, t4, 63
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
	srli t3, t3, 1
	addi t3, t3, 1
248:
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
	bnez t3, 248b
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
	srli t3, t3, 1
	addi t3, t3, 1
	addi t4, zero, 0
249:
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
	bnez t3, 249b
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
	srli t3, t3, 1
	addi t3, t3, 1
	addi t5, zero, 0
	sub t4, t5, t4
250:
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
	bnez t3, 250b
	addi t3, s8, 1
	srli t3, t3, 1
	slli s7, t3, 4
	sub s7, s7, t3
	addi s7, s7, 10
251:
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
	srli t3, t3, 1
	addi t3, t3, 1
	addi t4, zero, 0
252:
	ld t5, 0(t2)
	mul t6, a5, t5
	mulhu t5, a5, t5
	ld a4, 0(t1)
	add t6, t6, a4
	sltu a4, t6, a4
	add t5, t5, a4
	add t6, t6, t4
	sltu a4, t6, t4
	add t4, t5, a4
	sd t6, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 252b
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
	srli t3, t3, 1
	addi t3, t3, 1
	addi t4, zero, 0
253:
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
	bnez t3, 253b
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
	srli t3, t3, 1
	addi t3, t3, 1
	addi t5, zero, 0
	sub t4, t5, t4
254:
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
	bnez t3, 254b
	addi s7, s7, -1
	bnez s7, 251b
	addi t0, zero, 1
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t3, s9, 1
	addi t5, zero, 0
255:
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t3, t3, -1
	bnez t3, 255b
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
	srli t3, t3, 1
	addi t3, t3, 1
	addi t4, zero, 0
256:
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
	bnez t3, 256b
	addi t1, zero, 4
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s8, 1
	srli t3, t3, 1
	slli t3, t3, 3
	add t1, t1, t3
	ld t4, 0(t1)
	srai t4, t4, 63
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
	srli t3, t3, 1
	addi t3, t3, 1
257:
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
	bnez t3, 257b
	addi t0, zero, 3
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t3, s9, 1
	addi t5, zero, 0
258:
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t3, t3, -1
	bnez t3, 258b
	addi t0, zero, 3
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 6
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s8, 1
	srli t3, t3, 1
	addi t3, t3, 1
259:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 259b
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
260:
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
	bnez t3, 260b
	addi t0, zero, 36
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 32
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
	addi t0, zero, 37
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 35
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
	addi t0, zero, 38
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t3, s9, 1
	addi t5, zero, 0
263:
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t3, t3, -1
	bnez t3, 263b
	slli s7, s9, 6
	addi a4, zero, -1
264:
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
	beqz t2, 265f
267:
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
	bnez t2, 267b
	j 266f
265:
266:
	addi t2, s9, 1
	srli t2, t2, 2
	beqz t2, 268f
270:
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
	bnez t2, 270b
	j 269f
268:
269:
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
	bnez s7, 264b
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
271:
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
	bnez t3, 271b
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
272:
	ld t5, 0(t1)
	ld t6, 0(t2)
	xor t5, t5, t6
	or t4, t4, t5
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 272b
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
	addi t0, zero, 41
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 36
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
	addi t0, zero, 37
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 40
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
	addi t0, zero, 42
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
	addi t2, s9, 1
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
	bnez s7, 278b
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
	addi t0, zero, 0
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 42
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
	addi t0, zero, 8
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 40
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
	addi s8, zero, 2
	addi t0, zero, 2
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 8
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s8, 1
	srli t3, t3, 1
288:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 288b
	addi t1, zero, 2
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s8, 1
	srli t3, t3, 1
	slli t3, t3, 3
	add t1, t1, t3
	addi t5, zero, 0
	sd t5, 0(t1)
	addi a4, zero, 2
	mul a4, a4, s10
	add a4, a4, s11
	addi a4, a4, 256
	ld t5, 0(a4)
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
	srli t3, t3, 1
	addi t3, t3, 1
289:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 289b
	addi t0, zero, 0
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld a5, 0(t0)
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
	addi t3, s8, 1
	srli t3, t3, 1
	addi t4, zero, 0
290:
	ld t5, 0(t2)
	mul t6, a5, t5
	mulhu t5, a5, t5
	ld a4, 0(t1)
	add t6, t6, a4
	sltu a4, t6, a4
	add t5, t5, a4
	add t6, t6, t4
	sltu a4, t6, t4
	add t4, t5, a4
	sd t6, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 290b
	sd t4, 0(t0)
	addi t0, zero, 6
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t3, s8, 1
	srli t3, t3, 1
	addi t3, t3, 1
	addi t5, zero, 0
291:
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t3, t3, -1
	bnez t3, 291b
	addi t0, zero, 7
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t3, s8, 1
	srli t3, t3, 1
	addi t3, t3, 1
	addi t5, zero, 0
292:
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t3, t3, -1
	bnez t3, 292b
	addi t0, zero, 7
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t5, zero, 1
	sd t5, 0(t0)
	addi t0, zero, 9
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	sd t5, 0(t0)
	addi t3, s8, 1
	srli t3, t3, 1
	add s7, t3, t3
	add s7, s7, t3
	addi s7, s7, 2
293:
	addi t0, zero, 4
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld a4, 0(t0)
	addi t0, zero, 5
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld t0, 0(t0)
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
	sd s0, 0(t0)
	sd s1, 8(t0)
	sd s2, 16(t0)
	sd s3, 24(t0)
	sd s4, 32(t0)
	sd s5, 40(t0)
	addi t0, zero, 12
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	sd s6, 0(t0)
	sd a0, 8(t0)
	sd a1, 16(t0)
	sd a2, 24(t0)
	sd a3, 32(t0)
	sd a6, 40(t0)
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
	addi s1, zero, 9
	mul s1, s1, s10
	add s1, s1, s11
	addi s1, s1, 256
	ld s1, 24(s1)
	addi s2, zero, 9
	mul s2, s2, s10
	add s2, s2, s11
	addi s2, s2, 256
	ld s2, 32(s2)
	srai s3, a5, 63
	srai s4, a7, 63
	srai s5, s1, 63
	addi t0, zero, 4
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 5
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t4, zero, 0
	addi a4, zero, 0
	addi a0, zero, 0
	addi a1, zero, 0
	srai s6, s2, 63
	ld t5, 0(t0)
	ld t6, 0(t1)
	mul t2, a5, t5
	add t4, t4, t2
	sltu t2, t4, t2
	add a4, a4, t2
	mulhu t2, a5, t5
	add a4, a4, t2
	and t2, s3, t5
	sub a4, a4, t2
	mul t2, a7, t6
	add t4, t4, t2
	sltu t2, t4, t2
	add a4, a4, t2
	mulhu t2, a7, t6
	add a4, a4, t2
	and t2, s4, t6
	sub a4, a4, t2
	mul t2, s1, t5
	add a0, a0, t2
	sltu t2, a0, t2
	add a1, a1, t2
	mulhu t2, s1, t5
	add a1, a1, t2
	and t2, s5, t5
	sub a1, a1, t2
	mul t2, s2, t6
	add a0, a0, t2
	sltu t2, a0, t2
	add a1, a1, t2
	mulhu t2, s2, t6
	add a1, a1, t2
	and t2, s6, t6
	sub a1, a1, t2
	srli a2, t4, 59
	addi t4, a4, 0
	srai a4, a4, 63
	srli a3, a0, 59
	addi a0, a1, 0
	srai a1, a1, 63
	addi t3, s8, 1
	srli t3, t3, 1
294:
	ld t5, 8(t0)
	ld t6, 8(t1)
	mul t2, a5, t5
	add t4, t4, t2
	sltu t2, t4, t2
	add a4, a4, t2
	mulhu t2, a5, t5
	add a4, a4, t2
	and t2, s3, t5
	sub a4, a4, t2
	mul t2, a7, t6
	add t4, t4, t2
	sltu t2, t4, t2
	add a4, a4, t2
	mulhu t2, a7, t6
	add a4, a4, t2
	and t2, s4, t6
	sub a4, a4, t2
	mul t2, s1, t5
	add a0, a0, t2
	sltu t2, a0, t2
	add a1, a1, t2
	mulhu t2, s1, t5
	add a1, a1, t2
	and t2, s5, t5
	sub a1, a1, t2
	mul t2, s2, t6
	add a0, a0, t2
	sltu t2, a0, t2
	add a1, a1, t2
	mulhu t2, s2, t6
	add a1, a1, t2
	and t2, s6, t6
	sub a1, a1, t2
	slli t2, t4, 5
	add t2, a2, t2
	sd t2, 0(t0)
	slli t2, a0, 5
	add t2, a3, t2
	sd t2, 0(t1)
	srli a2, t4, 59
	addi t4, a4, 0
	srai a4, a4, 63
	srli a3, a0, 59
	addi a0, a1, 0
	srai a1, a1, 63
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 294b
	slli t2, a2, 59
	srai t2, t2, 59
	sd t2, 0(t0)
	slli t2, a3, 59
	srai t2, t2, 59
	sd t2, 0(t1)
	addi t0, zero, 11
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld s0, 0(t0)
	ld s1, 8(t0)
	ld s2, 16(t0)
	ld s3, 24(t0)
	ld s4, 32(t0)
	ld s5, 40(t0)
	addi t0, zero, 12
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld s6, 0(t0)
	ld a0, 8(t0)
	ld a1, 16(t0)
	ld a2, 24(t0)
	ld a3, 32(t0)
	ld a6, 40(t0)
	addi t0, zero, 11
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	sd s0, 0(t0)
	sd s1, 8(t0)
	sd s2, 16(t0)
	sd s3, 24(t0)
	sd s4, 32(t0)
	sd s5, 40(t0)
	addi t0, zero, 12
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	sd s6, 0(t0)
	sd a0, 8(t0)
	sd a1, 16(t0)
	sd a2, 24(t0)
	sd a3, 32(t0)
	sd a6, 40(t0)
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
	addi s1, zero, 9
	mul s1, s1, s10
	add s1, s1, s11
	addi s1, s1, 256
	ld s1, 24(s1)
	addi s2, zero, 9
	mul s2, s2, s10
	add s2, s2, s11
	addi s2, s2, 256
	ld s2, 32(s2)
	srai s3, a5, 63
	srai s4, a7, 63
	srai s5, s1, 63
	addi t0, zero, 6
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 7
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t4, zero, 0
	addi a4, zero, 0
	addi a0, zero, 0
	addi a1, zero, 0
	addi t2, zero, 2
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi a6, zero, 0
	addi s0, zero, 0
	ld t5, 0(t0)
	ld t6, 0(t1)
	mul s6, a5, t5
	add t4, t4, s6
	sltu s6, t4, s6
	add a4, a4, s6
	mulhu s6, a5, t5
	add a4, a4, s6
	and s6, s3, t5
	sub a4, a4, s6
	mul s6, a7, t6
	add t4, t4, s6
	sltu s6, t4, s6
	add a4, a4, s6
	mulhu s6, a7, t6
	add a4, a4, s6
	and s6, s4, t6
	sub a4, a4, s6
	mul s6, s1, t5
	add a0, a0, s6
	sltu s6, a0, s6
	add a1, a1, s6
	mulhu s6, s1, t5
	add a1, a1, s6
	and s6, s5, t5
	sub a1, a1, s6
	mul s6, s2, t6
	add a0, a0, s6
	sltu s6, a0, s6
	add a1, a1, s6
	mulhu s6, s2, t6
	add a1, a1, s6
	srai s6, s2, 63
	and s6, s6, t6
	sub a1, a1, s6
	addi t5, zero, 9
	mul t5, t5, s10
	add t5, t5, s11
	addi t5, t5, 256
	ld t5, 40(t5)
	mul a2, t4, t5
	mul a3, a0, t5
	ld t5, 0(t2)
	mul s6, a2, t5
	add s6, s6, t4
	sltu t4, s6, t4
	mulhu t6, a2, t5
	add t6, t6, t4
	add t4, s6, a6
	sltu s6, t4, a6
	add a6, t6, s6
	mul s6, a3, t5
	add s6, s6, a0
	sltu a0, s6, a0
	mulhu t6, a3, t5
	add t6, t6, a0
	add a0, s6, s0
	sltu s6, a0, s0
	add s0, t6, s6
	addi t4, a4, 0
	srai a4, a4, 63
	addi a0, a1, 0
	srai a1, a1, 63
	addi t3, s8, 1
	srli t3, t3, 1
	addi t3, t3, -1
	beqz t3, 295f
297:
	ld t5, 8(t0)
	ld t6, 8(t1)
	mul s6, a5, t5
	add t4, t4, s6
	sltu s6, t4, s6
	add a4, a4, s6
	mulhu s6, a5, t5
	add a4, a4, s6
	and s6, s3, t5
	sub a4, a4, s6
	mul s6, a7, t6
	add t4, t4, s6
	sltu s6, t4, s6
	add a4, a4, s6
	mulhu s6, a7, t6
	add a4, a4, s6
	and s6, s4, t6
	sub a4, a4, s6
	mul s6, s1, t5
	add a0, a0, s6
	sltu s6, a0, s6
	add a1, a1, s6
	mulhu s6, s1, t5
	add a1, a1, s6
	and s6, s5, t5
	sub a1, a1, s6
	mul s6, s2, t6
	add a0, a0, s6
	sltu s6, a0, s6
	add a1, a1, s6
	mulhu s6, s2, t6
	add a1, a1, s6
	srai s6, s2, 63
	and s6, s6, t6
	sub a1, a1, s6
	ld t5, 8(t2)
	mul s6, a2, t5
	add s6, s6, t4
	sltu t4, s6, t4
	mulhu t6, a2, t5
	add t6, t6, t4
	add t4, s6, a6
	sltu s6, t4, a6
	add a6, t6, s6
	sd t4, 0(t0)
	mul s6, a3, t5
	add s6, s6, a0
	sltu a0, s6, a0
	mulhu t6, a3, t5
	add t6, t6, a0
	add a0, s6, s0
	sltu s6, a0, s0
	add s0, t6, s6
	sd a0, 0(t1)
	addi t4, a4, 0
	srai a4, a4, 63
	addi a0, a1, 0
	srai a1, a1, 63
	addi t0, t0, 8
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 297b
	j 296f
295:
296:
	ld t5, 8(t0)
	ld t6, 8(t1)
	mul s6, a5, t5
	add t4, t4, s6
	sltu s6, t4, s6
	add a4, a4, s6
	mulhu s6, a5, t5
	add a4, a4, s6
	and s6, s3, t5
	sub a4, a4, s6
	mul s6, a7, t6
	add t4, t4, s6
	sltu s6, t4, s6
	add a4, a4, s6
	mulhu s6, a7, t6
	add a4, a4, s6
	and s6, s4, t6
	sub a4, a4, s6
	mul s6, s1, t5
	add a0, a0, s6
	sltu s6, a0, s6
	add a1, a1, s6
	mulhu s6, s1, t5
	add a1, a1, s6
	and s6, s5, t5
	sub a1, a1, s6
	mul s6, s2, t6
	add a0, a0, s6
	sltu s6, a0, s6
	add a1, a1, s6
	mulhu s6, s2, t6
	add a1, a1, s6
	srai s6, s2, 63
	and s6, s6, t6
	sub a1, a1, s6
	srai t5, t4, 63
	add t4, t4, a6
	sltu t6, t4, a6
	sd t4, 0(t0)
	add t5, t5, t6
	sd t5, 8(t0)
	srai t5, a0, 63
	add a0, a0, s0
	sltu t6, a0, s0
	sd a0, 0(t1)
	add t5, t5, t6
	sd t5, 8(t1)
	addi t0, zero, 11
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld s0, 0(t0)
	ld s1, 8(t0)
	ld s2, 16(t0)
	ld s3, 24(t0)
	ld s4, 32(t0)
	ld s5, 40(t0)
	addi t0, zero, 12
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld s6, 0(t0)
	ld a0, 8(t0)
	ld a1, 16(t0)
	ld a2, 24(t0)
	ld a3, 32(t0)
	ld a6, 40(t0)
	addi s7, s7, -1
	bnez s7, 293b
	addi a5, zero, 1
	addi t0, zero, 13
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
	srli t3, t3, 1
	addi t3, t3, 1
	addi t4, zero, 0
298:
	ld t5, 0(t2)
	mul t6, a5, t5
	mulhu t5, a5, t5
	ld a4, 0(t1)
	add t6, t6, a4
	sltu a4, t6, a4
	add t5, t5, a4
	add t6, t6, t4
	sltu a4, t6, t4
	add t4, t5, a4
	sd t6, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 298b
	addi t1, zero, 6
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s8, 1
	srli t3, t3, 1
	slli t3, t3, 3
	add t1, t1, t3
	ld t4, 0(t1)
	srai t4, t4, 63
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
	srli t3, t3, 1
	addi t3, t3, 1
299:
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
	bnez t3, 299b
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
	srli t3, t3, 1
	addi t3, t3, 1
	addi t4, zero, 0
2100:
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
	bnez t3, 2100b
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
	srli t3, t3, 1
	addi t3, t3, 1
	addi t5, zero, 0
	sub t4, t5, t4
2101:
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
	bnez t3, 2101b
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
	srli t3, t3, 1
	addi t3, t3, 1
	addi t4, zero, 0
2102:
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
	bnez t3, 2102b
	addi t1, zero, 4
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s8, 1
	srli t3, t3, 1
	slli t3, t3, 3
	add t1, t1, t3
	ld t4, 0(t1)
	srai t4, t4, 63
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
	srli t3, t3, 1
	addi t3, t3, 1
2103:
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
	bnez t3, 2103b
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
	srli t3, t3, 1
	addi t3, t3, 1
	addi t4, zero, 0
2104:
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
	bnez t3, 2104b
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
	srli t3, t3, 1
	addi t3, t3, 1
	addi t5, zero, 0
	sub t4, t5, t4
2105:
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
	bnez t3, 2105b
	addi t3, s8, 1
	srli t3, t3, 1
	slli s7, t3, 4
	sub s7, s7, t3
	addi s7, s7, 10
2106:
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
	srli t3, t3, 1
	addi t3, t3, 1
	addi t4, zero, 0
2107:
	ld t5, 0(t2)
	mul t6, a5, t5
	mulhu t5, a5, t5
	ld a4, 0(t1)
	add t6, t6, a4
	sltu a4, t6, a4
	add t5, t5, a4
	add t6, t6, t4
	sltu a4, t6, t4
	add t4, t5, a4
	sd t6, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 2107b
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
	srli t3, t3, 1
	addi t3, t3, 1
	addi t4, zero, 0
2108:
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
	bnez t3, 2108b
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
	srli t3, t3, 1
	addi t3, t3, 1
	addi t5, zero, 0
	sub t4, t5, t4
2109:
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
	bnez t3, 2109b
	addi s7, s7, -1
	bnez s7, 2106b
	addi t0, zero, 1
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t3, s9, 1
	addi t5, zero, 0
2110:
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t3, t3, -1
	bnez t3, 2110b
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
	srli t3, t3, 1
	addi t3, t3, 1
	addi t4, zero, 0
2111:
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
	bnez t3, 2111b
	addi t1, zero, 4
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s8, 1
	srli t3, t3, 1
	slli t3, t3, 3
	add t1, t1, t3
	ld t4, 0(t1)
	srai t4, t4, 63
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
	srli t3, t3, 1
	addi t3, t3, 1
2112:
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
	bnez t3, 2112b
	addi t0, zero, 3
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t3, s9, 1
	addi t5, zero, 0
2113:
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t3, t3, -1
	bnez t3, 2113b
	addi t0, zero, 3
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 6
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s8, 1
	srli t3, t3, 1
	addi t3, t3, 1
2114:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 2114b
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
2115:
	ld t5, 0(t1)
	ld t6, 0(t2)
	xor t5, t5, t6
	or t4, t4, t5
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 2115b
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
2116:
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
	bnez t3, 2116b
	addi t0, zero, 44
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 10
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
2117:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 2117b
	addi a2, zero, 41
	mul a2, a2, s10
	add a2, a2, s11
	addi a2, a2, 256
	addi a3, zero, 44
	mul a3, a3, s10
	add a3, a3, s11
	addi a3, a3, 256
	addi s8, s9, 0
2118:
	ld a6, 0(a2)
	addi t0, a3, 0
	addi t1, zero, 43
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s8, 0
	addi t4, zero, 0
2119:
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
	bnez t3, 2119b
	addi a2, a2, 8
	addi a3, a3, 8
	addi s8, s8, -1
	bnez s8, 2118b
	addi t0, zero, 45
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 10
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
2120:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 2120b
	addi a2, zero, 42
	mul a2, a2, s10
	add a2, a2, s11
	addi a2, a2, 256
	addi a3, zero, 45
	mul a3, a3, s10
	add a3, a3, s11
	addi a3, a3, 256
	addi s8, s9, 0
2121:
	ld a6, 0(a2)
	addi t0, a3, 0
	addi t1, zero, 43
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s8, 0
	addi t4, zero, 0
2122:
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
	bnez t3, 2122b
	addi a2, a2, 8
	addi a3, a3, 8
	addi s8, s8, -1
	bnez s8, 2121b
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
2123:
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
	bnez t3, 2123b
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
2124:
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
	bnez t3, 2124b
	addi t0, zero, 38
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t3, s9, 1
	addi t5, zero, 0
2125:
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t3, t3, -1
	bnez t3, 2125b
	slli s7, s9, 6
	addi a4, zero, -1
2126:
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
	beqz t2, 2127f
2129:
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
	bnez t2, 2129b
	j 2128f
2127:
2128:
	addi t2, s9, 1
	srli t2, t2, 2
	beqz t2, 2130f
2132:
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
	bnez t2, 2132b
	j 2131f
2130:
2131:
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
	bnez s7, 2126b
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
2133:
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
	bnez t3, 2133b
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
2134:
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
	bnez t3, 2134b
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
2135:
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
	bnez t3, 2135b
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
2136:
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
	bnez t3, 2136b
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
2137:
	ld t5, 0(t1)
	ld t6, 0(t2)
	xor t5, t5, t6
	or t4, t4, t5
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 2137b
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
2138:
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
	bnez t3, 2138b
	ld t5, 176(s11)
	bnez t5, 2139f
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
2141:
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
	bnez t3, 2141b
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
2142:
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
	bnez t3, 2142b
	addi t0, zero, 0
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 21
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
2143:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 2143b
	addi t0, zero, 8
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 48
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
2144:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 2144b
	srli s8, a1, 1
	addi t0, zero, 2
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 8
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s8, 1
	srli t3, t3, 1
2145:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 2145b
	addi t1, zero, 2
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s8, 1
	srli t3, t3, 1
	slli t3, t3, 3
	add t1, t1, t3
	addi t5, zero, 0
	sd t5, 0(t1)
	addi a4, zero, 2
	mul a4, a4, s10
	add a4, a4, s11
	addi a4, a4, 256
	ld t5, 0(a4)
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
	srli t3, t3, 1
	addi t3, t3, 1
2146:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 2146b
	addi t0, zero, 0
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld a5, 0(t0)
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
	addi t3, s8, 1
	srli t3, t3, 1
	addi t4, zero, 0
2147:
	ld t5, 0(t2)
	mul t6, a5, t5
	mulhu t5, a5, t5
	ld a4, 0(t1)
	add t6, t6, a4
	sltu a4, t6, a4
	add t5, t5, a4
	add t6, t6, t4
	sltu a4, t6, t4
	add t4, t5, a4
	sd t6, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 2147b
	sd t4, 0(t0)
	addi t0, zero, 6
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t3, s8, 1
	srli t3, t3, 1
	addi t3, t3, 1
	addi t5, zero, 0
2148:
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t3, t3, -1
	bnez t3, 2148b
	addi t0, zero, 7
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t3, s8, 1
	srli t3, t3, 1
	addi t3, t3, 1
	addi t5, zero, 0
2149:
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t3, t3, -1
	bnez t3, 2149b
	addi t0, zero, 7
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t5, zero, 1
	sd t5, 0(t0)
	addi t0, zero, 9
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	sd t5, 0(t0)
	addi t3, s8, 1
	srli t3, t3, 1
	add s7, t3, t3
	add s7, s7, t3
	addi s7, s7, 2
2150:
	addi t0, zero, 4
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld a4, 0(t0)
	addi t0, zero, 5
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld t0, 0(t0)
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
	sd s0, 0(t0)
	sd s1, 8(t0)
	sd s2, 16(t0)
	sd s3, 24(t0)
	sd s4, 32(t0)
	sd s5, 40(t0)
	addi t0, zero, 12
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	sd s6, 0(t0)
	sd a0, 8(t0)
	sd a1, 16(t0)
	sd a2, 24(t0)
	sd a3, 32(t0)
	sd a6, 40(t0)
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
	addi s1, zero, 9
	mul s1, s1, s10
	add s1, s1, s11
	addi s1, s1, 256
	ld s1, 24(s1)
	addi s2, zero, 9
	mul s2, s2, s10
	add s2, s2, s11
	addi s2, s2, 256
	ld s2, 32(s2)
	srai s3, a5, 63
	srai s4, a7, 63
	srai s5, s1, 63
	addi t0, zero, 4
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 5
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t4, zero, 0
	addi a4, zero, 0
	addi a0, zero, 0
	addi a1, zero, 0
	srai s6, s2, 63
	ld t5, 0(t0)
	ld t6, 0(t1)
	mul t2, a5, t5
	add t4, t4, t2
	sltu t2, t4, t2
	add a4, a4, t2
	mulhu t2, a5, t5
	add a4, a4, t2
	and t2, s3, t5
	sub a4, a4, t2
	mul t2, a7, t6
	add t4, t4, t2
	sltu t2, t4, t2
	add a4, a4, t2
	mulhu t2, a7, t6
	add a4, a4, t2
	and t2, s4, t6
	sub a4, a4, t2
	mul t2, s1, t5
	add a0, a0, t2
	sltu t2, a0, t2
	add a1, a1, t2
	mulhu t2, s1, t5
	add a1, a1, t2
	and t2, s5, t5
	sub a1, a1, t2
	mul t2, s2, t6
	add a0, a0, t2
	sltu t2, a0, t2
	add a1, a1, t2
	mulhu t2, s2, t6
	add a1, a1, t2
	and t2, s6, t6
	sub a1, a1, t2
	srli a2, t4, 59
	addi t4, a4, 0
	srai a4, a4, 63
	srli a3, a0, 59
	addi a0, a1, 0
	srai a1, a1, 63
	addi t3, s8, 1
	srli t3, t3, 1
2151:
	ld t5, 8(t0)
	ld t6, 8(t1)
	mul t2, a5, t5
	add t4, t4, t2
	sltu t2, t4, t2
	add a4, a4, t2
	mulhu t2, a5, t5
	add a4, a4, t2
	and t2, s3, t5
	sub a4, a4, t2
	mul t2, a7, t6
	add t4, t4, t2
	sltu t2, t4, t2
	add a4, a4, t2
	mulhu t2, a7, t6
	add a4, a4, t2
	and t2, s4, t6
	sub a4, a4, t2
	mul t2, s1, t5
	add a0, a0, t2
	sltu t2, a0, t2
	add a1, a1, t2
	mulhu t2, s1, t5
	add a1, a1, t2
	and t2, s5, t5
	sub a1, a1, t2
	mul t2, s2, t6
	add a0, a0, t2
	sltu t2, a0, t2
	add a1, a1, t2
	mulhu t2, s2, t6
	add a1, a1, t2
	and t2, s6, t6
	sub a1, a1, t2
	slli t2, t4, 5
	add t2, a2, t2
	sd t2, 0(t0)
	slli t2, a0, 5
	add t2, a3, t2
	sd t2, 0(t1)
	srli a2, t4, 59
	addi t4, a4, 0
	srai a4, a4, 63
	srli a3, a0, 59
	addi a0, a1, 0
	srai a1, a1, 63
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 2151b
	slli t2, a2, 59
	srai t2, t2, 59
	sd t2, 0(t0)
	slli t2, a3, 59
	srai t2, t2, 59
	sd t2, 0(t1)
	addi t0, zero, 11
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld s0, 0(t0)
	ld s1, 8(t0)
	ld s2, 16(t0)
	ld s3, 24(t0)
	ld s4, 32(t0)
	ld s5, 40(t0)
	addi t0, zero, 12
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld s6, 0(t0)
	ld a0, 8(t0)
	ld a1, 16(t0)
	ld a2, 24(t0)
	ld a3, 32(t0)
	ld a6, 40(t0)
	addi t0, zero, 11
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	sd s0, 0(t0)
	sd s1, 8(t0)
	sd s2, 16(t0)
	sd s3, 24(t0)
	sd s4, 32(t0)
	sd s5, 40(t0)
	addi t0, zero, 12
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	sd s6, 0(t0)
	sd a0, 8(t0)
	sd a1, 16(t0)
	sd a2, 24(t0)
	sd a3, 32(t0)
	sd a6, 40(t0)
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
	addi s1, zero, 9
	mul s1, s1, s10
	add s1, s1, s11
	addi s1, s1, 256
	ld s1, 24(s1)
	addi s2, zero, 9
	mul s2, s2, s10
	add s2, s2, s11
	addi s2, s2, 256
	ld s2, 32(s2)
	srai s3, a5, 63
	srai s4, a7, 63
	srai s5, s1, 63
	addi t0, zero, 6
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 7
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t4, zero, 0
	addi a4, zero, 0
	addi a0, zero, 0
	addi a1, zero, 0
	addi t2, zero, 2
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi a6, zero, 0
	addi s0, zero, 0
	ld t5, 0(t0)
	ld t6, 0(t1)
	mul s6, a5, t5
	add t4, t4, s6
	sltu s6, t4, s6
	add a4, a4, s6
	mulhu s6, a5, t5
	add a4, a4, s6
	and s6, s3, t5
	sub a4, a4, s6
	mul s6, a7, t6
	add t4, t4, s6
	sltu s6, t4, s6
	add a4, a4, s6
	mulhu s6, a7, t6
	add a4, a4, s6
	and s6, s4, t6
	sub a4, a4, s6
	mul s6, s1, t5
	add a0, a0, s6
	sltu s6, a0, s6
	add a1, a1, s6
	mulhu s6, s1, t5
	add a1, a1, s6
	and s6, s5, t5
	sub a1, a1, s6
	mul s6, s2, t6
	add a0, a0, s6
	sltu s6, a0, s6
	add a1, a1, s6
	mulhu s6, s2, t6
	add a1, a1, s6
	srai s6, s2, 63
	and s6, s6, t6
	sub a1, a1, s6
	addi t5, zero, 9
	mul t5, t5, s10
	add t5, t5, s11
	addi t5, t5, 256
	ld t5, 40(t5)
	mul a2, t4, t5
	mul a3, a0, t5
	ld t5, 0(t2)
	mul s6, a2, t5
	add s6, s6, t4
	sltu t4, s6, t4
	mulhu t6, a2, t5
	add t6, t6, t4
	add t4, s6, a6
	sltu s6, t4, a6
	add a6, t6, s6
	mul s6, a3, t5
	add s6, s6, a0
	sltu a0, s6, a0
	mulhu t6, a3, t5
	add t6, t6, a0
	add a0, s6, s0
	sltu s6, a0, s0
	add s0, t6, s6
	addi t4, a4, 0
	srai a4, a4, 63
	addi a0, a1, 0
	srai a1, a1, 63
	addi t3, s8, 1
	srli t3, t3, 1
	addi t3, t3, -1
	beqz t3, 2152f
2154:
	ld t5, 8(t0)
	ld t6, 8(t1)
	mul s6, a5, t5
	add t4, t4, s6
	sltu s6, t4, s6
	add a4, a4, s6
	mulhu s6, a5, t5
	add a4, a4, s6
	and s6, s3, t5
	sub a4, a4, s6
	mul s6, a7, t6
	add t4, t4, s6
	sltu s6, t4, s6
	add a4, a4, s6
	mulhu s6, a7, t6
	add a4, a4, s6
	and s6, s4, t6
	sub a4, a4, s6
	mul s6, s1, t5
	add a0, a0, s6
	sltu s6, a0, s6
	add a1, a1, s6
	mulhu s6, s1, t5
	add a1, a1, s6
	and s6, s5, t5
	sub a1, a1, s6
	mul s6, s2, t6
	add a0, a0, s6
	sltu s6, a0, s6
	add a1, a1, s6
	mulhu s6, s2, t6
	add a1, a1, s6
	srai s6, s2, 63
	and s6, s6, t6
	sub a1, a1, s6
	ld t5, 8(t2)
	mul s6, a2, t5
	add s6, s6, t4
	sltu t4, s6, t4
	mulhu t6, a2, t5
	add t6, t6, t4
	add t4, s6, a6
	sltu s6, t4, a6
	add a6, t6, s6
	sd t4, 0(t0)
	mul s6, a3, t5
	add s6, s6, a0
	sltu a0, s6, a0
	mulhu t6, a3, t5
	add t6, t6, a0
	add a0, s6, s0
	sltu s6, a0, s0
	add s0, t6, s6
	sd a0, 0(t1)
	addi t4, a4, 0
	srai a4, a4, 63
	addi a0, a1, 0
	srai a1, a1, 63
	addi t0, t0, 8
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 2154b
	j 2153f
2152:
2153:
	ld t5, 8(t0)
	ld t6, 8(t1)
	mul s6, a5, t5
	add t4, t4, s6
	sltu s6, t4, s6
	add a4, a4, s6
	mulhu s6, a5, t5
	add a4, a4, s6
	and s6, s3, t5
	sub a4, a4, s6
	mul s6, a7, t6
	add t4, t4, s6
	sltu s6, t4, s6
	add a4, a4, s6
	mulhu s6, a7, t6
	add a4, a4, s6
	and s6, s4, t6
	sub a4, a4, s6
	mul s6, s1, t5
	add a0, a0, s6
	sltu s6, a0, s6
	add a1, a1, s6
	mulhu s6, s1, t5
	add a1, a1, s6
	and s6, s5, t5
	sub a1, a1, s6
	mul s6, s2, t6
	add a0, a0, s6
	sltu s6, a0, s6
	add a1, a1, s6
	mulhu s6, s2, t6
	add a1, a1, s6
	srai s6, s2, 63
	and s6, s6, t6
	sub a1, a1, s6
	srai t5, t4, 63
	add t4, t4, a6
	sltu t6, t4, a6
	sd t4, 0(t0)
	add t5, t5, t6
	sd t5, 8(t0)
	srai t5, a0, 63
	add a0, a0, s0
	sltu t6, a0, s0
	sd a0, 0(t1)
	add t5, t5, t6
	sd t5, 8(t1)
	addi t0, zero, 11
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld s0, 0(t0)
	ld s1, 8(t0)
	ld s2, 16(t0)
	ld s3, 24(t0)
	ld s4, 32(t0)
	ld s5, 40(t0)
	addi t0, zero, 12
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld s6, 0(t0)
	ld a0, 8(t0)
	ld a1, 16(t0)
	ld a2, 24(t0)
	ld a3, 32(t0)
	ld a6, 40(t0)
	addi s7, s7, -1
	bnez s7, 2150b
	addi a5, zero, 1
	addi t0, zero, 13
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
	srli t3, t3, 1
	addi t3, t3, 1
	addi t4, zero, 0
2155:
	ld t5, 0(t2)
	mul t6, a5, t5
	mulhu t5, a5, t5
	ld a4, 0(t1)
	add t6, t6, a4
	sltu a4, t6, a4
	add t5, t5, a4
	add t6, t6, t4
	sltu a4, t6, t4
	add t4, t5, a4
	sd t6, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 2155b
	addi t1, zero, 6
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s8, 1
	srli t3, t3, 1
	slli t3, t3, 3
	add t1, t1, t3
	ld t4, 0(t1)
	srai t4, t4, 63
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
	srli t3, t3, 1
	addi t3, t3, 1
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
	srli t3, t3, 1
	addi t3, t3, 1
	addi t4, zero, 0
2157:
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
	bnez t3, 2157b
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
	srli t3, t3, 1
	addi t3, t3, 1
	addi t5, zero, 0
	sub t4, t5, t4
2158:
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
	bnez t3, 2158b
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
	srli t3, t3, 1
	addi t3, t3, 1
	addi t4, zero, 0
2159:
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
	bnez t3, 2159b
	addi t1, zero, 4
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s8, 1
	srli t3, t3, 1
	slli t3, t3, 3
	add t1, t1, t3
	ld t4, 0(t1)
	srai t4, t4, 63
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
	srli t3, t3, 1
	addi t3, t3, 1
2160:
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
	bnez t3, 2160b
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
	srli t3, t3, 1
	addi t3, t3, 1
	addi t4, zero, 0
2161:
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
	bnez t3, 2161b
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
	srli t3, t3, 1
	addi t3, t3, 1
	addi t5, zero, 0
	sub t4, t5, t4
2162:
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
	bnez t3, 2162b
	addi t3, s8, 1
	srli t3, t3, 1
	slli s7, t3, 4
	sub s7, s7, t3
	addi s7, s7, 10
2163:
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
	srli t3, t3, 1
	addi t3, t3, 1
	addi t4, zero, 0
2164:
	ld t5, 0(t2)
	mul t6, a5, t5
	mulhu t5, a5, t5
	ld a4, 0(t1)
	add t6, t6, a4
	sltu a4, t6, a4
	add t5, t5, a4
	add t6, t6, t4
	sltu a4, t6, t4
	add t4, t5, a4
	sd t6, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 2164b
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
	srli t3, t3, 1
	addi t3, t3, 1
	addi t4, zero, 0
2165:
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
	bnez t3, 2165b
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
	srli t3, t3, 1
	addi t3, t3, 1
	addi t5, zero, 0
	sub t4, t5, t4
2166:
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
	bnez t3, 2166b
	addi s7, s7, -1
	bnez s7, 2163b
	addi t0, zero, 1
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t3, s9, 1
	addi t5, zero, 0
2167:
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t3, t3, -1
	bnez t3, 2167b
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
	srli t3, t3, 1
	addi t3, t3, 1
	addi t4, zero, 0
2168:
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
	bnez t3, 2168b
	addi t1, zero, 4
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s8, 1
	srli t3, t3, 1
	slli t3, t3, 3
	add t1, t1, t3
	ld t4, 0(t1)
	srai t4, t4, 63
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
	srli t3, t3, 1
	addi t3, t3, 1
2169:
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
	bnez t3, 2169b
	addi t0, zero, 3
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t3, s9, 1
	addi t5, zero, 0
2170:
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t3, t3, -1
	bnez t3, 2170b
	addi t0, zero, 3
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 6
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s8, 1
	srli t3, t3, 1
	addi t3, t3, 1
2171:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 2171b
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
2172:
	ld t5, 0(t1)
	ld t6, 0(t2)
	xor t5, t5, t6
	or t4, t4, t5
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 2172b
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
2173:
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
	bnez t3, 2173b
	j 2140f
2139:
	addi t0, zero, 49
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 29
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
2174:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 2174b
2140:
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
2175:
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
	bnez t3, 2175b
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
2176:
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
	bnez t3, 2176b
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
2177:
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
	bnez t3, 2177b
	addi t0, zero, 0
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 25
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
2178:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 2178b
	addi t0, zero, 8
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 54
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
2179:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 2179b
	srli s8, a1, 2
	addi t0, zero, 2
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 8
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s8, 1
	srli t3, t3, 1
2180:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 2180b
	addi t1, zero, 2
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s8, 1
	srli t3, t3, 1
	slli t3, t3, 3
	add t1, t1, t3
	addi t5, zero, 0
	sd t5, 0(t1)
	addi a4, zero, 2
	mul a4, a4, s10
	add a4, a4, s11
	addi a4, a4, 256
	ld t5, 0(a4)
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
	srli t3, t3, 1
	addi t3, t3, 1
2181:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 2181b
	addi t0, zero, 0
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld a5, 0(t0)
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
	addi t3, s8, 1
	srli t3, t3, 1
	addi t4, zero, 0
2182:
	ld t5, 0(t2)
	mul t6, a5, t5
	mulhu t5, a5, t5
	ld a4, 0(t1)
	add t6, t6, a4
	sltu a4, t6, a4
	add t5, t5, a4
	add t6, t6, t4
	sltu a4, t6, t4
	add t4, t5, a4
	sd t6, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 2182b
	sd t4, 0(t0)
	addi t0, zero, 6
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t3, s8, 1
	srli t3, t3, 1
	addi t3, t3, 1
	addi t5, zero, 0
2183:
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t3, t3, -1
	bnez t3, 2183b
	addi t0, zero, 7
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t3, s8, 1
	srli t3, t3, 1
	addi t3, t3, 1
	addi t5, zero, 0
2184:
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t3, t3, -1
	bnez t3, 2184b
	addi t0, zero, 7
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t5, zero, 1
	sd t5, 0(t0)
	addi t0, zero, 9
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	sd t5, 0(t0)
	addi t3, s8, 1
	srli t3, t3, 1
	add s7, t3, t3
	add s7, s7, t3
	addi s7, s7, 2
2185:
	addi t0, zero, 4
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld a4, 0(t0)
	addi t0, zero, 5
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld t0, 0(t0)
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
	sd s0, 0(t0)
	sd s1, 8(t0)
	sd s2, 16(t0)
	sd s3, 24(t0)
	sd s4, 32(t0)
	sd s5, 40(t0)
	addi t0, zero, 12
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	sd s6, 0(t0)
	sd a0, 8(t0)
	sd a1, 16(t0)
	sd a2, 24(t0)
	sd a3, 32(t0)
	sd a6, 40(t0)
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
	addi s1, zero, 9
	mul s1, s1, s10
	add s1, s1, s11
	addi s1, s1, 256
	ld s1, 24(s1)
	addi s2, zero, 9
	mul s2, s2, s10
	add s2, s2, s11
	addi s2, s2, 256
	ld s2, 32(s2)
	srai s3, a5, 63
	srai s4, a7, 63
	srai s5, s1, 63
	addi t0, zero, 4
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 5
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t4, zero, 0
	addi a4, zero, 0
	addi a0, zero, 0
	addi a1, zero, 0
	srai s6, s2, 63
	ld t5, 0(t0)
	ld t6, 0(t1)
	mul t2, a5, t5
	add t4, t4, t2
	sltu t2, t4, t2
	add a4, a4, t2
	mulhu t2, a5, t5
	add a4, a4, t2
	and t2, s3, t5
	sub a4, a4, t2
	mul t2, a7, t6
	add t4, t4, t2
	sltu t2, t4, t2
	add a4, a4, t2
	mulhu t2, a7, t6
	add a4, a4, t2
	and t2, s4, t6
	sub a4, a4, t2
	mul t2, s1, t5
	add a0, a0, t2
	sltu t2, a0, t2
	add a1, a1, t2
	mulhu t2, s1, t5
	add a1, a1, t2
	and t2, s5, t5
	sub a1, a1, t2
	mul t2, s2, t6
	add a0, a0, t2
	sltu t2, a0, t2
	add a1, a1, t2
	mulhu t2, s2, t6
	add a1, a1, t2
	and t2, s6, t6
	sub a1, a1, t2
	srli a2, t4, 59
	addi t4, a4, 0
	srai a4, a4, 63
	srli a3, a0, 59
	addi a0, a1, 0
	srai a1, a1, 63
	addi t3, s8, 1
	srli t3, t3, 1
2186:
	ld t5, 8(t0)
	ld t6, 8(t1)
	mul t2, a5, t5
	add t4, t4, t2
	sltu t2, t4, t2
	add a4, a4, t2
	mulhu t2, a5, t5
	add a4, a4, t2
	and t2, s3, t5
	sub a4, a4, t2
	mul t2, a7, t6
	add t4, t4, t2
	sltu t2, t4, t2
	add a4, a4, t2
	mulhu t2, a7, t6
	add a4, a4, t2
	and t2, s4, t6
	sub a4, a4, t2
	mul t2, s1, t5
	add a0, a0, t2
	sltu t2, a0, t2
	add a1, a1, t2
	mulhu t2, s1, t5
	add a1, a1, t2
	and t2, s5, t5
	sub a1, a1, t2
	mul t2, s2, t6
	add a0, a0, t2
	sltu t2, a0, t2
	add a1, a1, t2
	mulhu t2, s2, t6
	add a1, a1, t2
	and t2, s6, t6
	sub a1, a1, t2
	slli t2, t4, 5
	add t2, a2, t2
	sd t2, 0(t0)
	slli t2, a0, 5
	add t2, a3, t2
	sd t2, 0(t1)
	srli a2, t4, 59
	addi t4, a4, 0
	srai a4, a4, 63
	srli a3, a0, 59
	addi a0, a1, 0
	srai a1, a1, 63
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 2186b
	slli t2, a2, 59
	srai t2, t2, 59
	sd t2, 0(t0)
	slli t2, a3, 59
	srai t2, t2, 59
	sd t2, 0(t1)
	addi t0, zero, 11
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld s0, 0(t0)
	ld s1, 8(t0)
	ld s2, 16(t0)
	ld s3, 24(t0)
	ld s4, 32(t0)
	ld s5, 40(t0)
	addi t0, zero, 12
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld s6, 0(t0)
	ld a0, 8(t0)
	ld a1, 16(t0)
	ld a2, 24(t0)
	ld a3, 32(t0)
	ld a6, 40(t0)
	addi t0, zero, 11
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	sd s0, 0(t0)
	sd s1, 8(t0)
	sd s2, 16(t0)
	sd s3, 24(t0)
	sd s4, 32(t0)
	sd s5, 40(t0)
	addi t0, zero, 12
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	sd s6, 0(t0)
	sd a0, 8(t0)
	sd a1, 16(t0)
	sd a2, 24(t0)
	sd a3, 32(t0)
	sd a6, 40(t0)
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
	addi s1, zero, 9
	mul s1, s1, s10
	add s1, s1, s11
	addi s1, s1, 256
	ld s1, 24(s1)
	addi s2, zero, 9
	mul s2, s2, s10
	add s2, s2, s11
	addi s2, s2, 256
	ld s2, 32(s2)
	srai s3, a5, 63
	srai s4, a7, 63
	srai s5, s1, 63
	addi t0, zero, 6
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 7
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t4, zero, 0
	addi a4, zero, 0
	addi a0, zero, 0
	addi a1, zero, 0
	addi t2, zero, 2
	mul t2, t2, s10
	add t2, t2, s11
	addi t2, t2, 256
	addi a6, zero, 0
	addi s0, zero, 0
	ld t5, 0(t0)
	ld t6, 0(t1)
	mul s6, a5, t5
	add t4, t4, s6
	sltu s6, t4, s6
	add a4, a4, s6
	mulhu s6, a5, t5
	add a4, a4, s6
	and s6, s3, t5
	sub a4, a4, s6
	mul s6, a7, t6
	add t4, t4, s6
	sltu s6, t4, s6
	add a4, a4, s6
	mulhu s6, a7, t6
	add a4, a4, s6
	and s6, s4, t6
	sub a4, a4, s6
	mul s6, s1, t5
	add a0, a0, s6
	sltu s6, a0, s6
	add a1, a1, s6
	mulhu s6, s1, t5
	add a1, a1, s6
	and s6, s5, t5
	sub a1, a1, s6
	mul s6, s2, t6
	add a0, a0, s6
	sltu s6, a0, s6
	add a1, a1, s6
	mulhu s6, s2, t6
	add a1, a1, s6
	srai s6, s2, 63
	and s6, s6, t6
	sub a1, a1, s6
	addi t5, zero, 9
	mul t5, t5, s10
	add t5, t5, s11
	addi t5, t5, 256
	ld t5, 40(t5)
	mul a2, t4, t5
	mul a3, a0, t5
	ld t5, 0(t2)
	mul s6, a2, t5
	add s6, s6, t4
	sltu t4, s6, t4
	mulhu t6, a2, t5
	add t6, t6, t4
	add t4, s6, a6
	sltu s6, t4, a6
	add a6, t6, s6
	mul s6, a3, t5
	add s6, s6, a0
	sltu a0, s6, a0
	mulhu t6, a3, t5
	add t6, t6, a0
	add a0, s6, s0
	sltu s6, a0, s0
	add s0, t6, s6
	addi t4, a4, 0
	srai a4, a4, 63
	addi a0, a1, 0
	srai a1, a1, 63
	addi t3, s8, 1
	srli t3, t3, 1
	addi t3, t3, -1
	beqz t3, 2187f
2189:
	ld t5, 8(t0)
	ld t6, 8(t1)
	mul s6, a5, t5
	add t4, t4, s6
	sltu s6, t4, s6
	add a4, a4, s6
	mulhu s6, a5, t5
	add a4, a4, s6
	and s6, s3, t5
	sub a4, a4, s6
	mul s6, a7, t6
	add t4, t4, s6
	sltu s6, t4, s6
	add a4, a4, s6
	mulhu s6, a7, t6
	add a4, a4, s6
	and s6, s4, t6
	sub a4, a4, s6
	mul s6, s1, t5
	add a0, a0, s6
	sltu s6, a0, s6
	add a1, a1, s6
	mulhu s6, s1, t5
	add a1, a1, s6
	and s6, s5, t5
	sub a1, a1, s6
	mul s6, s2, t6
	add a0, a0, s6
	sltu s6, a0, s6
	add a1, a1, s6
	mulhu s6, s2, t6
	add a1, a1, s6
	srai s6, s2, 63
	and s6, s6, t6
	sub a1, a1, s6
	ld t5, 8(t2)
	mul s6, a2, t5
	add s6, s6, t4
	sltu t4, s6, t4
	mulhu t6, a2, t5
	add t6, t6, t4
	add t4, s6, a6
	sltu s6, t4, a6
	add a6, t6, s6
	sd t4, 0(t0)
	mul s6, a3, t5
	add s6, s6, a0
	sltu a0, s6, a0
	mulhu t6, a3, t5
	add t6, t6, a0
	add a0, s6, s0
	sltu s6, a0, s0
	add s0, t6, s6
	sd a0, 0(t1)
	addi t4, a4, 0
	srai a4, a4, 63
	addi a0, a1, 0
	srai a1, a1, 63
	addi t0, t0, 8
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 2189b
	j 2188f
2187:
2188:
	ld t5, 8(t0)
	ld t6, 8(t1)
	mul s6, a5, t5
	add t4, t4, s6
	sltu s6, t4, s6
	add a4, a4, s6
	mulhu s6, a5, t5
	add a4, a4, s6
	and s6, s3, t5
	sub a4, a4, s6
	mul s6, a7, t6
	add t4, t4, s6
	sltu s6, t4, s6
	add a4, a4, s6
	mulhu s6, a7, t6
	add a4, a4, s6
	and s6, s4, t6
	sub a4, a4, s6
	mul s6, s1, t5
	add a0, a0, s6
	sltu s6, a0, s6
	add a1, a1, s6
	mulhu s6, s1, t5
	add a1, a1, s6
	and s6, s5, t5
	sub a1, a1, s6
	mul s6, s2, t6
	add a0, a0, s6
	sltu s6, a0, s6
	add a1, a1, s6
	mulhu s6, s2, t6
	add a1, a1, s6
	srai s6, s2, 63
	and s6, s6, t6
	sub a1, a1, s6
	srai t5, t4, 63
	add t4, t4, a6
	sltu t6, t4, a6
	sd t4, 0(t0)
	add t5, t5, t6
	sd t5, 8(t0)
	srai t5, a0, 63
	add a0, a0, s0
	sltu t6, a0, s0
	sd a0, 0(t1)
	add t5, t5, t6
	sd t5, 8(t1)
	addi t0, zero, 11
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld s0, 0(t0)
	ld s1, 8(t0)
	ld s2, 16(t0)
	ld s3, 24(t0)
	ld s4, 32(t0)
	ld s5, 40(t0)
	addi t0, zero, 12
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	ld s6, 0(t0)
	ld a0, 8(t0)
	ld a1, 16(t0)
	ld a2, 24(t0)
	ld a3, 32(t0)
	ld a6, 40(t0)
	addi s7, s7, -1
	bnez s7, 2185b
	addi a5, zero, 1
	addi t0, zero, 13
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
	srli t3, t3, 1
	addi t3, t3, 1
	addi t4, zero, 0
2190:
	ld t5, 0(t2)
	mul t6, a5, t5
	mulhu t5, a5, t5
	ld a4, 0(t1)
	add t6, t6, a4
	sltu a4, t6, a4
	add t5, t5, a4
	add t6, t6, t4
	sltu a4, t6, t4
	add t4, t5, a4
	sd t6, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 2190b
	addi t1, zero, 6
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s8, 1
	srli t3, t3, 1
	slli t3, t3, 3
	add t1, t1, t3
	ld t4, 0(t1)
	srai t4, t4, 63
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
	srli t3, t3, 1
	addi t3, t3, 1
2191:
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
	bnez t3, 2191b
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
	srli t3, t3, 1
	addi t3, t3, 1
	addi t4, zero, 0
2192:
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
	bnez t3, 2192b
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
	srli t3, t3, 1
	addi t3, t3, 1
	addi t5, zero, 0
	sub t4, t5, t4
2193:
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
	bnez t3, 2193b
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
	srli t3, t3, 1
	addi t3, t3, 1
	addi t4, zero, 0
2194:
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
	bnez t3, 2194b
	addi t1, zero, 4
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s8, 1
	srli t3, t3, 1
	slli t3, t3, 3
	add t1, t1, t3
	ld t4, 0(t1)
	srai t4, t4, 63
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
	srli t3, t3, 1
	addi t3, t3, 1
2195:
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
	bnez t3, 2195b
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
	srli t3, t3, 1
	addi t3, t3, 1
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
	srli t3, t3, 1
	addi t3, t3, 1
	addi t5, zero, 0
	sub t4, t5, t4
2197:
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
	bnez t3, 2197b
	addi t3, s8, 1
	srli t3, t3, 1
	slli s7, t3, 4
	sub s7, s7, t3
	addi s7, s7, 10
2198:
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
	srli t3, t3, 1
	addi t3, t3, 1
	addi t4, zero, 0
2199:
	ld t5, 0(t2)
	mul t6, a5, t5
	mulhu t5, a5, t5
	ld a4, 0(t1)
	add t6, t6, a4
	sltu a4, t6, a4
	add t5, t5, a4
	add t6, t6, t4
	sltu a4, t6, t4
	add t4, t5, a4
	sd t6, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 2199b
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
	srli t3, t3, 1
	addi t3, t3, 1
	addi t4, zero, 0
2200:
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
	bnez t3, 2200b
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
	srli t3, t3, 1
	addi t3, t3, 1
	addi t5, zero, 0
	sub t4, t5, t4
2201:
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
	bnez t3, 2201b
	addi s7, s7, -1
	bnez s7, 2198b
	addi t0, zero, 1
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t3, s9, 1
	addi t5, zero, 0
2202:
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t3, t3, -1
	bnez t3, 2202b
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
	srli t3, t3, 1
	addi t3, t3, 1
	addi t4, zero, 0
2203:
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
	bnez t3, 2203b
	addi t1, zero, 4
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s8, 1
	srli t3, t3, 1
	slli t3, t3, 3
	add t1, t1, t3
	ld t4, 0(t1)
	srai t4, t4, 63
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
	srli t3, t3, 1
	addi t3, t3, 1
2204:
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
	bnez t3, 2204b
	addi t0, zero, 3
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t3, s9, 1
	addi t5, zero, 0
2205:
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t3, t3, -1
	bnez t3, 2205b
	addi t0, zero, 3
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 6
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s8, 1
	srli t3, t3, 1
	addi t3, t3, 1
2206:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 2206b
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
2207:
	ld t5, 0(t1)
	ld t6, 0(t2)
	xor t5, t5, t6
	or t4, t4, t5
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 2207b
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
2208:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 2208b
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
2209:
	ld t5, 0(t1)
	ld t6, 0(t2)
	xor t5, t5, t6
	or t4, t4, t5
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 2209b
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
2210:
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
	bnez t3, 2210b
	addi t0, zero, 41
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 49
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
2211:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 2211b
	addi t0, zero, 37
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 29
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
	addi t0, zero, 50
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t3, s9, 1
	addi t5, zero, 0
2213:
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t3, t3, -1
	bnez t3, 2213b
	slli s7, s9, 6
	addi a4, zero, -1
2214:
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
	beqz t2, 2215f
2217:
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
	bnez t2, 2217b
	j 2216f
2215:
2216:
	addi t2, s9, 1
	srli t2, t2, 2
	beqz t2, 2218f
2220:
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
	bnez t2, 2220b
	j 2219f
2218:
2219:
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
	bnez s7, 2214b
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
2221:
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
	bnez t3, 2221b
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
2222:
	ld t5, 0(t1)
	ld t6, 0(t2)
	xor t5, t5, t6
	or t4, t4, t5
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 2222b
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
2223:
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
	bnez t3, 2223b
	addi t0, zero, 41
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 49
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
2224:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 2224b
	addi t0, zero, 37
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 29
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
2225:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 2225b
	addi t0, zero, 51
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t3, s9, 1
	addi t5, zero, 0
2226:
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t3, t3, -1
	bnez t3, 2226b
	slli s7, s9, 6
	addi a4, zero, -1
2227:
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
	beqz t2, 2228f
2230:
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
	bnez t2, 2230b
	j 2229f
2228:
2229:
	addi t2, s9, 1
	srli t2, t2, 2
	beqz t2, 2231f
2233:
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
	bnez t2, 2233b
	j 2232f
2231:
2232:
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
	bnez s7, 2227b
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
2234:
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
	bnez t3, 2234b
	addi t0, zero, 53
	mul t0, t0, s10
	add t0, t0, s11
	addi t0, t0, 256
	addi t1, zero, 10
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s9, 0
2235:
	ld t5, 0(t1)
	sd t5, 0(t0)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t3, t3, -1
	bnez t3, 2235b
	addi a2, zero, 24
	mul a2, a2, s10
	add a2, a2, s11
	addi a2, a2, 256
	addi a3, zero, 53
	mul a3, a3, s10
	add a3, a3, s11
	addi a3, a3, 256
	addi s8, s9, 0
2236:
	ld a6, 0(a2)
	addi t0, a3, 0
	addi t1, zero, 25
	mul t1, t1, s10
	add t1, t1, s11
	addi t1, t1, 256
	addi t3, s8, 0
	addi t4, zero, 0
2237:
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
	bnez t3, 2237b
	addi a2, a2, 8
	addi a3, a3, 8
	addi s8, s8, -1
	bnez s8, 2236b
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
2238:
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
	bnez t3, 2238b
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
2239:
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
	bnez t3, 2239b
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
2240:
	lbu t5, 0(t1)
	and t5, t5, t4
	sb t5, 0(t0)
	addi t0, t0, 1
	addi t1, t1, -1
	addi t3, t3, -1
	bnez t3, 2240b
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
2241:
	lbu t5, 0(t1)
	and t5, t5, t4
	sb t5, 0(t0)
	addi t0, t0, 1
	addi t1, t1, -1
	addi t3, t3, -1
	bnez t3, 2241b
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
2242:
	lbu t5, 0(t1)
	and t5, t5, t4
	sb t5, 0(t0)
	addi t0, t0, 1
	addi t1, t1, -1
	addi t3, t3, -1
	bnez t3, 2242b
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
2243:
	lbu t5, 0(t1)
	and t5, t5, t4
	sb t5, 0(t0)
	addi t0, t0, 1
	addi t1, t1, -1
	addi t3, t3, -1
	bnez t3, 2243b
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
2244:
	lbu t5, 0(t1)
	and t5, t5, t4
	sb t5, 0(t0)
	addi t0, t0, 1
	addi t1, t1, -1
	addi t3, t3, -1
	bnez t3, 2244b
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
2245:
	lbu t5, 0(t1)
	and t5, t5, t4
	sb t5, 0(t0)
	addi t0, t0, 1
	addi t1, t1, -1
	addi t3, t3, -1
	bnez t3, 2245b
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
2246:
	lbu t5, 0(t1)
	and t5, t5, t4
	sb t5, 0(t0)
	addi t0, t0, 1
	addi t1, t1, -1
	addi t3, t3, -1
	bnez t3, 2246b
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
