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
