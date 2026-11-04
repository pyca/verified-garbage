// The functions of `src/rsa_oaep.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_oaep_decrypt:
	.option push
	.option arch, +m, +c
	addi sp, sp, -128
	addi t0, sp, 0
	sd s0, 16(t0)
	sd s1, 24(t0)
	sd s2, 32(t0)
	sd s3, 40(t0)
	sd s4, 48(t0)
	sd s5, 56(t0)
	sd s6, 64(t0)
	sd s7, 72(t0)
	sd s8, 80(t0)
	sd s9, 88(t0)
	sd s10, 96(t0)
	sd s11, 104(t0)
	sd ra, 112(t0)
	addi t6, sp, 128
	ld s0, 104(t6)
	addi s1, a4, 0
	addi s2, a0, 0
	addi s3, a2, 0
	addi sp, sp, -96
	addi t0, sp, 0
	addi t6, sp, 224
	sd a7, 0(t0)
	ld t1, 0(t6)
	sd t1, 8(t0)
	ld t1, 8(t6)
	sd t1, 16(t0)
	ld t1, 16(t6)
	sd t1, 24(t0)
	ld t1, 24(t6)
	sd t1, 32(t0)
	ld t1, 32(t6)
	sd t1, 40(t0)
	ld t1, 40(t6)
	sd t1, 48(t0)
	ld t1, 48(t6)
	sd t1, 56(t0)
	ld t1, 56(t6)
	sd t1, 64(t0)
	ld t1, 64(t6)
	sd t1, 72(t0)
	addi t1, zero, 1024
	slli t1, t1, 3
	add t1, s0, t1
	sd t1, 80(t0)
	ld t1, 112(t6)
	addi t1, t1, -1024
	sd t1, 88(t0)
	addi a2, a3, 0
	addi a3, s1, 0
	addi a4, a5, 0
	addi a5, a6, 0
	ld a6, 88(t6)
	addi a7, s1, 0
	addi a0, s0, 0
	addi a1, s1, 0
	call {vg_rsa_private_checked}
	addi sp, sp, 96
	slli s4, a0, 32
	srli s4, s4, 32
	addi a0, sp, 248
	ld a0, 0(a0)
	ld a0, 32(a0)
	addi a1, a0, -20
	beqz a1, 20f
	addi a1, a0, -28
	beqz a1, 22f
	addi a1, a0, -32
	beqz a1, 24f
	addi a1, a0, -48
	beqz a1, 26f
	addi a0, zero, 130
	sub a0, s1, a0
	srli a0, a0, 63
	bnez a0, 28f
	addi s6, s0, 65
	addi s7, s1, -65
	addi s8, s0, 1
	addi s9, zero, 64
	addi s10, zero, 0
	addi s11, zero, 0
210:
	addi a0, s0, 1024
	addi t1, sp, 256
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, zero, 0
	addi a2, s6, 0
	addi a3, s7, 0
	addi t1, sp, 256
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a2, s0, 1344
	addi t1, s10, 0
	sb t1, 3(a2)
	srli t1, t1, 8
	sb t1, 2(a2)
	srli t1, t1, 8
	sb t1, 1(a2)
	srli t1, t1, 8
	sb t1, 0(a2)
	addi a0, s0, 1024
	addi a1, s7, 0
	addi a3, zero, 4
	addi t1, sp, 256
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, s7, 4
	addi a2, s0, 1280
	addi t1, sp, 256
	ld t1, 0(t1)
	ld t1, 16(t1)
	jalr ra, 0(t1)
	addi a6, sp, 256
	ld a6, 0(a6)
	ld a6, 32(a6)
	addi a4, s0, 1280
	add a5, s8, s11
	sub t1, s9, s11
	sub t2, t1, a6
	srli t3, t2, 63
	addi t4, zero, 0
	sub t3, t4, t3
	and t2, t2, t3
	add a6, a6, t2
211:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t2, t2, t1
	sb t2, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 211b
	addi t1, sp, 256
	ld t1, 0(t1)
	ld t1, 32(t1)
	addi s10, s10, 1
	add s11, s11, t1
	sub t1, s11, s9
	srli t1, t1, 63
	bnez t1, 210b
	addi s6, s0, 1
	addi s7, zero, 64
	addi s8, s0, 65
	addi s9, s1, -65
	addi s10, zero, 0
	addi s11, zero, 0
212:
	addi a0, s0, 1024
	addi t1, sp, 256
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, zero, 0
	addi a2, s6, 0
	addi a3, s7, 0
	addi t1, sp, 256
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a2, s0, 1344
	addi t1, s10, 0
	sb t1, 3(a2)
	srli t1, t1, 8
	sb t1, 2(a2)
	srli t1, t1, 8
	sb t1, 1(a2)
	srli t1, t1, 8
	sb t1, 0(a2)
	addi a0, s0, 1024
	addi a1, s7, 0
	addi a3, zero, 4
	addi t1, sp, 256
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, s7, 4
	addi a2, s0, 1280
	addi t1, sp, 256
	ld t1, 0(t1)
	ld t1, 16(t1)
	jalr ra, 0(t1)
	addi a6, sp, 256
	ld a6, 0(a6)
	ld a6, 32(a6)
	addi a4, s0, 1280
	add a5, s8, s11
	sub t1, s9, s11
	sub t2, t1, a6
	srli t3, t2, 63
	addi t4, zero, 0
	sub t3, t4, t3
	and t2, t2, t3
	add a6, a6, t2
213:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t2, t2, t1
	sb t2, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 213b
	addi t1, sp, 256
	ld t1, 0(t1)
	ld t1, 32(t1)
	addi s10, s10, 1
	add s11, s11, t1
	sub t1, s11, s9
	srli t1, t1, 63
	bnez t1, 212b
	addi a0, s0, 1024
	addi t1, sp, 248
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi t6, sp, 128
	addi a0, s0, 1024
	addi a1, zero, 0
	ld a2, 72(t6)
	ld a3, 80(t6)
	addi t1, sp, 248
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi t6, sp, 128
	addi a0, s0, 1024
	ld a1, 80(t6)
	addi a2, s0, 1280
	addi t1, sp, 248
	ld t1, 0(t1)
	ld t1, 16(t1)
	jalr ra, 0(t1)
	addi a4, s0, 65
	addi a5, s0, 1280
	lbu s5, 0(s0)
	addi a6, zero, 64
214:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t1, t1, t2
	or s5, s5, t1
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 214b
	addi a1, s0, 129
	addi a2, s1, -129
	addi a3, zero, 0
	addi a4, zero, 0
	addi a4, a4, -1
	addi s6, zero, 0
215:
	lbu a7, 0(a1)
	addi t1, a7, -1
	srli t1, t1, 63
	addi t2, zero, 1
	xor t2, a7, t2
	addi t2, t2, -1
	srli t2, t2, 63
	or t1, t1, t2
	addi t1, t1, -1
	and t1, t1, a4
	or s5, s5, t1
	addi t3, zero, 0
	sub t3, t3, t2
	and t1, a3, a4
	and t1, t1, t3
	or s6, s6, t1
	addi t2, t2, -1
	and a4, a4, t2
	addi a1, a1, 1
	addi a3, a3, 1
	addi a2, a2, -1
	bnez a2, 215b
	or s5, s5, a4
	addi a1, s0, 2047
	addi a1, a1, 513
	addi t5, zero, 1
	slli t5, t5, 11
	addi t0, zero, 0
216:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 216b
	addi a4, s0, 129
	addi a1, s0, 2047
	addi a1, a1, 513
	addi a5, s1, -129
217:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 217b
	addi s8, s6, 1
	addi s9, zero, 1
	addi s10, zero, 10
218:
	addi a1, s0, 2047
	addi a1, a1, 513
	add a2, a1, s9
	addi a3, zero, 1
	and a3, s8, a3
	addi a4, zero, 0
	sub a3, a4, a3
	addi a5, s1, 0
219:
	lbu t1, 0(a1)
	lbu t2, 0(a2)
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	sb t1, 0(a1)
	addi a1, a1, 1
	addi a2, a2, 1
	addi a5, a5, -1
	bnez a5, 219b
	srli s8, s8, 1
	add s9, s9, s9
	addi s10, s10, -1
	bnez s10, 218b
	addi a1, zero, 1
	xor a1, s4, a1
	addi a1, a1, -1
	srli a1, a1, 63
	addi a2, zero, 0
	sub a2, a2, s5
	or a2, a2, s5
	srli a2, a2, 63
	addi a3, zero, 1
	xor a2, a2, a3
	and a1, a1, a2
	addi s7, zero, 0
	sub s7, s7, a1
	addi a4, s0, 2047
	addi a4, a4, 513
	addi a5, s2, 0
	addi a6, s1, 0
220:
	lbu t1, 0(a4)
	and t1, t1, s7
	sb t1, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 220b
	addi a1, s1, -130
	sub a1, a1, s6
	and a1, a1, s7
	sd a1, 0(s3)
	addi a1, zero, 2
	xor a0, s4, a1
	addi a0, a0, -1
	srli a0, a0, 63
	add a0, a0, a0
	addi a1, zero, 1
	and a1, s7, a1
	or a0, a0, a1
	j 29f
28:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
221:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 221b
	addi t1, zero, 0
	sd t1, 0(s3)
	addi a1, zero, 2
	xor a0, s4, a1
	addi a0, a0, -1
	srli a0, a0, 63
	add a0, a0, a0
29:
	j 27f
26:
	addi a0, zero, 98
	sub a0, s1, a0
	srli a0, a0, 63
	bnez a0, 222f
	addi s6, s0, 49
	addi s7, s1, -49
	addi s8, s0, 1
	addi s9, zero, 48
	addi s10, zero, 0
	addi s11, zero, 0
224:
	addi a0, s0, 1024
	addi t1, sp, 256
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, zero, 0
	addi a2, s6, 0
	addi a3, s7, 0
	addi t1, sp, 256
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a2, s0, 1344
	addi t1, s10, 0
	sb t1, 3(a2)
	srli t1, t1, 8
	sb t1, 2(a2)
	srli t1, t1, 8
	sb t1, 1(a2)
	srli t1, t1, 8
	sb t1, 0(a2)
	addi a0, s0, 1024
	addi a1, s7, 0
	addi a3, zero, 4
	addi t1, sp, 256
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, s7, 4
	addi a2, s0, 1280
	addi t1, sp, 256
	ld t1, 0(t1)
	ld t1, 16(t1)
	jalr ra, 0(t1)
	addi a6, sp, 256
	ld a6, 0(a6)
	ld a6, 32(a6)
	addi a4, s0, 1280
	add a5, s8, s11
	sub t1, s9, s11
	sub t2, t1, a6
	srli t3, t2, 63
	addi t4, zero, 0
	sub t3, t4, t3
	and t2, t2, t3
	add a6, a6, t2
225:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t2, t2, t1
	sb t2, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 225b
	addi t1, sp, 256
	ld t1, 0(t1)
	ld t1, 32(t1)
	addi s10, s10, 1
	add s11, s11, t1
	sub t1, s11, s9
	srli t1, t1, 63
	bnez t1, 224b
	addi s6, s0, 1
	addi s7, zero, 48
	addi s8, s0, 49
	addi s9, s1, -49
	addi s10, zero, 0
	addi s11, zero, 0
226:
	addi a0, s0, 1024
	addi t1, sp, 256
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, zero, 0
	addi a2, s6, 0
	addi a3, s7, 0
	addi t1, sp, 256
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a2, s0, 1344
	addi t1, s10, 0
	sb t1, 3(a2)
	srli t1, t1, 8
	sb t1, 2(a2)
	srli t1, t1, 8
	sb t1, 1(a2)
	srli t1, t1, 8
	sb t1, 0(a2)
	addi a0, s0, 1024
	addi a1, s7, 0
	addi a3, zero, 4
	addi t1, sp, 256
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, s7, 4
	addi a2, s0, 1280
	addi t1, sp, 256
	ld t1, 0(t1)
	ld t1, 16(t1)
	jalr ra, 0(t1)
	addi a6, sp, 256
	ld a6, 0(a6)
	ld a6, 32(a6)
	addi a4, s0, 1280
	add a5, s8, s11
	sub t1, s9, s11
	sub t2, t1, a6
	srli t3, t2, 63
	addi t4, zero, 0
	sub t3, t4, t3
	and t2, t2, t3
	add a6, a6, t2
227:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t2, t2, t1
	sb t2, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 227b
	addi t1, sp, 256
	ld t1, 0(t1)
	ld t1, 32(t1)
	addi s10, s10, 1
	add s11, s11, t1
	sub t1, s11, s9
	srli t1, t1, 63
	bnez t1, 226b
	addi a0, s0, 1024
	addi t1, sp, 248
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi t6, sp, 128
	addi a0, s0, 1024
	addi a1, zero, 0
	ld a2, 72(t6)
	ld a3, 80(t6)
	addi t1, sp, 248
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi t6, sp, 128
	addi a0, s0, 1024
	ld a1, 80(t6)
	addi a2, s0, 1280
	addi t1, sp, 248
	ld t1, 0(t1)
	ld t1, 16(t1)
	jalr ra, 0(t1)
	addi a4, s0, 49
	addi a5, s0, 1280
	lbu s5, 0(s0)
	addi a6, zero, 48
228:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t1, t1, t2
	or s5, s5, t1
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 228b
	addi a1, s0, 97
	addi a2, s1, -97
	addi a3, zero, 0
	addi a4, zero, 0
	addi a4, a4, -1
	addi s6, zero, 0
229:
	lbu a7, 0(a1)
	addi t1, a7, -1
	srli t1, t1, 63
	addi t2, zero, 1
	xor t2, a7, t2
	addi t2, t2, -1
	srli t2, t2, 63
	or t1, t1, t2
	addi t1, t1, -1
	and t1, t1, a4
	or s5, s5, t1
	addi t3, zero, 0
	sub t3, t3, t2
	and t1, a3, a4
	and t1, t1, t3
	or s6, s6, t1
	addi t2, t2, -1
	and a4, a4, t2
	addi a1, a1, 1
	addi a3, a3, 1
	addi a2, a2, -1
	bnez a2, 229b
	or s5, s5, a4
	addi a1, s0, 2047
	addi a1, a1, 513
	addi t5, zero, 1
	slli t5, t5, 11
	addi t0, zero, 0
230:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 230b
	addi a4, s0, 97
	addi a1, s0, 2047
	addi a1, a1, 513
	addi a5, s1, -97
231:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 231b
	addi s8, s6, 1
	addi s9, zero, 1
	addi s10, zero, 10
232:
	addi a1, s0, 2047
	addi a1, a1, 513
	add a2, a1, s9
	addi a3, zero, 1
	and a3, s8, a3
	addi a4, zero, 0
	sub a3, a4, a3
	addi a5, s1, 0
233:
	lbu t1, 0(a1)
	lbu t2, 0(a2)
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	sb t1, 0(a1)
	addi a1, a1, 1
	addi a2, a2, 1
	addi a5, a5, -1
	bnez a5, 233b
	srli s8, s8, 1
	add s9, s9, s9
	addi s10, s10, -1
	bnez s10, 232b
	addi a1, zero, 1
	xor a1, s4, a1
	addi a1, a1, -1
	srli a1, a1, 63
	addi a2, zero, 0
	sub a2, a2, s5
	or a2, a2, s5
	srli a2, a2, 63
	addi a3, zero, 1
	xor a2, a2, a3
	and a1, a1, a2
	addi s7, zero, 0
	sub s7, s7, a1
	addi a4, s0, 2047
	addi a4, a4, 513
	addi a5, s2, 0
	addi a6, s1, 0
234:
	lbu t1, 0(a4)
	and t1, t1, s7
	sb t1, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 234b
	addi a1, s1, -98
	sub a1, a1, s6
	and a1, a1, s7
	sd a1, 0(s3)
	addi a1, zero, 2
	xor a0, s4, a1
	addi a0, a0, -1
	srli a0, a0, 63
	add a0, a0, a0
	addi a1, zero, 1
	and a1, s7, a1
	or a0, a0, a1
	j 223f
222:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
235:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 235b
	addi t1, zero, 0
	sd t1, 0(s3)
	addi a1, zero, 2
	xor a0, s4, a1
	addi a0, a0, -1
	srli a0, a0, 63
	add a0, a0, a0
223:
27:
	j 25f
24:
	addi a0, zero, 66
	sub a0, s1, a0
	srli a0, a0, 63
	bnez a0, 236f
	addi s6, s0, 33
	addi s7, s1, -33
	addi s8, s0, 1
	addi s9, zero, 32
	addi s10, zero, 0
	addi s11, zero, 0
238:
	addi a0, s0, 1024
	addi t1, sp, 256
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, zero, 0
	addi a2, s6, 0
	addi a3, s7, 0
	addi t1, sp, 256
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a2, s0, 1344
	addi t1, s10, 0
	sb t1, 3(a2)
	srli t1, t1, 8
	sb t1, 2(a2)
	srli t1, t1, 8
	sb t1, 1(a2)
	srli t1, t1, 8
	sb t1, 0(a2)
	addi a0, s0, 1024
	addi a1, s7, 0
	addi a3, zero, 4
	addi t1, sp, 256
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, s7, 4
	addi a2, s0, 1280
	addi t1, sp, 256
	ld t1, 0(t1)
	ld t1, 16(t1)
	jalr ra, 0(t1)
	addi a6, sp, 256
	ld a6, 0(a6)
	ld a6, 32(a6)
	addi a4, s0, 1280
	add a5, s8, s11
	sub t1, s9, s11
	sub t2, t1, a6
	srli t3, t2, 63
	addi t4, zero, 0
	sub t3, t4, t3
	and t2, t2, t3
	add a6, a6, t2
239:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t2, t2, t1
	sb t2, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 239b
	addi t1, sp, 256
	ld t1, 0(t1)
	ld t1, 32(t1)
	addi s10, s10, 1
	add s11, s11, t1
	sub t1, s11, s9
	srli t1, t1, 63
	bnez t1, 238b
	addi s6, s0, 1
	addi s7, zero, 32
	addi s8, s0, 33
	addi s9, s1, -33
	addi s10, zero, 0
	addi s11, zero, 0
240:
	addi a0, s0, 1024
	addi t1, sp, 256
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, zero, 0
	addi a2, s6, 0
	addi a3, s7, 0
	addi t1, sp, 256
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a2, s0, 1344
	addi t1, s10, 0
	sb t1, 3(a2)
	srli t1, t1, 8
	sb t1, 2(a2)
	srli t1, t1, 8
	sb t1, 1(a2)
	srli t1, t1, 8
	sb t1, 0(a2)
	addi a0, s0, 1024
	addi a1, s7, 0
	addi a3, zero, 4
	addi t1, sp, 256
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, s7, 4
	addi a2, s0, 1280
	addi t1, sp, 256
	ld t1, 0(t1)
	ld t1, 16(t1)
	jalr ra, 0(t1)
	addi a6, sp, 256
	ld a6, 0(a6)
	ld a6, 32(a6)
	addi a4, s0, 1280
	add a5, s8, s11
	sub t1, s9, s11
	sub t2, t1, a6
	srli t3, t2, 63
	addi t4, zero, 0
	sub t3, t4, t3
	and t2, t2, t3
	add a6, a6, t2
241:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t2, t2, t1
	sb t2, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 241b
	addi t1, sp, 256
	ld t1, 0(t1)
	ld t1, 32(t1)
	addi s10, s10, 1
	add s11, s11, t1
	sub t1, s11, s9
	srli t1, t1, 63
	bnez t1, 240b
	addi a0, s0, 1024
	addi t1, sp, 248
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi t6, sp, 128
	addi a0, s0, 1024
	addi a1, zero, 0
	ld a2, 72(t6)
	ld a3, 80(t6)
	addi t1, sp, 248
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi t6, sp, 128
	addi a0, s0, 1024
	ld a1, 80(t6)
	addi a2, s0, 1280
	addi t1, sp, 248
	ld t1, 0(t1)
	ld t1, 16(t1)
	jalr ra, 0(t1)
	addi a4, s0, 33
	addi a5, s0, 1280
	lbu s5, 0(s0)
	addi a6, zero, 32
242:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t1, t1, t2
	or s5, s5, t1
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 242b
	addi a1, s0, 65
	addi a2, s1, -65
	addi a3, zero, 0
	addi a4, zero, 0
	addi a4, a4, -1
	addi s6, zero, 0
243:
	lbu a7, 0(a1)
	addi t1, a7, -1
	srli t1, t1, 63
	addi t2, zero, 1
	xor t2, a7, t2
	addi t2, t2, -1
	srli t2, t2, 63
	or t1, t1, t2
	addi t1, t1, -1
	and t1, t1, a4
	or s5, s5, t1
	addi t3, zero, 0
	sub t3, t3, t2
	and t1, a3, a4
	and t1, t1, t3
	or s6, s6, t1
	addi t2, t2, -1
	and a4, a4, t2
	addi a1, a1, 1
	addi a3, a3, 1
	addi a2, a2, -1
	bnez a2, 243b
	or s5, s5, a4
	addi a1, s0, 2047
	addi a1, a1, 513
	addi t5, zero, 1
	slli t5, t5, 11
	addi t0, zero, 0
244:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 244b
	addi a4, s0, 65
	addi a1, s0, 2047
	addi a1, a1, 513
	addi a5, s1, -65
245:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 245b
	addi s8, s6, 1
	addi s9, zero, 1
	addi s10, zero, 10
246:
	addi a1, s0, 2047
	addi a1, a1, 513
	add a2, a1, s9
	addi a3, zero, 1
	and a3, s8, a3
	addi a4, zero, 0
	sub a3, a4, a3
	addi a5, s1, 0
247:
	lbu t1, 0(a1)
	lbu t2, 0(a2)
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	sb t1, 0(a1)
	addi a1, a1, 1
	addi a2, a2, 1
	addi a5, a5, -1
	bnez a5, 247b
	srli s8, s8, 1
	add s9, s9, s9
	addi s10, s10, -1
	bnez s10, 246b
	addi a1, zero, 1
	xor a1, s4, a1
	addi a1, a1, -1
	srli a1, a1, 63
	addi a2, zero, 0
	sub a2, a2, s5
	or a2, a2, s5
	srli a2, a2, 63
	addi a3, zero, 1
	xor a2, a2, a3
	and a1, a1, a2
	addi s7, zero, 0
	sub s7, s7, a1
	addi a4, s0, 2047
	addi a4, a4, 513
	addi a5, s2, 0
	addi a6, s1, 0
248:
	lbu t1, 0(a4)
	and t1, t1, s7
	sb t1, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 248b
	addi a1, s1, -66
	sub a1, a1, s6
	and a1, a1, s7
	sd a1, 0(s3)
	addi a1, zero, 2
	xor a0, s4, a1
	addi a0, a0, -1
	srli a0, a0, 63
	add a0, a0, a0
	addi a1, zero, 1
	and a1, s7, a1
	or a0, a0, a1
	j 237f
236:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
249:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 249b
	addi t1, zero, 0
	sd t1, 0(s3)
	addi a1, zero, 2
	xor a0, s4, a1
	addi a0, a0, -1
	srli a0, a0, 63
	add a0, a0, a0
237:
25:
	j 23f
22:
	addi a0, zero, 58
	sub a0, s1, a0
	srli a0, a0, 63
	bnez a0, 250f
	addi s6, s0, 29
	addi s7, s1, -29
	addi s8, s0, 1
	addi s9, zero, 28
	addi s10, zero, 0
	addi s11, zero, 0
252:
	addi a0, s0, 1024
	addi t1, sp, 256
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, zero, 0
	addi a2, s6, 0
	addi a3, s7, 0
	addi t1, sp, 256
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a2, s0, 1344
	addi t1, s10, 0
	sb t1, 3(a2)
	srli t1, t1, 8
	sb t1, 2(a2)
	srli t1, t1, 8
	sb t1, 1(a2)
	srli t1, t1, 8
	sb t1, 0(a2)
	addi a0, s0, 1024
	addi a1, s7, 0
	addi a3, zero, 4
	addi t1, sp, 256
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, s7, 4
	addi a2, s0, 1280
	addi t1, sp, 256
	ld t1, 0(t1)
	ld t1, 16(t1)
	jalr ra, 0(t1)
	addi a6, sp, 256
	ld a6, 0(a6)
	ld a6, 32(a6)
	addi a4, s0, 1280
	add a5, s8, s11
	sub t1, s9, s11
	sub t2, t1, a6
	srli t3, t2, 63
	addi t4, zero, 0
	sub t3, t4, t3
	and t2, t2, t3
	add a6, a6, t2
253:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t2, t2, t1
	sb t2, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 253b
	addi t1, sp, 256
	ld t1, 0(t1)
	ld t1, 32(t1)
	addi s10, s10, 1
	add s11, s11, t1
	sub t1, s11, s9
	srli t1, t1, 63
	bnez t1, 252b
	addi s6, s0, 1
	addi s7, zero, 28
	addi s8, s0, 29
	addi s9, s1, -29
	addi s10, zero, 0
	addi s11, zero, 0
254:
	addi a0, s0, 1024
	addi t1, sp, 256
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, zero, 0
	addi a2, s6, 0
	addi a3, s7, 0
	addi t1, sp, 256
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a2, s0, 1344
	addi t1, s10, 0
	sb t1, 3(a2)
	srli t1, t1, 8
	sb t1, 2(a2)
	srli t1, t1, 8
	sb t1, 1(a2)
	srli t1, t1, 8
	sb t1, 0(a2)
	addi a0, s0, 1024
	addi a1, s7, 0
	addi a3, zero, 4
	addi t1, sp, 256
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, s7, 4
	addi a2, s0, 1280
	addi t1, sp, 256
	ld t1, 0(t1)
	ld t1, 16(t1)
	jalr ra, 0(t1)
	addi a6, sp, 256
	ld a6, 0(a6)
	ld a6, 32(a6)
	addi a4, s0, 1280
	add a5, s8, s11
	sub t1, s9, s11
	sub t2, t1, a6
	srli t3, t2, 63
	addi t4, zero, 0
	sub t3, t4, t3
	and t2, t2, t3
	add a6, a6, t2
255:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t2, t2, t1
	sb t2, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 255b
	addi t1, sp, 256
	ld t1, 0(t1)
	ld t1, 32(t1)
	addi s10, s10, 1
	add s11, s11, t1
	sub t1, s11, s9
	srli t1, t1, 63
	bnez t1, 254b
	addi a0, s0, 1024
	addi t1, sp, 248
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi t6, sp, 128
	addi a0, s0, 1024
	addi a1, zero, 0
	ld a2, 72(t6)
	ld a3, 80(t6)
	addi t1, sp, 248
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi t6, sp, 128
	addi a0, s0, 1024
	ld a1, 80(t6)
	addi a2, s0, 1280
	addi t1, sp, 248
	ld t1, 0(t1)
	ld t1, 16(t1)
	jalr ra, 0(t1)
	addi a4, s0, 29
	addi a5, s0, 1280
	lbu s5, 0(s0)
	addi a6, zero, 28
256:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t1, t1, t2
	or s5, s5, t1
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 256b
	addi a1, s0, 57
	addi a2, s1, -57
	addi a3, zero, 0
	addi a4, zero, 0
	addi a4, a4, -1
	addi s6, zero, 0
257:
	lbu a7, 0(a1)
	addi t1, a7, -1
	srli t1, t1, 63
	addi t2, zero, 1
	xor t2, a7, t2
	addi t2, t2, -1
	srli t2, t2, 63
	or t1, t1, t2
	addi t1, t1, -1
	and t1, t1, a4
	or s5, s5, t1
	addi t3, zero, 0
	sub t3, t3, t2
	and t1, a3, a4
	and t1, t1, t3
	or s6, s6, t1
	addi t2, t2, -1
	and a4, a4, t2
	addi a1, a1, 1
	addi a3, a3, 1
	addi a2, a2, -1
	bnez a2, 257b
	or s5, s5, a4
	addi a1, s0, 2047
	addi a1, a1, 513
	addi t5, zero, 1
	slli t5, t5, 11
	addi t0, zero, 0
258:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 258b
	addi a4, s0, 57
	addi a1, s0, 2047
	addi a1, a1, 513
	addi a5, s1, -57
259:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 259b
	addi s8, s6, 1
	addi s9, zero, 1
	addi s10, zero, 10
260:
	addi a1, s0, 2047
	addi a1, a1, 513
	add a2, a1, s9
	addi a3, zero, 1
	and a3, s8, a3
	addi a4, zero, 0
	sub a3, a4, a3
	addi a5, s1, 0
261:
	lbu t1, 0(a1)
	lbu t2, 0(a2)
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	sb t1, 0(a1)
	addi a1, a1, 1
	addi a2, a2, 1
	addi a5, a5, -1
	bnez a5, 261b
	srli s8, s8, 1
	add s9, s9, s9
	addi s10, s10, -1
	bnez s10, 260b
	addi a1, zero, 1
	xor a1, s4, a1
	addi a1, a1, -1
	srli a1, a1, 63
	addi a2, zero, 0
	sub a2, a2, s5
	or a2, a2, s5
	srli a2, a2, 63
	addi a3, zero, 1
	xor a2, a2, a3
	and a1, a1, a2
	addi s7, zero, 0
	sub s7, s7, a1
	addi a4, s0, 2047
	addi a4, a4, 513
	addi a5, s2, 0
	addi a6, s1, 0
262:
	lbu t1, 0(a4)
	and t1, t1, s7
	sb t1, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 262b
	addi a1, s1, -58
	sub a1, a1, s6
	and a1, a1, s7
	sd a1, 0(s3)
	addi a1, zero, 2
	xor a0, s4, a1
	addi a0, a0, -1
	srli a0, a0, 63
	add a0, a0, a0
	addi a1, zero, 1
	and a1, s7, a1
	or a0, a0, a1
	j 251f
250:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
263:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 263b
	addi t1, zero, 0
	sd t1, 0(s3)
	addi a1, zero, 2
	xor a0, s4, a1
	addi a0, a0, -1
	srli a0, a0, 63
	add a0, a0, a0
251:
23:
	j 21f
20:
	addi a0, zero, 42
	sub a0, s1, a0
	srli a0, a0, 63
	bnez a0, 264f
	addi s6, s0, 21
	addi s7, s1, -21
	addi s8, s0, 1
	addi s9, zero, 20
	addi s10, zero, 0
	addi s11, zero, 0
266:
	addi a0, s0, 1024
	addi t1, sp, 256
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, zero, 0
	addi a2, s6, 0
	addi a3, s7, 0
	addi t1, sp, 256
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a2, s0, 1344
	addi t1, s10, 0
	sb t1, 3(a2)
	srli t1, t1, 8
	sb t1, 2(a2)
	srli t1, t1, 8
	sb t1, 1(a2)
	srli t1, t1, 8
	sb t1, 0(a2)
	addi a0, s0, 1024
	addi a1, s7, 0
	addi a3, zero, 4
	addi t1, sp, 256
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, s7, 4
	addi a2, s0, 1280
	addi t1, sp, 256
	ld t1, 0(t1)
	ld t1, 16(t1)
	jalr ra, 0(t1)
	addi a6, sp, 256
	ld a6, 0(a6)
	ld a6, 32(a6)
	addi a4, s0, 1280
	add a5, s8, s11
	sub t1, s9, s11
	sub t2, t1, a6
	srli t3, t2, 63
	addi t4, zero, 0
	sub t3, t4, t3
	and t2, t2, t3
	add a6, a6, t2
267:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t2, t2, t1
	sb t2, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 267b
	addi t1, sp, 256
	ld t1, 0(t1)
	ld t1, 32(t1)
	addi s10, s10, 1
	add s11, s11, t1
	sub t1, s11, s9
	srli t1, t1, 63
	bnez t1, 266b
	addi s6, s0, 1
	addi s7, zero, 20
	addi s8, s0, 21
	addi s9, s1, -21
	addi s10, zero, 0
	addi s11, zero, 0
268:
	addi a0, s0, 1024
	addi t1, sp, 256
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, zero, 0
	addi a2, s6, 0
	addi a3, s7, 0
	addi t1, sp, 256
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a2, s0, 1344
	addi t1, s10, 0
	sb t1, 3(a2)
	srli t1, t1, 8
	sb t1, 2(a2)
	srli t1, t1, 8
	sb t1, 1(a2)
	srli t1, t1, 8
	sb t1, 0(a2)
	addi a0, s0, 1024
	addi a1, s7, 0
	addi a3, zero, 4
	addi t1, sp, 256
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, s7, 4
	addi a2, s0, 1280
	addi t1, sp, 256
	ld t1, 0(t1)
	ld t1, 16(t1)
	jalr ra, 0(t1)
	addi a6, sp, 256
	ld a6, 0(a6)
	ld a6, 32(a6)
	addi a4, s0, 1280
	add a5, s8, s11
	sub t1, s9, s11
	sub t2, t1, a6
	srli t3, t2, 63
	addi t4, zero, 0
	sub t3, t4, t3
	and t2, t2, t3
	add a6, a6, t2
269:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t2, t2, t1
	sb t2, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 269b
	addi t1, sp, 256
	ld t1, 0(t1)
	ld t1, 32(t1)
	addi s10, s10, 1
	add s11, s11, t1
	sub t1, s11, s9
	srli t1, t1, 63
	bnez t1, 268b
	addi a0, s0, 1024
	addi t1, sp, 248
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi t6, sp, 128
	addi a0, s0, 1024
	addi a1, zero, 0
	ld a2, 72(t6)
	ld a3, 80(t6)
	addi t1, sp, 248
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi t6, sp, 128
	addi a0, s0, 1024
	ld a1, 80(t6)
	addi a2, s0, 1280
	addi t1, sp, 248
	ld t1, 0(t1)
	ld t1, 16(t1)
	jalr ra, 0(t1)
	addi a4, s0, 21
	addi a5, s0, 1280
	lbu s5, 0(s0)
	addi a6, zero, 20
270:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t1, t1, t2
	or s5, s5, t1
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 270b
	addi a1, s0, 41
	addi a2, s1, -41
	addi a3, zero, 0
	addi a4, zero, 0
	addi a4, a4, -1
	addi s6, zero, 0
271:
	lbu a7, 0(a1)
	addi t1, a7, -1
	srli t1, t1, 63
	addi t2, zero, 1
	xor t2, a7, t2
	addi t2, t2, -1
	srli t2, t2, 63
	or t1, t1, t2
	addi t1, t1, -1
	and t1, t1, a4
	or s5, s5, t1
	addi t3, zero, 0
	sub t3, t3, t2
	and t1, a3, a4
	and t1, t1, t3
	or s6, s6, t1
	addi t2, t2, -1
	and a4, a4, t2
	addi a1, a1, 1
	addi a3, a3, 1
	addi a2, a2, -1
	bnez a2, 271b
	or s5, s5, a4
	addi a1, s0, 2047
	addi a1, a1, 513
	addi t5, zero, 1
	slli t5, t5, 11
	addi t0, zero, 0
272:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 272b
	addi a4, s0, 41
	addi a1, s0, 2047
	addi a1, a1, 513
	addi a5, s1, -41
273:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 273b
	addi s8, s6, 1
	addi s9, zero, 1
	addi s10, zero, 10
274:
	addi a1, s0, 2047
	addi a1, a1, 513
	add a2, a1, s9
	addi a3, zero, 1
	and a3, s8, a3
	addi a4, zero, 0
	sub a3, a4, a3
	addi a5, s1, 0
275:
	lbu t1, 0(a1)
	lbu t2, 0(a2)
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	sb t1, 0(a1)
	addi a1, a1, 1
	addi a2, a2, 1
	addi a5, a5, -1
	bnez a5, 275b
	srli s8, s8, 1
	add s9, s9, s9
	addi s10, s10, -1
	bnez s10, 274b
	addi a1, zero, 1
	xor a1, s4, a1
	addi a1, a1, -1
	srli a1, a1, 63
	addi a2, zero, 0
	sub a2, a2, s5
	or a2, a2, s5
	srli a2, a2, 63
	addi a3, zero, 1
	xor a2, a2, a3
	and a1, a1, a2
	addi s7, zero, 0
	sub s7, s7, a1
	addi a4, s0, 2047
	addi a4, a4, 513
	addi a5, s2, 0
	addi a6, s1, 0
276:
	lbu t1, 0(a4)
	and t1, t1, s7
	sb t1, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 276b
	addi a1, s1, -42
	sub a1, a1, s6
	and a1, a1, s7
	sd a1, 0(s3)
	addi a1, zero, 2
	xor a0, s4, a1
	addi a0, a0, -1
	srli a0, a0, 63
	add a0, a0, a0
	addi a1, zero, 1
	and a1, s7, a1
	or a0, a0, a1
	j 265f
264:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
277:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 277b
	addi t1, zero, 0
	sd t1, 0(s3)
	addi a1, zero, 2
	xor a0, s4, a1
	addi a0, a0, -1
	srli a0, a0, 63
	add a0, a0, a0
265:
21:
	addi t0, sp, 0
	ld s0, 16(t0)
	ld s1, 24(t0)
	ld s2, 32(t0)
	ld s3, 40(t0)
	ld s4, 48(t0)
	ld s5, 56(t0)
	ld s6, 64(t0)
	ld s7, 72(t0)
	ld s8, 80(t0)
	ld s9, 88(t0)
	ld s10, 96(t0)
	ld s11, 104(t0)
	ld ra, 112(t0)
	addi sp, sp, 128
	ret
	.option pop

vg_rsa_oaep_encrypt_precomputed:
	.option push
	.option arch, +m, +c
	addi sp, sp, -128
	addi t0, sp, 0
	sd s0, 16(t0)
	sd s1, 24(t0)
	sd s2, 32(t0)
	sd s3, 40(t0)
	sd s4, 48(t0)
	sd s5, 56(t0)
	sd s6, 64(t0)
	sd s7, 72(t0)
	sd s8, 80(t0)
	sd s9, 88(t0)
	sd s10, 96(t0)
	sd s11, 104(t0)
	sd ra, 112(t0)
	addi t6, sp, 128
	ld s0, 32(t6)
	addi s1, a3, 0
	addi s2, a0, 0
	addi s3, a4, 0
	addi s4, a5, 0
	addi s6, a6, 0
	addi s7, a7, 0
	ld t2, 0(t6)
	ld t3, 8(t6)
	ld t4, 16(t6)
	addi a0, sp, 192
	ld a0, 0(a0)
	ld a0, 32(a0)
	addi a1, a0, -20
	beqz a1, 20f
	addi a1, a0, -28
	beqz a1, 22f
	addi a1, a0, -32
	beqz a1, 24f
	addi a1, a0, -48
	beqz a1, 26f
	addi a0, zero, 130
	sub a0, s1, a0
	srli a0, a0, 63
	bnez a0, 28f
	addi a0, zero, 130
	sub a1, s1, a0
	sub a1, a1, t3
	srli a1, a1, 63
	srli a0, t3, 63
	or a0, a0, a1
	bnez a0, 210f
	addi a1, s0, 0
	addi t5, zero, 1024
	addi t0, zero, 0
212:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 212b
	addi a4, t4, 0
	addi a1, s0, 1
	addi a5, zero, 64
213:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 213b
	add a1, s0, s1
	sub a1, a1, t3
	addi a1, a1, -1
	addi t1, zero, 1
	sb t1, 0(a1)
	addi a1, a1, 1
	addi a4, t2, 0
	addi a5, t3, 0
	bnez a5, 214f
	j 215f
214:
216:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 216b
215:
	addi a0, s0, 1024
	addi t1, sp, 192
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, zero, 0
	addi a2, s6, 0
	addi a3, s7, 0
	addi t1, sp, 192
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, s7, 0
	addi a2, s0, 1280
	addi t1, sp, 192
	ld t1, 0(t1)
	ld t1, 16(t1)
	jalr ra, 0(t1)
	addi a4, s0, 1280
	addi a1, s0, 65
	addi a5, zero, 64
217:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 217b
	addi s6, s0, 1
	addi s7, zero, 64
	addi s8, s0, 65
	addi s9, s1, -65
	addi s10, zero, 0
	addi s11, zero, 0
218:
	addi a0, s0, 1024
	addi t1, sp, 200
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, zero, 0
	addi a2, s6, 0
	addi a3, s7, 0
	addi t1, sp, 200
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a2, s0, 1344
	addi t1, s10, 0
	sb t1, 3(a2)
	srli t1, t1, 8
	sb t1, 2(a2)
	srli t1, t1, 8
	sb t1, 1(a2)
	srli t1, t1, 8
	sb t1, 0(a2)
	addi a0, s0, 1024
	addi a1, s7, 0
	addi a3, zero, 4
	addi t1, sp, 200
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, s7, 4
	addi a2, s0, 1280
	addi t1, sp, 200
	ld t1, 0(t1)
	ld t1, 16(t1)
	jalr ra, 0(t1)
	addi a6, sp, 200
	ld a6, 0(a6)
	ld a6, 32(a6)
	addi a4, s0, 1280
	add a5, s8, s11
	sub t1, s9, s11
	sub t2, t1, a6
	srli t3, t2, 63
	addi t4, zero, 0
	sub t3, t4, t3
	and t2, t2, t3
	add a6, a6, t2
219:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t2, t2, t1
	sb t2, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 219b
	addi t1, sp, 200
	ld t1, 0(t1)
	ld t1, 32(t1)
	addi s10, s10, 1
	add s11, s11, t1
	sub t1, s11, s9
	srli t1, t1, 63
	bnez t1, 218b
	addi s6, s0, 65
	addi s7, s1, -65
	addi s8, s0, 1
	addi s9, zero, 64
	addi s10, zero, 0
	addi s11, zero, 0
220:
	addi a0, s0, 1024
	addi t1, sp, 200
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, zero, 0
	addi a2, s6, 0
	addi a3, s7, 0
	addi t1, sp, 200
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a2, s0, 1344
	addi t1, s10, 0
	sb t1, 3(a2)
	srli t1, t1, 8
	sb t1, 2(a2)
	srli t1, t1, 8
	sb t1, 1(a2)
	srli t1, t1, 8
	sb t1, 0(a2)
	addi a0, s0, 1024
	addi a1, s7, 0
	addi a3, zero, 4
	addi t1, sp, 200
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, s7, 4
	addi a2, s0, 1280
	addi t1, sp, 200
	ld t1, 0(t1)
	ld t1, 16(t1)
	jalr ra, 0(t1)
	addi a6, sp, 200
	ld a6, 0(a6)
	ld a6, 32(a6)
	addi a4, s0, 1280
	add a5, s8, s11
	sub t1, s9, s11
	sub t2, t1, a6
	srli t3, t2, 63
	addi t4, zero, 0
	sub t3, t4, t3
	and t2, t2, t3
	add a6, a6, t2
221:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t2, t2, t1
	sb t2, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 221b
	addi t1, sp, 200
	ld t1, 0(t1)
	ld t1, 32(t1)
	addi s10, s10, 1
	add s11, s11, t1
	sub t1, s11, s9
	srli t1, t1, 63
	bnez t1, 220b
	addi t0, sp, 0
	addi t6, sp, 128
	addi t1, zero, 1024
	slli t1, t1, 3
	add t1, s0, t1
	sd t1, 0(t0)
	ld t1, 40(t6)
	addi t1, t1, -1024
	sd t1, 8(t0)
	addi a0, s2, 0
	addi a1, s1, 0
	ld a2, 48(t6)
	ld a3, 56(t6)
	addi a4, s3, 0
	addi a5, s4, 0
	addi a6, s0, 0
	addi a7, s1, 0
	call {vg_rsa_public_precomputed_checked}
	j 211f
210:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
222:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 222b
	addi a0, zero, 0
211:
	j 29f
28:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
223:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 223b
	addi a0, zero, 0
29:
	j 27f
26:
	addi a0, zero, 98
	sub a0, s1, a0
	srli a0, a0, 63
	bnez a0, 224f
	addi a0, zero, 98
	sub a1, s1, a0
	sub a1, a1, t3
	srli a1, a1, 63
	srli a0, t3, 63
	or a0, a0, a1
	bnez a0, 226f
	addi a1, s0, 0
	addi t5, zero, 1024
	addi t0, zero, 0
228:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 228b
	addi a4, t4, 0
	addi a1, s0, 1
	addi a5, zero, 48
229:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 229b
	add a1, s0, s1
	sub a1, a1, t3
	addi a1, a1, -1
	addi t1, zero, 1
	sb t1, 0(a1)
	addi a1, a1, 1
	addi a4, t2, 0
	addi a5, t3, 0
	bnez a5, 230f
	j 231f
230:
232:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 232b
231:
	addi a0, s0, 1024
	addi t1, sp, 192
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, zero, 0
	addi a2, s6, 0
	addi a3, s7, 0
	addi t1, sp, 192
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, s7, 0
	addi a2, s0, 1280
	addi t1, sp, 192
	ld t1, 0(t1)
	ld t1, 16(t1)
	jalr ra, 0(t1)
	addi a4, s0, 1280
	addi a1, s0, 49
	addi a5, zero, 48
233:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 233b
	addi s6, s0, 1
	addi s7, zero, 48
	addi s8, s0, 49
	addi s9, s1, -49
	addi s10, zero, 0
	addi s11, zero, 0
234:
	addi a0, s0, 1024
	addi t1, sp, 200
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, zero, 0
	addi a2, s6, 0
	addi a3, s7, 0
	addi t1, sp, 200
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a2, s0, 1344
	addi t1, s10, 0
	sb t1, 3(a2)
	srli t1, t1, 8
	sb t1, 2(a2)
	srli t1, t1, 8
	sb t1, 1(a2)
	srli t1, t1, 8
	sb t1, 0(a2)
	addi a0, s0, 1024
	addi a1, s7, 0
	addi a3, zero, 4
	addi t1, sp, 200
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, s7, 4
	addi a2, s0, 1280
	addi t1, sp, 200
	ld t1, 0(t1)
	ld t1, 16(t1)
	jalr ra, 0(t1)
	addi a6, sp, 200
	ld a6, 0(a6)
	ld a6, 32(a6)
	addi a4, s0, 1280
	add a5, s8, s11
	sub t1, s9, s11
	sub t2, t1, a6
	srli t3, t2, 63
	addi t4, zero, 0
	sub t3, t4, t3
	and t2, t2, t3
	add a6, a6, t2
235:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t2, t2, t1
	sb t2, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 235b
	addi t1, sp, 200
	ld t1, 0(t1)
	ld t1, 32(t1)
	addi s10, s10, 1
	add s11, s11, t1
	sub t1, s11, s9
	srli t1, t1, 63
	bnez t1, 234b
	addi s6, s0, 49
	addi s7, s1, -49
	addi s8, s0, 1
	addi s9, zero, 48
	addi s10, zero, 0
	addi s11, zero, 0
236:
	addi a0, s0, 1024
	addi t1, sp, 200
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, zero, 0
	addi a2, s6, 0
	addi a3, s7, 0
	addi t1, sp, 200
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a2, s0, 1344
	addi t1, s10, 0
	sb t1, 3(a2)
	srli t1, t1, 8
	sb t1, 2(a2)
	srli t1, t1, 8
	sb t1, 1(a2)
	srli t1, t1, 8
	sb t1, 0(a2)
	addi a0, s0, 1024
	addi a1, s7, 0
	addi a3, zero, 4
	addi t1, sp, 200
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, s7, 4
	addi a2, s0, 1280
	addi t1, sp, 200
	ld t1, 0(t1)
	ld t1, 16(t1)
	jalr ra, 0(t1)
	addi a6, sp, 200
	ld a6, 0(a6)
	ld a6, 32(a6)
	addi a4, s0, 1280
	add a5, s8, s11
	sub t1, s9, s11
	sub t2, t1, a6
	srli t3, t2, 63
	addi t4, zero, 0
	sub t3, t4, t3
	and t2, t2, t3
	add a6, a6, t2
237:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t2, t2, t1
	sb t2, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 237b
	addi t1, sp, 200
	ld t1, 0(t1)
	ld t1, 32(t1)
	addi s10, s10, 1
	add s11, s11, t1
	sub t1, s11, s9
	srli t1, t1, 63
	bnez t1, 236b
	addi t0, sp, 0
	addi t6, sp, 128
	addi t1, zero, 1024
	slli t1, t1, 3
	add t1, s0, t1
	sd t1, 0(t0)
	ld t1, 40(t6)
	addi t1, t1, -1024
	sd t1, 8(t0)
	addi a0, s2, 0
	addi a1, s1, 0
	ld a2, 48(t6)
	ld a3, 56(t6)
	addi a4, s3, 0
	addi a5, s4, 0
	addi a6, s0, 0
	addi a7, s1, 0
	call {vg_rsa_public_precomputed_checked}
	j 227f
226:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
238:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 238b
	addi a0, zero, 0
227:
	j 225f
224:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
239:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 239b
	addi a0, zero, 0
225:
27:
	j 25f
24:
	addi a0, zero, 66
	sub a0, s1, a0
	srli a0, a0, 63
	bnez a0, 240f
	addi a0, zero, 66
	sub a1, s1, a0
	sub a1, a1, t3
	srli a1, a1, 63
	srli a0, t3, 63
	or a0, a0, a1
	bnez a0, 242f
	addi a1, s0, 0
	addi t5, zero, 1024
	addi t0, zero, 0
244:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 244b
	addi a4, t4, 0
	addi a1, s0, 1
	addi a5, zero, 32
245:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 245b
	add a1, s0, s1
	sub a1, a1, t3
	addi a1, a1, -1
	addi t1, zero, 1
	sb t1, 0(a1)
	addi a1, a1, 1
	addi a4, t2, 0
	addi a5, t3, 0
	bnez a5, 246f
	j 247f
246:
248:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 248b
247:
	addi a0, s0, 1024
	addi t1, sp, 192
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, zero, 0
	addi a2, s6, 0
	addi a3, s7, 0
	addi t1, sp, 192
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, s7, 0
	addi a2, s0, 1280
	addi t1, sp, 192
	ld t1, 0(t1)
	ld t1, 16(t1)
	jalr ra, 0(t1)
	addi a4, s0, 1280
	addi a1, s0, 33
	addi a5, zero, 32
249:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 249b
	addi s6, s0, 1
	addi s7, zero, 32
	addi s8, s0, 33
	addi s9, s1, -33
	addi s10, zero, 0
	addi s11, zero, 0
250:
	addi a0, s0, 1024
	addi t1, sp, 200
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, zero, 0
	addi a2, s6, 0
	addi a3, s7, 0
	addi t1, sp, 200
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a2, s0, 1344
	addi t1, s10, 0
	sb t1, 3(a2)
	srli t1, t1, 8
	sb t1, 2(a2)
	srli t1, t1, 8
	sb t1, 1(a2)
	srli t1, t1, 8
	sb t1, 0(a2)
	addi a0, s0, 1024
	addi a1, s7, 0
	addi a3, zero, 4
	addi t1, sp, 200
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, s7, 4
	addi a2, s0, 1280
	addi t1, sp, 200
	ld t1, 0(t1)
	ld t1, 16(t1)
	jalr ra, 0(t1)
	addi a6, sp, 200
	ld a6, 0(a6)
	ld a6, 32(a6)
	addi a4, s0, 1280
	add a5, s8, s11
	sub t1, s9, s11
	sub t2, t1, a6
	srli t3, t2, 63
	addi t4, zero, 0
	sub t3, t4, t3
	and t2, t2, t3
	add a6, a6, t2
251:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t2, t2, t1
	sb t2, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 251b
	addi t1, sp, 200
	ld t1, 0(t1)
	ld t1, 32(t1)
	addi s10, s10, 1
	add s11, s11, t1
	sub t1, s11, s9
	srli t1, t1, 63
	bnez t1, 250b
	addi s6, s0, 33
	addi s7, s1, -33
	addi s8, s0, 1
	addi s9, zero, 32
	addi s10, zero, 0
	addi s11, zero, 0
252:
	addi a0, s0, 1024
	addi t1, sp, 200
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, zero, 0
	addi a2, s6, 0
	addi a3, s7, 0
	addi t1, sp, 200
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a2, s0, 1344
	addi t1, s10, 0
	sb t1, 3(a2)
	srli t1, t1, 8
	sb t1, 2(a2)
	srli t1, t1, 8
	sb t1, 1(a2)
	srli t1, t1, 8
	sb t1, 0(a2)
	addi a0, s0, 1024
	addi a1, s7, 0
	addi a3, zero, 4
	addi t1, sp, 200
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, s7, 4
	addi a2, s0, 1280
	addi t1, sp, 200
	ld t1, 0(t1)
	ld t1, 16(t1)
	jalr ra, 0(t1)
	addi a6, sp, 200
	ld a6, 0(a6)
	ld a6, 32(a6)
	addi a4, s0, 1280
	add a5, s8, s11
	sub t1, s9, s11
	sub t2, t1, a6
	srli t3, t2, 63
	addi t4, zero, 0
	sub t3, t4, t3
	and t2, t2, t3
	add a6, a6, t2
253:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t2, t2, t1
	sb t2, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 253b
	addi t1, sp, 200
	ld t1, 0(t1)
	ld t1, 32(t1)
	addi s10, s10, 1
	add s11, s11, t1
	sub t1, s11, s9
	srli t1, t1, 63
	bnez t1, 252b
	addi t0, sp, 0
	addi t6, sp, 128
	addi t1, zero, 1024
	slli t1, t1, 3
	add t1, s0, t1
	sd t1, 0(t0)
	ld t1, 40(t6)
	addi t1, t1, -1024
	sd t1, 8(t0)
	addi a0, s2, 0
	addi a1, s1, 0
	ld a2, 48(t6)
	ld a3, 56(t6)
	addi a4, s3, 0
	addi a5, s4, 0
	addi a6, s0, 0
	addi a7, s1, 0
	call {vg_rsa_public_precomputed_checked}
	j 243f
242:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
254:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 254b
	addi a0, zero, 0
243:
	j 241f
240:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
255:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 255b
	addi a0, zero, 0
241:
25:
	j 23f
22:
	addi a0, zero, 58
	sub a0, s1, a0
	srli a0, a0, 63
	bnez a0, 256f
	addi a0, zero, 58
	sub a1, s1, a0
	sub a1, a1, t3
	srli a1, a1, 63
	srli a0, t3, 63
	or a0, a0, a1
	bnez a0, 258f
	addi a1, s0, 0
	addi t5, zero, 1024
	addi t0, zero, 0
260:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 260b
	addi a4, t4, 0
	addi a1, s0, 1
	addi a5, zero, 28
261:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 261b
	add a1, s0, s1
	sub a1, a1, t3
	addi a1, a1, -1
	addi t1, zero, 1
	sb t1, 0(a1)
	addi a1, a1, 1
	addi a4, t2, 0
	addi a5, t3, 0
	bnez a5, 262f
	j 263f
262:
264:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 264b
263:
	addi a0, s0, 1024
	addi t1, sp, 192
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, zero, 0
	addi a2, s6, 0
	addi a3, s7, 0
	addi t1, sp, 192
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, s7, 0
	addi a2, s0, 1280
	addi t1, sp, 192
	ld t1, 0(t1)
	ld t1, 16(t1)
	jalr ra, 0(t1)
	addi a4, s0, 1280
	addi a1, s0, 29
	addi a5, zero, 28
265:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 265b
	addi s6, s0, 1
	addi s7, zero, 28
	addi s8, s0, 29
	addi s9, s1, -29
	addi s10, zero, 0
	addi s11, zero, 0
266:
	addi a0, s0, 1024
	addi t1, sp, 200
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, zero, 0
	addi a2, s6, 0
	addi a3, s7, 0
	addi t1, sp, 200
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a2, s0, 1344
	addi t1, s10, 0
	sb t1, 3(a2)
	srli t1, t1, 8
	sb t1, 2(a2)
	srli t1, t1, 8
	sb t1, 1(a2)
	srli t1, t1, 8
	sb t1, 0(a2)
	addi a0, s0, 1024
	addi a1, s7, 0
	addi a3, zero, 4
	addi t1, sp, 200
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, s7, 4
	addi a2, s0, 1280
	addi t1, sp, 200
	ld t1, 0(t1)
	ld t1, 16(t1)
	jalr ra, 0(t1)
	addi a6, sp, 200
	ld a6, 0(a6)
	ld a6, 32(a6)
	addi a4, s0, 1280
	add a5, s8, s11
	sub t1, s9, s11
	sub t2, t1, a6
	srli t3, t2, 63
	addi t4, zero, 0
	sub t3, t4, t3
	and t2, t2, t3
	add a6, a6, t2
267:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t2, t2, t1
	sb t2, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 267b
	addi t1, sp, 200
	ld t1, 0(t1)
	ld t1, 32(t1)
	addi s10, s10, 1
	add s11, s11, t1
	sub t1, s11, s9
	srli t1, t1, 63
	bnez t1, 266b
	addi s6, s0, 29
	addi s7, s1, -29
	addi s8, s0, 1
	addi s9, zero, 28
	addi s10, zero, 0
	addi s11, zero, 0
268:
	addi a0, s0, 1024
	addi t1, sp, 200
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, zero, 0
	addi a2, s6, 0
	addi a3, s7, 0
	addi t1, sp, 200
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a2, s0, 1344
	addi t1, s10, 0
	sb t1, 3(a2)
	srli t1, t1, 8
	sb t1, 2(a2)
	srli t1, t1, 8
	sb t1, 1(a2)
	srli t1, t1, 8
	sb t1, 0(a2)
	addi a0, s0, 1024
	addi a1, s7, 0
	addi a3, zero, 4
	addi t1, sp, 200
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, s7, 4
	addi a2, s0, 1280
	addi t1, sp, 200
	ld t1, 0(t1)
	ld t1, 16(t1)
	jalr ra, 0(t1)
	addi a6, sp, 200
	ld a6, 0(a6)
	ld a6, 32(a6)
	addi a4, s0, 1280
	add a5, s8, s11
	sub t1, s9, s11
	sub t2, t1, a6
	srli t3, t2, 63
	addi t4, zero, 0
	sub t3, t4, t3
	and t2, t2, t3
	add a6, a6, t2
269:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t2, t2, t1
	sb t2, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 269b
	addi t1, sp, 200
	ld t1, 0(t1)
	ld t1, 32(t1)
	addi s10, s10, 1
	add s11, s11, t1
	sub t1, s11, s9
	srli t1, t1, 63
	bnez t1, 268b
	addi t0, sp, 0
	addi t6, sp, 128
	addi t1, zero, 1024
	slli t1, t1, 3
	add t1, s0, t1
	sd t1, 0(t0)
	ld t1, 40(t6)
	addi t1, t1, -1024
	sd t1, 8(t0)
	addi a0, s2, 0
	addi a1, s1, 0
	ld a2, 48(t6)
	ld a3, 56(t6)
	addi a4, s3, 0
	addi a5, s4, 0
	addi a6, s0, 0
	addi a7, s1, 0
	call {vg_rsa_public_precomputed_checked}
	j 259f
258:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
270:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 270b
	addi a0, zero, 0
259:
	j 257f
256:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
271:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 271b
	addi a0, zero, 0
257:
23:
	j 21f
20:
	addi a0, zero, 42
	sub a0, s1, a0
	srli a0, a0, 63
	bnez a0, 272f
	addi a0, zero, 42
	sub a1, s1, a0
	sub a1, a1, t3
	srli a1, a1, 63
	srli a0, t3, 63
	or a0, a0, a1
	bnez a0, 274f
	addi a1, s0, 0
	addi t5, zero, 1024
	addi t0, zero, 0
276:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 276b
	addi a4, t4, 0
	addi a1, s0, 1
	addi a5, zero, 20
277:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 277b
	add a1, s0, s1
	sub a1, a1, t3
	addi a1, a1, -1
	addi t1, zero, 1
	sb t1, 0(a1)
	addi a1, a1, 1
	addi a4, t2, 0
	addi a5, t3, 0
	bnez a5, 278f
	j 279f
278:
280:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 280b
279:
	addi a0, s0, 1024
	addi t1, sp, 192
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, zero, 0
	addi a2, s6, 0
	addi a3, s7, 0
	addi t1, sp, 192
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, s7, 0
	addi a2, s0, 1280
	addi t1, sp, 192
	ld t1, 0(t1)
	ld t1, 16(t1)
	jalr ra, 0(t1)
	addi a4, s0, 1280
	addi a1, s0, 21
	addi a5, zero, 20
281:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 281b
	addi s6, s0, 1
	addi s7, zero, 20
	addi s8, s0, 21
	addi s9, s1, -21
	addi s10, zero, 0
	addi s11, zero, 0
282:
	addi a0, s0, 1024
	addi t1, sp, 200
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, zero, 0
	addi a2, s6, 0
	addi a3, s7, 0
	addi t1, sp, 200
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a2, s0, 1344
	addi t1, s10, 0
	sb t1, 3(a2)
	srli t1, t1, 8
	sb t1, 2(a2)
	srli t1, t1, 8
	sb t1, 1(a2)
	srli t1, t1, 8
	sb t1, 0(a2)
	addi a0, s0, 1024
	addi a1, s7, 0
	addi a3, zero, 4
	addi t1, sp, 200
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, s7, 4
	addi a2, s0, 1280
	addi t1, sp, 200
	ld t1, 0(t1)
	ld t1, 16(t1)
	jalr ra, 0(t1)
	addi a6, sp, 200
	ld a6, 0(a6)
	ld a6, 32(a6)
	addi a4, s0, 1280
	add a5, s8, s11
	sub t1, s9, s11
	sub t2, t1, a6
	srli t3, t2, 63
	addi t4, zero, 0
	sub t3, t4, t3
	and t2, t2, t3
	add a6, a6, t2
283:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t2, t2, t1
	sb t2, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 283b
	addi t1, sp, 200
	ld t1, 0(t1)
	ld t1, 32(t1)
	addi s10, s10, 1
	add s11, s11, t1
	sub t1, s11, s9
	srli t1, t1, 63
	bnez t1, 282b
	addi s6, s0, 21
	addi s7, s1, -21
	addi s8, s0, 1
	addi s9, zero, 20
	addi s10, zero, 0
	addi s11, zero, 0
284:
	addi a0, s0, 1024
	addi t1, sp, 200
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, zero, 0
	addi a2, s6, 0
	addi a3, s7, 0
	addi t1, sp, 200
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a2, s0, 1344
	addi t1, s10, 0
	sb t1, 3(a2)
	srli t1, t1, 8
	sb t1, 2(a2)
	srli t1, t1, 8
	sb t1, 1(a2)
	srli t1, t1, 8
	sb t1, 0(a2)
	addi a0, s0, 1024
	addi a1, s7, 0
	addi a3, zero, 4
	addi t1, sp, 200
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, s7, 4
	addi a2, s0, 1280
	addi t1, sp, 200
	ld t1, 0(t1)
	ld t1, 16(t1)
	jalr ra, 0(t1)
	addi a6, sp, 200
	ld a6, 0(a6)
	ld a6, 32(a6)
	addi a4, s0, 1280
	add a5, s8, s11
	sub t1, s9, s11
	sub t2, t1, a6
	srli t3, t2, 63
	addi t4, zero, 0
	sub t3, t4, t3
	and t2, t2, t3
	add a6, a6, t2
285:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t2, t2, t1
	sb t2, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 285b
	addi t1, sp, 200
	ld t1, 0(t1)
	ld t1, 32(t1)
	addi s10, s10, 1
	add s11, s11, t1
	sub t1, s11, s9
	srli t1, t1, 63
	bnez t1, 284b
	addi t0, sp, 0
	addi t6, sp, 128
	addi t1, zero, 1024
	slli t1, t1, 3
	add t1, s0, t1
	sd t1, 0(t0)
	ld t1, 40(t6)
	addi t1, t1, -1024
	sd t1, 8(t0)
	addi a0, s2, 0
	addi a1, s1, 0
	ld a2, 48(t6)
	ld a3, 56(t6)
	addi a4, s3, 0
	addi a5, s4, 0
	addi a6, s0, 0
	addi a7, s1, 0
	call {vg_rsa_public_precomputed_checked}
	j 275f
274:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
286:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 286b
	addi a0, zero, 0
275:
	j 273f
272:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
287:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 287b
	addi a0, zero, 0
273:
21:
	addi t0, sp, 0
	ld s0, 16(t0)
	ld s1, 24(t0)
	ld s2, 32(t0)
	ld s3, 40(t0)
	ld s4, 48(t0)
	ld s5, 56(t0)
	ld s6, 64(t0)
	ld s7, 72(t0)
	ld s8, 80(t0)
	ld s9, 88(t0)
	ld s10, 96(t0)
	ld s11, 104(t0)
	ld ra, 112(t0)
	addi sp, sp, 128
	ret
	.option pop
