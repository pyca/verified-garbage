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
	addi a1, a0, -16
	beqz a1, 20f
	addi a1, a0, -20
	beqz a1, 22f
	addi a1, a0, -28
	beqz a1, 24f
	addi a1, a0, -32
	beqz a1, 26f
	addi a1, a0, -48
	beqz a1, 28f
	addi a0, zero, 130
	sub a0, s1, a0
	srli a0, a0, 63
	bnez a0, 210f
	addi s6, s0, 65
	addi s7, s1, -65
	addi s8, s0, 1
	addi s9, zero, 64
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
	addi s6, s0, 1
	addi s7, zero, 64
	addi s8, s0, 65
	addi s9, s1, -65
	addi s10, zero, 0
	addi s11, zero, 0
214:
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
215:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t2, t2, t1
	sb t2, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 215b
	addi t1, sp, 256
	ld t1, 0(t1)
	ld t1, 32(t1)
	addi s10, s10, 1
	add s11, s11, t1
	sub t1, s11, s9
	srli t1, t1, 63
	bnez t1, 214b
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
216:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t1, t1, t2
	or s5, s5, t1
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 216b
	addi a1, s0, 129
	addi a2, s1, -129
	addi a3, zero, 0
	addi a4, zero, 0
	addi a4, a4, -1
	addi s6, zero, 0
217:
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
	bnez a2, 217b
	or s5, s5, a4
	addi a1, s0, 2047
	addi a1, a1, 513
	addi t5, zero, 1
	slli t5, t5, 11
	addi t0, zero, 0
218:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 218b
	addi a4, s0, 129
	addi a1, s0, 2047
	addi a1, a1, 513
	addi a5, s1, -129
219:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 219b
	addi s8, s6, 1
	addi s9, zero, 1
	addi s10, zero, 10
220:
	addi a1, s0, 2047
	addi a1, a1, 513
	add a2, a1, s9
	addi a3, zero, 1
	and a3, s8, a3
	addi a4, zero, 0
	sub a3, a4, a3
	addi a5, s1, 0
221:
	lbu t1, 0(a1)
	lbu t2, 0(a2)
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	sb t1, 0(a1)
	addi a1, a1, 1
	addi a2, a2, 1
	addi a5, a5, -1
	bnez a5, 221b
	srli s8, s8, 1
	add s9, s9, s9
	addi s10, s10, -1
	bnez s10, 220b
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
222:
	lbu t1, 0(a4)
	and t1, t1, s7
	sb t1, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 222b
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
	j 211f
210:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
223:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 223b
	addi t1, zero, 0
	sd t1, 0(s3)
	addi a1, zero, 2
	xor a0, s4, a1
	addi a0, a0, -1
	srli a0, a0, 63
	add a0, a0, a0
211:
	j 29f
28:
	addi a0, zero, 98
	sub a0, s1, a0
	srli a0, a0, 63
	bnez a0, 224f
	addi s6, s0, 49
	addi s7, s1, -49
	addi s8, s0, 1
	addi s9, zero, 48
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
	addi s6, s0, 1
	addi s7, zero, 48
	addi s8, s0, 49
	addi s9, s1, -49
	addi s10, zero, 0
	addi s11, zero, 0
228:
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
229:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t2, t2, t1
	sb t2, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 229b
	addi t1, sp, 256
	ld t1, 0(t1)
	ld t1, 32(t1)
	addi s10, s10, 1
	add s11, s11, t1
	sub t1, s11, s9
	srli t1, t1, 63
	bnez t1, 228b
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
230:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t1, t1, t2
	or s5, s5, t1
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 230b
	addi a1, s0, 97
	addi a2, s1, -97
	addi a3, zero, 0
	addi a4, zero, 0
	addi a4, a4, -1
	addi s6, zero, 0
231:
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
	bnez a2, 231b
	or s5, s5, a4
	addi a1, s0, 2047
	addi a1, a1, 513
	addi t5, zero, 1
	slli t5, t5, 11
	addi t0, zero, 0
232:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 232b
	addi a4, s0, 97
	addi a1, s0, 2047
	addi a1, a1, 513
	addi a5, s1, -97
233:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 233b
	addi s8, s6, 1
	addi s9, zero, 1
	addi s10, zero, 10
234:
	addi a1, s0, 2047
	addi a1, a1, 513
	add a2, a1, s9
	addi a3, zero, 1
	and a3, s8, a3
	addi a4, zero, 0
	sub a3, a4, a3
	addi a5, s1, 0
235:
	lbu t1, 0(a1)
	lbu t2, 0(a2)
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	sb t1, 0(a1)
	addi a1, a1, 1
	addi a2, a2, 1
	addi a5, a5, -1
	bnez a5, 235b
	srli s8, s8, 1
	add s9, s9, s9
	addi s10, s10, -1
	bnez s10, 234b
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
236:
	lbu t1, 0(a4)
	and t1, t1, s7
	sb t1, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 236b
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
	j 225f
224:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
237:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 237b
	addi t1, zero, 0
	sd t1, 0(s3)
	addi a1, zero, 2
	xor a0, s4, a1
	addi a0, a0, -1
	srli a0, a0, 63
	add a0, a0, a0
225:
29:
	j 27f
26:
	addi a0, zero, 66
	sub a0, s1, a0
	srli a0, a0, 63
	bnez a0, 238f
	addi s6, s0, 33
	addi s7, s1, -33
	addi s8, s0, 1
	addi s9, zero, 32
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
	addi s6, s0, 1
	addi s7, zero, 32
	addi s8, s0, 33
	addi s9, s1, -33
	addi s10, zero, 0
	addi s11, zero, 0
242:
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
243:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t2, t2, t1
	sb t2, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 243b
	addi t1, sp, 256
	ld t1, 0(t1)
	ld t1, 32(t1)
	addi s10, s10, 1
	add s11, s11, t1
	sub t1, s11, s9
	srli t1, t1, 63
	bnez t1, 242b
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
244:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t1, t1, t2
	or s5, s5, t1
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 244b
	addi a1, s0, 65
	addi a2, s1, -65
	addi a3, zero, 0
	addi a4, zero, 0
	addi a4, a4, -1
	addi s6, zero, 0
245:
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
	bnez a2, 245b
	or s5, s5, a4
	addi a1, s0, 2047
	addi a1, a1, 513
	addi t5, zero, 1
	slli t5, t5, 11
	addi t0, zero, 0
246:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 246b
	addi a4, s0, 65
	addi a1, s0, 2047
	addi a1, a1, 513
	addi a5, s1, -65
247:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 247b
	addi s8, s6, 1
	addi s9, zero, 1
	addi s10, zero, 10
248:
	addi a1, s0, 2047
	addi a1, a1, 513
	add a2, a1, s9
	addi a3, zero, 1
	and a3, s8, a3
	addi a4, zero, 0
	sub a3, a4, a3
	addi a5, s1, 0
249:
	lbu t1, 0(a1)
	lbu t2, 0(a2)
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	sb t1, 0(a1)
	addi a1, a1, 1
	addi a2, a2, 1
	addi a5, a5, -1
	bnez a5, 249b
	srli s8, s8, 1
	add s9, s9, s9
	addi s10, s10, -1
	bnez s10, 248b
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
250:
	lbu t1, 0(a4)
	and t1, t1, s7
	sb t1, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 250b
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
	j 239f
238:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
251:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 251b
	addi t1, zero, 0
	sd t1, 0(s3)
	addi a1, zero, 2
	xor a0, s4, a1
	addi a0, a0, -1
	srli a0, a0, 63
	add a0, a0, a0
239:
27:
	j 25f
24:
	addi a0, zero, 58
	sub a0, s1, a0
	srli a0, a0, 63
	bnez a0, 252f
	addi s6, s0, 29
	addi s7, s1, -29
	addi s8, s0, 1
	addi s9, zero, 28
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
	addi s6, s0, 1
	addi s7, zero, 28
	addi s8, s0, 29
	addi s9, s1, -29
	addi s10, zero, 0
	addi s11, zero, 0
256:
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
257:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t2, t2, t1
	sb t2, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 257b
	addi t1, sp, 256
	ld t1, 0(t1)
	ld t1, 32(t1)
	addi s10, s10, 1
	add s11, s11, t1
	sub t1, s11, s9
	srli t1, t1, 63
	bnez t1, 256b
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
258:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t1, t1, t2
	or s5, s5, t1
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 258b
	addi a1, s0, 57
	addi a2, s1, -57
	addi a3, zero, 0
	addi a4, zero, 0
	addi a4, a4, -1
	addi s6, zero, 0
259:
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
	bnez a2, 259b
	or s5, s5, a4
	addi a1, s0, 2047
	addi a1, a1, 513
	addi t5, zero, 1
	slli t5, t5, 11
	addi t0, zero, 0
260:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 260b
	addi a4, s0, 57
	addi a1, s0, 2047
	addi a1, a1, 513
	addi a5, s1, -57
261:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 261b
	addi s8, s6, 1
	addi s9, zero, 1
	addi s10, zero, 10
262:
	addi a1, s0, 2047
	addi a1, a1, 513
	add a2, a1, s9
	addi a3, zero, 1
	and a3, s8, a3
	addi a4, zero, 0
	sub a3, a4, a3
	addi a5, s1, 0
263:
	lbu t1, 0(a1)
	lbu t2, 0(a2)
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	sb t1, 0(a1)
	addi a1, a1, 1
	addi a2, a2, 1
	addi a5, a5, -1
	bnez a5, 263b
	srli s8, s8, 1
	add s9, s9, s9
	addi s10, s10, -1
	bnez s10, 262b
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
264:
	lbu t1, 0(a4)
	and t1, t1, s7
	sb t1, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 264b
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
	j 253f
252:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
265:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 265b
	addi t1, zero, 0
	sd t1, 0(s3)
	addi a1, zero, 2
	xor a0, s4, a1
	addi a0, a0, -1
	srli a0, a0, 63
	add a0, a0, a0
253:
25:
	j 23f
22:
	addi a0, zero, 42
	sub a0, s1, a0
	srli a0, a0, 63
	bnez a0, 266f
	addi s6, s0, 21
	addi s7, s1, -21
	addi s8, s0, 1
	addi s9, zero, 20
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
	addi s6, s0, 1
	addi s7, zero, 20
	addi s8, s0, 21
	addi s9, s1, -21
	addi s10, zero, 0
	addi s11, zero, 0
270:
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
271:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t2, t2, t1
	sb t2, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 271b
	addi t1, sp, 256
	ld t1, 0(t1)
	ld t1, 32(t1)
	addi s10, s10, 1
	add s11, s11, t1
	sub t1, s11, s9
	srli t1, t1, 63
	bnez t1, 270b
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
272:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t1, t1, t2
	or s5, s5, t1
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 272b
	addi a1, s0, 41
	addi a2, s1, -41
	addi a3, zero, 0
	addi a4, zero, 0
	addi a4, a4, -1
	addi s6, zero, 0
273:
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
	bnez a2, 273b
	or s5, s5, a4
	addi a1, s0, 2047
	addi a1, a1, 513
	addi t5, zero, 1
	slli t5, t5, 11
	addi t0, zero, 0
274:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 274b
	addi a4, s0, 41
	addi a1, s0, 2047
	addi a1, a1, 513
	addi a5, s1, -41
275:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 275b
	addi s8, s6, 1
	addi s9, zero, 1
	addi s10, zero, 10
276:
	addi a1, s0, 2047
	addi a1, a1, 513
	add a2, a1, s9
	addi a3, zero, 1
	and a3, s8, a3
	addi a4, zero, 0
	sub a3, a4, a3
	addi a5, s1, 0
277:
	lbu t1, 0(a1)
	lbu t2, 0(a2)
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	sb t1, 0(a1)
	addi a1, a1, 1
	addi a2, a2, 1
	addi a5, a5, -1
	bnez a5, 277b
	srli s8, s8, 1
	add s9, s9, s9
	addi s10, s10, -1
	bnez s10, 276b
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
278:
	lbu t1, 0(a4)
	and t1, t1, s7
	sb t1, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 278b
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
	j 267f
266:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
279:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 279b
	addi t1, zero, 0
	sd t1, 0(s3)
	addi a1, zero, 2
	xor a0, s4, a1
	addi a0, a0, -1
	srli a0, a0, 63
	add a0, a0, a0
267:
23:
	j 21f
20:
	addi a0, zero, 34
	sub a0, s1, a0
	srli a0, a0, 63
	bnez a0, 280f
	addi s6, s0, 17
	addi s7, s1, -17
	addi s8, s0, 1
	addi s9, zero, 16
	addi s10, zero, 0
	addi s11, zero, 0
282:
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
283:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t2, t2, t1
	sb t2, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 283b
	addi t1, sp, 256
	ld t1, 0(t1)
	ld t1, 32(t1)
	addi s10, s10, 1
	add s11, s11, t1
	sub t1, s11, s9
	srli t1, t1, 63
	bnez t1, 282b
	addi s6, s0, 1
	addi s7, zero, 16
	addi s8, s0, 17
	addi s9, s1, -17
	addi s10, zero, 0
	addi s11, zero, 0
284:
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
285:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t2, t2, t1
	sb t2, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 285b
	addi t1, sp, 256
	ld t1, 0(t1)
	ld t1, 32(t1)
	addi s10, s10, 1
	add s11, s11, t1
	sub t1, s11, s9
	srli t1, t1, 63
	bnez t1, 284b
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
	addi a4, s0, 17
	addi a5, s0, 1280
	lbu s5, 0(s0)
	addi a6, zero, 16
286:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t1, t1, t2
	or s5, s5, t1
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 286b
	addi a1, s0, 33
	addi a2, s1, -33
	addi a3, zero, 0
	addi a4, zero, 0
	addi a4, a4, -1
	addi s6, zero, 0
287:
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
	bnez a2, 287b
	or s5, s5, a4
	addi a1, s0, 2047
	addi a1, a1, 513
	addi t5, zero, 1
	slli t5, t5, 11
	addi t0, zero, 0
288:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 288b
	addi a4, s0, 33
	addi a1, s0, 2047
	addi a1, a1, 513
	addi a5, s1, -33
289:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 289b
	addi s8, s6, 1
	addi s9, zero, 1
	addi s10, zero, 10
290:
	addi a1, s0, 2047
	addi a1, a1, 513
	add a2, a1, s9
	addi a3, zero, 1
	and a3, s8, a3
	addi a4, zero, 0
	sub a3, a4, a3
	addi a5, s1, 0
291:
	lbu t1, 0(a1)
	lbu t2, 0(a2)
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	sb t1, 0(a1)
	addi a1, a1, 1
	addi a2, a2, 1
	addi a5, a5, -1
	bnez a5, 291b
	srli s8, s8, 1
	add s9, s9, s9
	addi s10, s10, -1
	bnez s10, 290b
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
292:
	lbu t1, 0(a4)
	and t1, t1, s7
	sb t1, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 292b
	addi a1, s1, -34
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
	j 281f
280:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
293:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 293b
	addi t1, zero, 0
	sd t1, 0(s3)
	addi a1, zero, 2
	xor a0, s4, a1
	addi a0, a0, -1
	srli a0, a0, 63
	add a0, a0, a0
281:
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
	addi a1, a0, -16
	beqz a1, 20f
	addi a1, a0, -20
	beqz a1, 22f
	addi a1, a0, -28
	beqz a1, 24f
	addi a1, a0, -32
	beqz a1, 26f
	addi a1, a0, -48
	beqz a1, 28f
	addi a0, zero, 130
	sub a0, s1, a0
	srli a0, a0, 63
	bnez a0, 210f
	addi a0, zero, 130
	sub a1, s1, a0
	sub a1, a1, t3
	srli a1, a1, 63
	srli a0, t3, 63
	or a0, a0, a1
	bnez a0, 212f
	addi a1, s0, 0
	addi t5, zero, 1024
	addi t0, zero, 0
214:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 214b
	addi a4, t4, 0
	addi a1, s0, 1
	addi a5, zero, 64
215:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 215b
	add a1, s0, s1
	sub a1, a1, t3
	addi a1, a1, -1
	addi t1, zero, 1
	sb t1, 0(a1)
	addi a1, a1, 1
	addi a4, t2, 0
	addi a5, t3, 0
	bnez a5, 216f
	j 217f
216:
218:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 218b
217:
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
219:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 219b
	addi s6, s0, 1
	addi s7, zero, 64
	addi s8, s0, 65
	addi s9, s1, -65
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
	addi s6, s0, 65
	addi s7, s1, -65
	addi s8, s0, 1
	addi s9, zero, 64
	addi s10, zero, 0
	addi s11, zero, 0
222:
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
223:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t2, t2, t1
	sb t2, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 223b
	addi t1, sp, 200
	ld t1, 0(t1)
	ld t1, 32(t1)
	addi s10, s10, 1
	add s11, s11, t1
	sub t1, s11, s9
	srli t1, t1, 63
	bnez t1, 222b
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
	j 213f
212:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
224:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 224b
	addi a0, zero, 0
213:
	j 211f
210:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
225:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 225b
	addi a0, zero, 0
211:
	j 29f
28:
	addi a0, zero, 98
	sub a0, s1, a0
	srli a0, a0, 63
	bnez a0, 226f
	addi a0, zero, 98
	sub a1, s1, a0
	sub a1, a1, t3
	srli a1, a1, 63
	srli a0, t3, 63
	or a0, a0, a1
	bnez a0, 228f
	addi a1, s0, 0
	addi t5, zero, 1024
	addi t0, zero, 0
230:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 230b
	addi a4, t4, 0
	addi a1, s0, 1
	addi a5, zero, 48
231:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 231b
	add a1, s0, s1
	sub a1, a1, t3
	addi a1, a1, -1
	addi t1, zero, 1
	sb t1, 0(a1)
	addi a1, a1, 1
	addi a4, t2, 0
	addi a5, t3, 0
	bnez a5, 232f
	j 233f
232:
234:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 234b
233:
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
235:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 235b
	addi s6, s0, 1
	addi s7, zero, 48
	addi s8, s0, 49
	addi s9, s1, -49
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
	addi s6, s0, 49
	addi s7, s1, -49
	addi s8, s0, 1
	addi s9, zero, 48
	addi s10, zero, 0
	addi s11, zero, 0
238:
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
239:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t2, t2, t1
	sb t2, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 239b
	addi t1, sp, 200
	ld t1, 0(t1)
	ld t1, 32(t1)
	addi s10, s10, 1
	add s11, s11, t1
	sub t1, s11, s9
	srli t1, t1, 63
	bnez t1, 238b
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
	j 229f
228:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
240:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 240b
	addi a0, zero, 0
229:
	j 227f
226:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
241:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 241b
	addi a0, zero, 0
227:
29:
	j 27f
26:
	addi a0, zero, 66
	sub a0, s1, a0
	srli a0, a0, 63
	bnez a0, 242f
	addi a0, zero, 66
	sub a1, s1, a0
	sub a1, a1, t3
	srli a1, a1, 63
	srli a0, t3, 63
	or a0, a0, a1
	bnez a0, 244f
	addi a1, s0, 0
	addi t5, zero, 1024
	addi t0, zero, 0
246:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 246b
	addi a4, t4, 0
	addi a1, s0, 1
	addi a5, zero, 32
247:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 247b
	add a1, s0, s1
	sub a1, a1, t3
	addi a1, a1, -1
	addi t1, zero, 1
	sb t1, 0(a1)
	addi a1, a1, 1
	addi a4, t2, 0
	addi a5, t3, 0
	bnez a5, 248f
	j 249f
248:
250:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 250b
249:
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
251:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 251b
	addi s6, s0, 1
	addi s7, zero, 32
	addi s8, s0, 33
	addi s9, s1, -33
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
	addi s6, s0, 33
	addi s7, s1, -33
	addi s8, s0, 1
	addi s9, zero, 32
	addi s10, zero, 0
	addi s11, zero, 0
254:
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
255:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t2, t2, t1
	sb t2, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 255b
	addi t1, sp, 200
	ld t1, 0(t1)
	ld t1, 32(t1)
	addi s10, s10, 1
	add s11, s11, t1
	sub t1, s11, s9
	srli t1, t1, 63
	bnez t1, 254b
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
	j 245f
244:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
256:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 256b
	addi a0, zero, 0
245:
	j 243f
242:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
257:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 257b
	addi a0, zero, 0
243:
27:
	j 25f
24:
	addi a0, zero, 58
	sub a0, s1, a0
	srli a0, a0, 63
	bnez a0, 258f
	addi a0, zero, 58
	sub a1, s1, a0
	sub a1, a1, t3
	srli a1, a1, 63
	srli a0, t3, 63
	or a0, a0, a1
	bnez a0, 260f
	addi a1, s0, 0
	addi t5, zero, 1024
	addi t0, zero, 0
262:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 262b
	addi a4, t4, 0
	addi a1, s0, 1
	addi a5, zero, 28
263:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 263b
	add a1, s0, s1
	sub a1, a1, t3
	addi a1, a1, -1
	addi t1, zero, 1
	sb t1, 0(a1)
	addi a1, a1, 1
	addi a4, t2, 0
	addi a5, t3, 0
	bnez a5, 264f
	j 265f
264:
266:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 266b
265:
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
267:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 267b
	addi s6, s0, 1
	addi s7, zero, 28
	addi s8, s0, 29
	addi s9, s1, -29
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
	addi s6, s0, 29
	addi s7, s1, -29
	addi s8, s0, 1
	addi s9, zero, 28
	addi s10, zero, 0
	addi s11, zero, 0
270:
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
271:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t2, t2, t1
	sb t2, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 271b
	addi t1, sp, 200
	ld t1, 0(t1)
	ld t1, 32(t1)
	addi s10, s10, 1
	add s11, s11, t1
	sub t1, s11, s9
	srli t1, t1, 63
	bnez t1, 270b
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
	j 261f
260:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
272:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 272b
	addi a0, zero, 0
261:
	j 259f
258:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
273:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 273b
	addi a0, zero, 0
259:
25:
	j 23f
22:
	addi a0, zero, 42
	sub a0, s1, a0
	srli a0, a0, 63
	bnez a0, 274f
	addi a0, zero, 42
	sub a1, s1, a0
	sub a1, a1, t3
	srli a1, a1, 63
	srli a0, t3, 63
	or a0, a0, a1
	bnez a0, 276f
	addi a1, s0, 0
	addi t5, zero, 1024
	addi t0, zero, 0
278:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 278b
	addi a4, t4, 0
	addi a1, s0, 1
	addi a5, zero, 20
279:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 279b
	add a1, s0, s1
	sub a1, a1, t3
	addi a1, a1, -1
	addi t1, zero, 1
	sb t1, 0(a1)
	addi a1, a1, 1
	addi a4, t2, 0
	addi a5, t3, 0
	bnez a5, 280f
	j 281f
280:
282:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 282b
281:
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
283:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 283b
	addi s6, s0, 1
	addi s7, zero, 20
	addi s8, s0, 21
	addi s9, s1, -21
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
	addi s6, s0, 21
	addi s7, s1, -21
	addi s8, s0, 1
	addi s9, zero, 20
	addi s10, zero, 0
	addi s11, zero, 0
286:
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
287:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t2, t2, t1
	sb t2, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 287b
	addi t1, sp, 200
	ld t1, 0(t1)
	ld t1, 32(t1)
	addi s10, s10, 1
	add s11, s11, t1
	sub t1, s11, s9
	srli t1, t1, 63
	bnez t1, 286b
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
	j 277f
276:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
288:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 288b
	addi a0, zero, 0
277:
	j 275f
274:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
289:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 289b
	addi a0, zero, 0
275:
23:
	j 21f
20:
	addi a0, zero, 34
	sub a0, s1, a0
	srli a0, a0, 63
	bnez a0, 290f
	addi a0, zero, 34
	sub a1, s1, a0
	sub a1, a1, t3
	srli a1, a1, 63
	srli a0, t3, 63
	or a0, a0, a1
	bnez a0, 292f
	addi a1, s0, 0
	addi t5, zero, 1024
	addi t0, zero, 0
294:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 294b
	addi a4, t4, 0
	addi a1, s0, 1
	addi a5, zero, 16
295:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 295b
	add a1, s0, s1
	sub a1, a1, t3
	addi a1, a1, -1
	addi t1, zero, 1
	sb t1, 0(a1)
	addi a1, a1, 1
	addi a4, t2, 0
	addi a5, t3, 0
	bnez a5, 296f
	j 297f
296:
298:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 298b
297:
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
	addi a1, s0, 17
	addi a5, zero, 16
299:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 299b
	addi s6, s0, 1
	addi s7, zero, 16
	addi s8, s0, 17
	addi s9, s1, -17
	addi s10, zero, 0
	addi s11, zero, 0
2100:
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
2101:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t2, t2, t1
	sb t2, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 2101b
	addi t1, sp, 200
	ld t1, 0(t1)
	ld t1, 32(t1)
	addi s10, s10, 1
	add s11, s11, t1
	sub t1, s11, s9
	srli t1, t1, 63
	bnez t1, 2100b
	addi s6, s0, 17
	addi s7, s1, -17
	addi s8, s0, 1
	addi s9, zero, 16
	addi s10, zero, 0
	addi s11, zero, 0
2102:
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
2103:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t2, t2, t1
	sb t2, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 2103b
	addi t1, sp, 200
	ld t1, 0(t1)
	ld t1, 32(t1)
	addi s10, s10, 1
	add s11, s11, t1
	sub t1, s11, s9
	srli t1, t1, 63
	bnez t1, 2102b
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
	j 293f
292:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
2104:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 2104b
	addi a0, zero, 0
293:
	j 291f
290:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
2105:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 2105b
	addi a0, zero, 0
291:
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
