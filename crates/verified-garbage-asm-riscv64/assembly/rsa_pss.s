// The functions of `src/rsa_pss.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_pss_verify_precomputed:
	.option push
	.option arch, +m, +c
	addi t5, sp, 48
	ld t5, 0(t5)
	ld t5, 40(t5)
	addi t4, t5, 0
	beqz t4, 20f
	addi t4, t5, -1
	beqz t4, 22f
	addi t4, t5, -2
	beqz t4, 24f
	addi t4, t5, -3
	beqz t4, 26f
	addi t4, t5, -4
	beqz t4, 28f
	addi t4, t5, -5
	beqz t4, 210f
	addi t4, t5, -6
	beqz t4, 212f
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
	ld s7, 8(t6)
	slli s7, s7, 32
	srli s7, s7, 32
	ld s0, 16(t6)
	addi s1, a1, 0
	addi s2, a4, 0
	ld s6, 0(t6)
	addi s8, a2, 0
	addi s9, a3, 0
	addi s10, a6, 0
	lbu t1, 0(a0)
	srli t2, t1, 1
	srli t3, t2, 1
	or t2, t2, t3
	srli t3, t2, 2
	or t2, t2, t3
	srli t3, t2, 4
	or t2, t2, t3
	addi t3, t2, -1
	srli s3, t3, 63
	addi t3, zero, 0
	sub t3, t3, s3
	addi t4, zero, 255
	and t3, t3, t4
	or s5, t2, t3
	sub s4, s1, s3
	addi s4, s4, -33
	beqz t1, 214f
	sub a0, s1, s3
	addi a0, a0, -34
	srli a0, a0, 63
	bnez a0, 216f
	beqz s7, 218f
	addi a1, zero, 0
	j 219f
218:
	addi a1, s6, 0
219:
	sub a0, s1, s3
	addi a0, a0, -34
	sub a0, a0, a1
	srli a0, a0, 63
	srli a2, a1, 63
	or a0, a0, a2
	bnez a0, 220f
	addi t0, sp, 0
	addi t6, sp, 128
	addi t1, zero, 1024
	slli t1, t1, 3
	add t1, s0, t1
	sd t1, 0(t0)
	ld t1, 24(t6)
	addi t1, t1, -1024
	sd t1, 8(t0)
	addi a0, s0, 0
	addi a1, s1, 0
	ld a2, 32(t6)
	ld a3, 40(t6)
	addi a4, s8, 0
	addi a5, s9, 0
	addi a6, s10, 0
	addi a7, s1, 0
	call {vg_rsa_public_precomputed_checked}
	add a1, s0, s1
	addi a1, a1, -1
	lbu a2, 0(a1)
	addi a3, zero, 188
	xor a2, a2, a3
	add a4, s0, s3
	lbu a3, 0(a4)
	addi a5, zero, 255
	xor a5, a5, s5
	and a3, a3, a5
	or a2, a2, a3
	lbu a3, 0(s0)
	addi a5, zero, 0
	sub a5, a5, s3
	and a3, a3, a5
	or a2, a2, a3
	sb a2, 0(a1)
	sd s5, 1352(s0)
	sd s6, 1360(s0)
	sd s7, 1368(s0)
	add s8, s0, s3
	addi s9, s4, 0
	add s6, s8, s4
	addi s7, zero, 32
	addi s10, zero, 0
	addi s11, zero, 0
222:
	addi a0, s0, 1024
	addi t1, sp, 184
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, zero, 0
	addi a2, s6, 0
	addi a3, s7, 0
	addi t1, sp, 184
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
	addi t1, sp, 184
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, s7, 4
	addi a2, s0, 1280
	addi t1, sp, 184
	ld t1, 0(t1)
	ld t1, 16(t1)
	jalr ra, 0(t1)
	addi a6, sp, 184
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
	addi t1, sp, 184
	ld t1, 0(t1)
	ld t1, 32(t1)
	addi s10, s10, 1
	add s11, s11, t1
	sub t1, s11, s9
	srli t1, t1, 63
	bnez t1, 222b
	ld s5, 1352(s0)
	ld s6, 1360(s0)
	ld s7, 1368(s0)
	add a1, s0, s3
	lbu a2, 0(a1)
	and a2, a2, s5
	sb a2, 0(a1)
	add a1, s0, s3
	addi a2, s4, 0
	addi a3, zero, 0
	addi a4, zero, 0
	addi a4, a4, -1
	addi a5, zero, 0
	addi a6, zero, 0
224:
	lbu a7, 0(a1)
	addi t1, a7, -1
	srli t1, t1, 63
	addi t2, t1, -1
	and t2, t2, a4
	and t3, a3, t2
	or a5, a5, t3
	and t3, a7, t2
	or a6, a6, t3
	addi t3, zero, 0
	sub t3, t3, t1
	and a4, a4, t3
	addi a1, a1, 1
	addi a3, a3, 1
	addi a2, a2, -1
	bnez a2, 224b
	add t1, s0, s1
	addi t1, t1, -1
	lbu s10, 0(t1)
	addi t2, zero, 1
	xor a6, a6, t2
	or s10, s10, a6
	sub s11, s4, a5
	addi s11, s11, -1
	addi s8, a5, 0
	beqz s7, 225f
	j 226f
225:
	xor t1, s11, s6
	or s10, s10, t1
226:
	beqz s7, 227f
	addi a1, s0, 2047
	addi a1, a1, 1
	addi t5, zero, 1024
	slli t5, t5, 1
	addi t0, zero, 0
229:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 229b
	addi a4, s2, 0
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 8
	addi a5, zero, 32
230:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 230b
	add a4, s0, s3
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 40
	addi a5, s4, 0
231:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 231b
	addi s8, s8, 1
	addi s9, zero, 1
	addi s5, zero, 10
232:
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 40
	add a2, a1, s9
	addi a3, zero, 1
	and a3, s8, a3
	addi a4, zero, 0
	sub a3, a4, a3
	addi a5, s4, 0
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
	addi s5, s5, -1
	bnez s5, 232b
	addi a0, s0, 1024
	addi t1, sp, 176
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi a1, zero, 0
	addi a2, s0, 2047
	addi a2, a2, 1
	addi a3, zero, 40
	addi a0, s0, 1024
	addi t1, sp, 176
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi s8, zero, 0
	addi s9, s4, 0
234:
	addi a4, s0, 1024
	addi a1, s0, 1376
	addi a5, zero, 192
235:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 235b
	addi a1, s8, 40
	addi a0, s0, 1024
	addi a2, s0, 1280
	addi t1, sp, 176
	ld t1, 0(t1)
	ld t1, 16(t1)
	jalr ra, 0(t1)
	xor t3, s8, s11
	addi t3, t3, -1
	srli t3, t3, 63
	addi t4, zero, 0
	sub t3, t4, t3
	addi a1, s0, 1280
	addi a2, s0, 1568
	addi a3, zero, 32
236:
	lbu t1, 0(a1)
	lbu t2, 0(a2)
	xor t1, t1, t2
	and t1, t1, t3
	xor t2, t2, t1
	sb t2, 0(a2)
	addi a1, a1, 1
	addi a2, a2, 1
	addi a3, a3, -1
	bnez a3, 236b
	addi a4, s0, 1376
	addi a1, s0, 1024
	addi a5, zero, 192
237:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 237b
	addi a1, s8, 40
	addi a2, s0, 2047
	addi a2, a2, 1
	addi a2, a2, 40
	add a2, a2, s8
	addi a3, zero, 1
	addi a0, s0, 1024
	addi t1, sp, 176
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi s8, s8, 1
	addi s9, s9, -1
	bnez s9, 234b
	add a1, s0, s3
	add a1, a1, s4
	addi a2, s0, 1568
	addi a3, zero, 32
238:
	lbu t1, 0(a1)
	lbu t2, 0(a2)
	xor t1, t1, t2
	or s10, s10, t1
	addi a1, a1, 1
	addi a2, a2, 1
	addi a3, a3, -1
	bnez a3, 238b
	addi a0, s10, -1
	srli a0, a0, 63
	j 228f
227:
	addi a1, s0, 2047
	addi a1, a1, 1
	addi t5, zero, 8
	addi t0, zero, 0
239:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 239b
	addi a4, s2, 0
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 8
	addi a5, zero, 32
240:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 240b
	add a4, s0, s3
	add a4, a4, s4
	sub a4, a4, s6
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 40
	addi a5, s6, 0
	bnez a5, 241f
	j 242f
241:
243:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 243b
242:
	addi a0, s0, 1024
	addi t1, sp, 176
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi t2, s6, 40
	addi t3, t2, 16
	srli t3, t3, 7
	addi t3, t3, 1
	slli t3, t3, 7
	addi a1, s0, 2047
	addi a1, a1, 1
	add a1, a1, t2
	sub t5, t3, t2
	addi t0, zero, 0
244:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 244b
	addi a1, s0, 2047
	addi a1, a1, 1
	add a1, a1, t2
	addi t1, zero, 128
	sb t1, 0(a1)
	addi a1, s0, 2047
	addi a1, a1, 1
	add a1, a1, t3
	addi a1, a1, -8
	slli t1, t2, 3
	srli t4, t1, 56
	sb t4, 0(a1)
	srli t4, t1, 48
	sb t4, 1(a1)
	srli t4, t1, 40
	sb t4, 2(a1)
	srli t4, t1, 32
	sb t4, 3(a1)
	srli t4, t1, 24
	sb t4, 4(a1)
	srli t4, t1, 16
	sb t4, 5(a1)
	srli t4, t1, 8
	sb t4, 6(a1)
	srli t4, t1, 0
	sb t4, 7(a1)
	addi a0, s0, 1024
	addi a1, s0, 2047
	addi a1, a1, 1
	srli a2, t3, 7
	addi a3, s0, 1664
	addi t1, sp, 176
	ld t1, 0(t1)
	ld t1, 24(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, s0, 1280
	addi t1, sp, 176
	ld t1, 0(t1)
	ld t1, 32(t1)
	jalr ra, 0(t1)
	add a1, s0, s3
	add a1, a1, s4
	addi a2, s0, 1280
	addi a3, zero, 32
245:
	lbu t1, 0(a1)
	lbu t2, 0(a2)
	xor t1, t1, t2
	or s10, s10, t1
	addi a1, a1, 1
	addi a2, a2, 1
	addi a3, a3, -1
	bnez a3, 245b
	addi a0, s10, -1
	srli a0, a0, 63
228:
	j 221f
220:
	addi a0, zero, 0
221:
	j 217f
216:
	addi a0, zero, 0
217:
	j 215f
214:
	addi a0, zero, 0
215:
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
	j 213f
212:
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
	ld s7, 8(t6)
	slli s7, s7, 32
	srli s7, s7, 32
	ld s0, 16(t6)
	addi s1, a1, 0
	addi s2, a4, 0
	ld s6, 0(t6)
	addi s8, a2, 0
	addi s9, a3, 0
	addi s10, a6, 0
	lbu t1, 0(a0)
	srli t2, t1, 1
	srli t3, t2, 1
	or t2, t2, t3
	srli t3, t2, 2
	or t2, t2, t3
	srli t3, t2, 4
	or t2, t2, t3
	addi t3, t2, -1
	srli s3, t3, 63
	addi t3, zero, 0
	sub t3, t3, s3
	addi t4, zero, 255
	and t3, t3, t4
	or s5, t2, t3
	sub s4, s1, s3
	addi s4, s4, -29
	beqz t1, 246f
	sub a0, s1, s3
	addi a0, a0, -30
	srli a0, a0, 63
	bnez a0, 248f
	beqz s7, 250f
	addi a1, zero, 0
	j 251f
250:
	addi a1, s6, 0
251:
	sub a0, s1, s3
	addi a0, a0, -30
	sub a0, a0, a1
	srli a0, a0, 63
	srli a2, a1, 63
	or a0, a0, a2
	bnez a0, 252f
	addi t0, sp, 0
	addi t6, sp, 128
	addi t1, zero, 1024
	slli t1, t1, 3
	add t1, s0, t1
	sd t1, 0(t0)
	ld t1, 24(t6)
	addi t1, t1, -1024
	sd t1, 8(t0)
	addi a0, s0, 0
	addi a1, s1, 0
	ld a2, 32(t6)
	ld a3, 40(t6)
	addi a4, s8, 0
	addi a5, s9, 0
	addi a6, s10, 0
	addi a7, s1, 0
	call {vg_rsa_public_precomputed_checked}
	add a1, s0, s1
	addi a1, a1, -1
	lbu a2, 0(a1)
	addi a3, zero, 188
	xor a2, a2, a3
	add a4, s0, s3
	lbu a3, 0(a4)
	addi a5, zero, 255
	xor a5, a5, s5
	and a3, a3, a5
	or a2, a2, a3
	lbu a3, 0(s0)
	addi a5, zero, 0
	sub a5, a5, s3
	and a3, a3, a5
	or a2, a2, a3
	sb a2, 0(a1)
	sd s5, 1352(s0)
	sd s6, 1360(s0)
	sd s7, 1368(s0)
	add s8, s0, s3
	addi s9, s4, 0
	add s6, s8, s4
	addi s7, zero, 28
	addi s10, zero, 0
	addi s11, zero, 0
254:
	addi a0, s0, 1024
	addi t1, sp, 184
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, zero, 0
	addi a2, s6, 0
	addi a3, s7, 0
	addi t1, sp, 184
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
	addi t1, sp, 184
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, s7, 4
	addi a2, s0, 1280
	addi t1, sp, 184
	ld t1, 0(t1)
	ld t1, 16(t1)
	jalr ra, 0(t1)
	addi a6, sp, 184
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
	addi t1, sp, 184
	ld t1, 0(t1)
	ld t1, 32(t1)
	addi s10, s10, 1
	add s11, s11, t1
	sub t1, s11, s9
	srli t1, t1, 63
	bnez t1, 254b
	ld s5, 1352(s0)
	ld s6, 1360(s0)
	ld s7, 1368(s0)
	add a1, s0, s3
	lbu a2, 0(a1)
	and a2, a2, s5
	sb a2, 0(a1)
	add a1, s0, s3
	addi a2, s4, 0
	addi a3, zero, 0
	addi a4, zero, 0
	addi a4, a4, -1
	addi a5, zero, 0
	addi a6, zero, 0
256:
	lbu a7, 0(a1)
	addi t1, a7, -1
	srli t1, t1, 63
	addi t2, t1, -1
	and t2, t2, a4
	and t3, a3, t2
	or a5, a5, t3
	and t3, a7, t2
	or a6, a6, t3
	addi t3, zero, 0
	sub t3, t3, t1
	and a4, a4, t3
	addi a1, a1, 1
	addi a3, a3, 1
	addi a2, a2, -1
	bnez a2, 256b
	add t1, s0, s1
	addi t1, t1, -1
	lbu s10, 0(t1)
	addi t2, zero, 1
	xor a6, a6, t2
	or s10, s10, a6
	sub s11, s4, a5
	addi s11, s11, -1
	addi s8, a5, 0
	beqz s7, 257f
	j 258f
257:
	xor t1, s11, s6
	or s10, s10, t1
258:
	beqz s7, 259f
	addi a1, s0, 2047
	addi a1, a1, 1
	addi t5, zero, 1024
	slli t5, t5, 1
	addi t0, zero, 0
261:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 261b
	addi a4, s2, 0
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 8
	addi a5, zero, 28
262:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 262b
	add a4, s0, s3
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 36
	addi a5, s4, 0
263:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 263b
	addi s8, s8, 1
	addi s9, zero, 1
	addi s5, zero, 10
264:
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 36
	add a2, a1, s9
	addi a3, zero, 1
	and a3, s8, a3
	addi a4, zero, 0
	sub a3, a4, a3
	addi a5, s4, 0
265:
	lbu t1, 0(a1)
	lbu t2, 0(a2)
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	sb t1, 0(a1)
	addi a1, a1, 1
	addi a2, a2, 1
	addi a5, a5, -1
	bnez a5, 265b
	srli s8, s8, 1
	add s9, s9, s9
	addi s5, s5, -1
	bnez s5, 264b
	addi a0, s0, 1024
	addi t1, sp, 176
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi a1, zero, 0
	addi a2, s0, 2047
	addi a2, a2, 1
	addi a3, zero, 36
	addi a0, s0, 1024
	addi t1, sp, 176
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi s8, zero, 0
	addi s9, s4, 0
266:
	addi a4, s0, 1024
	addi a1, s0, 1376
	addi a5, zero, 192
267:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 267b
	addi a1, s8, 36
	addi a0, s0, 1024
	addi a2, s0, 1280
	addi t1, sp, 176
	ld t1, 0(t1)
	ld t1, 16(t1)
	jalr ra, 0(t1)
	xor t3, s8, s11
	addi t3, t3, -1
	srli t3, t3, 63
	addi t4, zero, 0
	sub t3, t4, t3
	addi a1, s0, 1280
	addi a2, s0, 1568
	addi a3, zero, 28
268:
	lbu t1, 0(a1)
	lbu t2, 0(a2)
	xor t1, t1, t2
	and t1, t1, t3
	xor t2, t2, t1
	sb t2, 0(a2)
	addi a1, a1, 1
	addi a2, a2, 1
	addi a3, a3, -1
	bnez a3, 268b
	addi a4, s0, 1376
	addi a1, s0, 1024
	addi a5, zero, 192
269:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 269b
	addi a1, s8, 36
	addi a2, s0, 2047
	addi a2, a2, 1
	addi a2, a2, 36
	add a2, a2, s8
	addi a3, zero, 1
	addi a0, s0, 1024
	addi t1, sp, 176
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi s8, s8, 1
	addi s9, s9, -1
	bnez s9, 266b
	add a1, s0, s3
	add a1, a1, s4
	addi a2, s0, 1568
	addi a3, zero, 28
270:
	lbu t1, 0(a1)
	lbu t2, 0(a2)
	xor t1, t1, t2
	or s10, s10, t1
	addi a1, a1, 1
	addi a2, a2, 1
	addi a3, a3, -1
	bnez a3, 270b
	addi a0, s10, -1
	srli a0, a0, 63
	j 260f
259:
	addi a1, s0, 2047
	addi a1, a1, 1
	addi t5, zero, 8
	addi t0, zero, 0
271:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 271b
	addi a4, s2, 0
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 8
	addi a5, zero, 28
272:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 272b
	add a4, s0, s3
	add a4, a4, s4
	sub a4, a4, s6
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 36
	addi a5, s6, 0
	bnez a5, 273f
	j 274f
273:
275:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 275b
274:
	addi a0, s0, 1024
	addi t1, sp, 176
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi t2, s6, 36
	addi t3, t2, 16
	srli t3, t3, 7
	addi t3, t3, 1
	slli t3, t3, 7
	addi a1, s0, 2047
	addi a1, a1, 1
	add a1, a1, t2
	sub t5, t3, t2
	addi t0, zero, 0
276:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 276b
	addi a1, s0, 2047
	addi a1, a1, 1
	add a1, a1, t2
	addi t1, zero, 128
	sb t1, 0(a1)
	addi a1, s0, 2047
	addi a1, a1, 1
	add a1, a1, t3
	addi a1, a1, -8
	slli t1, t2, 3
	srli t4, t1, 56
	sb t4, 0(a1)
	srli t4, t1, 48
	sb t4, 1(a1)
	srli t4, t1, 40
	sb t4, 2(a1)
	srli t4, t1, 32
	sb t4, 3(a1)
	srli t4, t1, 24
	sb t4, 4(a1)
	srli t4, t1, 16
	sb t4, 5(a1)
	srli t4, t1, 8
	sb t4, 6(a1)
	srli t4, t1, 0
	sb t4, 7(a1)
	addi a0, s0, 1024
	addi a1, s0, 2047
	addi a1, a1, 1
	srli a2, t3, 7
	addi a3, s0, 1664
	addi t1, sp, 176
	ld t1, 0(t1)
	ld t1, 24(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, s0, 1280
	addi t1, sp, 176
	ld t1, 0(t1)
	ld t1, 32(t1)
	jalr ra, 0(t1)
	add a1, s0, s3
	add a1, a1, s4
	addi a2, s0, 1280
	addi a3, zero, 28
277:
	lbu t1, 0(a1)
	lbu t2, 0(a2)
	xor t1, t1, t2
	or s10, s10, t1
	addi a1, a1, 1
	addi a2, a2, 1
	addi a3, a3, -1
	bnez a3, 277b
	addi a0, s10, -1
	srli a0, a0, 63
260:
	j 253f
252:
	addi a0, zero, 0
253:
	j 249f
248:
	addi a0, zero, 0
249:
	j 247f
246:
	addi a0, zero, 0
247:
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
213:
	j 211f
210:
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
	ld s7, 8(t6)
	slli s7, s7, 32
	srli s7, s7, 32
	ld s0, 16(t6)
	addi s1, a1, 0
	addi s2, a4, 0
	ld s6, 0(t6)
	addi s8, a2, 0
	addi s9, a3, 0
	addi s10, a6, 0
	lbu t1, 0(a0)
	srli t2, t1, 1
	srli t3, t2, 1
	or t2, t2, t3
	srli t3, t2, 2
	or t2, t2, t3
	srli t3, t2, 4
	or t2, t2, t3
	addi t3, t2, -1
	srli s3, t3, 63
	addi t3, zero, 0
	sub t3, t3, s3
	addi t4, zero, 255
	and t3, t3, t4
	or s5, t2, t3
	sub s4, s1, s3
	addi s4, s4, -65
	beqz t1, 278f
	sub a0, s1, s3
	addi a0, a0, -66
	srli a0, a0, 63
	bnez a0, 280f
	beqz s7, 282f
	addi a1, zero, 0
	j 283f
282:
	addi a1, s6, 0
283:
	sub a0, s1, s3
	addi a0, a0, -66
	sub a0, a0, a1
	srli a0, a0, 63
	srli a2, a1, 63
	or a0, a0, a2
	bnez a0, 284f
	addi t0, sp, 0
	addi t6, sp, 128
	addi t1, zero, 1024
	slli t1, t1, 3
	add t1, s0, t1
	sd t1, 0(t0)
	ld t1, 24(t6)
	addi t1, t1, -1024
	sd t1, 8(t0)
	addi a0, s0, 0
	addi a1, s1, 0
	ld a2, 32(t6)
	ld a3, 40(t6)
	addi a4, s8, 0
	addi a5, s9, 0
	addi a6, s10, 0
	addi a7, s1, 0
	call {vg_rsa_public_precomputed_checked}
	add a1, s0, s1
	addi a1, a1, -1
	lbu a2, 0(a1)
	addi a3, zero, 188
	xor a2, a2, a3
	add a4, s0, s3
	lbu a3, 0(a4)
	addi a5, zero, 255
	xor a5, a5, s5
	and a3, a3, a5
	or a2, a2, a3
	lbu a3, 0(s0)
	addi a5, zero, 0
	sub a5, a5, s3
	and a3, a3, a5
	or a2, a2, a3
	sb a2, 0(a1)
	sd s5, 1352(s0)
	sd s6, 1360(s0)
	sd s7, 1368(s0)
	add s8, s0, s3
	addi s9, s4, 0
	add s6, s8, s4
	addi s7, zero, 64
	addi s10, zero, 0
	addi s11, zero, 0
286:
	addi a0, s0, 1024
	addi t1, sp, 184
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, zero, 0
	addi a2, s6, 0
	addi a3, s7, 0
	addi t1, sp, 184
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
	addi t1, sp, 184
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, s7, 4
	addi a2, s0, 1280
	addi t1, sp, 184
	ld t1, 0(t1)
	ld t1, 16(t1)
	jalr ra, 0(t1)
	addi a6, sp, 184
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
	addi t1, sp, 184
	ld t1, 0(t1)
	ld t1, 32(t1)
	addi s10, s10, 1
	add s11, s11, t1
	sub t1, s11, s9
	srli t1, t1, 63
	bnez t1, 286b
	ld s5, 1352(s0)
	ld s6, 1360(s0)
	ld s7, 1368(s0)
	add a1, s0, s3
	lbu a2, 0(a1)
	and a2, a2, s5
	sb a2, 0(a1)
	add a1, s0, s3
	addi a2, s4, 0
	addi a3, zero, 0
	addi a4, zero, 0
	addi a4, a4, -1
	addi a5, zero, 0
	addi a6, zero, 0
288:
	lbu a7, 0(a1)
	addi t1, a7, -1
	srli t1, t1, 63
	addi t2, t1, -1
	and t2, t2, a4
	and t3, a3, t2
	or a5, a5, t3
	and t3, a7, t2
	or a6, a6, t3
	addi t3, zero, 0
	sub t3, t3, t1
	and a4, a4, t3
	addi a1, a1, 1
	addi a3, a3, 1
	addi a2, a2, -1
	bnez a2, 288b
	add t1, s0, s1
	addi t1, t1, -1
	lbu s10, 0(t1)
	addi t2, zero, 1
	xor a6, a6, t2
	or s10, s10, a6
	sub s11, s4, a5
	addi s11, s11, -1
	addi s8, a5, 0
	beqz s7, 289f
	j 290f
289:
	xor t1, s11, s6
	or s10, s10, t1
290:
	beqz s7, 291f
	addi a1, s0, 2047
	addi a1, a1, 1
	addi t5, zero, 1024
	slli t5, t5, 1
	addi t0, zero, 0
293:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 293b
	addi a4, s2, 0
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 8
	addi a5, zero, 64
294:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 294b
	add a4, s0, s3
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 72
	addi a5, s4, 0
295:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 295b
	addi s8, s8, 1
	addi s9, zero, 1
	addi s5, zero, 10
296:
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 72
	add a2, a1, s9
	addi a3, zero, 1
	and a3, s8, a3
	addi a4, zero, 0
	sub a3, a4, a3
	addi a5, s4, 0
297:
	lbu t1, 0(a1)
	lbu t2, 0(a2)
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	sb t1, 0(a1)
	addi a1, a1, 1
	addi a2, a2, 1
	addi a5, a5, -1
	bnez a5, 297b
	srli s8, s8, 1
	add s9, s9, s9
	addi s5, s5, -1
	bnez s5, 296b
	addi a0, s0, 1024
	addi t1, sp, 176
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi a1, zero, 0
	addi a2, s0, 2047
	addi a2, a2, 1
	addi a3, zero, 72
	addi a0, s0, 1024
	addi t1, sp, 176
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi s8, zero, 0
	addi s9, s4, 0
298:
	addi a4, s0, 1024
	addi a1, s0, 1376
	addi a5, zero, 192
299:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 299b
	addi a1, s8, 72
	addi a0, s0, 1024
	addi a2, s0, 1280
	addi t1, sp, 176
	ld t1, 0(t1)
	ld t1, 16(t1)
	jalr ra, 0(t1)
	xor t3, s8, s11
	addi t3, t3, -1
	srli t3, t3, 63
	addi t4, zero, 0
	sub t3, t4, t3
	addi a1, s0, 1280
	addi a2, s0, 1568
	addi a3, zero, 64
2100:
	lbu t1, 0(a1)
	lbu t2, 0(a2)
	xor t1, t1, t2
	and t1, t1, t3
	xor t2, t2, t1
	sb t2, 0(a2)
	addi a1, a1, 1
	addi a2, a2, 1
	addi a3, a3, -1
	bnez a3, 2100b
	addi a4, s0, 1376
	addi a1, s0, 1024
	addi a5, zero, 192
2101:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 2101b
	addi a1, s8, 72
	addi a2, s0, 2047
	addi a2, a2, 1
	addi a2, a2, 72
	add a2, a2, s8
	addi a3, zero, 1
	addi a0, s0, 1024
	addi t1, sp, 176
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi s8, s8, 1
	addi s9, s9, -1
	bnez s9, 298b
	add a1, s0, s3
	add a1, a1, s4
	addi a2, s0, 1568
	addi a3, zero, 64
2102:
	lbu t1, 0(a1)
	lbu t2, 0(a2)
	xor t1, t1, t2
	or s10, s10, t1
	addi a1, a1, 1
	addi a2, a2, 1
	addi a3, a3, -1
	bnez a3, 2102b
	addi a0, s10, -1
	srli a0, a0, 63
	j 292f
291:
	addi a1, s0, 2047
	addi a1, a1, 1
	addi t5, zero, 8
	addi t0, zero, 0
2103:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 2103b
	addi a4, s2, 0
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 8
	addi a5, zero, 64
2104:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 2104b
	add a4, s0, s3
	add a4, a4, s4
	sub a4, a4, s6
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 72
	addi a5, s6, 0
	bnez a5, 2105f
	j 2106f
2105:
2107:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 2107b
2106:
	addi a0, s0, 1024
	addi t1, sp, 176
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi t2, s6, 72
	addi t3, t2, 16
	srli t3, t3, 7
	addi t3, t3, 1
	slli t3, t3, 7
	addi a1, s0, 2047
	addi a1, a1, 1
	add a1, a1, t2
	sub t5, t3, t2
	addi t0, zero, 0
2108:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 2108b
	addi a1, s0, 2047
	addi a1, a1, 1
	add a1, a1, t2
	addi t1, zero, 128
	sb t1, 0(a1)
	addi a1, s0, 2047
	addi a1, a1, 1
	add a1, a1, t3
	addi a1, a1, -8
	slli t1, t2, 3
	srli t4, t1, 56
	sb t4, 0(a1)
	srli t4, t1, 48
	sb t4, 1(a1)
	srli t4, t1, 40
	sb t4, 2(a1)
	srli t4, t1, 32
	sb t4, 3(a1)
	srli t4, t1, 24
	sb t4, 4(a1)
	srli t4, t1, 16
	sb t4, 5(a1)
	srli t4, t1, 8
	sb t4, 6(a1)
	srli t4, t1, 0
	sb t4, 7(a1)
	addi a0, s0, 1024
	addi a1, s0, 2047
	addi a1, a1, 1
	srli a2, t3, 7
	addi a3, s0, 1664
	addi t1, sp, 176
	ld t1, 0(t1)
	ld t1, 24(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, s0, 1280
	addi t1, sp, 176
	ld t1, 0(t1)
	ld t1, 32(t1)
	jalr ra, 0(t1)
	add a1, s0, s3
	add a1, a1, s4
	addi a2, s0, 1280
	addi a3, zero, 64
2109:
	lbu t1, 0(a1)
	lbu t2, 0(a2)
	xor t1, t1, t2
	or s10, s10, t1
	addi a1, a1, 1
	addi a2, a2, 1
	addi a3, a3, -1
	bnez a3, 2109b
	addi a0, s10, -1
	srli a0, a0, 63
292:
	j 285f
284:
	addi a0, zero, 0
285:
	j 281f
280:
	addi a0, zero, 0
281:
	j 279f
278:
	addi a0, zero, 0
279:
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
211:
	j 29f
28:
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
	ld s7, 8(t6)
	slli s7, s7, 32
	srli s7, s7, 32
	ld s0, 16(t6)
	addi s1, a1, 0
	addi s2, a4, 0
	ld s6, 0(t6)
	addi s8, a2, 0
	addi s9, a3, 0
	addi s10, a6, 0
	lbu t1, 0(a0)
	srli t2, t1, 1
	srli t3, t2, 1
	or t2, t2, t3
	srli t3, t2, 2
	or t2, t2, t3
	srli t3, t2, 4
	or t2, t2, t3
	addi t3, t2, -1
	srli s3, t3, 63
	addi t3, zero, 0
	sub t3, t3, s3
	addi t4, zero, 255
	and t3, t3, t4
	or s5, t2, t3
	sub s4, s1, s3
	addi s4, s4, -49
	beqz t1, 2110f
	sub a0, s1, s3
	addi a0, a0, -50
	srli a0, a0, 63
	bnez a0, 2112f
	beqz s7, 2114f
	addi a1, zero, 0
	j 2115f
2114:
	addi a1, s6, 0
2115:
	sub a0, s1, s3
	addi a0, a0, -50
	sub a0, a0, a1
	srli a0, a0, 63
	srli a2, a1, 63
	or a0, a0, a2
	bnez a0, 2116f
	addi t0, sp, 0
	addi t6, sp, 128
	addi t1, zero, 1024
	slli t1, t1, 3
	add t1, s0, t1
	sd t1, 0(t0)
	ld t1, 24(t6)
	addi t1, t1, -1024
	sd t1, 8(t0)
	addi a0, s0, 0
	addi a1, s1, 0
	ld a2, 32(t6)
	ld a3, 40(t6)
	addi a4, s8, 0
	addi a5, s9, 0
	addi a6, s10, 0
	addi a7, s1, 0
	call {vg_rsa_public_precomputed_checked}
	add a1, s0, s1
	addi a1, a1, -1
	lbu a2, 0(a1)
	addi a3, zero, 188
	xor a2, a2, a3
	add a4, s0, s3
	lbu a3, 0(a4)
	addi a5, zero, 255
	xor a5, a5, s5
	and a3, a3, a5
	or a2, a2, a3
	lbu a3, 0(s0)
	addi a5, zero, 0
	sub a5, a5, s3
	and a3, a3, a5
	or a2, a2, a3
	sb a2, 0(a1)
	sd s5, 1352(s0)
	sd s6, 1360(s0)
	sd s7, 1368(s0)
	add s8, s0, s3
	addi s9, s4, 0
	add s6, s8, s4
	addi s7, zero, 48
	addi s10, zero, 0
	addi s11, zero, 0
2118:
	addi a0, s0, 1024
	addi t1, sp, 184
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, zero, 0
	addi a2, s6, 0
	addi a3, s7, 0
	addi t1, sp, 184
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
	addi t1, sp, 184
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, s7, 4
	addi a2, s0, 1280
	addi t1, sp, 184
	ld t1, 0(t1)
	ld t1, 16(t1)
	jalr ra, 0(t1)
	addi a6, sp, 184
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
2119:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t2, t2, t1
	sb t2, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 2119b
	addi t1, sp, 184
	ld t1, 0(t1)
	ld t1, 32(t1)
	addi s10, s10, 1
	add s11, s11, t1
	sub t1, s11, s9
	srli t1, t1, 63
	bnez t1, 2118b
	ld s5, 1352(s0)
	ld s6, 1360(s0)
	ld s7, 1368(s0)
	add a1, s0, s3
	lbu a2, 0(a1)
	and a2, a2, s5
	sb a2, 0(a1)
	add a1, s0, s3
	addi a2, s4, 0
	addi a3, zero, 0
	addi a4, zero, 0
	addi a4, a4, -1
	addi a5, zero, 0
	addi a6, zero, 0
2120:
	lbu a7, 0(a1)
	addi t1, a7, -1
	srli t1, t1, 63
	addi t2, t1, -1
	and t2, t2, a4
	and t3, a3, t2
	or a5, a5, t3
	and t3, a7, t2
	or a6, a6, t3
	addi t3, zero, 0
	sub t3, t3, t1
	and a4, a4, t3
	addi a1, a1, 1
	addi a3, a3, 1
	addi a2, a2, -1
	bnez a2, 2120b
	add t1, s0, s1
	addi t1, t1, -1
	lbu s10, 0(t1)
	addi t2, zero, 1
	xor a6, a6, t2
	or s10, s10, a6
	sub s11, s4, a5
	addi s11, s11, -1
	addi s8, a5, 0
	beqz s7, 2121f
	j 2122f
2121:
	xor t1, s11, s6
	or s10, s10, t1
2122:
	beqz s7, 2123f
	addi a1, s0, 2047
	addi a1, a1, 1
	addi t5, zero, 1024
	slli t5, t5, 1
	addi t0, zero, 0
2125:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 2125b
	addi a4, s2, 0
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 8
	addi a5, zero, 48
2126:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 2126b
	add a4, s0, s3
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 56
	addi a5, s4, 0
2127:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 2127b
	addi s8, s8, 1
	addi s9, zero, 1
	addi s5, zero, 10
2128:
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 56
	add a2, a1, s9
	addi a3, zero, 1
	and a3, s8, a3
	addi a4, zero, 0
	sub a3, a4, a3
	addi a5, s4, 0
2129:
	lbu t1, 0(a1)
	lbu t2, 0(a2)
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	sb t1, 0(a1)
	addi a1, a1, 1
	addi a2, a2, 1
	addi a5, a5, -1
	bnez a5, 2129b
	srli s8, s8, 1
	add s9, s9, s9
	addi s5, s5, -1
	bnez s5, 2128b
	addi a0, s0, 1024
	addi t1, sp, 176
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi a1, zero, 0
	addi a2, s0, 2047
	addi a2, a2, 1
	addi a3, zero, 56
	addi a0, s0, 1024
	addi t1, sp, 176
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi s8, zero, 0
	addi s9, s4, 0
2130:
	addi a4, s0, 1024
	addi a1, s0, 1376
	addi a5, zero, 192
2131:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 2131b
	addi a1, s8, 56
	addi a0, s0, 1024
	addi a2, s0, 1280
	addi t1, sp, 176
	ld t1, 0(t1)
	ld t1, 16(t1)
	jalr ra, 0(t1)
	xor t3, s8, s11
	addi t3, t3, -1
	srli t3, t3, 63
	addi t4, zero, 0
	sub t3, t4, t3
	addi a1, s0, 1280
	addi a2, s0, 1568
	addi a3, zero, 48
2132:
	lbu t1, 0(a1)
	lbu t2, 0(a2)
	xor t1, t1, t2
	and t1, t1, t3
	xor t2, t2, t1
	sb t2, 0(a2)
	addi a1, a1, 1
	addi a2, a2, 1
	addi a3, a3, -1
	bnez a3, 2132b
	addi a4, s0, 1376
	addi a1, s0, 1024
	addi a5, zero, 192
2133:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 2133b
	addi a1, s8, 56
	addi a2, s0, 2047
	addi a2, a2, 1
	addi a2, a2, 56
	add a2, a2, s8
	addi a3, zero, 1
	addi a0, s0, 1024
	addi t1, sp, 176
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi s8, s8, 1
	addi s9, s9, -1
	bnez s9, 2130b
	add a1, s0, s3
	add a1, a1, s4
	addi a2, s0, 1568
	addi a3, zero, 48
2134:
	lbu t1, 0(a1)
	lbu t2, 0(a2)
	xor t1, t1, t2
	or s10, s10, t1
	addi a1, a1, 1
	addi a2, a2, 1
	addi a3, a3, -1
	bnez a3, 2134b
	addi a0, s10, -1
	srli a0, a0, 63
	j 2124f
2123:
	addi a1, s0, 2047
	addi a1, a1, 1
	addi t5, zero, 8
	addi t0, zero, 0
2135:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 2135b
	addi a4, s2, 0
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 8
	addi a5, zero, 48
2136:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 2136b
	add a4, s0, s3
	add a4, a4, s4
	sub a4, a4, s6
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 56
	addi a5, s6, 0
	bnez a5, 2137f
	j 2138f
2137:
2139:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 2139b
2138:
	addi a0, s0, 1024
	addi t1, sp, 176
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi t2, s6, 56
	addi t3, t2, 16
	srli t3, t3, 7
	addi t3, t3, 1
	slli t3, t3, 7
	addi a1, s0, 2047
	addi a1, a1, 1
	add a1, a1, t2
	sub t5, t3, t2
	addi t0, zero, 0
2140:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 2140b
	addi a1, s0, 2047
	addi a1, a1, 1
	add a1, a1, t2
	addi t1, zero, 128
	sb t1, 0(a1)
	addi a1, s0, 2047
	addi a1, a1, 1
	add a1, a1, t3
	addi a1, a1, -8
	slli t1, t2, 3
	srli t4, t1, 56
	sb t4, 0(a1)
	srli t4, t1, 48
	sb t4, 1(a1)
	srli t4, t1, 40
	sb t4, 2(a1)
	srli t4, t1, 32
	sb t4, 3(a1)
	srli t4, t1, 24
	sb t4, 4(a1)
	srli t4, t1, 16
	sb t4, 5(a1)
	srli t4, t1, 8
	sb t4, 6(a1)
	srli t4, t1, 0
	sb t4, 7(a1)
	addi a0, s0, 1024
	addi a1, s0, 2047
	addi a1, a1, 1
	srli a2, t3, 7
	addi a3, s0, 1664
	addi t1, sp, 176
	ld t1, 0(t1)
	ld t1, 24(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, s0, 1280
	addi t1, sp, 176
	ld t1, 0(t1)
	ld t1, 32(t1)
	jalr ra, 0(t1)
	add a1, s0, s3
	add a1, a1, s4
	addi a2, s0, 1280
	addi a3, zero, 48
2141:
	lbu t1, 0(a1)
	lbu t2, 0(a2)
	xor t1, t1, t2
	or s10, s10, t1
	addi a1, a1, 1
	addi a2, a2, 1
	addi a3, a3, -1
	bnez a3, 2141b
	addi a0, s10, -1
	srli a0, a0, 63
2124:
	j 2117f
2116:
	addi a0, zero, 0
2117:
	j 2113f
2112:
	addi a0, zero, 0
2113:
	j 2111f
2110:
	addi a0, zero, 0
2111:
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
29:
	j 27f
26:
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
	ld s7, 8(t6)
	slli s7, s7, 32
	srli s7, s7, 32
	ld s0, 16(t6)
	addi s1, a1, 0
	addi s2, a4, 0
	ld s6, 0(t6)
	addi s8, a2, 0
	addi s9, a3, 0
	addi s10, a6, 0
	lbu t1, 0(a0)
	srli t2, t1, 1
	srli t3, t2, 1
	or t2, t2, t3
	srli t3, t2, 2
	or t2, t2, t3
	srli t3, t2, 4
	or t2, t2, t3
	addi t3, t2, -1
	srli s3, t3, 63
	addi t3, zero, 0
	sub t3, t3, s3
	addi t4, zero, 255
	and t3, t3, t4
	or s5, t2, t3
	sub s4, s1, s3
	addi s4, s4, -33
	beqz t1, 2142f
	sub a0, s1, s3
	addi a0, a0, -34
	srli a0, a0, 63
	bnez a0, 2144f
	beqz s7, 2146f
	addi a1, zero, 0
	j 2147f
2146:
	addi a1, s6, 0
2147:
	sub a0, s1, s3
	addi a0, a0, -34
	sub a0, a0, a1
	srli a0, a0, 63
	srli a2, a1, 63
	or a0, a0, a2
	bnez a0, 2148f
	addi t0, sp, 0
	addi t6, sp, 128
	addi t1, zero, 1024
	slli t1, t1, 3
	add t1, s0, t1
	sd t1, 0(t0)
	ld t1, 24(t6)
	addi t1, t1, -1024
	sd t1, 8(t0)
	addi a0, s0, 0
	addi a1, s1, 0
	ld a2, 32(t6)
	ld a3, 40(t6)
	addi a4, s8, 0
	addi a5, s9, 0
	addi a6, s10, 0
	addi a7, s1, 0
	call {vg_rsa_public_precomputed_checked}
	add a1, s0, s1
	addi a1, a1, -1
	lbu a2, 0(a1)
	addi a3, zero, 188
	xor a2, a2, a3
	add a4, s0, s3
	lbu a3, 0(a4)
	addi a5, zero, 255
	xor a5, a5, s5
	and a3, a3, a5
	or a2, a2, a3
	lbu a3, 0(s0)
	addi a5, zero, 0
	sub a5, a5, s3
	and a3, a3, a5
	or a2, a2, a3
	sb a2, 0(a1)
	sd s5, 1352(s0)
	sd s6, 1360(s0)
	sd s7, 1368(s0)
	add s8, s0, s3
	addi s9, s4, 0
	add s6, s8, s4
	addi s7, zero, 32
	addi s10, zero, 0
	addi s11, zero, 0
2150:
	addi a0, s0, 1024
	addi t1, sp, 184
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, zero, 0
	addi a2, s6, 0
	addi a3, s7, 0
	addi t1, sp, 184
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
	addi t1, sp, 184
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, s7, 4
	addi a2, s0, 1280
	addi t1, sp, 184
	ld t1, 0(t1)
	ld t1, 16(t1)
	jalr ra, 0(t1)
	addi a6, sp, 184
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
2151:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t2, t2, t1
	sb t2, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 2151b
	addi t1, sp, 184
	ld t1, 0(t1)
	ld t1, 32(t1)
	addi s10, s10, 1
	add s11, s11, t1
	sub t1, s11, s9
	srli t1, t1, 63
	bnez t1, 2150b
	ld s5, 1352(s0)
	ld s6, 1360(s0)
	ld s7, 1368(s0)
	add a1, s0, s3
	lbu a2, 0(a1)
	and a2, a2, s5
	sb a2, 0(a1)
	add a1, s0, s3
	addi a2, s4, 0
	addi a3, zero, 0
	addi a4, zero, 0
	addi a4, a4, -1
	addi a5, zero, 0
	addi a6, zero, 0
2152:
	lbu a7, 0(a1)
	addi t1, a7, -1
	srli t1, t1, 63
	addi t2, t1, -1
	and t2, t2, a4
	and t3, a3, t2
	or a5, a5, t3
	and t3, a7, t2
	or a6, a6, t3
	addi t3, zero, 0
	sub t3, t3, t1
	and a4, a4, t3
	addi a1, a1, 1
	addi a3, a3, 1
	addi a2, a2, -1
	bnez a2, 2152b
	add t1, s0, s1
	addi t1, t1, -1
	lbu s10, 0(t1)
	addi t2, zero, 1
	xor a6, a6, t2
	or s10, s10, a6
	sub s11, s4, a5
	addi s11, s11, -1
	addi s8, a5, 0
	beqz s7, 2153f
	j 2154f
2153:
	xor t1, s11, s6
	or s10, s10, t1
2154:
	beqz s7, 2155f
	addi a1, s0, 2047
	addi a1, a1, 1
	addi t5, zero, 1024
	slli t5, t5, 1
	addi t0, zero, 0
2157:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 2157b
	addi a4, s2, 0
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 8
	addi a5, zero, 32
2158:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 2158b
	add a4, s0, s3
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 40
	addi a5, s4, 0
2159:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 2159b
	addi s8, s8, 1
	addi s9, zero, 1
	addi s5, zero, 10
2160:
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 40
	add a2, a1, s9
	addi a3, zero, 1
	and a3, s8, a3
	addi a4, zero, 0
	sub a3, a4, a3
	addi a5, s4, 0
2161:
	lbu t1, 0(a1)
	lbu t2, 0(a2)
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	sb t1, 0(a1)
	addi a1, a1, 1
	addi a2, a2, 1
	addi a5, a5, -1
	bnez a5, 2161b
	srli s8, s8, 1
	add s9, s9, s9
	addi s5, s5, -1
	bnez s5, 2160b
	addi a0, s0, 1024
	addi t1, sp, 176
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi a1, zero, 0
	addi a2, s0, 2047
	addi a2, a2, 1
	addi a3, zero, 40
	addi a0, s0, 1024
	addi t1, sp, 176
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi s8, zero, 0
	addi s9, s4, 0
2162:
	addi a4, s0, 1024
	addi a1, s0, 1376
	addi a5, zero, 96
2163:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 2163b
	addi a1, s8, 40
	addi a0, s0, 1024
	addi a2, s0, 1280
	addi t1, sp, 176
	ld t1, 0(t1)
	ld t1, 16(t1)
	jalr ra, 0(t1)
	xor t3, s8, s11
	addi t3, t3, -1
	srli t3, t3, 63
	addi t4, zero, 0
	sub t3, t4, t3
	addi a1, s0, 1280
	addi a2, s0, 1568
	addi a3, zero, 32
2164:
	lbu t1, 0(a1)
	lbu t2, 0(a2)
	xor t1, t1, t2
	and t1, t1, t3
	xor t2, t2, t1
	sb t2, 0(a2)
	addi a1, a1, 1
	addi a2, a2, 1
	addi a3, a3, -1
	bnez a3, 2164b
	addi a4, s0, 1376
	addi a1, s0, 1024
	addi a5, zero, 96
2165:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 2165b
	addi a1, s8, 40
	addi a2, s0, 2047
	addi a2, a2, 1
	addi a2, a2, 40
	add a2, a2, s8
	addi a3, zero, 1
	addi a0, s0, 1024
	addi t1, sp, 176
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi s8, s8, 1
	addi s9, s9, -1
	bnez s9, 2162b
	add a1, s0, s3
	add a1, a1, s4
	addi a2, s0, 1568
	addi a3, zero, 32
2166:
	lbu t1, 0(a1)
	lbu t2, 0(a2)
	xor t1, t1, t2
	or s10, s10, t1
	addi a1, a1, 1
	addi a2, a2, 1
	addi a3, a3, -1
	bnez a3, 2166b
	addi a0, s10, -1
	srli a0, a0, 63
	j 2156f
2155:
	addi a1, s0, 2047
	addi a1, a1, 1
	addi t5, zero, 8
	addi t0, zero, 0
2167:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 2167b
	addi a4, s2, 0
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 8
	addi a5, zero, 32
2168:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 2168b
	add a4, s0, s3
	add a4, a4, s4
	sub a4, a4, s6
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 40
	addi a5, s6, 0
	bnez a5, 2169f
	j 2170f
2169:
2171:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 2171b
2170:
	addi a0, s0, 1024
	addi t1, sp, 176
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi t2, s6, 40
	addi t3, t2, 8
	srli t3, t3, 6
	addi t3, t3, 1
	slli t3, t3, 6
	addi a1, s0, 2047
	addi a1, a1, 1
	add a1, a1, t2
	sub t5, t3, t2
	addi t0, zero, 0
2172:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 2172b
	addi a1, s0, 2047
	addi a1, a1, 1
	add a1, a1, t2
	addi t1, zero, 128
	sb t1, 0(a1)
	addi a1, s0, 2047
	addi a1, a1, 1
	add a1, a1, t3
	addi a1, a1, -8
	slli t1, t2, 3
	srli t4, t1, 56
	sb t4, 0(a1)
	srli t4, t1, 48
	sb t4, 1(a1)
	srli t4, t1, 40
	sb t4, 2(a1)
	srli t4, t1, 32
	sb t4, 3(a1)
	srli t4, t1, 24
	sb t4, 4(a1)
	srli t4, t1, 16
	sb t4, 5(a1)
	srli t4, t1, 8
	sb t4, 6(a1)
	srli t4, t1, 0
	sb t4, 7(a1)
	addi a0, s0, 1024
	addi a1, s0, 2047
	addi a1, a1, 1
	srli a2, t3, 6
	addi a3, s0, 1664
	addi t1, sp, 176
	ld t1, 0(t1)
	ld t1, 24(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, s0, 1280
	addi t1, sp, 176
	ld t1, 0(t1)
	ld t1, 32(t1)
	jalr ra, 0(t1)
	add a1, s0, s3
	add a1, a1, s4
	addi a2, s0, 1280
	addi a3, zero, 32
2173:
	lbu t1, 0(a1)
	lbu t2, 0(a2)
	xor t1, t1, t2
	or s10, s10, t1
	addi a1, a1, 1
	addi a2, a2, 1
	addi a3, a3, -1
	bnez a3, 2173b
	addi a0, s10, -1
	srli a0, a0, 63
2156:
	j 2149f
2148:
	addi a0, zero, 0
2149:
	j 2145f
2144:
	addi a0, zero, 0
2145:
	j 2143f
2142:
	addi a0, zero, 0
2143:
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
27:
	j 25f
24:
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
	ld s7, 8(t6)
	slli s7, s7, 32
	srli s7, s7, 32
	ld s0, 16(t6)
	addi s1, a1, 0
	addi s2, a4, 0
	ld s6, 0(t6)
	addi s8, a2, 0
	addi s9, a3, 0
	addi s10, a6, 0
	lbu t1, 0(a0)
	srli t2, t1, 1
	srli t3, t2, 1
	or t2, t2, t3
	srli t3, t2, 2
	or t2, t2, t3
	srli t3, t2, 4
	or t2, t2, t3
	addi t3, t2, -1
	srli s3, t3, 63
	addi t3, zero, 0
	sub t3, t3, s3
	addi t4, zero, 255
	and t3, t3, t4
	or s5, t2, t3
	sub s4, s1, s3
	addi s4, s4, -29
	beqz t1, 2174f
	sub a0, s1, s3
	addi a0, a0, -30
	srli a0, a0, 63
	bnez a0, 2176f
	beqz s7, 2178f
	addi a1, zero, 0
	j 2179f
2178:
	addi a1, s6, 0
2179:
	sub a0, s1, s3
	addi a0, a0, -30
	sub a0, a0, a1
	srli a0, a0, 63
	srli a2, a1, 63
	or a0, a0, a2
	bnez a0, 2180f
	addi t0, sp, 0
	addi t6, sp, 128
	addi t1, zero, 1024
	slli t1, t1, 3
	add t1, s0, t1
	sd t1, 0(t0)
	ld t1, 24(t6)
	addi t1, t1, -1024
	sd t1, 8(t0)
	addi a0, s0, 0
	addi a1, s1, 0
	ld a2, 32(t6)
	ld a3, 40(t6)
	addi a4, s8, 0
	addi a5, s9, 0
	addi a6, s10, 0
	addi a7, s1, 0
	call {vg_rsa_public_precomputed_checked}
	add a1, s0, s1
	addi a1, a1, -1
	lbu a2, 0(a1)
	addi a3, zero, 188
	xor a2, a2, a3
	add a4, s0, s3
	lbu a3, 0(a4)
	addi a5, zero, 255
	xor a5, a5, s5
	and a3, a3, a5
	or a2, a2, a3
	lbu a3, 0(s0)
	addi a5, zero, 0
	sub a5, a5, s3
	and a3, a3, a5
	or a2, a2, a3
	sb a2, 0(a1)
	sd s5, 1352(s0)
	sd s6, 1360(s0)
	sd s7, 1368(s0)
	add s8, s0, s3
	addi s9, s4, 0
	add s6, s8, s4
	addi s7, zero, 28
	addi s10, zero, 0
	addi s11, zero, 0
2182:
	addi a0, s0, 1024
	addi t1, sp, 184
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, zero, 0
	addi a2, s6, 0
	addi a3, s7, 0
	addi t1, sp, 184
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
	addi t1, sp, 184
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, s7, 4
	addi a2, s0, 1280
	addi t1, sp, 184
	ld t1, 0(t1)
	ld t1, 16(t1)
	jalr ra, 0(t1)
	addi a6, sp, 184
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
2183:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t2, t2, t1
	sb t2, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 2183b
	addi t1, sp, 184
	ld t1, 0(t1)
	ld t1, 32(t1)
	addi s10, s10, 1
	add s11, s11, t1
	sub t1, s11, s9
	srli t1, t1, 63
	bnez t1, 2182b
	ld s5, 1352(s0)
	ld s6, 1360(s0)
	ld s7, 1368(s0)
	add a1, s0, s3
	lbu a2, 0(a1)
	and a2, a2, s5
	sb a2, 0(a1)
	add a1, s0, s3
	addi a2, s4, 0
	addi a3, zero, 0
	addi a4, zero, 0
	addi a4, a4, -1
	addi a5, zero, 0
	addi a6, zero, 0
2184:
	lbu a7, 0(a1)
	addi t1, a7, -1
	srli t1, t1, 63
	addi t2, t1, -1
	and t2, t2, a4
	and t3, a3, t2
	or a5, a5, t3
	and t3, a7, t2
	or a6, a6, t3
	addi t3, zero, 0
	sub t3, t3, t1
	and a4, a4, t3
	addi a1, a1, 1
	addi a3, a3, 1
	addi a2, a2, -1
	bnez a2, 2184b
	add t1, s0, s1
	addi t1, t1, -1
	lbu s10, 0(t1)
	addi t2, zero, 1
	xor a6, a6, t2
	or s10, s10, a6
	sub s11, s4, a5
	addi s11, s11, -1
	addi s8, a5, 0
	beqz s7, 2185f
	j 2186f
2185:
	xor t1, s11, s6
	or s10, s10, t1
2186:
	beqz s7, 2187f
	addi a1, s0, 2047
	addi a1, a1, 1
	addi t5, zero, 1024
	slli t5, t5, 1
	addi t0, zero, 0
2189:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 2189b
	addi a4, s2, 0
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 8
	addi a5, zero, 28
2190:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 2190b
	add a4, s0, s3
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 36
	addi a5, s4, 0
2191:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 2191b
	addi s8, s8, 1
	addi s9, zero, 1
	addi s5, zero, 10
2192:
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 36
	add a2, a1, s9
	addi a3, zero, 1
	and a3, s8, a3
	addi a4, zero, 0
	sub a3, a4, a3
	addi a5, s4, 0
2193:
	lbu t1, 0(a1)
	lbu t2, 0(a2)
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	sb t1, 0(a1)
	addi a1, a1, 1
	addi a2, a2, 1
	addi a5, a5, -1
	bnez a5, 2193b
	srli s8, s8, 1
	add s9, s9, s9
	addi s5, s5, -1
	bnez s5, 2192b
	addi a0, s0, 1024
	addi t1, sp, 176
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi a1, zero, 0
	addi a2, s0, 2047
	addi a2, a2, 1
	addi a3, zero, 36
	addi a0, s0, 1024
	addi t1, sp, 176
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi s8, zero, 0
	addi s9, s4, 0
2194:
	addi a4, s0, 1024
	addi a1, s0, 1376
	addi a5, zero, 96
2195:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 2195b
	addi a1, s8, 36
	addi a0, s0, 1024
	addi a2, s0, 1280
	addi t1, sp, 176
	ld t1, 0(t1)
	ld t1, 16(t1)
	jalr ra, 0(t1)
	xor t3, s8, s11
	addi t3, t3, -1
	srli t3, t3, 63
	addi t4, zero, 0
	sub t3, t4, t3
	addi a1, s0, 1280
	addi a2, s0, 1568
	addi a3, zero, 28
2196:
	lbu t1, 0(a1)
	lbu t2, 0(a2)
	xor t1, t1, t2
	and t1, t1, t3
	xor t2, t2, t1
	sb t2, 0(a2)
	addi a1, a1, 1
	addi a2, a2, 1
	addi a3, a3, -1
	bnez a3, 2196b
	addi a4, s0, 1376
	addi a1, s0, 1024
	addi a5, zero, 96
2197:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 2197b
	addi a1, s8, 36
	addi a2, s0, 2047
	addi a2, a2, 1
	addi a2, a2, 36
	add a2, a2, s8
	addi a3, zero, 1
	addi a0, s0, 1024
	addi t1, sp, 176
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi s8, s8, 1
	addi s9, s9, -1
	bnez s9, 2194b
	add a1, s0, s3
	add a1, a1, s4
	addi a2, s0, 1568
	addi a3, zero, 28
2198:
	lbu t1, 0(a1)
	lbu t2, 0(a2)
	xor t1, t1, t2
	or s10, s10, t1
	addi a1, a1, 1
	addi a2, a2, 1
	addi a3, a3, -1
	bnez a3, 2198b
	addi a0, s10, -1
	srli a0, a0, 63
	j 2188f
2187:
	addi a1, s0, 2047
	addi a1, a1, 1
	addi t5, zero, 8
	addi t0, zero, 0
2199:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 2199b
	addi a4, s2, 0
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 8
	addi a5, zero, 28
2200:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 2200b
	add a4, s0, s3
	add a4, a4, s4
	sub a4, a4, s6
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 36
	addi a5, s6, 0
	bnez a5, 2201f
	j 2202f
2201:
2203:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 2203b
2202:
	addi a0, s0, 1024
	addi t1, sp, 176
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi t2, s6, 36
	addi t3, t2, 8
	srli t3, t3, 6
	addi t3, t3, 1
	slli t3, t3, 6
	addi a1, s0, 2047
	addi a1, a1, 1
	add a1, a1, t2
	sub t5, t3, t2
	addi t0, zero, 0
2204:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 2204b
	addi a1, s0, 2047
	addi a1, a1, 1
	add a1, a1, t2
	addi t1, zero, 128
	sb t1, 0(a1)
	addi a1, s0, 2047
	addi a1, a1, 1
	add a1, a1, t3
	addi a1, a1, -8
	slli t1, t2, 3
	srli t4, t1, 56
	sb t4, 0(a1)
	srli t4, t1, 48
	sb t4, 1(a1)
	srli t4, t1, 40
	sb t4, 2(a1)
	srli t4, t1, 32
	sb t4, 3(a1)
	srli t4, t1, 24
	sb t4, 4(a1)
	srli t4, t1, 16
	sb t4, 5(a1)
	srli t4, t1, 8
	sb t4, 6(a1)
	srli t4, t1, 0
	sb t4, 7(a1)
	addi a0, s0, 1024
	addi a1, s0, 2047
	addi a1, a1, 1
	srli a2, t3, 6
	addi a3, s0, 1664
	addi t1, sp, 176
	ld t1, 0(t1)
	ld t1, 24(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, s0, 1280
	addi t1, sp, 176
	ld t1, 0(t1)
	ld t1, 32(t1)
	jalr ra, 0(t1)
	add a1, s0, s3
	add a1, a1, s4
	addi a2, s0, 1280
	addi a3, zero, 28
2205:
	lbu t1, 0(a1)
	lbu t2, 0(a2)
	xor t1, t1, t2
	or s10, s10, t1
	addi a1, a1, 1
	addi a2, a2, 1
	addi a3, a3, -1
	bnez a3, 2205b
	addi a0, s10, -1
	srli a0, a0, 63
2188:
	j 2181f
2180:
	addi a0, zero, 0
2181:
	j 2177f
2176:
	addi a0, zero, 0
2177:
	j 2175f
2174:
	addi a0, zero, 0
2175:
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
25:
	j 23f
22:
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
	ld s7, 8(t6)
	slli s7, s7, 32
	srli s7, s7, 32
	ld s0, 16(t6)
	addi s1, a1, 0
	addi s2, a4, 0
	ld s6, 0(t6)
	addi s8, a2, 0
	addi s9, a3, 0
	addi s10, a6, 0
	lbu t1, 0(a0)
	srli t2, t1, 1
	srli t3, t2, 1
	or t2, t2, t3
	srli t3, t2, 2
	or t2, t2, t3
	srli t3, t2, 4
	or t2, t2, t3
	addi t3, t2, -1
	srli s3, t3, 63
	addi t3, zero, 0
	sub t3, t3, s3
	addi t4, zero, 255
	and t3, t3, t4
	or s5, t2, t3
	sub s4, s1, s3
	addi s4, s4, -21
	beqz t1, 2206f
	sub a0, s1, s3
	addi a0, a0, -22
	srli a0, a0, 63
	bnez a0, 2208f
	beqz s7, 2210f
	addi a1, zero, 0
	j 2211f
2210:
	addi a1, s6, 0
2211:
	sub a0, s1, s3
	addi a0, a0, -22
	sub a0, a0, a1
	srli a0, a0, 63
	srli a2, a1, 63
	or a0, a0, a2
	bnez a0, 2212f
	addi t0, sp, 0
	addi t6, sp, 128
	addi t1, zero, 1024
	slli t1, t1, 3
	add t1, s0, t1
	sd t1, 0(t0)
	ld t1, 24(t6)
	addi t1, t1, -1024
	sd t1, 8(t0)
	addi a0, s0, 0
	addi a1, s1, 0
	ld a2, 32(t6)
	ld a3, 40(t6)
	addi a4, s8, 0
	addi a5, s9, 0
	addi a6, s10, 0
	addi a7, s1, 0
	call {vg_rsa_public_precomputed_checked}
	add a1, s0, s1
	addi a1, a1, -1
	lbu a2, 0(a1)
	addi a3, zero, 188
	xor a2, a2, a3
	add a4, s0, s3
	lbu a3, 0(a4)
	addi a5, zero, 255
	xor a5, a5, s5
	and a3, a3, a5
	or a2, a2, a3
	lbu a3, 0(s0)
	addi a5, zero, 0
	sub a5, a5, s3
	and a3, a3, a5
	or a2, a2, a3
	sb a2, 0(a1)
	sd s5, 1352(s0)
	sd s6, 1360(s0)
	sd s7, 1368(s0)
	add s8, s0, s3
	addi s9, s4, 0
	add s6, s8, s4
	addi s7, zero, 20
	addi s10, zero, 0
	addi s11, zero, 0
2214:
	addi a0, s0, 1024
	addi t1, sp, 184
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, zero, 0
	addi a2, s6, 0
	addi a3, s7, 0
	addi t1, sp, 184
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
	addi t1, sp, 184
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, s7, 4
	addi a2, s0, 1280
	addi t1, sp, 184
	ld t1, 0(t1)
	ld t1, 16(t1)
	jalr ra, 0(t1)
	addi a6, sp, 184
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
2215:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t2, t2, t1
	sb t2, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 2215b
	addi t1, sp, 184
	ld t1, 0(t1)
	ld t1, 32(t1)
	addi s10, s10, 1
	add s11, s11, t1
	sub t1, s11, s9
	srli t1, t1, 63
	bnez t1, 2214b
	ld s5, 1352(s0)
	ld s6, 1360(s0)
	ld s7, 1368(s0)
	add a1, s0, s3
	lbu a2, 0(a1)
	and a2, a2, s5
	sb a2, 0(a1)
	add a1, s0, s3
	addi a2, s4, 0
	addi a3, zero, 0
	addi a4, zero, 0
	addi a4, a4, -1
	addi a5, zero, 0
	addi a6, zero, 0
2216:
	lbu a7, 0(a1)
	addi t1, a7, -1
	srli t1, t1, 63
	addi t2, t1, -1
	and t2, t2, a4
	and t3, a3, t2
	or a5, a5, t3
	and t3, a7, t2
	or a6, a6, t3
	addi t3, zero, 0
	sub t3, t3, t1
	and a4, a4, t3
	addi a1, a1, 1
	addi a3, a3, 1
	addi a2, a2, -1
	bnez a2, 2216b
	add t1, s0, s1
	addi t1, t1, -1
	lbu s10, 0(t1)
	addi t2, zero, 1
	xor a6, a6, t2
	or s10, s10, a6
	sub s11, s4, a5
	addi s11, s11, -1
	addi s8, a5, 0
	beqz s7, 2217f
	j 2218f
2217:
	xor t1, s11, s6
	or s10, s10, t1
2218:
	beqz s7, 2219f
	addi a1, s0, 2047
	addi a1, a1, 1
	addi t5, zero, 1024
	slli t5, t5, 1
	addi t0, zero, 0
2221:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 2221b
	addi a4, s2, 0
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 8
	addi a5, zero, 20
2222:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 2222b
	add a4, s0, s3
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 28
	addi a5, s4, 0
2223:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 2223b
	addi s8, s8, 1
	addi s9, zero, 1
	addi s5, zero, 10
2224:
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 28
	add a2, a1, s9
	addi a3, zero, 1
	and a3, s8, a3
	addi a4, zero, 0
	sub a3, a4, a3
	addi a5, s4, 0
2225:
	lbu t1, 0(a1)
	lbu t2, 0(a2)
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	sb t1, 0(a1)
	addi a1, a1, 1
	addi a2, a2, 1
	addi a5, a5, -1
	bnez a5, 2225b
	srli s8, s8, 1
	add s9, s9, s9
	addi s5, s5, -1
	bnez s5, 2224b
	addi a0, s0, 1024
	addi t1, sp, 176
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi a1, zero, 0
	addi a2, s0, 2047
	addi a2, a2, 1
	addi a3, zero, 28
	addi a0, s0, 1024
	addi t1, sp, 176
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi s8, zero, 0
	addi s9, s4, 0
2226:
	addi a4, s0, 1024
	addi a1, s0, 1376
	addi a5, zero, 84
2227:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 2227b
	addi a1, s8, 28
	addi a0, s0, 1024
	addi a2, s0, 1280
	addi t1, sp, 176
	ld t1, 0(t1)
	ld t1, 16(t1)
	jalr ra, 0(t1)
	xor t3, s8, s11
	addi t3, t3, -1
	srli t3, t3, 63
	addi t4, zero, 0
	sub t3, t4, t3
	addi a1, s0, 1280
	addi a2, s0, 1568
	addi a3, zero, 20
2228:
	lbu t1, 0(a1)
	lbu t2, 0(a2)
	xor t1, t1, t2
	and t1, t1, t3
	xor t2, t2, t1
	sb t2, 0(a2)
	addi a1, a1, 1
	addi a2, a2, 1
	addi a3, a3, -1
	bnez a3, 2228b
	addi a4, s0, 1376
	addi a1, s0, 1024
	addi a5, zero, 84
2229:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 2229b
	addi a1, s8, 28
	addi a2, s0, 2047
	addi a2, a2, 1
	addi a2, a2, 28
	add a2, a2, s8
	addi a3, zero, 1
	addi a0, s0, 1024
	addi t1, sp, 176
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi s8, s8, 1
	addi s9, s9, -1
	bnez s9, 2226b
	add a1, s0, s3
	add a1, a1, s4
	addi a2, s0, 1568
	addi a3, zero, 20
2230:
	lbu t1, 0(a1)
	lbu t2, 0(a2)
	xor t1, t1, t2
	or s10, s10, t1
	addi a1, a1, 1
	addi a2, a2, 1
	addi a3, a3, -1
	bnez a3, 2230b
	addi a0, s10, -1
	srli a0, a0, 63
	j 2220f
2219:
	addi a1, s0, 2047
	addi a1, a1, 1
	addi t5, zero, 8
	addi t0, zero, 0
2231:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 2231b
	addi a4, s2, 0
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 8
	addi a5, zero, 20
2232:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 2232b
	add a4, s0, s3
	add a4, a4, s4
	sub a4, a4, s6
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 28
	addi a5, s6, 0
	bnez a5, 2233f
	j 2234f
2233:
2235:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 2235b
2234:
	addi a0, s0, 1024
	addi t1, sp, 176
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi t2, s6, 28
	addi t3, t2, 8
	srli t3, t3, 6
	addi t3, t3, 1
	slli t3, t3, 6
	addi a1, s0, 2047
	addi a1, a1, 1
	add a1, a1, t2
	sub t5, t3, t2
	addi t0, zero, 0
2236:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 2236b
	addi a1, s0, 2047
	addi a1, a1, 1
	add a1, a1, t2
	addi t1, zero, 128
	sb t1, 0(a1)
	addi a1, s0, 2047
	addi a1, a1, 1
	add a1, a1, t3
	addi a1, a1, -8
	slli t1, t2, 3
	srli t4, t1, 56
	sb t4, 0(a1)
	srli t4, t1, 48
	sb t4, 1(a1)
	srli t4, t1, 40
	sb t4, 2(a1)
	srli t4, t1, 32
	sb t4, 3(a1)
	srli t4, t1, 24
	sb t4, 4(a1)
	srli t4, t1, 16
	sb t4, 5(a1)
	srli t4, t1, 8
	sb t4, 6(a1)
	srli t4, t1, 0
	sb t4, 7(a1)
	addi a0, s0, 1024
	addi a1, s0, 2047
	addi a1, a1, 1
	srli a2, t3, 6
	addi a3, s0, 1664
	addi t1, sp, 176
	ld t1, 0(t1)
	ld t1, 24(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, s0, 1280
	addi t1, sp, 176
	ld t1, 0(t1)
	ld t1, 32(t1)
	jalr ra, 0(t1)
	add a1, s0, s3
	add a1, a1, s4
	addi a2, s0, 1280
	addi a3, zero, 20
2237:
	lbu t1, 0(a1)
	lbu t2, 0(a2)
	xor t1, t1, t2
	or s10, s10, t1
	addi a1, a1, 1
	addi a2, a2, 1
	addi a3, a3, -1
	bnez a3, 2237b
	addi a0, s10, -1
	srli a0, a0, 63
2220:
	j 2213f
2212:
	addi a0, zero, 0
2213:
	j 2209f
2208:
	addi a0, zero, 0
2209:
	j 2207f
2206:
	addi a0, zero, 0
2207:
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
23:
	j 21f
20:
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
	ld s7, 8(t6)
	slli s7, s7, 32
	srli s7, s7, 32
	ld s0, 16(t6)
	addi s1, a1, 0
	addi s2, a4, 0
	ld s6, 0(t6)
	addi s8, a2, 0
	addi s9, a3, 0
	addi s10, a6, 0
	lbu t1, 0(a0)
	srli t2, t1, 1
	srli t3, t2, 1
	or t2, t2, t3
	srli t3, t2, 2
	or t2, t2, t3
	srli t3, t2, 4
	or t2, t2, t3
	addi t3, t2, -1
	srli s3, t3, 63
	addi t3, zero, 0
	sub t3, t3, s3
	addi t4, zero, 255
	and t3, t3, t4
	or s5, t2, t3
	sub s4, s1, s3
	addi s4, s4, -17
	beqz t1, 2238f
	sub a0, s1, s3
	addi a0, a0, -18
	srli a0, a0, 63
	bnez a0, 2240f
	beqz s7, 2242f
	addi a1, zero, 0
	j 2243f
2242:
	addi a1, s6, 0
2243:
	sub a0, s1, s3
	addi a0, a0, -18
	sub a0, a0, a1
	srli a0, a0, 63
	srli a2, a1, 63
	or a0, a0, a2
	bnez a0, 2244f
	addi t0, sp, 0
	addi t6, sp, 128
	addi t1, zero, 1024
	slli t1, t1, 3
	add t1, s0, t1
	sd t1, 0(t0)
	ld t1, 24(t6)
	addi t1, t1, -1024
	sd t1, 8(t0)
	addi a0, s0, 0
	addi a1, s1, 0
	ld a2, 32(t6)
	ld a3, 40(t6)
	addi a4, s8, 0
	addi a5, s9, 0
	addi a6, s10, 0
	addi a7, s1, 0
	call {vg_rsa_public_precomputed_checked}
	add a1, s0, s1
	addi a1, a1, -1
	lbu a2, 0(a1)
	addi a3, zero, 188
	xor a2, a2, a3
	add a4, s0, s3
	lbu a3, 0(a4)
	addi a5, zero, 255
	xor a5, a5, s5
	and a3, a3, a5
	or a2, a2, a3
	lbu a3, 0(s0)
	addi a5, zero, 0
	sub a5, a5, s3
	and a3, a3, a5
	or a2, a2, a3
	sb a2, 0(a1)
	sd s5, 1352(s0)
	sd s6, 1360(s0)
	sd s7, 1368(s0)
	add s8, s0, s3
	addi s9, s4, 0
	add s6, s8, s4
	addi s7, zero, 16
	addi s10, zero, 0
	addi s11, zero, 0
2246:
	addi a0, s0, 1024
	addi t1, sp, 184
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, zero, 0
	addi a2, s6, 0
	addi a3, s7, 0
	addi t1, sp, 184
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
	addi t1, sp, 184
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, s7, 4
	addi a2, s0, 1280
	addi t1, sp, 184
	ld t1, 0(t1)
	ld t1, 16(t1)
	jalr ra, 0(t1)
	addi a6, sp, 184
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
2247:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t2, t2, t1
	sb t2, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 2247b
	addi t1, sp, 184
	ld t1, 0(t1)
	ld t1, 32(t1)
	addi s10, s10, 1
	add s11, s11, t1
	sub t1, s11, s9
	srli t1, t1, 63
	bnez t1, 2246b
	ld s5, 1352(s0)
	ld s6, 1360(s0)
	ld s7, 1368(s0)
	add a1, s0, s3
	lbu a2, 0(a1)
	and a2, a2, s5
	sb a2, 0(a1)
	add a1, s0, s3
	addi a2, s4, 0
	addi a3, zero, 0
	addi a4, zero, 0
	addi a4, a4, -1
	addi a5, zero, 0
	addi a6, zero, 0
2248:
	lbu a7, 0(a1)
	addi t1, a7, -1
	srli t1, t1, 63
	addi t2, t1, -1
	and t2, t2, a4
	and t3, a3, t2
	or a5, a5, t3
	and t3, a7, t2
	or a6, a6, t3
	addi t3, zero, 0
	sub t3, t3, t1
	and a4, a4, t3
	addi a1, a1, 1
	addi a3, a3, 1
	addi a2, a2, -1
	bnez a2, 2248b
	add t1, s0, s1
	addi t1, t1, -1
	lbu s10, 0(t1)
	addi t2, zero, 1
	xor a6, a6, t2
	or s10, s10, a6
	sub s11, s4, a5
	addi s11, s11, -1
	addi s8, a5, 0
	beqz s7, 2249f
	j 2250f
2249:
	xor t1, s11, s6
	or s10, s10, t1
2250:
	beqz s7, 2251f
	addi a1, s0, 2047
	addi a1, a1, 1
	addi t5, zero, 1024
	slli t5, t5, 1
	addi t0, zero, 0
2253:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 2253b
	addi a4, s2, 0
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 8
	addi a5, zero, 16
2254:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 2254b
	add a4, s0, s3
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 24
	addi a5, s4, 0
2255:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 2255b
	addi s8, s8, 1
	addi s9, zero, 1
	addi s5, zero, 10
2256:
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 24
	add a2, a1, s9
	addi a3, zero, 1
	and a3, s8, a3
	addi a4, zero, 0
	sub a3, a4, a3
	addi a5, s4, 0
2257:
	lbu t1, 0(a1)
	lbu t2, 0(a2)
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	sb t1, 0(a1)
	addi a1, a1, 1
	addi a2, a2, 1
	addi a5, a5, -1
	bnez a5, 2257b
	srli s8, s8, 1
	add s9, s9, s9
	addi s5, s5, -1
	bnez s5, 2256b
	addi a0, s0, 1024
	addi t1, sp, 176
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi a1, zero, 0
	addi a2, s0, 2047
	addi a2, a2, 1
	addi a3, zero, 24
	addi a0, s0, 1024
	addi t1, sp, 176
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi s8, zero, 0
	addi s9, s4, 0
2258:
	addi a4, s0, 1024
	addi a1, s0, 1376
	addi a5, zero, 80
2259:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 2259b
	addi a1, s8, 24
	addi a0, s0, 1024
	addi a2, s0, 1280
	addi t1, sp, 176
	ld t1, 0(t1)
	ld t1, 16(t1)
	jalr ra, 0(t1)
	xor t3, s8, s11
	addi t3, t3, -1
	srli t3, t3, 63
	addi t4, zero, 0
	sub t3, t4, t3
	addi a1, s0, 1280
	addi a2, s0, 1568
	addi a3, zero, 16
2260:
	lbu t1, 0(a1)
	lbu t2, 0(a2)
	xor t1, t1, t2
	and t1, t1, t3
	xor t2, t2, t1
	sb t2, 0(a2)
	addi a1, a1, 1
	addi a2, a2, 1
	addi a3, a3, -1
	bnez a3, 2260b
	addi a4, s0, 1376
	addi a1, s0, 1024
	addi a5, zero, 80
2261:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 2261b
	addi a1, s8, 24
	addi a2, s0, 2047
	addi a2, a2, 1
	addi a2, a2, 24
	add a2, a2, s8
	addi a3, zero, 1
	addi a0, s0, 1024
	addi t1, sp, 176
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi s8, s8, 1
	addi s9, s9, -1
	bnez s9, 2258b
	add a1, s0, s3
	add a1, a1, s4
	addi a2, s0, 1568
	addi a3, zero, 16
2262:
	lbu t1, 0(a1)
	lbu t2, 0(a2)
	xor t1, t1, t2
	or s10, s10, t1
	addi a1, a1, 1
	addi a2, a2, 1
	addi a3, a3, -1
	bnez a3, 2262b
	addi a0, s10, -1
	srli a0, a0, 63
	j 2252f
2251:
	addi a1, s0, 2047
	addi a1, a1, 1
	addi t5, zero, 8
	addi t0, zero, 0
2263:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 2263b
	addi a4, s2, 0
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 8
	addi a5, zero, 16
2264:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 2264b
	add a4, s0, s3
	add a4, a4, s4
	sub a4, a4, s6
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 24
	addi a5, s6, 0
	bnez a5, 2265f
	j 2266f
2265:
2267:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 2267b
2266:
	addi a0, s0, 1024
	addi t1, sp, 176
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi t2, s6, 24
	addi t3, t2, 8
	srli t3, t3, 6
	addi t3, t3, 1
	slli t3, t3, 6
	addi a1, s0, 2047
	addi a1, a1, 1
	add a1, a1, t2
	sub t5, t3, t2
	addi t0, zero, 0
2268:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 2268b
	addi a1, s0, 2047
	addi a1, a1, 1
	add a1, a1, t2
	addi t1, zero, 128
	sb t1, 0(a1)
	addi a1, s0, 2047
	addi a1, a1, 1
	add a1, a1, t3
	addi a1, a1, -8
	slli t1, t2, 3
	sb t1, 0(a1)
	srli t4, t1, 8
	sb t4, 1(a1)
	srli t4, t1, 16
	sb t4, 2(a1)
	srli t4, t1, 24
	sb t4, 3(a1)
	srli t4, t1, 32
	sb t4, 4(a1)
	srli t5, t4, 8
	sb t5, 5(a1)
	srli t5, t4, 16
	sb t5, 6(a1)
	srli t5, t4, 24
	sb t5, 7(a1)
	addi a0, s0, 1024
	addi a1, s0, 2047
	addi a1, a1, 1
	srli a2, t3, 6
	addi a3, s0, 1664
	addi t1, sp, 176
	ld t1, 0(t1)
	ld t1, 24(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, s0, 1280
	addi t1, sp, 176
	ld t1, 0(t1)
	ld t1, 32(t1)
	jalr ra, 0(t1)
	add a1, s0, s3
	add a1, a1, s4
	addi a2, s0, 1280
	addi a3, zero, 16
2269:
	lbu t1, 0(a1)
	lbu t2, 0(a2)
	xor t1, t1, t2
	or s10, s10, t1
	addi a1, a1, 1
	addi a2, a2, 1
	addi a3, a3, -1
	bnez a3, 2269b
	addi a0, s10, -1
	srli a0, a0, 63
2252:
	j 2245f
2244:
	addi a0, zero, 0
2245:
	j 2241f
2240:
	addi a0, zero, 0
2241:
	j 2239f
2238:
	addi a0, zero, 0
2239:
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
21:
	ret
	.option pop

vg_rsa_pss_sign:
	.option push
	.option arch, +m, +c
	addi t5, sp, 112
	ld t5, 0(t5)
	ld t5, 40(t5)
	addi t4, t5, 0
	beqz t4, 20f
	addi t4, t5, -1
	beqz t4, 22f
	addi t4, t5, -2
	beqz t4, 24f
	addi t4, t5, -3
	beqz t4, 26f
	addi t4, t5, -4
	beqz t4, 28f
	addi t4, t5, -5
	beqz t4, 210f
	addi t4, t5, -6
	beqz t4, 212f
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
	ld s0, 96(t6)
	addi s1, a3, 0
	addi s2, a0, 0
	ld s4, 88(t6)
	sd a2, 1352(s0)
	sd a4, 1360(s0)
	sd a5, 1368(s0)
	sd a6, 1376(s0)
	sd a7, 1384(s0)
	lbu t1, 0(a2)
	srli t2, t1, 1
	srli t3, t2, 1
	or t2, t2, t3
	srli t3, t2, 2
	or t2, t2, t3
	srli t3, t2, 4
	or t2, t2, t3
	addi t3, t2, -1
	srli s3, t3, 63
	addi t3, zero, 0
	sub t3, t3, s3
	addi t4, zero, 255
	and t3, t3, t4
	or t2, t2, t3
	sd t2, 1392(s0)
	beqz t1, 214f
	sub a0, s1, s3
	addi a0, a0, -34
	srli a0, a0, 63
	bnez a0, 216f
	sub a0, s1, s3
	addi a0, a0, -34
	sub a0, a0, s4
	srli a0, a0, 63
	srli a2, s4, 63
	or a0, a0, a2
	bnez a0, 218f
	addi a1, s0, 2047
	addi a1, a1, 1
	addi t5, zero, 8
	addi t0, zero, 0
220:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 220b
	addi t6, sp, 128
	ld a4, 64(t6)
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 8
	addi a5, zero, 32
221:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 221b
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 40
	addi t6, sp, 128
	ld a4, 80(t6)
	addi a5, s4, 0
	bnez a5, 222f
	j 223f
222:
224:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 224b
223:
	addi s6, s4, 0
	addi a0, s0, 1024
	addi t1, sp, 240
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi t2, s6, 40
	addi t3, t2, 16
	srli t3, t3, 7
	addi t3, t3, 1
	slli t3, t3, 7
	addi a1, s0, 2047
	addi a1, a1, 1
	add a1, a1, t2
	sub t5, t3, t2
	addi t0, zero, 0
225:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 225b
	addi a1, s0, 2047
	addi a1, a1, 1
	add a1, a1, t2
	addi t1, zero, 128
	sb t1, 0(a1)
	addi a1, s0, 2047
	addi a1, a1, 1
	add a1, a1, t3
	addi a1, a1, -8
	slli t1, t2, 3
	srli t4, t1, 56
	sb t4, 0(a1)
	srli t4, t1, 48
	sb t4, 1(a1)
	srli t4, t1, 40
	sb t4, 2(a1)
	srli t4, t1, 32
	sb t4, 3(a1)
	srli t4, t1, 24
	sb t4, 4(a1)
	srli t4, t1, 16
	sb t4, 5(a1)
	srli t4, t1, 8
	sb t4, 6(a1)
	srli t4, t1, 0
	sb t4, 7(a1)
	addi a0, s0, 1024
	addi a1, s0, 2047
	addi a1, a1, 1
	srli a2, t3, 7
	addi a3, s0, 1664
	addi t1, sp, 240
	ld t1, 0(t1)
	ld t1, 24(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, s0, 1280
	addi t1, sp, 240
	ld t1, 0(t1)
	ld t1, 32(t1)
	jalr ra, 0(t1)
	addi a1, s0, 0
	addi t5, zero, 1024
	addi t0, zero, 0
226:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 226b
	add a1, s0, s1
	sub a1, a1, s4
	addi a1, a1, -34
	addi t1, zero, 1
	sb t1, 0(a1)
	addi a1, a1, 1
	addi t6, sp, 128
	ld a4, 80(t6)
	addi a5, s4, 0
	bnez a5, 227f
	j 228f
227:
229:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 229b
228:
	addi a4, s0, 1280
	add a1, s0, s1
	addi a1, a1, -33
	addi a5, zero, 32
230:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 230b
	add a1, s0, s1
	addi a1, a1, -1
	addi t1, zero, 188
	sb t1, 0(a1)
	add s6, s0, s1
	addi s6, s6, -33
	addi s7, zero, 32
	add s8, s0, s3
	sub s9, s1, s3
	addi s9, s9, -33
	addi s10, zero, 0
	addi s11, zero, 0
231:
	addi a0, s0, 1024
	addi t1, sp, 248
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, zero, 0
	addi a2, s6, 0
	addi a3, s7, 0
	addi t1, sp, 248
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
	addi t1, sp, 248
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, s7, 4
	addi a2, s0, 1280
	addi t1, sp, 248
	ld t1, 0(t1)
	ld t1, 16(t1)
	jalr ra, 0(t1)
	addi a6, sp, 248
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
232:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t2, t2, t1
	sb t2, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 232b
	addi t1, sp, 248
	ld t1, 0(t1)
	ld t1, 32(t1)
	addi s10, s10, 1
	add s11, s11, t1
	sub t1, s11, s9
	srli t1, t1, 63
	bnez t1, 231b
	ld t2, 1392(s0)
	add a1, s0, s3
	lbu a2, 0(a1)
	and a2, a2, t2
	sb a2, 0(a1)
	addi sp, sp, -96
	addi t0, sp, 0
	addi t6, sp, 224
	ld t1, 1376(s0)
	sd t1, 0(t0)
	ld t1, 1384(s0)
	sd t1, 8(t0)
	ld t1, 0(t6)
	sd t1, 16(t0)
	ld t1, 8(t6)
	sd t1, 24(t0)
	ld t1, 16(t6)
	sd t1, 32(t0)
	ld t1, 24(t6)
	sd t1, 40(t0)
	ld t1, 32(t6)
	sd t1, 48(t0)
	ld t1, 40(t6)
	sd t1, 56(t0)
	ld t1, 48(t6)
	sd t1, 64(t0)
	ld t1, 56(t6)
	sd t1, 72(t0)
	addi t1, zero, 1024
	slli t1, t1, 3
	add t1, s0, t1
	sd t1, 80(t0)
	ld t1, 104(t6)
	addi t1, t1, -1024
	sd t1, 88(t0)
	addi a0, s2, 0
	addi a1, s1, 0
	ld a2, 1352(s0)
	addi a3, s1, 0
	ld a4, 1360(s0)
	ld a5, 1368(s0)
	addi a6, s0, 0
	addi a7, s1, 0
	call {vg_rsa_private_checked}
	addi sp, sp, 96
	j 219f
218:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
233:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 233b
	addi a0, zero, 0
219:
	j 217f
216:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
234:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 234b
	addi a0, zero, 0
217:
	j 215f
214:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
235:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 235b
	addi a0, zero, 0
215:
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
	j 213f
212:
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
	ld s0, 96(t6)
	addi s1, a3, 0
	addi s2, a0, 0
	ld s4, 88(t6)
	sd a2, 1352(s0)
	sd a4, 1360(s0)
	sd a5, 1368(s0)
	sd a6, 1376(s0)
	sd a7, 1384(s0)
	lbu t1, 0(a2)
	srli t2, t1, 1
	srli t3, t2, 1
	or t2, t2, t3
	srli t3, t2, 2
	or t2, t2, t3
	srli t3, t2, 4
	or t2, t2, t3
	addi t3, t2, -1
	srli s3, t3, 63
	addi t3, zero, 0
	sub t3, t3, s3
	addi t4, zero, 255
	and t3, t3, t4
	or t2, t2, t3
	sd t2, 1392(s0)
	beqz t1, 236f
	sub a0, s1, s3
	addi a0, a0, -30
	srli a0, a0, 63
	bnez a0, 238f
	sub a0, s1, s3
	addi a0, a0, -30
	sub a0, a0, s4
	srli a0, a0, 63
	srli a2, s4, 63
	or a0, a0, a2
	bnez a0, 240f
	addi a1, s0, 2047
	addi a1, a1, 1
	addi t5, zero, 8
	addi t0, zero, 0
242:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 242b
	addi t6, sp, 128
	ld a4, 64(t6)
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 8
	addi a5, zero, 28
243:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 243b
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 36
	addi t6, sp, 128
	ld a4, 80(t6)
	addi a5, s4, 0
	bnez a5, 244f
	j 245f
244:
246:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 246b
245:
	addi s6, s4, 0
	addi a0, s0, 1024
	addi t1, sp, 240
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi t2, s6, 36
	addi t3, t2, 16
	srli t3, t3, 7
	addi t3, t3, 1
	slli t3, t3, 7
	addi a1, s0, 2047
	addi a1, a1, 1
	add a1, a1, t2
	sub t5, t3, t2
	addi t0, zero, 0
247:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 247b
	addi a1, s0, 2047
	addi a1, a1, 1
	add a1, a1, t2
	addi t1, zero, 128
	sb t1, 0(a1)
	addi a1, s0, 2047
	addi a1, a1, 1
	add a1, a1, t3
	addi a1, a1, -8
	slli t1, t2, 3
	srli t4, t1, 56
	sb t4, 0(a1)
	srli t4, t1, 48
	sb t4, 1(a1)
	srli t4, t1, 40
	sb t4, 2(a1)
	srli t4, t1, 32
	sb t4, 3(a1)
	srli t4, t1, 24
	sb t4, 4(a1)
	srli t4, t1, 16
	sb t4, 5(a1)
	srli t4, t1, 8
	sb t4, 6(a1)
	srli t4, t1, 0
	sb t4, 7(a1)
	addi a0, s0, 1024
	addi a1, s0, 2047
	addi a1, a1, 1
	srli a2, t3, 7
	addi a3, s0, 1664
	addi t1, sp, 240
	ld t1, 0(t1)
	ld t1, 24(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, s0, 1280
	addi t1, sp, 240
	ld t1, 0(t1)
	ld t1, 32(t1)
	jalr ra, 0(t1)
	addi a1, s0, 0
	addi t5, zero, 1024
	addi t0, zero, 0
248:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 248b
	add a1, s0, s1
	sub a1, a1, s4
	addi a1, a1, -30
	addi t1, zero, 1
	sb t1, 0(a1)
	addi a1, a1, 1
	addi t6, sp, 128
	ld a4, 80(t6)
	addi a5, s4, 0
	bnez a5, 249f
	j 250f
249:
251:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 251b
250:
	addi a4, s0, 1280
	add a1, s0, s1
	addi a1, a1, -29
	addi a5, zero, 28
252:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 252b
	add a1, s0, s1
	addi a1, a1, -1
	addi t1, zero, 188
	sb t1, 0(a1)
	add s6, s0, s1
	addi s6, s6, -29
	addi s7, zero, 28
	add s8, s0, s3
	sub s9, s1, s3
	addi s9, s9, -29
	addi s10, zero, 0
	addi s11, zero, 0
253:
	addi a0, s0, 1024
	addi t1, sp, 248
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, zero, 0
	addi a2, s6, 0
	addi a3, s7, 0
	addi t1, sp, 248
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
	addi t1, sp, 248
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, s7, 4
	addi a2, s0, 1280
	addi t1, sp, 248
	ld t1, 0(t1)
	ld t1, 16(t1)
	jalr ra, 0(t1)
	addi a6, sp, 248
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
254:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t2, t2, t1
	sb t2, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 254b
	addi t1, sp, 248
	ld t1, 0(t1)
	ld t1, 32(t1)
	addi s10, s10, 1
	add s11, s11, t1
	sub t1, s11, s9
	srli t1, t1, 63
	bnez t1, 253b
	ld t2, 1392(s0)
	add a1, s0, s3
	lbu a2, 0(a1)
	and a2, a2, t2
	sb a2, 0(a1)
	addi sp, sp, -96
	addi t0, sp, 0
	addi t6, sp, 224
	ld t1, 1376(s0)
	sd t1, 0(t0)
	ld t1, 1384(s0)
	sd t1, 8(t0)
	ld t1, 0(t6)
	sd t1, 16(t0)
	ld t1, 8(t6)
	sd t1, 24(t0)
	ld t1, 16(t6)
	sd t1, 32(t0)
	ld t1, 24(t6)
	sd t1, 40(t0)
	ld t1, 32(t6)
	sd t1, 48(t0)
	ld t1, 40(t6)
	sd t1, 56(t0)
	ld t1, 48(t6)
	sd t1, 64(t0)
	ld t1, 56(t6)
	sd t1, 72(t0)
	addi t1, zero, 1024
	slli t1, t1, 3
	add t1, s0, t1
	sd t1, 80(t0)
	ld t1, 104(t6)
	addi t1, t1, -1024
	sd t1, 88(t0)
	addi a0, s2, 0
	addi a1, s1, 0
	ld a2, 1352(s0)
	addi a3, s1, 0
	ld a4, 1360(s0)
	ld a5, 1368(s0)
	addi a6, s0, 0
	addi a7, s1, 0
	call {vg_rsa_private_checked}
	addi sp, sp, 96
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
	j 239f
238:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
256:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 256b
	addi a0, zero, 0
239:
	j 237f
236:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
257:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 257b
	addi a0, zero, 0
237:
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
213:
	j 211f
210:
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
	ld s0, 96(t6)
	addi s1, a3, 0
	addi s2, a0, 0
	ld s4, 88(t6)
	sd a2, 1352(s0)
	sd a4, 1360(s0)
	sd a5, 1368(s0)
	sd a6, 1376(s0)
	sd a7, 1384(s0)
	lbu t1, 0(a2)
	srli t2, t1, 1
	srli t3, t2, 1
	or t2, t2, t3
	srli t3, t2, 2
	or t2, t2, t3
	srli t3, t2, 4
	or t2, t2, t3
	addi t3, t2, -1
	srli s3, t3, 63
	addi t3, zero, 0
	sub t3, t3, s3
	addi t4, zero, 255
	and t3, t3, t4
	or t2, t2, t3
	sd t2, 1392(s0)
	beqz t1, 258f
	sub a0, s1, s3
	addi a0, a0, -66
	srli a0, a0, 63
	bnez a0, 260f
	sub a0, s1, s3
	addi a0, a0, -66
	sub a0, a0, s4
	srli a0, a0, 63
	srli a2, s4, 63
	or a0, a0, a2
	bnez a0, 262f
	addi a1, s0, 2047
	addi a1, a1, 1
	addi t5, zero, 8
	addi t0, zero, 0
264:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 264b
	addi t6, sp, 128
	ld a4, 64(t6)
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 8
	addi a5, zero, 64
265:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 265b
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 72
	addi t6, sp, 128
	ld a4, 80(t6)
	addi a5, s4, 0
	bnez a5, 266f
	j 267f
266:
268:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 268b
267:
	addi s6, s4, 0
	addi a0, s0, 1024
	addi t1, sp, 240
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi t2, s6, 72
	addi t3, t2, 16
	srli t3, t3, 7
	addi t3, t3, 1
	slli t3, t3, 7
	addi a1, s0, 2047
	addi a1, a1, 1
	add a1, a1, t2
	sub t5, t3, t2
	addi t0, zero, 0
269:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 269b
	addi a1, s0, 2047
	addi a1, a1, 1
	add a1, a1, t2
	addi t1, zero, 128
	sb t1, 0(a1)
	addi a1, s0, 2047
	addi a1, a1, 1
	add a1, a1, t3
	addi a1, a1, -8
	slli t1, t2, 3
	srli t4, t1, 56
	sb t4, 0(a1)
	srli t4, t1, 48
	sb t4, 1(a1)
	srli t4, t1, 40
	sb t4, 2(a1)
	srli t4, t1, 32
	sb t4, 3(a1)
	srli t4, t1, 24
	sb t4, 4(a1)
	srli t4, t1, 16
	sb t4, 5(a1)
	srli t4, t1, 8
	sb t4, 6(a1)
	srli t4, t1, 0
	sb t4, 7(a1)
	addi a0, s0, 1024
	addi a1, s0, 2047
	addi a1, a1, 1
	srli a2, t3, 7
	addi a3, s0, 1664
	addi t1, sp, 240
	ld t1, 0(t1)
	ld t1, 24(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, s0, 1280
	addi t1, sp, 240
	ld t1, 0(t1)
	ld t1, 32(t1)
	jalr ra, 0(t1)
	addi a1, s0, 0
	addi t5, zero, 1024
	addi t0, zero, 0
270:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 270b
	add a1, s0, s1
	sub a1, a1, s4
	addi a1, a1, -66
	addi t1, zero, 1
	sb t1, 0(a1)
	addi a1, a1, 1
	addi t6, sp, 128
	ld a4, 80(t6)
	addi a5, s4, 0
	bnez a5, 271f
	j 272f
271:
273:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 273b
272:
	addi a4, s0, 1280
	add a1, s0, s1
	addi a1, a1, -65
	addi a5, zero, 64
274:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 274b
	add a1, s0, s1
	addi a1, a1, -1
	addi t1, zero, 188
	sb t1, 0(a1)
	add s6, s0, s1
	addi s6, s6, -65
	addi s7, zero, 64
	add s8, s0, s3
	sub s9, s1, s3
	addi s9, s9, -65
	addi s10, zero, 0
	addi s11, zero, 0
275:
	addi a0, s0, 1024
	addi t1, sp, 248
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, zero, 0
	addi a2, s6, 0
	addi a3, s7, 0
	addi t1, sp, 248
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
	addi t1, sp, 248
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, s7, 4
	addi a2, s0, 1280
	addi t1, sp, 248
	ld t1, 0(t1)
	ld t1, 16(t1)
	jalr ra, 0(t1)
	addi a6, sp, 248
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
276:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t2, t2, t1
	sb t2, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 276b
	addi t1, sp, 248
	ld t1, 0(t1)
	ld t1, 32(t1)
	addi s10, s10, 1
	add s11, s11, t1
	sub t1, s11, s9
	srli t1, t1, 63
	bnez t1, 275b
	ld t2, 1392(s0)
	add a1, s0, s3
	lbu a2, 0(a1)
	and a2, a2, t2
	sb a2, 0(a1)
	addi sp, sp, -96
	addi t0, sp, 0
	addi t6, sp, 224
	ld t1, 1376(s0)
	sd t1, 0(t0)
	ld t1, 1384(s0)
	sd t1, 8(t0)
	ld t1, 0(t6)
	sd t1, 16(t0)
	ld t1, 8(t6)
	sd t1, 24(t0)
	ld t1, 16(t6)
	sd t1, 32(t0)
	ld t1, 24(t6)
	sd t1, 40(t0)
	ld t1, 32(t6)
	sd t1, 48(t0)
	ld t1, 40(t6)
	sd t1, 56(t0)
	ld t1, 48(t6)
	sd t1, 64(t0)
	ld t1, 56(t6)
	sd t1, 72(t0)
	addi t1, zero, 1024
	slli t1, t1, 3
	add t1, s0, t1
	sd t1, 80(t0)
	ld t1, 104(t6)
	addi t1, t1, -1024
	sd t1, 88(t0)
	addi a0, s2, 0
	addi a1, s1, 0
	ld a2, 1352(s0)
	addi a3, s1, 0
	ld a4, 1360(s0)
	ld a5, 1368(s0)
	addi a6, s0, 0
	addi a7, s1, 0
	call {vg_rsa_private_checked}
	addi sp, sp, 96
	j 263f
262:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
277:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 277b
	addi a0, zero, 0
263:
	j 261f
260:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
278:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 278b
	addi a0, zero, 0
261:
	j 259f
258:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
279:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 279b
	addi a0, zero, 0
259:
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
211:
	j 29f
28:
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
	ld s0, 96(t6)
	addi s1, a3, 0
	addi s2, a0, 0
	ld s4, 88(t6)
	sd a2, 1352(s0)
	sd a4, 1360(s0)
	sd a5, 1368(s0)
	sd a6, 1376(s0)
	sd a7, 1384(s0)
	lbu t1, 0(a2)
	srli t2, t1, 1
	srli t3, t2, 1
	or t2, t2, t3
	srli t3, t2, 2
	or t2, t2, t3
	srli t3, t2, 4
	or t2, t2, t3
	addi t3, t2, -1
	srli s3, t3, 63
	addi t3, zero, 0
	sub t3, t3, s3
	addi t4, zero, 255
	and t3, t3, t4
	or t2, t2, t3
	sd t2, 1392(s0)
	beqz t1, 280f
	sub a0, s1, s3
	addi a0, a0, -50
	srli a0, a0, 63
	bnez a0, 282f
	sub a0, s1, s3
	addi a0, a0, -50
	sub a0, a0, s4
	srli a0, a0, 63
	srli a2, s4, 63
	or a0, a0, a2
	bnez a0, 284f
	addi a1, s0, 2047
	addi a1, a1, 1
	addi t5, zero, 8
	addi t0, zero, 0
286:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 286b
	addi t6, sp, 128
	ld a4, 64(t6)
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 8
	addi a5, zero, 48
287:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 287b
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 56
	addi t6, sp, 128
	ld a4, 80(t6)
	addi a5, s4, 0
	bnez a5, 288f
	j 289f
288:
290:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 290b
289:
	addi s6, s4, 0
	addi a0, s0, 1024
	addi t1, sp, 240
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi t2, s6, 56
	addi t3, t2, 16
	srli t3, t3, 7
	addi t3, t3, 1
	slli t3, t3, 7
	addi a1, s0, 2047
	addi a1, a1, 1
	add a1, a1, t2
	sub t5, t3, t2
	addi t0, zero, 0
291:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 291b
	addi a1, s0, 2047
	addi a1, a1, 1
	add a1, a1, t2
	addi t1, zero, 128
	sb t1, 0(a1)
	addi a1, s0, 2047
	addi a1, a1, 1
	add a1, a1, t3
	addi a1, a1, -8
	slli t1, t2, 3
	srli t4, t1, 56
	sb t4, 0(a1)
	srli t4, t1, 48
	sb t4, 1(a1)
	srli t4, t1, 40
	sb t4, 2(a1)
	srli t4, t1, 32
	sb t4, 3(a1)
	srli t4, t1, 24
	sb t4, 4(a1)
	srli t4, t1, 16
	sb t4, 5(a1)
	srli t4, t1, 8
	sb t4, 6(a1)
	srli t4, t1, 0
	sb t4, 7(a1)
	addi a0, s0, 1024
	addi a1, s0, 2047
	addi a1, a1, 1
	srli a2, t3, 7
	addi a3, s0, 1664
	addi t1, sp, 240
	ld t1, 0(t1)
	ld t1, 24(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, s0, 1280
	addi t1, sp, 240
	ld t1, 0(t1)
	ld t1, 32(t1)
	jalr ra, 0(t1)
	addi a1, s0, 0
	addi t5, zero, 1024
	addi t0, zero, 0
292:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 292b
	add a1, s0, s1
	sub a1, a1, s4
	addi a1, a1, -50
	addi t1, zero, 1
	sb t1, 0(a1)
	addi a1, a1, 1
	addi t6, sp, 128
	ld a4, 80(t6)
	addi a5, s4, 0
	bnez a5, 293f
	j 294f
293:
295:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 295b
294:
	addi a4, s0, 1280
	add a1, s0, s1
	addi a1, a1, -49
	addi a5, zero, 48
296:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 296b
	add a1, s0, s1
	addi a1, a1, -1
	addi t1, zero, 188
	sb t1, 0(a1)
	add s6, s0, s1
	addi s6, s6, -49
	addi s7, zero, 48
	add s8, s0, s3
	sub s9, s1, s3
	addi s9, s9, -49
	addi s10, zero, 0
	addi s11, zero, 0
297:
	addi a0, s0, 1024
	addi t1, sp, 248
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, zero, 0
	addi a2, s6, 0
	addi a3, s7, 0
	addi t1, sp, 248
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
	addi t1, sp, 248
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, s7, 4
	addi a2, s0, 1280
	addi t1, sp, 248
	ld t1, 0(t1)
	ld t1, 16(t1)
	jalr ra, 0(t1)
	addi a6, sp, 248
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
298:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t2, t2, t1
	sb t2, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 298b
	addi t1, sp, 248
	ld t1, 0(t1)
	ld t1, 32(t1)
	addi s10, s10, 1
	add s11, s11, t1
	sub t1, s11, s9
	srli t1, t1, 63
	bnez t1, 297b
	ld t2, 1392(s0)
	add a1, s0, s3
	lbu a2, 0(a1)
	and a2, a2, t2
	sb a2, 0(a1)
	addi sp, sp, -96
	addi t0, sp, 0
	addi t6, sp, 224
	ld t1, 1376(s0)
	sd t1, 0(t0)
	ld t1, 1384(s0)
	sd t1, 8(t0)
	ld t1, 0(t6)
	sd t1, 16(t0)
	ld t1, 8(t6)
	sd t1, 24(t0)
	ld t1, 16(t6)
	sd t1, 32(t0)
	ld t1, 24(t6)
	sd t1, 40(t0)
	ld t1, 32(t6)
	sd t1, 48(t0)
	ld t1, 40(t6)
	sd t1, 56(t0)
	ld t1, 48(t6)
	sd t1, 64(t0)
	ld t1, 56(t6)
	sd t1, 72(t0)
	addi t1, zero, 1024
	slli t1, t1, 3
	add t1, s0, t1
	sd t1, 80(t0)
	ld t1, 104(t6)
	addi t1, t1, -1024
	sd t1, 88(t0)
	addi a0, s2, 0
	addi a1, s1, 0
	ld a2, 1352(s0)
	addi a3, s1, 0
	ld a4, 1360(s0)
	ld a5, 1368(s0)
	addi a6, s0, 0
	addi a7, s1, 0
	call {vg_rsa_private_checked}
	addi sp, sp, 96
	j 285f
284:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
299:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 299b
	addi a0, zero, 0
285:
	j 283f
282:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
2100:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 2100b
	addi a0, zero, 0
283:
	j 281f
280:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
2101:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 2101b
	addi a0, zero, 0
281:
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
29:
	j 27f
26:
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
	ld s0, 96(t6)
	addi s1, a3, 0
	addi s2, a0, 0
	ld s4, 88(t6)
	sd a2, 1352(s0)
	sd a4, 1360(s0)
	sd a5, 1368(s0)
	sd a6, 1376(s0)
	sd a7, 1384(s0)
	lbu t1, 0(a2)
	srli t2, t1, 1
	srli t3, t2, 1
	or t2, t2, t3
	srli t3, t2, 2
	or t2, t2, t3
	srli t3, t2, 4
	or t2, t2, t3
	addi t3, t2, -1
	srli s3, t3, 63
	addi t3, zero, 0
	sub t3, t3, s3
	addi t4, zero, 255
	and t3, t3, t4
	or t2, t2, t3
	sd t2, 1392(s0)
	beqz t1, 2102f
	sub a0, s1, s3
	addi a0, a0, -34
	srli a0, a0, 63
	bnez a0, 2104f
	sub a0, s1, s3
	addi a0, a0, -34
	sub a0, a0, s4
	srli a0, a0, 63
	srli a2, s4, 63
	or a0, a0, a2
	bnez a0, 2106f
	addi a1, s0, 2047
	addi a1, a1, 1
	addi t5, zero, 8
	addi t0, zero, 0
2108:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 2108b
	addi t6, sp, 128
	ld a4, 64(t6)
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 8
	addi a5, zero, 32
2109:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 2109b
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 40
	addi t6, sp, 128
	ld a4, 80(t6)
	addi a5, s4, 0
	bnez a5, 2110f
	j 2111f
2110:
2112:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 2112b
2111:
	addi s6, s4, 0
	addi a0, s0, 1024
	addi t1, sp, 240
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi t2, s6, 40
	addi t3, t2, 8
	srli t3, t3, 6
	addi t3, t3, 1
	slli t3, t3, 6
	addi a1, s0, 2047
	addi a1, a1, 1
	add a1, a1, t2
	sub t5, t3, t2
	addi t0, zero, 0
2113:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 2113b
	addi a1, s0, 2047
	addi a1, a1, 1
	add a1, a1, t2
	addi t1, zero, 128
	sb t1, 0(a1)
	addi a1, s0, 2047
	addi a1, a1, 1
	add a1, a1, t3
	addi a1, a1, -8
	slli t1, t2, 3
	srli t4, t1, 56
	sb t4, 0(a1)
	srli t4, t1, 48
	sb t4, 1(a1)
	srli t4, t1, 40
	sb t4, 2(a1)
	srli t4, t1, 32
	sb t4, 3(a1)
	srli t4, t1, 24
	sb t4, 4(a1)
	srli t4, t1, 16
	sb t4, 5(a1)
	srli t4, t1, 8
	sb t4, 6(a1)
	srli t4, t1, 0
	sb t4, 7(a1)
	addi a0, s0, 1024
	addi a1, s0, 2047
	addi a1, a1, 1
	srli a2, t3, 6
	addi a3, s0, 1664
	addi t1, sp, 240
	ld t1, 0(t1)
	ld t1, 24(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, s0, 1280
	addi t1, sp, 240
	ld t1, 0(t1)
	ld t1, 32(t1)
	jalr ra, 0(t1)
	addi a1, s0, 0
	addi t5, zero, 1024
	addi t0, zero, 0
2114:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 2114b
	add a1, s0, s1
	sub a1, a1, s4
	addi a1, a1, -34
	addi t1, zero, 1
	sb t1, 0(a1)
	addi a1, a1, 1
	addi t6, sp, 128
	ld a4, 80(t6)
	addi a5, s4, 0
	bnez a5, 2115f
	j 2116f
2115:
2117:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 2117b
2116:
	addi a4, s0, 1280
	add a1, s0, s1
	addi a1, a1, -33
	addi a5, zero, 32
2118:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 2118b
	add a1, s0, s1
	addi a1, a1, -1
	addi t1, zero, 188
	sb t1, 0(a1)
	add s6, s0, s1
	addi s6, s6, -33
	addi s7, zero, 32
	add s8, s0, s3
	sub s9, s1, s3
	addi s9, s9, -33
	addi s10, zero, 0
	addi s11, zero, 0
2119:
	addi a0, s0, 1024
	addi t1, sp, 248
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, zero, 0
	addi a2, s6, 0
	addi a3, s7, 0
	addi t1, sp, 248
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
	addi t1, sp, 248
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, s7, 4
	addi a2, s0, 1280
	addi t1, sp, 248
	ld t1, 0(t1)
	ld t1, 16(t1)
	jalr ra, 0(t1)
	addi a6, sp, 248
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
2120:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t2, t2, t1
	sb t2, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 2120b
	addi t1, sp, 248
	ld t1, 0(t1)
	ld t1, 32(t1)
	addi s10, s10, 1
	add s11, s11, t1
	sub t1, s11, s9
	srli t1, t1, 63
	bnez t1, 2119b
	ld t2, 1392(s0)
	add a1, s0, s3
	lbu a2, 0(a1)
	and a2, a2, t2
	sb a2, 0(a1)
	addi sp, sp, -96
	addi t0, sp, 0
	addi t6, sp, 224
	ld t1, 1376(s0)
	sd t1, 0(t0)
	ld t1, 1384(s0)
	sd t1, 8(t0)
	ld t1, 0(t6)
	sd t1, 16(t0)
	ld t1, 8(t6)
	sd t1, 24(t0)
	ld t1, 16(t6)
	sd t1, 32(t0)
	ld t1, 24(t6)
	sd t1, 40(t0)
	ld t1, 32(t6)
	sd t1, 48(t0)
	ld t1, 40(t6)
	sd t1, 56(t0)
	ld t1, 48(t6)
	sd t1, 64(t0)
	ld t1, 56(t6)
	sd t1, 72(t0)
	addi t1, zero, 1024
	slli t1, t1, 3
	add t1, s0, t1
	sd t1, 80(t0)
	ld t1, 104(t6)
	addi t1, t1, -1024
	sd t1, 88(t0)
	addi a0, s2, 0
	addi a1, s1, 0
	ld a2, 1352(s0)
	addi a3, s1, 0
	ld a4, 1360(s0)
	ld a5, 1368(s0)
	addi a6, s0, 0
	addi a7, s1, 0
	call {vg_rsa_private_checked}
	addi sp, sp, 96
	j 2107f
2106:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
2121:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 2121b
	addi a0, zero, 0
2107:
	j 2105f
2104:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
2122:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 2122b
	addi a0, zero, 0
2105:
	j 2103f
2102:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
2123:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 2123b
	addi a0, zero, 0
2103:
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
27:
	j 25f
24:
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
	ld s0, 96(t6)
	addi s1, a3, 0
	addi s2, a0, 0
	ld s4, 88(t6)
	sd a2, 1352(s0)
	sd a4, 1360(s0)
	sd a5, 1368(s0)
	sd a6, 1376(s0)
	sd a7, 1384(s0)
	lbu t1, 0(a2)
	srli t2, t1, 1
	srli t3, t2, 1
	or t2, t2, t3
	srli t3, t2, 2
	or t2, t2, t3
	srli t3, t2, 4
	or t2, t2, t3
	addi t3, t2, -1
	srli s3, t3, 63
	addi t3, zero, 0
	sub t3, t3, s3
	addi t4, zero, 255
	and t3, t3, t4
	or t2, t2, t3
	sd t2, 1392(s0)
	beqz t1, 2124f
	sub a0, s1, s3
	addi a0, a0, -30
	srli a0, a0, 63
	bnez a0, 2126f
	sub a0, s1, s3
	addi a0, a0, -30
	sub a0, a0, s4
	srli a0, a0, 63
	srli a2, s4, 63
	or a0, a0, a2
	bnez a0, 2128f
	addi a1, s0, 2047
	addi a1, a1, 1
	addi t5, zero, 8
	addi t0, zero, 0
2130:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 2130b
	addi t6, sp, 128
	ld a4, 64(t6)
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 8
	addi a5, zero, 28
2131:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 2131b
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 36
	addi t6, sp, 128
	ld a4, 80(t6)
	addi a5, s4, 0
	bnez a5, 2132f
	j 2133f
2132:
2134:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 2134b
2133:
	addi s6, s4, 0
	addi a0, s0, 1024
	addi t1, sp, 240
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi t2, s6, 36
	addi t3, t2, 8
	srli t3, t3, 6
	addi t3, t3, 1
	slli t3, t3, 6
	addi a1, s0, 2047
	addi a1, a1, 1
	add a1, a1, t2
	sub t5, t3, t2
	addi t0, zero, 0
2135:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 2135b
	addi a1, s0, 2047
	addi a1, a1, 1
	add a1, a1, t2
	addi t1, zero, 128
	sb t1, 0(a1)
	addi a1, s0, 2047
	addi a1, a1, 1
	add a1, a1, t3
	addi a1, a1, -8
	slli t1, t2, 3
	srli t4, t1, 56
	sb t4, 0(a1)
	srli t4, t1, 48
	sb t4, 1(a1)
	srli t4, t1, 40
	sb t4, 2(a1)
	srli t4, t1, 32
	sb t4, 3(a1)
	srli t4, t1, 24
	sb t4, 4(a1)
	srli t4, t1, 16
	sb t4, 5(a1)
	srli t4, t1, 8
	sb t4, 6(a1)
	srli t4, t1, 0
	sb t4, 7(a1)
	addi a0, s0, 1024
	addi a1, s0, 2047
	addi a1, a1, 1
	srli a2, t3, 6
	addi a3, s0, 1664
	addi t1, sp, 240
	ld t1, 0(t1)
	ld t1, 24(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, s0, 1280
	addi t1, sp, 240
	ld t1, 0(t1)
	ld t1, 32(t1)
	jalr ra, 0(t1)
	addi a1, s0, 0
	addi t5, zero, 1024
	addi t0, zero, 0
2136:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 2136b
	add a1, s0, s1
	sub a1, a1, s4
	addi a1, a1, -30
	addi t1, zero, 1
	sb t1, 0(a1)
	addi a1, a1, 1
	addi t6, sp, 128
	ld a4, 80(t6)
	addi a5, s4, 0
	bnez a5, 2137f
	j 2138f
2137:
2139:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 2139b
2138:
	addi a4, s0, 1280
	add a1, s0, s1
	addi a1, a1, -29
	addi a5, zero, 28
2140:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 2140b
	add a1, s0, s1
	addi a1, a1, -1
	addi t1, zero, 188
	sb t1, 0(a1)
	add s6, s0, s1
	addi s6, s6, -29
	addi s7, zero, 28
	add s8, s0, s3
	sub s9, s1, s3
	addi s9, s9, -29
	addi s10, zero, 0
	addi s11, zero, 0
2141:
	addi a0, s0, 1024
	addi t1, sp, 248
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, zero, 0
	addi a2, s6, 0
	addi a3, s7, 0
	addi t1, sp, 248
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
	addi t1, sp, 248
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, s7, 4
	addi a2, s0, 1280
	addi t1, sp, 248
	ld t1, 0(t1)
	ld t1, 16(t1)
	jalr ra, 0(t1)
	addi a6, sp, 248
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
2142:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t2, t2, t1
	sb t2, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 2142b
	addi t1, sp, 248
	ld t1, 0(t1)
	ld t1, 32(t1)
	addi s10, s10, 1
	add s11, s11, t1
	sub t1, s11, s9
	srli t1, t1, 63
	bnez t1, 2141b
	ld t2, 1392(s0)
	add a1, s0, s3
	lbu a2, 0(a1)
	and a2, a2, t2
	sb a2, 0(a1)
	addi sp, sp, -96
	addi t0, sp, 0
	addi t6, sp, 224
	ld t1, 1376(s0)
	sd t1, 0(t0)
	ld t1, 1384(s0)
	sd t1, 8(t0)
	ld t1, 0(t6)
	sd t1, 16(t0)
	ld t1, 8(t6)
	sd t1, 24(t0)
	ld t1, 16(t6)
	sd t1, 32(t0)
	ld t1, 24(t6)
	sd t1, 40(t0)
	ld t1, 32(t6)
	sd t1, 48(t0)
	ld t1, 40(t6)
	sd t1, 56(t0)
	ld t1, 48(t6)
	sd t1, 64(t0)
	ld t1, 56(t6)
	sd t1, 72(t0)
	addi t1, zero, 1024
	slli t1, t1, 3
	add t1, s0, t1
	sd t1, 80(t0)
	ld t1, 104(t6)
	addi t1, t1, -1024
	sd t1, 88(t0)
	addi a0, s2, 0
	addi a1, s1, 0
	ld a2, 1352(s0)
	addi a3, s1, 0
	ld a4, 1360(s0)
	ld a5, 1368(s0)
	addi a6, s0, 0
	addi a7, s1, 0
	call {vg_rsa_private_checked}
	addi sp, sp, 96
	j 2129f
2128:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
2143:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 2143b
	addi a0, zero, 0
2129:
	j 2127f
2126:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
2144:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 2144b
	addi a0, zero, 0
2127:
	j 2125f
2124:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
2145:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 2145b
	addi a0, zero, 0
2125:
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
25:
	j 23f
22:
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
	ld s0, 96(t6)
	addi s1, a3, 0
	addi s2, a0, 0
	ld s4, 88(t6)
	sd a2, 1352(s0)
	sd a4, 1360(s0)
	sd a5, 1368(s0)
	sd a6, 1376(s0)
	sd a7, 1384(s0)
	lbu t1, 0(a2)
	srli t2, t1, 1
	srli t3, t2, 1
	or t2, t2, t3
	srli t3, t2, 2
	or t2, t2, t3
	srli t3, t2, 4
	or t2, t2, t3
	addi t3, t2, -1
	srli s3, t3, 63
	addi t3, zero, 0
	sub t3, t3, s3
	addi t4, zero, 255
	and t3, t3, t4
	or t2, t2, t3
	sd t2, 1392(s0)
	beqz t1, 2146f
	sub a0, s1, s3
	addi a0, a0, -22
	srli a0, a0, 63
	bnez a0, 2148f
	sub a0, s1, s3
	addi a0, a0, -22
	sub a0, a0, s4
	srli a0, a0, 63
	srli a2, s4, 63
	or a0, a0, a2
	bnez a0, 2150f
	addi a1, s0, 2047
	addi a1, a1, 1
	addi t5, zero, 8
	addi t0, zero, 0
2152:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 2152b
	addi t6, sp, 128
	ld a4, 64(t6)
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 8
	addi a5, zero, 20
2153:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 2153b
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 28
	addi t6, sp, 128
	ld a4, 80(t6)
	addi a5, s4, 0
	bnez a5, 2154f
	j 2155f
2154:
2156:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 2156b
2155:
	addi s6, s4, 0
	addi a0, s0, 1024
	addi t1, sp, 240
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi t2, s6, 28
	addi t3, t2, 8
	srli t3, t3, 6
	addi t3, t3, 1
	slli t3, t3, 6
	addi a1, s0, 2047
	addi a1, a1, 1
	add a1, a1, t2
	sub t5, t3, t2
	addi t0, zero, 0
2157:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 2157b
	addi a1, s0, 2047
	addi a1, a1, 1
	add a1, a1, t2
	addi t1, zero, 128
	sb t1, 0(a1)
	addi a1, s0, 2047
	addi a1, a1, 1
	add a1, a1, t3
	addi a1, a1, -8
	slli t1, t2, 3
	srli t4, t1, 56
	sb t4, 0(a1)
	srli t4, t1, 48
	sb t4, 1(a1)
	srli t4, t1, 40
	sb t4, 2(a1)
	srli t4, t1, 32
	sb t4, 3(a1)
	srli t4, t1, 24
	sb t4, 4(a1)
	srli t4, t1, 16
	sb t4, 5(a1)
	srli t4, t1, 8
	sb t4, 6(a1)
	srli t4, t1, 0
	sb t4, 7(a1)
	addi a0, s0, 1024
	addi a1, s0, 2047
	addi a1, a1, 1
	srli a2, t3, 6
	addi a3, s0, 1664
	addi t1, sp, 240
	ld t1, 0(t1)
	ld t1, 24(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, s0, 1280
	addi t1, sp, 240
	ld t1, 0(t1)
	ld t1, 32(t1)
	jalr ra, 0(t1)
	addi a1, s0, 0
	addi t5, zero, 1024
	addi t0, zero, 0
2158:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 2158b
	add a1, s0, s1
	sub a1, a1, s4
	addi a1, a1, -22
	addi t1, zero, 1
	sb t1, 0(a1)
	addi a1, a1, 1
	addi t6, sp, 128
	ld a4, 80(t6)
	addi a5, s4, 0
	bnez a5, 2159f
	j 2160f
2159:
2161:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 2161b
2160:
	addi a4, s0, 1280
	add a1, s0, s1
	addi a1, a1, -21
	addi a5, zero, 20
2162:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 2162b
	add a1, s0, s1
	addi a1, a1, -1
	addi t1, zero, 188
	sb t1, 0(a1)
	add s6, s0, s1
	addi s6, s6, -21
	addi s7, zero, 20
	add s8, s0, s3
	sub s9, s1, s3
	addi s9, s9, -21
	addi s10, zero, 0
	addi s11, zero, 0
2163:
	addi a0, s0, 1024
	addi t1, sp, 248
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, zero, 0
	addi a2, s6, 0
	addi a3, s7, 0
	addi t1, sp, 248
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
	addi t1, sp, 248
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, s7, 4
	addi a2, s0, 1280
	addi t1, sp, 248
	ld t1, 0(t1)
	ld t1, 16(t1)
	jalr ra, 0(t1)
	addi a6, sp, 248
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
2164:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t2, t2, t1
	sb t2, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 2164b
	addi t1, sp, 248
	ld t1, 0(t1)
	ld t1, 32(t1)
	addi s10, s10, 1
	add s11, s11, t1
	sub t1, s11, s9
	srli t1, t1, 63
	bnez t1, 2163b
	ld t2, 1392(s0)
	add a1, s0, s3
	lbu a2, 0(a1)
	and a2, a2, t2
	sb a2, 0(a1)
	addi sp, sp, -96
	addi t0, sp, 0
	addi t6, sp, 224
	ld t1, 1376(s0)
	sd t1, 0(t0)
	ld t1, 1384(s0)
	sd t1, 8(t0)
	ld t1, 0(t6)
	sd t1, 16(t0)
	ld t1, 8(t6)
	sd t1, 24(t0)
	ld t1, 16(t6)
	sd t1, 32(t0)
	ld t1, 24(t6)
	sd t1, 40(t0)
	ld t1, 32(t6)
	sd t1, 48(t0)
	ld t1, 40(t6)
	sd t1, 56(t0)
	ld t1, 48(t6)
	sd t1, 64(t0)
	ld t1, 56(t6)
	sd t1, 72(t0)
	addi t1, zero, 1024
	slli t1, t1, 3
	add t1, s0, t1
	sd t1, 80(t0)
	ld t1, 104(t6)
	addi t1, t1, -1024
	sd t1, 88(t0)
	addi a0, s2, 0
	addi a1, s1, 0
	ld a2, 1352(s0)
	addi a3, s1, 0
	ld a4, 1360(s0)
	ld a5, 1368(s0)
	addi a6, s0, 0
	addi a7, s1, 0
	call {vg_rsa_private_checked}
	addi sp, sp, 96
	j 2151f
2150:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
2165:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 2165b
	addi a0, zero, 0
2151:
	j 2149f
2148:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
2166:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 2166b
	addi a0, zero, 0
2149:
	j 2147f
2146:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
2167:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 2167b
	addi a0, zero, 0
2147:
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
23:
	j 21f
20:
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
	ld s0, 96(t6)
	addi s1, a3, 0
	addi s2, a0, 0
	ld s4, 88(t6)
	sd a2, 1352(s0)
	sd a4, 1360(s0)
	sd a5, 1368(s0)
	sd a6, 1376(s0)
	sd a7, 1384(s0)
	lbu t1, 0(a2)
	srli t2, t1, 1
	srli t3, t2, 1
	or t2, t2, t3
	srli t3, t2, 2
	or t2, t2, t3
	srli t3, t2, 4
	or t2, t2, t3
	addi t3, t2, -1
	srli s3, t3, 63
	addi t3, zero, 0
	sub t3, t3, s3
	addi t4, zero, 255
	and t3, t3, t4
	or t2, t2, t3
	sd t2, 1392(s0)
	beqz t1, 2168f
	sub a0, s1, s3
	addi a0, a0, -18
	srli a0, a0, 63
	bnez a0, 2170f
	sub a0, s1, s3
	addi a0, a0, -18
	sub a0, a0, s4
	srli a0, a0, 63
	srli a2, s4, 63
	or a0, a0, a2
	bnez a0, 2172f
	addi a1, s0, 2047
	addi a1, a1, 1
	addi t5, zero, 8
	addi t0, zero, 0
2174:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 2174b
	addi t6, sp, 128
	ld a4, 64(t6)
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 8
	addi a5, zero, 16
2175:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 2175b
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 24
	addi t6, sp, 128
	ld a4, 80(t6)
	addi a5, s4, 0
	bnez a5, 2176f
	j 2177f
2176:
2178:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 2178b
2177:
	addi s6, s4, 0
	addi a0, s0, 1024
	addi t1, sp, 240
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi t2, s6, 24
	addi t3, t2, 8
	srli t3, t3, 6
	addi t3, t3, 1
	slli t3, t3, 6
	addi a1, s0, 2047
	addi a1, a1, 1
	add a1, a1, t2
	sub t5, t3, t2
	addi t0, zero, 0
2179:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 2179b
	addi a1, s0, 2047
	addi a1, a1, 1
	add a1, a1, t2
	addi t1, zero, 128
	sb t1, 0(a1)
	addi a1, s0, 2047
	addi a1, a1, 1
	add a1, a1, t3
	addi a1, a1, -8
	slli t1, t2, 3
	sb t1, 0(a1)
	srli t4, t1, 8
	sb t4, 1(a1)
	srli t4, t1, 16
	sb t4, 2(a1)
	srli t4, t1, 24
	sb t4, 3(a1)
	srli t4, t1, 32
	sb t4, 4(a1)
	srli t5, t4, 8
	sb t5, 5(a1)
	srli t5, t4, 16
	sb t5, 6(a1)
	srli t5, t4, 24
	sb t5, 7(a1)
	addi a0, s0, 1024
	addi a1, s0, 2047
	addi a1, a1, 1
	srli a2, t3, 6
	addi a3, s0, 1664
	addi t1, sp, 240
	ld t1, 0(t1)
	ld t1, 24(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, s0, 1280
	addi t1, sp, 240
	ld t1, 0(t1)
	ld t1, 32(t1)
	jalr ra, 0(t1)
	addi a1, s0, 0
	addi t5, zero, 1024
	addi t0, zero, 0
2180:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 2180b
	add a1, s0, s1
	sub a1, a1, s4
	addi a1, a1, -18
	addi t1, zero, 1
	sb t1, 0(a1)
	addi a1, a1, 1
	addi t6, sp, 128
	ld a4, 80(t6)
	addi a5, s4, 0
	bnez a5, 2181f
	j 2182f
2181:
2183:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 2183b
2182:
	addi a4, s0, 1280
	add a1, s0, s1
	addi a1, a1, -17
	addi a5, zero, 16
2184:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 2184b
	add a1, s0, s1
	addi a1, a1, -1
	addi t1, zero, 188
	sb t1, 0(a1)
	add s6, s0, s1
	addi s6, s6, -17
	addi s7, zero, 16
	add s8, s0, s3
	sub s9, s1, s3
	addi s9, s9, -17
	addi s10, zero, 0
	addi s11, zero, 0
2185:
	addi a0, s0, 1024
	addi t1, sp, 248
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, zero, 0
	addi a2, s6, 0
	addi a3, s7, 0
	addi t1, sp, 248
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
	addi t1, sp, 248
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, s7, 4
	addi a2, s0, 1280
	addi t1, sp, 248
	ld t1, 0(t1)
	ld t1, 16(t1)
	jalr ra, 0(t1)
	addi a6, sp, 248
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
2186:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t2, t2, t1
	sb t2, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 2186b
	addi t1, sp, 248
	ld t1, 0(t1)
	ld t1, 32(t1)
	addi s10, s10, 1
	add s11, s11, t1
	sub t1, s11, s9
	srli t1, t1, 63
	bnez t1, 2185b
	ld t2, 1392(s0)
	add a1, s0, s3
	lbu a2, 0(a1)
	and a2, a2, t2
	sb a2, 0(a1)
	addi sp, sp, -96
	addi t0, sp, 0
	addi t6, sp, 224
	ld t1, 1376(s0)
	sd t1, 0(t0)
	ld t1, 1384(s0)
	sd t1, 8(t0)
	ld t1, 0(t6)
	sd t1, 16(t0)
	ld t1, 8(t6)
	sd t1, 24(t0)
	ld t1, 16(t6)
	sd t1, 32(t0)
	ld t1, 24(t6)
	sd t1, 40(t0)
	ld t1, 32(t6)
	sd t1, 48(t0)
	ld t1, 40(t6)
	sd t1, 56(t0)
	ld t1, 48(t6)
	sd t1, 64(t0)
	ld t1, 56(t6)
	sd t1, 72(t0)
	addi t1, zero, 1024
	slli t1, t1, 3
	add t1, s0, t1
	sd t1, 80(t0)
	ld t1, 104(t6)
	addi t1, t1, -1024
	sd t1, 88(t0)
	addi a0, s2, 0
	addi a1, s1, 0
	ld a2, 1352(s0)
	addi a3, s1, 0
	ld a4, 1360(s0)
	ld a5, 1368(s0)
	addi a6, s0, 0
	addi a7, s1, 0
	call {vg_rsa_private_checked}
	addi sp, sp, 96
	j 2173f
2172:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
2187:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 2187b
	addi a0, zero, 0
2173:
	j 2171f
2170:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
2188:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 2188b
	addi a0, zero, 0
2171:
	j 2169f
2168:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
2189:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 2189b
	addi a0, zero, 0
2169:
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
21:
	ret
	.option pop
