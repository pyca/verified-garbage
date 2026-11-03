// The functions of `src/rsa_pss_sha512_mgf1_sha512.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_pss_sha512_mgf1_sha512_verify_precomputed:
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
	ld s7, 0(t6)
	slli s7, s7, 32
	srli s7, s7, 32
	ld s0, 8(t6)
	addi s1, a1, 0
	addi s2, a4, 0
	addi s6, a7, 0
	addi s8, a2, 0
	addi s9, a3, 0
	addi s10, a5, 0
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
	beqz t1, 20f
	sub a0, s1, s3
	addi a0, a0, -66
	srli a0, a0, 63
	bnez a0, 22f
	beqz s7, 24f
	addi a1, zero, 0
	j 25f
24:
	addi a1, s6, 0
25:
	sub a0, s1, s3
	addi a0, a0, -66
	sub a0, a0, a1
	srli a0, a0, 63
	srli a2, a1, 63
	or a0, a0, a2
	bnez a0, 26f
	addi t0, sp, 0
	addi t6, sp, 128
	addi t1, zero, 1024
	slli t1, t1, 3
	add t1, s0, t1
	sd t1, 0(t0)
	ld t1, 16(t6)
	addi t1, t1, -1024
	sd t1, 8(t0)
	addi a0, s0, 0
	addi a1, s1, 0
	ld a2, 24(t6)
	ld a3, 32(t6)
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
28:
	addi a0, s0, 1024
	call {vg_sha512_init}
	addi a0, s0, 1024
	addi a1, zero, 0
	addi a2, s6, 0
	addi a3, s7, 0
	call {vg_sha512_update}
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
	call {vg_sha512_update}
	addi a0, s0, 1024
	addi a1, s7, 4
	addi a2, s0, 1280
	call {vg_sha512_finalize}
	addi a4, s0, 1280
	add a5, s8, s11
	sub t1, s9, s11
	addi a6, zero, 64
	sub t2, t1, a6
	srli t3, t2, 63
	addi t4, zero, 0
	sub t3, t4, t3
	and t2, t2, t3
	add a6, a6, t2
29:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t2, t2, t1
	sb t2, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 29b
	addi s10, s10, 1
	addi s11, s11, 64
	sub t1, s11, s9
	srli t1, t1, 63
	bnez t1, 28b
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
210:
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
	bnez a2, 210b
	add t1, s0, s1
	addi t1, t1, -1
	lbu s10, 0(t1)
	addi t2, zero, 1
	xor a6, a6, t2
	or s10, s10, a6
	sub s11, s4, a5
	addi s11, s11, -1
	addi s8, a5, 0
	beqz s7, 211f
	j 212f
211:
	xor t1, s11, s6
	or s10, s10, t1
212:
	beqz s7, 213f
	addi a1, s0, 2047
	addi a1, a1, 1
	addi t5, zero, 1024
	slli t5, t5, 1
	addi t0, zero, 0
215:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 215b
	addi a4, s2, 0
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 8
	addi a5, zero, 64
216:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 216b
	add a4, s0, s3
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 72
	addi a5, s4, 0
217:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 217b
	addi s8, s8, 1
	addi s9, zero, 1
	addi s5, zero, 10
218:
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 72
	add a2, a1, s9
	addi a3, zero, 1
	and a3, s8, a3
	addi a4, zero, 0
	sub a3, a4, a3
	addi a5, s4, 0
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
	addi s5, s5, -1
	bnez s5, 218b
	addi a0, s0, 1024
	call {vg_sha512_init}
	addi a1, zero, 0
	addi a2, s0, 2047
	addi a2, a2, 1
	addi a3, zero, 72
	addi a0, s0, 1024
	call {vg_sha512_update}
	addi s8, zero, 0
	addi s9, s4, 0
220:
	addi a4, s0, 1024
	addi a1, s0, 1376
	addi a5, zero, 192
221:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 221b
	addi a1, s8, 72
	addi a0, s0, 1024
	addi a2, s0, 1280
	call {vg_sha512_finalize}
	xor t3, s8, s11
	addi t3, t3, -1
	srli t3, t3, 63
	addi t4, zero, 0
	sub t3, t4, t3
	addi a1, s0, 1280
	addi a2, s0, 1568
	addi a3, zero, 64
222:
	lbu t1, 0(a1)
	lbu t2, 0(a2)
	xor t1, t1, t2
	and t1, t1, t3
	xor t2, t2, t1
	sb t2, 0(a2)
	addi a1, a1, 1
	addi a2, a2, 1
	addi a3, a3, -1
	bnez a3, 222b
	addi a4, s0, 1376
	addi a1, s0, 1024
	addi a5, zero, 192
223:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 223b
	addi a1, s8, 72
	addi a2, s0, 2047
	addi a2, a2, 1
	addi a2, a2, 72
	add a2, a2, s8
	addi a3, zero, 1
	addi a0, s0, 1024
	call {vg_sha512_update}
	addi s8, s8, 1
	addi s9, s9, -1
	bnez s9, 220b
	add a1, s0, s3
	add a1, a1, s4
	addi a2, s0, 1568
	addi a3, zero, 64
224:
	lbu t1, 0(a1)
	lbu t2, 0(a2)
	xor t1, t1, t2
	or s10, s10, t1
	addi a1, a1, 1
	addi a2, a2, 1
	addi a3, a3, -1
	bnez a3, 224b
	addi a0, s10, -1
	srli a0, a0, 63
	j 214f
213:
	addi a1, s0, 2047
	addi a1, a1, 1
	addi t5, zero, 8
	addi t0, zero, 0
225:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 225b
	addi a4, s2, 0
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 8
	addi a5, zero, 64
226:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 226b
	add a4, s0, s3
	add a4, a4, s4
	sub a4, a4, s6
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 72
	addi a5, s6, 0
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
	addi a0, s0, 1024
	call {vg_sha512_init}
	addi a1, zero, 0
	addi a2, s0, 2047
	addi a2, a2, 1
	addi a3, s6, 72
	addi a0, s0, 1024
	call {vg_sha512_update}
	addi a1, s6, 72
	addi a0, s0, 1024
	addi a2, s0, 1280
	call {vg_sha512_finalize}
	add a1, s0, s3
	add a1, a1, s4
	addi a2, s0, 1280
	addi a3, zero, 64
230:
	lbu t1, 0(a1)
	lbu t2, 0(a2)
	xor t1, t1, t2
	or s10, s10, t1
	addi a1, a1, 1
	addi a2, a2, 1
	addi a3, a3, -1
	bnez a3, 230b
	addi a0, s10, -1
	srli a0, a0, 63
214:
	j 27f
26:
	addi a0, zero, 0
27:
	j 23f
22:
	addi a0, zero, 0
23:
	j 21f
20:
	addi a0, zero, 0
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

vg_rsa_pss_sha512_mgf1_sha512_sign:
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
	ld s0, 88(t6)
	addi s1, a3, 0
	addi s2, a0, 0
	ld s4, 80(t6)
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
	beqz t1, 20f
	sub a0, s1, s3
	addi a0, a0, -66
	srli a0, a0, 63
	bnez a0, 22f
	sub a0, s1, s3
	addi a0, a0, -66
	sub a0, a0, s4
	srli a0, a0, 63
	srli a2, s4, 63
	or a0, a0, a2
	bnez a0, 24f
	addi a1, s0, 2047
	addi a1, a1, 1
	addi t5, zero, 8
	addi t0, zero, 0
26:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 26b
	addi t6, sp, 128
	ld a4, 64(t6)
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 8
	addi a5, zero, 64
27:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 27b
	addi a1, s0, 2047
	addi a1, a1, 1
	addi a1, a1, 72
	addi t6, sp, 128
	ld a4, 72(t6)
	addi a5, s4, 0
	bnez a5, 28f
	j 29f
28:
210:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 210b
29:
	addi s6, s4, 0
	addi a0, s0, 1024
	call {vg_sha512_init}
	addi a1, zero, 0
	addi a2, s0, 2047
	addi a2, a2, 1
	addi a3, s6, 72
	addi a0, s0, 1024
	call {vg_sha512_update}
	addi a1, s6, 72
	addi a0, s0, 1024
	addi a2, s0, 1280
	call {vg_sha512_finalize}
	addi a1, s0, 0
	addi t5, zero, 1024
	addi t0, zero, 0
211:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 211b
	add a1, s0, s1
	sub a1, a1, s4
	addi a1, a1, -66
	addi t1, zero, 1
	sb t1, 0(a1)
	addi a1, a1, 1
	addi t6, sp, 128
	ld a4, 72(t6)
	addi a5, s4, 0
	bnez a5, 212f
	j 213f
212:
214:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 214b
213:
	addi a4, s0, 1280
	add a1, s0, s1
	addi a1, a1, -65
	addi a5, zero, 64
215:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 215b
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
216:
	addi a0, s0, 1024
	call {vg_sha512_init}
	addi a0, s0, 1024
	addi a1, zero, 0
	addi a2, s6, 0
	addi a3, s7, 0
	call {vg_sha512_update}
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
	call {vg_sha512_update}
	addi a0, s0, 1024
	addi a1, s7, 4
	addi a2, s0, 1280
	call {vg_sha512_finalize}
	addi a4, s0, 1280
	add a5, s8, s11
	sub t1, s9, s11
	addi a6, zero, 64
	sub t2, t1, a6
	srli t3, t2, 63
	addi t4, zero, 0
	sub t3, t4, t3
	and t2, t2, t3
	add a6, a6, t2
217:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t2, t2, t1
	sb t2, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 217b
	addi s10, s10, 1
	addi s11, s11, 64
	sub t1, s11, s9
	srli t1, t1, 63
	bnez t1, 216b
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
	ld t1, 96(t6)
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
	j 25f
24:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
218:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 218b
	addi a0, zero, 0
25:
	j 23f
22:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
219:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 219b
	addi a0, zero, 0
23:
	j 21f
20:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
220:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 220b
	addi a0, zero, 0
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
