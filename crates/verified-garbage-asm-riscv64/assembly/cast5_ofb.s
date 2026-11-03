// The functions of `src/cast5_ofb.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_cast5_ofb:
	.option push
	.option arch, +m, +c
	addi t0, a1, 0
	addi a1, a2, 0
	addi a2, a3, 0
	addi a3, a4, 0
	addi t0, t0, -12
	beqz t0, 20f
	addi sp, sp, -128
	addi t0, sp, 0
	sd s1, 0(t0)
	sd s2, 8(t0)
	sd s3, 16(t0)
	sd s4, 24(t0)
	addi s4, t0, 0
	addi s1, a1, 0
	addi s2, a1, 0
	addi s3, a3, 0
	lbu t0, 0(s2)
	lbu t2, 1(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 4(s2)
	lbu t2, 5(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	addi s2, a2, 0
	andi t0, s2, 3
	beqz t0, 22f
	beqz s3, 24f
26:
	lwu t0, 32(s4)
	sw t0, 48(s4)
	lwu t0, 36(s4)
	sw t0, 52(s4)
	sd s0, 56(s4)
	sd s5, 64(s4)
	sd s6, 72(s4)
	sd s7, 80(s4)
	sd s8, 88(s4)
	sd s9, 96(s4)
	sd s10, 104(s4)
	sd s11, 112(s4)
	sd ra, 120(s4)
	addi a2, s4, 48
	addi a3, s1, 0
	addi a4, s2, 0
	addi s11, s3, 0
	addi ra, s4, 0
	lla t4, {VG_CAST5_S1234}
	addi a1, zero, 16
	lbu a6, 0(a2)
	slli a6, a6, 24
	lbu t0, 1(a2)
	slli t0, t0, 16
	or a6, a6, t0
	lbu t0, 2(a2)
	slli t0, t0, 8
	or a6, a6, t0
	lbu t0, 3(a2)
	or a6, a6, t0
	lbu a7, 4(a2)
	slli a7, a7, 24
	lbu t0, 5(a2)
	slli t0, t0, 16
	or a7, a7, t0
	lbu t0, 6(a2)
	slli t0, t0, 8
	or a7, a7, t0
	lbu t0, 7(a2)
	or a7, a7, t0
	addi s8, a0, 0
	addi s9, a1, 0
	addi s10, zero, 1
27:
	beqz s10, 28f
	addi t0, s10, -1
	beqz t0, 210f
	lbu t5, 0(s8)
	lbu t0, 1(s8)
	slli t0, t0, 8
	or t5, t5, t0
	lbu t0, 2(s8)
	slli t0, t0, 16
	or t5, t5, t0
	lbu t0, 3(s8)
	slli t0, t0, 24
	or t5, t5, t0
	xor t5, t5, a7
	j 211f
210:
	lbu t5, 0(s8)
	lbu t0, 1(s8)
	slli t0, t0, 8
	or t5, t5, t0
	lbu t0, 2(s8)
	slli t0, t0, 16
	or t5, t5, t0
	lbu t0, 3(s8)
	slli t0, t0, 24
	or t5, t5, t0
	add t5, t5, a7
211:
	j 29f
28:
	lbu t5, 0(s8)
	lbu t0, 1(s8)
	slli t0, t0, 8
	or t5, t5, t0
	lbu t0, 2(s8)
	slli t0, t0, 16
	or t5, t5, t0
	lbu t0, 3(s8)
	slli t0, t0, 24
	or t5, t5, t0
	sub t5, t5, a7
29:
	lbu t6, 64(s8)
	addi t1, zero, 32
	sub t1, t1, t6
	srlw t1, t5, t1
	sllw t5, t5, t6
	or t5, t5, t1
	andi s0, t5, 255
	srliw s1, t5, 8
	andi s1, s1, 255
	srliw s2, t5, 16
	andi s2, s2, 255
	srliw s3, t5, 24
	slli t0, s0, 63
	srai t0, t0, 63
	srli t0, t0, 32
	slli a5, s1, 63
	srai a5, a5, 63
	slli a5, a5, 32
	or t0, t0, a5
	slli t1, s0, 62
	srai t1, t1, 63
	srli t1, t1, 32
	slli a5, s1, 62
	srai a5, a5, 63
	slli a5, a5, 32
	or t1, t1, a5
	slli t2, s0, 61
	srai t2, t2, 63
	srli t2, t2, 32
	slli a5, s1, 61
	srai a5, a5, 63
	slli a5, a5, 32
	or t2, t2, a5
	slli t5, s0, 60
	srai t5, t5, 63
	srli t5, t5, 32
	slli a5, s1, 60
	srai a5, a5, 63
	slli a5, a5, 32
	or t5, t5, a5
	srli s0, s0, 4
	addi s0, s0, -17
	srli s1, s1, 4
	addi s1, s1, -17
	addi t3, t4, 2047
	addi t3, t3, 2047
	addi t3, t3, 2
212:
	addi t3, t3, -256
	addi s0, s0, 1
	addi s1, s1, 1
	ld s5, 0(t3)
	ld s6, 16(t3)
	xor s6, s6, s5
	and s6, s6, t0
	xor s5, s5, s6
	ld s6, 32(t3)
	ld a5, 48(t3)
	xor a5, a5, s6
	and a5, a5, t0
	xor s6, s6, a5
	xor s6, s6, s5
	and s6, s6, t1
	xor s5, s5, s6
	ld s6, 64(t3)
	ld a5, 80(t3)
	xor a5, a5, s6
	and a5, a5, t0
	xor s6, s6, a5
	ld a5, 96(t3)
	ld t6, 112(t3)
	xor t6, t6, a5
	and t6, t6, t0
	xor a5, a5, t6
	xor a5, a5, s6
	and a5, a5, t1
	xor s6, s6, a5
	xor s6, s6, s5
	and s6, s6, t2
	xor s5, s5, s6
	ld s6, 128(t3)
	ld a5, 144(t3)
	xor a5, a5, s6
	and a5, a5, t0
	xor s6, s6, a5
	ld a5, 160(t3)
	ld t6, 176(t3)
	xor t6, t6, a5
	and t6, t6, t0
	xor a5, a5, t6
	xor a5, a5, s6
	and a5, a5, t1
	xor s6, s6, a5
	ld a5, 192(t3)
	ld t6, 208(t3)
	xor t6, t6, a5
	and t6, t6, t0
	xor a5, a5, t6
	ld t6, 224(t3)
	ld s7, 240(t3)
	xor s7, s7, t6
	and s7, s7, t0
	xor t6, t6, s7
	xor t6, t6, a5
	and t6, t6, t1
	xor a5, a5, t6
	xor a5, a5, s6
	and a5, a5, t2
	xor s6, s6, a5
	xor s6, s6, s5
	and s6, s6, t5
	xor s5, s5, s6
	srli s6, s0, 32
	srai a5, s1, 63
	slli a5, a5, 32
	or s6, s6, a5
	xor s5, s5, s4
	and s5, s5, s6
	xor s4, s4, s5
	bne t3, t4, 212b
	srli s5, s4, 32
	slli s4, s4, 32
	srli s4, s4, 32
	slli t0, s2, 63
	srai t0, t0, 63
	srli t0, t0, 32
	slli a5, s3, 63
	srai a5, a5, 63
	slli a5, a5, 32
	or t0, t0, a5
	slli t1, s2, 62
	srai t1, t1, 63
	srli t1, t1, 32
	slli a5, s3, 62
	srai a5, a5, 63
	slli a5, a5, 32
	or t1, t1, a5
	slli t2, s2, 61
	srai t2, t2, 63
	srli t2, t2, 32
	slli a5, s3, 61
	srai a5, a5, 63
	slli a5, a5, 32
	or t2, t2, a5
	slli t5, s2, 60
	srai t5, t5, 63
	srli t5, t5, 32
	slli a5, s3, 60
	srai a5, a5, 63
	slli a5, a5, 32
	or t5, t5, a5
	srli s2, s2, 4
	addi s2, s2, -17
	srli s3, s3, 4
	addi s3, s3, -17
	addi t3, t4, 2047
	addi t3, t3, 2047
	addi t3, t3, 2
213:
	addi t3, t3, -256
	addi s2, s2, 1
	addi s3, s3, 1
	ld s0, 8(t3)
	ld s1, 24(t3)
	xor s1, s1, s0
	and s1, s1, t0
	xor s0, s0, s1
	ld s1, 40(t3)
	ld a5, 56(t3)
	xor a5, a5, s1
	and a5, a5, t0
	xor s1, s1, a5
	xor s1, s1, s0
	and s1, s1, t1
	xor s0, s0, s1
	ld s1, 72(t3)
	ld a5, 88(t3)
	xor a5, a5, s1
	and a5, a5, t0
	xor s1, s1, a5
	ld a5, 104(t3)
	ld t6, 120(t3)
	xor t6, t6, a5
	and t6, t6, t0
	xor a5, a5, t6
	xor a5, a5, s1
	and a5, a5, t1
	xor s1, s1, a5
	xor s1, s1, s0
	and s1, s1, t2
	xor s0, s0, s1
	ld s1, 136(t3)
	ld a5, 152(t3)
	xor a5, a5, s1
	and a5, a5, t0
	xor s1, s1, a5
	ld a5, 168(t3)
	ld t6, 184(t3)
	xor t6, t6, a5
	and t6, t6, t0
	xor a5, a5, t6
	xor a5, a5, s1
	and a5, a5, t1
	xor s1, s1, a5
	ld a5, 200(t3)
	ld t6, 216(t3)
	xor t6, t6, a5
	and t6, t6, t0
	xor a5, a5, t6
	ld t6, 232(t3)
	ld s7, 248(t3)
	xor s7, s7, t6
	and s7, s7, t0
	xor t6, t6, s7
	xor t6, t6, a5
	and t6, t6, t1
	xor a5, a5, t6
	xor a5, a5, s1
	and a5, a5, t2
	xor s1, s1, a5
	xor s1, s1, s0
	and s1, s1, t5
	xor s0, s0, s1
	srli s1, s2, 32
	srai a5, s3, 63
	slli a5, a5, 32
	or s1, s1, a5
	xor s0, s0, s6
	and s0, s0, s1
	xor s6, s6, s0
	bne t3, t4, 213b
	srli s7, s6, 32
	slli s6, s6, 32
	srli s6, s6, 32
	beqz s10, 214f
	addi t0, s10, -1
	beqz t0, 216f
	sub t5, s7, s6
	add t5, t5, s5
	xor t5, t5, s4
	j 217f
216:
	xor t5, s7, s6
	sub t5, t5, s5
	add t5, t5, s4
217:
	j 215f
214:
	add t5, s7, s6
	xor t5, t5, s5
	sub t5, t5, s4
215:
	xor t5, t5, a6
	addi a6, a7, 0
	addi a7, t5, 0
	addi s8, s8, 4
	addi t0, s10, -2
	beqz t0, 218f
	addi s10, s10, 1
	j 219f
218:
	addi s10, zero, 0
219:
	addi s9, s9, -1
	bnez s9, 27b
	srli t0, a7, 24
	sb t0, 0(a2)
	srli t0, a7, 16
	sb t0, 1(a2)
	srli t0, a7, 8
	sb t0, 2(a2)
	srli t0, a7, 0
	sb t0, 3(a2)
	srli t0, a6, 24
	sb t0, 4(a2)
	srli t0, a6, 16
	sb t0, 5(a2)
	srli t0, a6, 8
	sb t0, 6(a2)
	srli t0, a6, 0
	sb t0, 7(a2)
	addi s1, a3, 0
	addi s2, a4, 0
	addi s3, s11, 0
	addi s4, ra, 0
	ld s0, 56(s4)
	ld s5, 64(s4)
	ld s6, 72(s4)
	ld s7, 80(s4)
	ld s8, 88(s4)
	ld s9, 96(s4)
	ld s10, 104(s4)
	ld s11, 112(s4)
	ld ra, 120(s4)
	lwu t0, 48(s4)
	sw t0, 32(s4)
	lwu t0, 52(s4)
	sw t0, 36(s4)
	lbu t0, 0(s2)
	lbu t2, 1(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 48(s4)
	xor t0, t0, t1
	sb t0, 0(s2)
	srli t2, t0, 8
	sb t2, 1(s2)
	srli t2, t0, 16
	sb t2, 2(s2)
	srli t2, t0, 24
	sb t2, 3(s2)
	lbu t0, 4(s2)
	lbu t2, 5(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 52(s4)
	xor t0, t0, t1
	sb t0, 4(s2)
	srli t2, t0, 8
	sb t2, 5(s2)
	srli t2, t0, 16
	sb t2, 6(s2)
	srli t2, t0, 24
	sb t2, 7(s2)
	addi s2, s2, 8
	addi s3, s3, -1
	bnez s3, 26b
	j 25f
24:
25:
	j 23f
22:
	beqz s3, 220f
222:
	lwu t0, 32(s4)
	sw t0, 48(s4)
	lwu t0, 36(s4)
	sw t0, 52(s4)
	sd s0, 56(s4)
	sd s5, 64(s4)
	sd s6, 72(s4)
	sd s7, 80(s4)
	sd s8, 88(s4)
	sd s9, 96(s4)
	sd s10, 104(s4)
	sd s11, 112(s4)
	sd ra, 120(s4)
	addi a2, s4, 48
	addi a3, s1, 0
	addi a4, s2, 0
	addi s11, s3, 0
	addi ra, s4, 0
	lla t4, {VG_CAST5_S1234}
	addi a1, zero, 16
	lbu a6, 0(a2)
	slli a6, a6, 24
	lbu t0, 1(a2)
	slli t0, t0, 16
	or a6, a6, t0
	lbu t0, 2(a2)
	slli t0, t0, 8
	or a6, a6, t0
	lbu t0, 3(a2)
	or a6, a6, t0
	lbu a7, 4(a2)
	slli a7, a7, 24
	lbu t0, 5(a2)
	slli t0, t0, 16
	or a7, a7, t0
	lbu t0, 6(a2)
	slli t0, t0, 8
	or a7, a7, t0
	lbu t0, 7(a2)
	or a7, a7, t0
	addi s8, a0, 0
	addi s9, a1, 0
	addi s10, zero, 1
223:
	beqz s10, 224f
	addi t0, s10, -1
	beqz t0, 226f
	lbu t5, 0(s8)
	lbu t0, 1(s8)
	slli t0, t0, 8
	or t5, t5, t0
	lbu t0, 2(s8)
	slli t0, t0, 16
	or t5, t5, t0
	lbu t0, 3(s8)
	slli t0, t0, 24
	or t5, t5, t0
	xor t5, t5, a7
	j 227f
226:
	lbu t5, 0(s8)
	lbu t0, 1(s8)
	slli t0, t0, 8
	or t5, t5, t0
	lbu t0, 2(s8)
	slli t0, t0, 16
	or t5, t5, t0
	lbu t0, 3(s8)
	slli t0, t0, 24
	or t5, t5, t0
	add t5, t5, a7
227:
	j 225f
224:
	lbu t5, 0(s8)
	lbu t0, 1(s8)
	slli t0, t0, 8
	or t5, t5, t0
	lbu t0, 2(s8)
	slli t0, t0, 16
	or t5, t5, t0
	lbu t0, 3(s8)
	slli t0, t0, 24
	or t5, t5, t0
	sub t5, t5, a7
225:
	lbu t6, 64(s8)
	addi t1, zero, 32
	sub t1, t1, t6
	srlw t1, t5, t1
	sllw t5, t5, t6
	or t5, t5, t1
	andi s0, t5, 255
	srliw s1, t5, 8
	andi s1, s1, 255
	srliw s2, t5, 16
	andi s2, s2, 255
	srliw s3, t5, 24
	slli t0, s0, 63
	srai t0, t0, 63
	srli t0, t0, 32
	slli a5, s1, 63
	srai a5, a5, 63
	slli a5, a5, 32
	or t0, t0, a5
	slli t1, s0, 62
	srai t1, t1, 63
	srli t1, t1, 32
	slli a5, s1, 62
	srai a5, a5, 63
	slli a5, a5, 32
	or t1, t1, a5
	slli t2, s0, 61
	srai t2, t2, 63
	srli t2, t2, 32
	slli a5, s1, 61
	srai a5, a5, 63
	slli a5, a5, 32
	or t2, t2, a5
	slli t5, s0, 60
	srai t5, t5, 63
	srli t5, t5, 32
	slli a5, s1, 60
	srai a5, a5, 63
	slli a5, a5, 32
	or t5, t5, a5
	srli s0, s0, 4
	addi s0, s0, -17
	srli s1, s1, 4
	addi s1, s1, -17
	addi t3, t4, 2047
	addi t3, t3, 2047
	addi t3, t3, 2
228:
	addi t3, t3, -256
	addi s0, s0, 1
	addi s1, s1, 1
	ld s5, 0(t3)
	ld s6, 16(t3)
	xor s6, s6, s5
	and s6, s6, t0
	xor s5, s5, s6
	ld s6, 32(t3)
	ld a5, 48(t3)
	xor a5, a5, s6
	and a5, a5, t0
	xor s6, s6, a5
	xor s6, s6, s5
	and s6, s6, t1
	xor s5, s5, s6
	ld s6, 64(t3)
	ld a5, 80(t3)
	xor a5, a5, s6
	and a5, a5, t0
	xor s6, s6, a5
	ld a5, 96(t3)
	ld t6, 112(t3)
	xor t6, t6, a5
	and t6, t6, t0
	xor a5, a5, t6
	xor a5, a5, s6
	and a5, a5, t1
	xor s6, s6, a5
	xor s6, s6, s5
	and s6, s6, t2
	xor s5, s5, s6
	ld s6, 128(t3)
	ld a5, 144(t3)
	xor a5, a5, s6
	and a5, a5, t0
	xor s6, s6, a5
	ld a5, 160(t3)
	ld t6, 176(t3)
	xor t6, t6, a5
	and t6, t6, t0
	xor a5, a5, t6
	xor a5, a5, s6
	and a5, a5, t1
	xor s6, s6, a5
	ld a5, 192(t3)
	ld t6, 208(t3)
	xor t6, t6, a5
	and t6, t6, t0
	xor a5, a5, t6
	ld t6, 224(t3)
	ld s7, 240(t3)
	xor s7, s7, t6
	and s7, s7, t0
	xor t6, t6, s7
	xor t6, t6, a5
	and t6, t6, t1
	xor a5, a5, t6
	xor a5, a5, s6
	and a5, a5, t2
	xor s6, s6, a5
	xor s6, s6, s5
	and s6, s6, t5
	xor s5, s5, s6
	srli s6, s0, 32
	srai a5, s1, 63
	slli a5, a5, 32
	or s6, s6, a5
	xor s5, s5, s4
	and s5, s5, s6
	xor s4, s4, s5
	bne t3, t4, 228b
	srli s5, s4, 32
	slli s4, s4, 32
	srli s4, s4, 32
	slli t0, s2, 63
	srai t0, t0, 63
	srli t0, t0, 32
	slli a5, s3, 63
	srai a5, a5, 63
	slli a5, a5, 32
	or t0, t0, a5
	slli t1, s2, 62
	srai t1, t1, 63
	srli t1, t1, 32
	slli a5, s3, 62
	srai a5, a5, 63
	slli a5, a5, 32
	or t1, t1, a5
	slli t2, s2, 61
	srai t2, t2, 63
	srli t2, t2, 32
	slli a5, s3, 61
	srai a5, a5, 63
	slli a5, a5, 32
	or t2, t2, a5
	slli t5, s2, 60
	srai t5, t5, 63
	srli t5, t5, 32
	slli a5, s3, 60
	srai a5, a5, 63
	slli a5, a5, 32
	or t5, t5, a5
	srli s2, s2, 4
	addi s2, s2, -17
	srli s3, s3, 4
	addi s3, s3, -17
	addi t3, t4, 2047
	addi t3, t3, 2047
	addi t3, t3, 2
229:
	addi t3, t3, -256
	addi s2, s2, 1
	addi s3, s3, 1
	ld s0, 8(t3)
	ld s1, 24(t3)
	xor s1, s1, s0
	and s1, s1, t0
	xor s0, s0, s1
	ld s1, 40(t3)
	ld a5, 56(t3)
	xor a5, a5, s1
	and a5, a5, t0
	xor s1, s1, a5
	xor s1, s1, s0
	and s1, s1, t1
	xor s0, s0, s1
	ld s1, 72(t3)
	ld a5, 88(t3)
	xor a5, a5, s1
	and a5, a5, t0
	xor s1, s1, a5
	ld a5, 104(t3)
	ld t6, 120(t3)
	xor t6, t6, a5
	and t6, t6, t0
	xor a5, a5, t6
	xor a5, a5, s1
	and a5, a5, t1
	xor s1, s1, a5
	xor s1, s1, s0
	and s1, s1, t2
	xor s0, s0, s1
	ld s1, 136(t3)
	ld a5, 152(t3)
	xor a5, a5, s1
	and a5, a5, t0
	xor s1, s1, a5
	ld a5, 168(t3)
	ld t6, 184(t3)
	xor t6, t6, a5
	and t6, t6, t0
	xor a5, a5, t6
	xor a5, a5, s1
	and a5, a5, t1
	xor s1, s1, a5
	ld a5, 200(t3)
	ld t6, 216(t3)
	xor t6, t6, a5
	and t6, t6, t0
	xor a5, a5, t6
	ld t6, 232(t3)
	ld s7, 248(t3)
	xor s7, s7, t6
	and s7, s7, t0
	xor t6, t6, s7
	xor t6, t6, a5
	and t6, t6, t1
	xor a5, a5, t6
	xor a5, a5, s1
	and a5, a5, t2
	xor s1, s1, a5
	xor s1, s1, s0
	and s1, s1, t5
	xor s0, s0, s1
	srli s1, s2, 32
	srai a5, s3, 63
	slli a5, a5, 32
	or s1, s1, a5
	xor s0, s0, s6
	and s0, s0, s1
	xor s6, s6, s0
	bne t3, t4, 229b
	srli s7, s6, 32
	slli s6, s6, 32
	srli s6, s6, 32
	beqz s10, 230f
	addi t0, s10, -1
	beqz t0, 232f
	sub t5, s7, s6
	add t5, t5, s5
	xor t5, t5, s4
	j 233f
232:
	xor t5, s7, s6
	sub t5, t5, s5
	add t5, t5, s4
233:
	j 231f
230:
	add t5, s7, s6
	xor t5, t5, s5
	sub t5, t5, s4
231:
	xor t5, t5, a6
	addi a6, a7, 0
	addi a7, t5, 0
	addi s8, s8, 4
	addi t0, s10, -2
	beqz t0, 234f
	addi s10, s10, 1
	j 235f
234:
	addi s10, zero, 0
235:
	addi s9, s9, -1
	bnez s9, 223b
	srli t0, a7, 24
	sb t0, 0(a2)
	srli t0, a7, 16
	sb t0, 1(a2)
	srli t0, a7, 8
	sb t0, 2(a2)
	srli t0, a7, 0
	sb t0, 3(a2)
	srli t0, a6, 24
	sb t0, 4(a2)
	srli t0, a6, 16
	sb t0, 5(a2)
	srli t0, a6, 8
	sb t0, 6(a2)
	srli t0, a6, 0
	sb t0, 7(a2)
	addi s1, a3, 0
	addi s2, a4, 0
	addi s3, s11, 0
	addi s4, ra, 0
	ld s0, 56(s4)
	ld s5, 64(s4)
	ld s6, 72(s4)
	ld s7, 80(s4)
	ld s8, 88(s4)
	ld s9, 96(s4)
	ld s10, 104(s4)
	ld s11, 112(s4)
	ld ra, 120(s4)
	lwu t0, 48(s4)
	sw t0, 32(s4)
	lwu t0, 52(s4)
	sw t0, 36(s4)
	lwu t0, 0(s2)
	lwu t1, 48(s4)
	xor t0, t0, t1
	sw t0, 0(s2)
	lwu t0, 4(s2)
	lwu t1, 52(s4)
	xor t0, t0, t1
	sw t0, 4(s2)
	addi s2, s2, 8
	addi s3, s3, -1
	bnez s3, 222b
	j 221f
220:
221:
23:
	addi s2, s1, 0
	lwu t0, 32(s4)
	sb t0, 0(s2)
	srli t2, t0, 8
	sb t2, 1(s2)
	srli t2, t0, 16
	sb t2, 2(s2)
	srli t2, t0, 24
	sb t2, 3(s2)
	lwu t0, 36(s4)
	sb t0, 4(s2)
	srli t2, t0, 8
	sb t2, 5(s2)
	srli t2, t0, 16
	sb t2, 6(s2)
	srli t2, t0, 24
	sb t2, 7(s2)
	addi t3, s4, 0
	ld s1, 0(t3)
	ld s2, 8(t3)
	ld s3, 16(t3)
	ld s4, 24(t3)
	addi t0, zero, 0
	addi t1, t3, 0
	addi t2, zero, 16
236:
	sd t0, 0(t1)
	addi t1, t1, 8
	addi t2, t2, -1
	bnez t2, 236b
	addi sp, sp, 128
	j 21f
20:
	addi sp, sp, -128
	addi t0, sp, 0
	sd s1, 0(t0)
	sd s2, 8(t0)
	sd s3, 16(t0)
	sd s4, 24(t0)
	addi s4, t0, 0
	addi s1, a1, 0
	addi s2, a1, 0
	addi s3, a3, 0
	lbu t0, 0(s2)
	lbu t2, 1(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 4(s2)
	lbu t2, 5(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	addi s2, a2, 0
	andi t0, s2, 3
	beqz t0, 237f
	beqz s3, 239f
241:
	lwu t0, 32(s4)
	sw t0, 48(s4)
	lwu t0, 36(s4)
	sw t0, 52(s4)
	sd s0, 56(s4)
	sd s5, 64(s4)
	sd s6, 72(s4)
	sd s7, 80(s4)
	sd s8, 88(s4)
	sd s9, 96(s4)
	sd s10, 104(s4)
	sd s11, 112(s4)
	sd ra, 120(s4)
	addi a2, s4, 48
	addi a3, s1, 0
	addi a4, s2, 0
	addi s11, s3, 0
	addi ra, s4, 0
	lla t4, {VG_CAST5_S1234}
	addi a1, zero, 12
	lbu a6, 0(a2)
	slli a6, a6, 24
	lbu t0, 1(a2)
	slli t0, t0, 16
	or a6, a6, t0
	lbu t0, 2(a2)
	slli t0, t0, 8
	or a6, a6, t0
	lbu t0, 3(a2)
	or a6, a6, t0
	lbu a7, 4(a2)
	slli a7, a7, 24
	lbu t0, 5(a2)
	slli t0, t0, 16
	or a7, a7, t0
	lbu t0, 6(a2)
	slli t0, t0, 8
	or a7, a7, t0
	lbu t0, 7(a2)
	or a7, a7, t0
	addi s8, a0, 0
	addi s9, a1, 0
	addi s10, zero, 1
242:
	beqz s10, 243f
	addi t0, s10, -1
	beqz t0, 245f
	lbu t5, 0(s8)
	lbu t0, 1(s8)
	slli t0, t0, 8
	or t5, t5, t0
	lbu t0, 2(s8)
	slli t0, t0, 16
	or t5, t5, t0
	lbu t0, 3(s8)
	slli t0, t0, 24
	or t5, t5, t0
	xor t5, t5, a7
	j 246f
245:
	lbu t5, 0(s8)
	lbu t0, 1(s8)
	slli t0, t0, 8
	or t5, t5, t0
	lbu t0, 2(s8)
	slli t0, t0, 16
	or t5, t5, t0
	lbu t0, 3(s8)
	slli t0, t0, 24
	or t5, t5, t0
	add t5, t5, a7
246:
	j 244f
243:
	lbu t5, 0(s8)
	lbu t0, 1(s8)
	slli t0, t0, 8
	or t5, t5, t0
	lbu t0, 2(s8)
	slli t0, t0, 16
	or t5, t5, t0
	lbu t0, 3(s8)
	slli t0, t0, 24
	or t5, t5, t0
	sub t5, t5, a7
244:
	lbu t6, 64(s8)
	addi t1, zero, 32
	sub t1, t1, t6
	srlw t1, t5, t1
	sllw t5, t5, t6
	or t5, t5, t1
	andi s0, t5, 255
	srliw s1, t5, 8
	andi s1, s1, 255
	srliw s2, t5, 16
	andi s2, s2, 255
	srliw s3, t5, 24
	slli t0, s0, 63
	srai t0, t0, 63
	srli t0, t0, 32
	slli a5, s1, 63
	srai a5, a5, 63
	slli a5, a5, 32
	or t0, t0, a5
	slli t1, s0, 62
	srai t1, t1, 63
	srli t1, t1, 32
	slli a5, s1, 62
	srai a5, a5, 63
	slli a5, a5, 32
	or t1, t1, a5
	slli t2, s0, 61
	srai t2, t2, 63
	srli t2, t2, 32
	slli a5, s1, 61
	srai a5, a5, 63
	slli a5, a5, 32
	or t2, t2, a5
	slli t5, s0, 60
	srai t5, t5, 63
	srli t5, t5, 32
	slli a5, s1, 60
	srai a5, a5, 63
	slli a5, a5, 32
	or t5, t5, a5
	srli s0, s0, 4
	addi s0, s0, -17
	srli s1, s1, 4
	addi s1, s1, -17
	addi t3, t4, 2047
	addi t3, t3, 2047
	addi t3, t3, 2
247:
	addi t3, t3, -256
	addi s0, s0, 1
	addi s1, s1, 1
	ld s5, 0(t3)
	ld s6, 16(t3)
	xor s6, s6, s5
	and s6, s6, t0
	xor s5, s5, s6
	ld s6, 32(t3)
	ld a5, 48(t3)
	xor a5, a5, s6
	and a5, a5, t0
	xor s6, s6, a5
	xor s6, s6, s5
	and s6, s6, t1
	xor s5, s5, s6
	ld s6, 64(t3)
	ld a5, 80(t3)
	xor a5, a5, s6
	and a5, a5, t0
	xor s6, s6, a5
	ld a5, 96(t3)
	ld t6, 112(t3)
	xor t6, t6, a5
	and t6, t6, t0
	xor a5, a5, t6
	xor a5, a5, s6
	and a5, a5, t1
	xor s6, s6, a5
	xor s6, s6, s5
	and s6, s6, t2
	xor s5, s5, s6
	ld s6, 128(t3)
	ld a5, 144(t3)
	xor a5, a5, s6
	and a5, a5, t0
	xor s6, s6, a5
	ld a5, 160(t3)
	ld t6, 176(t3)
	xor t6, t6, a5
	and t6, t6, t0
	xor a5, a5, t6
	xor a5, a5, s6
	and a5, a5, t1
	xor s6, s6, a5
	ld a5, 192(t3)
	ld t6, 208(t3)
	xor t6, t6, a5
	and t6, t6, t0
	xor a5, a5, t6
	ld t6, 224(t3)
	ld s7, 240(t3)
	xor s7, s7, t6
	and s7, s7, t0
	xor t6, t6, s7
	xor t6, t6, a5
	and t6, t6, t1
	xor a5, a5, t6
	xor a5, a5, s6
	and a5, a5, t2
	xor s6, s6, a5
	xor s6, s6, s5
	and s6, s6, t5
	xor s5, s5, s6
	srli s6, s0, 32
	srai a5, s1, 63
	slli a5, a5, 32
	or s6, s6, a5
	xor s5, s5, s4
	and s5, s5, s6
	xor s4, s4, s5
	bne t3, t4, 247b
	srli s5, s4, 32
	slli s4, s4, 32
	srli s4, s4, 32
	slli t0, s2, 63
	srai t0, t0, 63
	srli t0, t0, 32
	slli a5, s3, 63
	srai a5, a5, 63
	slli a5, a5, 32
	or t0, t0, a5
	slli t1, s2, 62
	srai t1, t1, 63
	srli t1, t1, 32
	slli a5, s3, 62
	srai a5, a5, 63
	slli a5, a5, 32
	or t1, t1, a5
	slli t2, s2, 61
	srai t2, t2, 63
	srli t2, t2, 32
	slli a5, s3, 61
	srai a5, a5, 63
	slli a5, a5, 32
	or t2, t2, a5
	slli t5, s2, 60
	srai t5, t5, 63
	srli t5, t5, 32
	slli a5, s3, 60
	srai a5, a5, 63
	slli a5, a5, 32
	or t5, t5, a5
	srli s2, s2, 4
	addi s2, s2, -17
	srli s3, s3, 4
	addi s3, s3, -17
	addi t3, t4, 2047
	addi t3, t3, 2047
	addi t3, t3, 2
248:
	addi t3, t3, -256
	addi s2, s2, 1
	addi s3, s3, 1
	ld s0, 8(t3)
	ld s1, 24(t3)
	xor s1, s1, s0
	and s1, s1, t0
	xor s0, s0, s1
	ld s1, 40(t3)
	ld a5, 56(t3)
	xor a5, a5, s1
	and a5, a5, t0
	xor s1, s1, a5
	xor s1, s1, s0
	and s1, s1, t1
	xor s0, s0, s1
	ld s1, 72(t3)
	ld a5, 88(t3)
	xor a5, a5, s1
	and a5, a5, t0
	xor s1, s1, a5
	ld a5, 104(t3)
	ld t6, 120(t3)
	xor t6, t6, a5
	and t6, t6, t0
	xor a5, a5, t6
	xor a5, a5, s1
	and a5, a5, t1
	xor s1, s1, a5
	xor s1, s1, s0
	and s1, s1, t2
	xor s0, s0, s1
	ld s1, 136(t3)
	ld a5, 152(t3)
	xor a5, a5, s1
	and a5, a5, t0
	xor s1, s1, a5
	ld a5, 168(t3)
	ld t6, 184(t3)
	xor t6, t6, a5
	and t6, t6, t0
	xor a5, a5, t6
	xor a5, a5, s1
	and a5, a5, t1
	xor s1, s1, a5
	ld a5, 200(t3)
	ld t6, 216(t3)
	xor t6, t6, a5
	and t6, t6, t0
	xor a5, a5, t6
	ld t6, 232(t3)
	ld s7, 248(t3)
	xor s7, s7, t6
	and s7, s7, t0
	xor t6, t6, s7
	xor t6, t6, a5
	and t6, t6, t1
	xor a5, a5, t6
	xor a5, a5, s1
	and a5, a5, t2
	xor s1, s1, a5
	xor s1, s1, s0
	and s1, s1, t5
	xor s0, s0, s1
	srli s1, s2, 32
	srai a5, s3, 63
	slli a5, a5, 32
	or s1, s1, a5
	xor s0, s0, s6
	and s0, s0, s1
	xor s6, s6, s0
	bne t3, t4, 248b
	srli s7, s6, 32
	slli s6, s6, 32
	srli s6, s6, 32
	beqz s10, 249f
	addi t0, s10, -1
	beqz t0, 251f
	sub t5, s7, s6
	add t5, t5, s5
	xor t5, t5, s4
	j 252f
251:
	xor t5, s7, s6
	sub t5, t5, s5
	add t5, t5, s4
252:
	j 250f
249:
	add t5, s7, s6
	xor t5, t5, s5
	sub t5, t5, s4
250:
	xor t5, t5, a6
	addi a6, a7, 0
	addi a7, t5, 0
	addi s8, s8, 4
	addi t0, s10, -2
	beqz t0, 253f
	addi s10, s10, 1
	j 254f
253:
	addi s10, zero, 0
254:
	addi s9, s9, -1
	bnez s9, 242b
	srli t0, a7, 24
	sb t0, 0(a2)
	srli t0, a7, 16
	sb t0, 1(a2)
	srli t0, a7, 8
	sb t0, 2(a2)
	srli t0, a7, 0
	sb t0, 3(a2)
	srli t0, a6, 24
	sb t0, 4(a2)
	srli t0, a6, 16
	sb t0, 5(a2)
	srli t0, a6, 8
	sb t0, 6(a2)
	srli t0, a6, 0
	sb t0, 7(a2)
	addi s1, a3, 0
	addi s2, a4, 0
	addi s3, s11, 0
	addi s4, ra, 0
	ld s0, 56(s4)
	ld s5, 64(s4)
	ld s6, 72(s4)
	ld s7, 80(s4)
	ld s8, 88(s4)
	ld s9, 96(s4)
	ld s10, 104(s4)
	ld s11, 112(s4)
	ld ra, 120(s4)
	lwu t0, 48(s4)
	sw t0, 32(s4)
	lwu t0, 52(s4)
	sw t0, 36(s4)
	lbu t0, 0(s2)
	lbu t2, 1(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 48(s4)
	xor t0, t0, t1
	sb t0, 0(s2)
	srli t2, t0, 8
	sb t2, 1(s2)
	srli t2, t0, 16
	sb t2, 2(s2)
	srli t2, t0, 24
	sb t2, 3(s2)
	lbu t0, 4(s2)
	lbu t2, 5(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 52(s4)
	xor t0, t0, t1
	sb t0, 4(s2)
	srli t2, t0, 8
	sb t2, 5(s2)
	srli t2, t0, 16
	sb t2, 6(s2)
	srli t2, t0, 24
	sb t2, 7(s2)
	addi s2, s2, 8
	addi s3, s3, -1
	bnez s3, 241b
	j 240f
239:
240:
	j 238f
237:
	beqz s3, 255f
257:
	lwu t0, 32(s4)
	sw t0, 48(s4)
	lwu t0, 36(s4)
	sw t0, 52(s4)
	sd s0, 56(s4)
	sd s5, 64(s4)
	sd s6, 72(s4)
	sd s7, 80(s4)
	sd s8, 88(s4)
	sd s9, 96(s4)
	sd s10, 104(s4)
	sd s11, 112(s4)
	sd ra, 120(s4)
	addi a2, s4, 48
	addi a3, s1, 0
	addi a4, s2, 0
	addi s11, s3, 0
	addi ra, s4, 0
	lla t4, {VG_CAST5_S1234}
	addi a1, zero, 12
	lbu a6, 0(a2)
	slli a6, a6, 24
	lbu t0, 1(a2)
	slli t0, t0, 16
	or a6, a6, t0
	lbu t0, 2(a2)
	slli t0, t0, 8
	or a6, a6, t0
	lbu t0, 3(a2)
	or a6, a6, t0
	lbu a7, 4(a2)
	slli a7, a7, 24
	lbu t0, 5(a2)
	slli t0, t0, 16
	or a7, a7, t0
	lbu t0, 6(a2)
	slli t0, t0, 8
	or a7, a7, t0
	lbu t0, 7(a2)
	or a7, a7, t0
	addi s8, a0, 0
	addi s9, a1, 0
	addi s10, zero, 1
258:
	beqz s10, 259f
	addi t0, s10, -1
	beqz t0, 261f
	lbu t5, 0(s8)
	lbu t0, 1(s8)
	slli t0, t0, 8
	or t5, t5, t0
	lbu t0, 2(s8)
	slli t0, t0, 16
	or t5, t5, t0
	lbu t0, 3(s8)
	slli t0, t0, 24
	or t5, t5, t0
	xor t5, t5, a7
	j 262f
261:
	lbu t5, 0(s8)
	lbu t0, 1(s8)
	slli t0, t0, 8
	or t5, t5, t0
	lbu t0, 2(s8)
	slli t0, t0, 16
	or t5, t5, t0
	lbu t0, 3(s8)
	slli t0, t0, 24
	or t5, t5, t0
	add t5, t5, a7
262:
	j 260f
259:
	lbu t5, 0(s8)
	lbu t0, 1(s8)
	slli t0, t0, 8
	or t5, t5, t0
	lbu t0, 2(s8)
	slli t0, t0, 16
	or t5, t5, t0
	lbu t0, 3(s8)
	slli t0, t0, 24
	or t5, t5, t0
	sub t5, t5, a7
260:
	lbu t6, 64(s8)
	addi t1, zero, 32
	sub t1, t1, t6
	srlw t1, t5, t1
	sllw t5, t5, t6
	or t5, t5, t1
	andi s0, t5, 255
	srliw s1, t5, 8
	andi s1, s1, 255
	srliw s2, t5, 16
	andi s2, s2, 255
	srliw s3, t5, 24
	slli t0, s0, 63
	srai t0, t0, 63
	srli t0, t0, 32
	slli a5, s1, 63
	srai a5, a5, 63
	slli a5, a5, 32
	or t0, t0, a5
	slli t1, s0, 62
	srai t1, t1, 63
	srli t1, t1, 32
	slli a5, s1, 62
	srai a5, a5, 63
	slli a5, a5, 32
	or t1, t1, a5
	slli t2, s0, 61
	srai t2, t2, 63
	srli t2, t2, 32
	slli a5, s1, 61
	srai a5, a5, 63
	slli a5, a5, 32
	or t2, t2, a5
	slli t5, s0, 60
	srai t5, t5, 63
	srli t5, t5, 32
	slli a5, s1, 60
	srai a5, a5, 63
	slli a5, a5, 32
	or t5, t5, a5
	srli s0, s0, 4
	addi s0, s0, -17
	srli s1, s1, 4
	addi s1, s1, -17
	addi t3, t4, 2047
	addi t3, t3, 2047
	addi t3, t3, 2
263:
	addi t3, t3, -256
	addi s0, s0, 1
	addi s1, s1, 1
	ld s5, 0(t3)
	ld s6, 16(t3)
	xor s6, s6, s5
	and s6, s6, t0
	xor s5, s5, s6
	ld s6, 32(t3)
	ld a5, 48(t3)
	xor a5, a5, s6
	and a5, a5, t0
	xor s6, s6, a5
	xor s6, s6, s5
	and s6, s6, t1
	xor s5, s5, s6
	ld s6, 64(t3)
	ld a5, 80(t3)
	xor a5, a5, s6
	and a5, a5, t0
	xor s6, s6, a5
	ld a5, 96(t3)
	ld t6, 112(t3)
	xor t6, t6, a5
	and t6, t6, t0
	xor a5, a5, t6
	xor a5, a5, s6
	and a5, a5, t1
	xor s6, s6, a5
	xor s6, s6, s5
	and s6, s6, t2
	xor s5, s5, s6
	ld s6, 128(t3)
	ld a5, 144(t3)
	xor a5, a5, s6
	and a5, a5, t0
	xor s6, s6, a5
	ld a5, 160(t3)
	ld t6, 176(t3)
	xor t6, t6, a5
	and t6, t6, t0
	xor a5, a5, t6
	xor a5, a5, s6
	and a5, a5, t1
	xor s6, s6, a5
	ld a5, 192(t3)
	ld t6, 208(t3)
	xor t6, t6, a5
	and t6, t6, t0
	xor a5, a5, t6
	ld t6, 224(t3)
	ld s7, 240(t3)
	xor s7, s7, t6
	and s7, s7, t0
	xor t6, t6, s7
	xor t6, t6, a5
	and t6, t6, t1
	xor a5, a5, t6
	xor a5, a5, s6
	and a5, a5, t2
	xor s6, s6, a5
	xor s6, s6, s5
	and s6, s6, t5
	xor s5, s5, s6
	srli s6, s0, 32
	srai a5, s1, 63
	slli a5, a5, 32
	or s6, s6, a5
	xor s5, s5, s4
	and s5, s5, s6
	xor s4, s4, s5
	bne t3, t4, 263b
	srli s5, s4, 32
	slli s4, s4, 32
	srli s4, s4, 32
	slli t0, s2, 63
	srai t0, t0, 63
	srli t0, t0, 32
	slli a5, s3, 63
	srai a5, a5, 63
	slli a5, a5, 32
	or t0, t0, a5
	slli t1, s2, 62
	srai t1, t1, 63
	srli t1, t1, 32
	slli a5, s3, 62
	srai a5, a5, 63
	slli a5, a5, 32
	or t1, t1, a5
	slli t2, s2, 61
	srai t2, t2, 63
	srli t2, t2, 32
	slli a5, s3, 61
	srai a5, a5, 63
	slli a5, a5, 32
	or t2, t2, a5
	slli t5, s2, 60
	srai t5, t5, 63
	srli t5, t5, 32
	slli a5, s3, 60
	srai a5, a5, 63
	slli a5, a5, 32
	or t5, t5, a5
	srli s2, s2, 4
	addi s2, s2, -17
	srli s3, s3, 4
	addi s3, s3, -17
	addi t3, t4, 2047
	addi t3, t3, 2047
	addi t3, t3, 2
264:
	addi t3, t3, -256
	addi s2, s2, 1
	addi s3, s3, 1
	ld s0, 8(t3)
	ld s1, 24(t3)
	xor s1, s1, s0
	and s1, s1, t0
	xor s0, s0, s1
	ld s1, 40(t3)
	ld a5, 56(t3)
	xor a5, a5, s1
	and a5, a5, t0
	xor s1, s1, a5
	xor s1, s1, s0
	and s1, s1, t1
	xor s0, s0, s1
	ld s1, 72(t3)
	ld a5, 88(t3)
	xor a5, a5, s1
	and a5, a5, t0
	xor s1, s1, a5
	ld a5, 104(t3)
	ld t6, 120(t3)
	xor t6, t6, a5
	and t6, t6, t0
	xor a5, a5, t6
	xor a5, a5, s1
	and a5, a5, t1
	xor s1, s1, a5
	xor s1, s1, s0
	and s1, s1, t2
	xor s0, s0, s1
	ld s1, 136(t3)
	ld a5, 152(t3)
	xor a5, a5, s1
	and a5, a5, t0
	xor s1, s1, a5
	ld a5, 168(t3)
	ld t6, 184(t3)
	xor t6, t6, a5
	and t6, t6, t0
	xor a5, a5, t6
	xor a5, a5, s1
	and a5, a5, t1
	xor s1, s1, a5
	ld a5, 200(t3)
	ld t6, 216(t3)
	xor t6, t6, a5
	and t6, t6, t0
	xor a5, a5, t6
	ld t6, 232(t3)
	ld s7, 248(t3)
	xor s7, s7, t6
	and s7, s7, t0
	xor t6, t6, s7
	xor t6, t6, a5
	and t6, t6, t1
	xor a5, a5, t6
	xor a5, a5, s1
	and a5, a5, t2
	xor s1, s1, a5
	xor s1, s1, s0
	and s1, s1, t5
	xor s0, s0, s1
	srli s1, s2, 32
	srai a5, s3, 63
	slli a5, a5, 32
	or s1, s1, a5
	xor s0, s0, s6
	and s0, s0, s1
	xor s6, s6, s0
	bne t3, t4, 264b
	srli s7, s6, 32
	slli s6, s6, 32
	srli s6, s6, 32
	beqz s10, 265f
	addi t0, s10, -1
	beqz t0, 267f
	sub t5, s7, s6
	add t5, t5, s5
	xor t5, t5, s4
	j 268f
267:
	xor t5, s7, s6
	sub t5, t5, s5
	add t5, t5, s4
268:
	j 266f
265:
	add t5, s7, s6
	xor t5, t5, s5
	sub t5, t5, s4
266:
	xor t5, t5, a6
	addi a6, a7, 0
	addi a7, t5, 0
	addi s8, s8, 4
	addi t0, s10, -2
	beqz t0, 269f
	addi s10, s10, 1
	j 270f
269:
	addi s10, zero, 0
270:
	addi s9, s9, -1
	bnez s9, 258b
	srli t0, a7, 24
	sb t0, 0(a2)
	srli t0, a7, 16
	sb t0, 1(a2)
	srli t0, a7, 8
	sb t0, 2(a2)
	srli t0, a7, 0
	sb t0, 3(a2)
	srli t0, a6, 24
	sb t0, 4(a2)
	srli t0, a6, 16
	sb t0, 5(a2)
	srli t0, a6, 8
	sb t0, 6(a2)
	srli t0, a6, 0
	sb t0, 7(a2)
	addi s1, a3, 0
	addi s2, a4, 0
	addi s3, s11, 0
	addi s4, ra, 0
	ld s0, 56(s4)
	ld s5, 64(s4)
	ld s6, 72(s4)
	ld s7, 80(s4)
	ld s8, 88(s4)
	ld s9, 96(s4)
	ld s10, 104(s4)
	ld s11, 112(s4)
	ld ra, 120(s4)
	lwu t0, 48(s4)
	sw t0, 32(s4)
	lwu t0, 52(s4)
	sw t0, 36(s4)
	lwu t0, 0(s2)
	lwu t1, 48(s4)
	xor t0, t0, t1
	sw t0, 0(s2)
	lwu t0, 4(s2)
	lwu t1, 52(s4)
	xor t0, t0, t1
	sw t0, 4(s2)
	addi s2, s2, 8
	addi s3, s3, -1
	bnez s3, 257b
	j 256f
255:
256:
238:
	addi s2, s1, 0
	lwu t0, 32(s4)
	sb t0, 0(s2)
	srli t2, t0, 8
	sb t2, 1(s2)
	srli t2, t0, 16
	sb t2, 2(s2)
	srli t2, t0, 24
	sb t2, 3(s2)
	lwu t0, 36(s4)
	sb t0, 4(s2)
	srli t2, t0, 8
	sb t2, 5(s2)
	srli t2, t0, 16
	sb t2, 6(s2)
	srli t2, t0, 24
	sb t2, 7(s2)
	addi t3, s4, 0
	ld s1, 0(t3)
	ld s2, 8(t3)
	ld s3, 16(t3)
	ld s4, 24(t3)
	addi t0, zero, 0
	addi t1, t3, 0
	addi t2, zero, 16
271:
	sd t0, 0(t1)
	addi t1, t1, 8
	addi t2, t2, -1
	bnez t2, 271b
	addi sp, sp, 128
21:
	ret
	.option pop
