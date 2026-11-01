// The functions of `src/md5.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_md5_init:
	.option push
	.option arch, +m, +c
	lui t0, 422994
	addiw t0, t0, 769
	sb t0, 0(a0)
	srli t1, t0, 8
	sb t1, 1(a0)
	srli t1, t0, 16
	sb t1, 2(a0)
	srli t1, t0, 24
	sb t1, 3(a0)
	lui t0, 982235
	addiw t0, t0, -1143
	sb t0, 4(a0)
	srli t1, t0, 8
	sb t1, 5(a0)
	srli t1, t0, 16
	sb t1, 6(a0)
	srli t1, t0, 24
	sb t1, 7(a0)
	lui t0, 625582
	addiw t0, t0, -770
	sb t0, 8(a0)
	srli t1, t0, 8
	sb t1, 9(a0)
	srli t1, t0, 16
	sb t1, 10(a0)
	srli t1, t0, 24
	sb t1, 11(a0)
	lui t0, 66341
	addiw t0, t0, 1142
	sb t0, 12(a0)
	srli t1, t0, 8
	sb t1, 13(a0)
	srli t1, t0, 16
	sb t1, 14(a0)
	srli t1, t0, 24
	sb t1, 15(a0)
	ret
	.option pop

vg_md5_update:
	.option push
	.option arch, +m, +c
	addi sp, sp, -144
	addi t0, sp, 0
	sd ra, 80(t0)
	sd s1, 88(t0)
	sd s2, 96(t0)
	sd s3, 104(t0)
	sd s4, 112(t0)
	sd s5, 120(t0)
	sd s6, 128(t0)
	addi s1, a0, 0
	addi s2, t0, 0
	addi s3, a2, 0
	addi s4, a3, 0
	andi s5, a1, 63
	beqz s4, 20f
22:
	addi t0, zero, 0
	beqz s5, 23f
	addi t2, zero, 64
	sub t2, t2, s5
	srli t1, s4, 6
	beqz t1, 25f
	j 26f
25:
	add t1, s4, s5
	srli t1, t1, 6
	beqz t1, 27f
	j 28f
27:
	addi t2, s4, 0
28:
26:
	sub s4, s4, t2
29:
	lbu t1, 0(s3)
	add t3, s1, s5
	sb t1, 16(t3)
	addi s3, s3, 1
	addi s5, s5, 1
	addi t2, t2, -1
	bnez t2, 29b
	addi t1, s5, -64
	beqz t1, 210f
	j 211f
210:
	addi a1, s1, 16
	addi s5, zero, 0
	addi t0, zero, 1
211:
	j 24f
23:
	srli t1, s4, 6
	beqz t1, 212f
	addi a1, s3, 0
	addi s3, s3, 64
	addi s4, s4, -64
	addi t0, zero, 1
	j 213f
212:
	addi t2, zero, 64
	sub t2, t2, s5
	srli t1, s4, 6
	beqz t1, 214f
	j 215f
214:
	add t1, s4, s5
	srli t1, t1, 6
	beqz t1, 216f
	j 217f
216:
	addi t2, s4, 0
217:
215:
	sub s4, s4, t2
218:
	lbu t1, 0(s3)
	add t3, s1, s5
	sb t1, 16(t3)
	addi s3, s3, 1
	addi s5, s5, 1
	addi t2, t2, -1
	bnez t2, 218b
	addi t1, s5, -64
	beqz t1, 219f
	j 220f
219:
	addi a1, s1, 16
	addi s5, zero, 0
	addi t0, zero, 1
220:
213:
24:
	beqz t0, 221f
	addi a0, s1, 0
	addi a2, zero, 1
	addi a3, s2, 0
	call {vg_md5_compress}
	j 222f
221:
222:
	bnez s4, 22b
	j 21f
20:
21:
	ld ra, 80(s2)
	ld s1, 88(s2)
	ld s3, 104(s2)
	ld s4, 112(s2)
	ld s5, 120(s2)
	ld s6, 128(s2)
	ld s2, 96(s2)
	addi sp, sp, 144
	ret
	.option pop

vg_md5_finalize:
	.option push
	.option arch, +m, +c
	addi sp, sp, -144
	addi t0, sp, 0
	sd ra, 80(t0)
	sd s1, 88(t0)
	sd s2, 96(t0)
	sd s3, 104(t0)
	sd s4, 112(t0)
	sd s5, 120(t0)
	sd s6, 128(t0)
	addi s1, a0, 0
	addi s2, t0, 0
	addi s3, a2, 0
	addi s4, a1, 0
	andi s5, s4, 63
	addi t1, zero, 128
	add t3, s1, s5
	sb t1, 16(t3)
	addi s5, s5, 1
	addi s6, s5, 7
	srli s6, s6, 6
20:
	addi t2, zero, 64
	beqz s6, 21f
	j 22f
21:
	addi t2, zero, 56
22:
	addi t1, zero, 0
	sub t2, t2, s5
	beqz t2, 23f
25:
	add t3, s1, s5
	sb t1, 16(t3)
	addi s5, s5, 1
	addi t2, t2, -1
	bnez t2, 25b
	j 24f
23:
24:
	beqz s6, 26f
	j 27f
26:
	slli t1, s4, 3
	sb t1, 72(s1)
	srli t3, t1, 8
	sb t3, 73(s1)
	srli t3, t1, 16
	sb t3, 74(s1)
	srli t3, t1, 24
	sb t3, 75(s1)
	srli t1, t1, 32
	sb t1, 76(s1)
	srli t3, t1, 8
	sb t3, 77(s1)
	srli t3, t1, 16
	sb t3, 78(s1)
	srli t3, t1, 24
	sb t3, 79(s1)
27:
	addi a1, s1, 16
	addi a0, s1, 0
	addi a2, zero, 1
	addi a3, s2, 0
	call {vg_md5_compress}
	addi s5, zero, 0
	addi s6, s6, -1
	beqz s6, 20b
	lbu t1, 0(s1)
	lbu t2, 1(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 2(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 3(s1)
	slli t2, t2, 24
	or t1, t1, t2
	sb t1, 0(s3)
	srli t2, t1, 8
	sb t2, 1(s3)
	srli t2, t1, 16
	sb t2, 2(s3)
	srli t2, t1, 24
	sb t2, 3(s3)
	lbu t1, 4(s1)
	lbu t2, 5(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 6(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 7(s1)
	slli t2, t2, 24
	or t1, t1, t2
	sb t1, 4(s3)
	srli t2, t1, 8
	sb t2, 5(s3)
	srli t2, t1, 16
	sb t2, 6(s3)
	srli t2, t1, 24
	sb t2, 7(s3)
	lbu t1, 8(s1)
	lbu t2, 9(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 10(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 11(s1)
	slli t2, t2, 24
	or t1, t1, t2
	sb t1, 8(s3)
	srli t2, t1, 8
	sb t2, 9(s3)
	srli t2, t1, 16
	sb t2, 10(s3)
	srli t2, t1, 24
	sb t2, 11(s3)
	lbu t1, 12(s1)
	lbu t2, 13(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 14(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 15(s1)
	slli t2, t2, 24
	or t1, t1, t2
	sb t1, 12(s3)
	srli t2, t1, 8
	sb t2, 13(s3)
	srli t2, t1, 16
	sb t2, 14(s3)
	srli t2, t1, 24
	sb t2, 15(s3)
	ld ra, 80(s2)
	ld s1, 88(s2)
	ld s3, 104(s2)
	ld s4, 112(s2)
	ld s5, 120(s2)
	ld s6, 128(s2)
	ld s2, 96(s2)
	addi sp, sp, 144
	ret
	.option pop
