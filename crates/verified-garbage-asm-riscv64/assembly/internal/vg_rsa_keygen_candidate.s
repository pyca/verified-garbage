// The functions of `src/internal/vg_rsa_keygen_candidate.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

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
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
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
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 24(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 24(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 32(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 32(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 40(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
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
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
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
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 24(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 24(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 32(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 32(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 40(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
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
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
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
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 24(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 24(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 32(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 32(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 40(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
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
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
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
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 24(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 24(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 32(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 32(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 40(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
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
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
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
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 24(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 24(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 32(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 32(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 40(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
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
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
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
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 24(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 24(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 32(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 32(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 40(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
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
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
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
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 24(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 24(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 32(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 32(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 40(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
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
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
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
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 16(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 16(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 0(t3)
	ld s2, 16(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 24(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 24(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 8(t3)
	ld s2, 24(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 32(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
	ld a7, 32(a0)
	add s3, s3, s4
	add s2, s2, s1
	sltu s4, s2, s1
	add s1, s3, s4
	sd s2, 16(t3)
	ld s2, 32(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	mulhu s3, t6, a6
	mul s2, t6, a6
	ld a6, 40(t4)
	add s3, s3, s4
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	add s1, s1, s2
	sltu s4, s1, s2
	mulhu s3, t2, a7
	mul s2, t2, a7
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
