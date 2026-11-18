// The functions of `src/internal/vg_md5_update_core.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_md5_update_core:
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
