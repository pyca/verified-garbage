// The functions of `src/internal/vg_sha512_update_core.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha512_update_core:
	.option push
	.option arch, +m, +c
	andi t0, a1, 127
	xori t2, t0, 127
	bltu t2, a3, 20f
	beqz a3, 22f
	add t3, a0, t0
	add t4, a2, a3
24:
	lbu t1, 0(a2)
	sb t1, 64(t3)
	addi a2, a2, 1
	addi t3, t3, 1
	bne a2, t4, 24b
23:
21:
	ret
22:
	j 23b
20:
	addi sp, sp, -208
	addi t0, sp, 0
	sd ra, 144(t0)
	sd s1, 152(t0)
	sd s2, 160(t0)
	sd s3, 168(t0)
	sd s4, 176(t0)
	sd s5, 184(t0)
	sd s6, 192(t0)
	addi s1, a0, 0
	addi s2, t0, 0
	addi s3, a2, 0
	addi s4, a3, 0
	andi s5, a1, 127
	beqz s4, 25f
27:
	addi t0, zero, 0
	beqz s5, 28f
	addi t2, zero, 128
	sub t2, t2, s5
	srli t1, s4, 7
	beqz t1, 210f
	j 211f
210:
	add t1, s4, s5
	srli t1, t1, 7
	beqz t1, 212f
	j 213f
212:
	addi t2, s4, 0
213:
211:
	sub s4, s4, t2
214:
	lbu t1, 0(s3)
	add t3, s1, s5
	sb t1, 64(t3)
	addi s3, s3, 1
	addi s5, s5, 1
	addi t2, t2, -1
	bnez t2, 214b
	addi t1, s5, -128
	beqz t1, 215f
	j 216f
215:
	addi a1, s1, 64
	addi s5, zero, 0
	addi t0, zero, 1
216:
	j 29f
28:
	srli t1, s4, 7
	beqz t1, 217f
	addi a1, s3, 0
	addi s3, s3, 128
	addi s4, s4, -128
	addi t0, zero, 1
	j 218f
217:
	addi t2, zero, 128
	sub t2, t2, s5
	srli t1, s4, 7
	beqz t1, 219f
	j 220f
219:
	add t1, s4, s5
	srli t1, t1, 7
	beqz t1, 221f
	j 222f
221:
	addi t2, s4, 0
222:
220:
	sub s4, s4, t2
223:
	lbu t1, 0(s3)
	add t3, s1, s5
	sb t1, 64(t3)
	addi s3, s3, 1
	addi s5, s5, 1
	addi t2, t2, -1
	bnez t2, 223b
	addi t1, s5, -128
	beqz t1, 224f
	j 225f
224:
	addi a1, s1, 64
	addi s5, zero, 0
	addi t0, zero, 1
225:
218:
29:
	beqz t0, 226f
	addi a0, s1, 0
	addi a2, zero, 1
	addi a3, s2, 0
	call {vg_sha512_compress}
	j 227f
226:
227:
	bnez s4, 27b
	j 26f
25:
26:
	ld ra, 144(s2)
	ld s1, 152(s2)
	ld s3, 168(s2)
	ld s4, 176(s2)
	ld s5, 184(s2)
	ld s6, 192(s2)
	ld s2, 160(s2)
	addi sp, sp, 208
	j 21b
	.option pop
