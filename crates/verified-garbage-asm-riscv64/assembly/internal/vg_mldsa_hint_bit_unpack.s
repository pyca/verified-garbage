// The functions of `src/internal/vg_mldsa_hint_bit_unpack.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_hint_bit_unpack:
	.option push
	.option arch, +m, +c
	slli a2, a2, 32
	srli a2, a2, 32
	sub t2, a1, a2
	addi a6, a4, 0
	addi t0, zero, 0
	addi a7, a3, 0
20:
	sw t0, 0(a7)
	addi a7, a7, 4
	addi a6, a6, -1
	bnez a6, 20b
	addi t1, zero, 0
	add a7, a0, a2
21:
	sub t0, a2, t1
	srli t0, t0, 63
	beqz t0, 22f
	j 23f
22:
	lbu a5, 0(a7)
	sub t0, a5, t1
	srli t0, t0, 63
	beqz t0, 24f
	addi t1, zero, 256
	j 25f
24:
	sub t0, a2, a5
	srli t0, t0, 63
	beqz t0, 26f
	addi t1, zero, 256
	j 27f
26:
	sub t0, t1, a5
	srli t0, t0, 63
	beqz t0, 28f
	add a6, a0, t1
	lbu a6, 0(a6)
	slli a6, a6, 2
	add a6, a3, a6
	addi t0, zero, 1
	sw t0, 0(a6)
	addi t1, t1, 1
	sub t0, t1, a5
	srli t0, t0, 63
	beqz t0, 210f
212:
	add a6, a0, t1
	lbu t0, 0(a6)
	addi a6, a6, -1
	lbu a6, 0(a6)
	sub t0, a6, t0
	srli t0, t0, 63
	beqz t0, 213f
	add a6, a0, t1
	lbu a6, 0(a6)
	slli a6, a6, 2
	add a6, a3, a6
	addi t0, zero, 1
	sw t0, 0(a6)
	addi t1, t1, 1
	j 214f
213:
	addi t1, zero, 256
214:
	sub t0, t1, a5
	srli t0, t0, 63
	bnez t0, 212b
	j 211f
210:
211:
	j 29f
28:
29:
27:
25:
23:
	addi a7, a7, 1
	addi a3, a3, 1024
	addi t2, t2, -1
	bnez t2, 21b
	sub t0, t1, a2
	srli t0, t0, 63
	beqz t0, 215f
217:
	add a6, a0, t1
	lbu a6, 0(a6)
	beqz a6, 218f
	addi t1, zero, 256
	j 219f
218:
	addi t1, t1, 1
219:
	sub t0, t1, a2
	srli t0, t0, 63
	bnez t0, 217b
	j 216f
215:
216:
	sub t0, a2, t1
	srli t0, t0, 63
	addi a0, zero, 1
	sub a0, a0, t0
	ret
	.option pop
