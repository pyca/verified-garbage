// The functions of `src/internal/vg_chacha20_xor.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_chacha20_xor:
	.option push
	.option arch, +m, +c
	addi t0, a3, 263
	andi t0, t0, -8
	sd s5, 0(t0)
	sd s6, 8(t0)
	sd ra, 16(t0)
	addi s5, a1, 0
	addi s6, a2, 0
	addi a1, a3, 0
	beqz s6, 20f
22:
	call {vg_chacha20_block}
	srli t1, s6, 6
	addi a2, s6, 0
	beqz t1, 23f
	addi a2, zero, 64
	j 24f
23:
24:
	sub s6, s6, a2
	addi t2, a1, 0
	or t3, s5, t2
	or t3, t3, a2
	andi t3, t3, 7
	beqz t3, 25f
27:
	lbu t3, 0(s5)
	lbu t4, 0(t2)
	xor t3, t3, t4
	sb t3, 0(s5)
	addi s5, s5, 1
	addi t2, t2, 1
	addi a2, a2, -1
	bnez a2, 27b
	j 26f
25:
28:
	ld t3, 0(s5)
	ld t4, 0(t2)
	xor t3, t3, t4
	sd t3, 0(s5)
	addi s5, s5, 8
	addi t2, t2, 8
	addi a2, a2, -8
	bnez a2, 28b
26:
	lwu t1, 48(a0)
	addi t1, t1, 1
	sw t1, 48(a0)
	bnez s6, 22b
	j 21f
20:
21:
	addi t0, a1, 263
	andi t0, t0, -8
	ld ra, 16(t0)
	ld s5, 0(t0)
	ld s6, 8(t0)
	ret
	.option pop
