// The functions of `src/internal/vg_blake2b_update_scratch.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_blake2b_update_scratch:
	.option push
	.option arch, +m, +c
	addi t0, a4, 7
	andi t0, t0, -8
	sd ra, 512(t0)
	sd s7, 520(t0)
	sd s9, 528(t0)
	sd s10, 536(t0)
	sd s11, 544(t0)
	sd s8, 552(t0)
	addi s7, a0, 0
	addi s8, t0, 0
	addi s9, a2, 0
	addi s10, a3, 0
	addi s11, a1, 0
	addi a7, s11, -1
	andi a7, a7, 127
	addi a7, a7, 1
	beqz s11, 20f
	j 21f
20:
	addi a7, zero, 0
21:
	beqz s10, 22f
	beqz a7, 24f
	addi t3, zero, 128
	sub t3, t3, a7
	srli t1, s10, 7
	beqz t1, 26f
	j 27f
26:
	add t1, s10, a7
	srli t1, t1, 7
	beqz t1, 28f
	j 29f
28:
	addi t3, s10, 0
29:
27:
	sub s10, s10, t3
	add s11, s11, t3
	beqz t3, 210f
212:
	lbu t1, 0(s9)
	add t2, s7, a7
	sb t1, 64(t2)
	addi s9, s9, 1
	addi a7, a7, 1
	addi t3, t3, -1
	bnez t3, 212b
	j 211f
210:
211:
	beqz s10, 213f
	addi a0, s7, 0
	addi a1, s7, 64
	addi a2, zero, 1
	addi a3, s11, 0
	addi a4, zero, 0
	addi a5, s8, 0
	call {vg_blake2b_compress}
	addi a7, zero, 0
	j 214f
213:
214:
	j 25f
24:
25:
	beqz s10, 215f
	addi t1, s10, -1
	srli t2, t1, 7
	beqz t2, 217f
	addi a0, s7, 0
	addi a1, s9, 0
	addi a2, t2, 0
	addi a3, s11, 128
	addi a4, zero, 0
	addi a5, s8, 0
	call {vg_blake2b_compress}
	addi t1, s10, -1
	andi t1, t1, 127
	addi t1, t1, 1
	sub t2, s10, t1
	add s9, s9, t2
	add s11, s11, t2
	addi s10, t1, 0
	addi a7, zero, 0
	j 218f
217:
218:
	addi t3, s10, 0
	add s11, s11, s10
	addi s10, zero, 0
219:
	lbu t1, 0(s9)
	add t2, s7, a7
	sb t1, 64(t2)
	addi s9, s9, 1
	addi a7, a7, 1
	addi t3, t3, -1
	bnez t3, 219b
	j 216f
215:
216:
	j 23f
22:
23:
	ld ra, 512(s8)
	ld s7, 520(s8)
	ld s9, 528(s8)
	ld s10, 536(s8)
	ld s11, 544(s8)
	ld s8, 552(s8)
	ret
	.option pop
