// The functions of `src/internal/vg_keccak_pad.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_keccak_pad:
	.option push
	.option arch, +m, +c
	addi sp, sp, -528
	addi t0, sp, 0
	sd ra, 512(t0)
	add t1, a0, a2
	lbu t2, 0(t1)
	xor t2, t2, a3
	sb t2, 0(t1)
	add t1, a0, a1
	addi t1, t1, -1
	lbu t2, 0(t1)
	xori t2, t2, 128
	sb t2, 0(t1)
	addi a1, sp, 0
	call {vg_keccak_f1600}
	addi t0, sp, 0
	ld ra, 512(t0)
	addi sp, sp, 528
	ret
	.option pop
