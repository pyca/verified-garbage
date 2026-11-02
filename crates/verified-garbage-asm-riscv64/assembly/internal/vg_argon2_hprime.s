// The functions of `src/internal/vg_argon2_hprime.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_argon2_hprime:
	.option push
	.option arch, +m, +c
	sd ra, 880(a4)
	sd s0, 840(a4)
	sd s1, 848(a4)
	sd s2, 856(a4)
	sd s3, 864(a4)
	sd s4, 872(a4)
	addi s4, a4, 0
	addi s0, a0, 0
	addi s1, a1, 0
	addi s2, a2, 0
	addi s3, a3, 0
	sw a3, 832(s4)
	addi a1, s3, 0
	addi a7, a1, -65
	srli a7, a7, 63
	bnez a7, 20f
	addi a1, zero, 64
	j 21f
20:
21:
	addi a0, s4, 0
	addi a2, s4, 832
	addi a3, zero, 0
	call {vg_blake2b_init}
	addi a1, zero, 0
	addi a2, s4, 832
	addi a3, zero, 4
	addi a0, s4, 0
	addi a4, s4, 192
	call {vg_blake2b_update_scratch}
	addi a1, zero, 4
	addi a2, s0, 0
	addi a3, s1, 0
	addi a0, s4, 0
	addi a4, s4, 192
	call {vg_blake2b_update_scratch}
	addi a1, s1, 4
	addi a0, s4, 0
	addi a2, s4, 768
	addi a3, s4, 192
	call {vg_blake2b_finalize_scratch}
	addi a7, s3, -65
	srli a7, a7, 63
	bnez a7, 22f
	addi a6, zero, 32
	addi a2, s4, 768
24:
	lbu a3, 0(a2)
	sb a3, 0(s2)
	addi a2, a2, 1
	addi s2, s2, 1
	addi a6, a6, -1
	bnez a6, 24b
	addi s3, s3, -32
	addi a7, s3, -65
	srli a7, a7, 63
	bnez a7, 25f
27:
	addi a1, zero, 64
	addi a0, s4, 0
	addi a2, s4, 832
	addi a3, zero, 0
	call {vg_blake2b_init}
	addi a1, zero, 0
	addi a2, s4, 768
	addi a3, zero, 64
	addi a0, s4, 0
	addi a4, s4, 192
	call {vg_blake2b_update_scratch}
	addi a1, zero, 64
	addi a0, s4, 0
	addi a2, s4, 768
	addi a3, s4, 192
	call {vg_blake2b_finalize_scratch}
	addi a6, zero, 32
	addi a2, s4, 768
28:
	lbu a3, 0(a2)
	sb a3, 0(s2)
	addi a2, a2, 1
	addi s2, s2, 1
	addi a6, a6, -1
	bnez a6, 28b
	addi s3, s3, -32
	addi a7, s3, -65
	srli a7, a7, 63
	beqz a7, 27b
	j 26f
25:
26:
	addi a1, s3, 0
	addi a0, s4, 0
	addi a2, s4, 832
	addi a3, zero, 0
	call {vg_blake2b_init}
	addi a1, zero, 0
	addi a2, s4, 768
	addi a3, zero, 64
	addi a0, s4, 0
	addi a4, s4, 192
	call {vg_blake2b_update_scratch}
	addi a1, zero, 64
	addi a0, s4, 0
	addi a2, s4, 768
	addi a3, s4, 192
	call {vg_blake2b_finalize_scratch}
	j 23f
22:
23:
	addi a6, s3, 0
	addi a2, s4, 768
29:
	lbu a3, 0(a2)
	sb a3, 0(s2)
	addi a2, a2, 1
	addi s2, s2, 1
	addi a6, a6, -1
	bnez a6, 29b
	ld ra, 880(s4)
	ld s0, 840(s4)
	ld s1, 848(s4)
	ld s2, 856(s4)
	ld s3, 864(s4)
	ld s4, 872(s4)
	ret
	.option pop
