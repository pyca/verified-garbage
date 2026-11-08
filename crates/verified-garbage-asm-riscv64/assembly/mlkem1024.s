// The functions of `src/mlkem1024.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem1024_check_ek:
	.option push
	.option arch, +m, +c
	addi a1, zero, 512
	addi a2, zero, 0
	lui a5, 1
	addi a5, a5, -768
20:
	lbu a3, 1(a0)
	slli a3, a3, 60
	srli a3, a3, 52
	lbu a4, 0(a0)
	add a3, a3, a4
	sub a4, a5, a3
	srli a4, a4, 63
	add a2, a2, a4
	lbu a3, 1(a0)
	srli a3, a3, 4
	lbu a4, 2(a0)
	slli a4, a4, 4
	add a3, a3, a4
	sub a4, a5, a3
	srli a4, a4, 63
	add a2, a2, a4
	addi a0, a0, 3
	addi a1, a1, -1
	bnez a1, 20b
	addi a3, zero, 0
	sub a3, a3, a2
	srli a3, a3, 63
	addi a0, zero, 1
	sub a0, a0, a3
	ret
	.option pop

vg_mlkem1024_keygen:
	.option push
	.option arch, +m, +c
	addi sp, sp, -64
	addi t0, sp, 0
	sd ra, 0(t0)
	sd a3, 8(t0)
	call {vg_mlkem1024_keygen_body}
	addi t0, sp, 0
	sd a0, 16(t0)
	ld a0, 8(t0)
	lui a1, 12
	call {vg_zeroize}
	addi t0, sp, 0
	ld a0, 16(t0)
	ld ra, 0(t0)
	addi sp, sp, 64
	ret
	.option pop

vg_mlkem1024_encaps:
	.option push
	.option arch, +m, +c
	addi sp, sp, -64
	addi t0, sp, 0
	sd ra, 0(t0)
	sd a4, 8(t0)
	call {vg_mlkem1024_encaps_body}
	addi t0, sp, 0
	sd a0, 16(t0)
	ld a0, 8(t0)
	lui a1, 12
	call {vg_zeroize}
	addi t0, sp, 0
	ld a0, 16(t0)
	ld ra, 0(t0)
	addi sp, sp, 64
	ret
	.option pop

vg_mlkem1024_encaps_h:
	.option push
	.option arch, +m, +c
	addi sp, sp, -64
	addi t0, sp, 0
	sd ra, 0(t0)
	sd a5, 8(t0)
	call {vg_mlkem1024_encaps_h_body}
	addi t0, sp, 0
	sd a0, 16(t0)
	ld a0, 8(t0)
	lui a1, 12
	call {vg_zeroize}
	addi t0, sp, 0
	ld a0, 16(t0)
	ld ra, 0(t0)
	addi sp, sp, 64
	ret
	.option pop

vg_mlkem1024_decaps:
	.option push
	.option arch, +m, +c
	addi sp, sp, -64
	addi t0, sp, 0
	sd ra, 0(t0)
	sd a3, 8(t0)
	call {vg_mlkem1024_decaps_body}
	addi t0, sp, 0
	sd a0, 16(t0)
	ld a0, 8(t0)
	lui a1, 12
	call {vg_zeroize}
	addi t0, sp, 0
	ld a0, 16(t0)
	ld ra, 0(t0)
	addi sp, sp, 64
	ret
	.option pop
