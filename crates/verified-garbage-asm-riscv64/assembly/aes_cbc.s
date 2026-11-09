// The functions of `src/aes_cbc.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_cbc_encrypt:
	.option push
	.option arch, +m, +c
	addi sp, sp, -32
	addi t0, sp, 0
	sd ra, 0(t0)
	sd a5, 8(t0)
	call {vg_aes_cbc_encrypt_unwiped}
	addi t0, sp, 0
	sd a0, 16(t0)
	ld a0, 8(t0)
	addi a1, zero, 2047
	addi a1, a1, 129
	call {vg_zeroize}
	addi t0, sp, 0
	ld a0, 16(t0)
	ld ra, 0(t0)
	addi sp, sp, 32
	ret
	.option pop

vg_aes_cbc_decrypt:
	.option push
	.option arch, +m, +c
	addi sp, sp, -32
	addi t0, sp, 0
	sd ra, 0(t0)
	sd a5, 8(t0)
	call {vg_aes_cbc_decrypt_unwiped}
	addi t0, sp, 0
	sd a0, 16(t0)
	ld a0, 8(t0)
	addi a1, zero, 2047
	addi a1, a1, 129
	call {vg_zeroize}
	addi t0, sp, 0
	ld a0, 16(t0)
	ld ra, 0(t0)
	addi sp, sp, 32
	ret
	.option pop
