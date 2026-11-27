// The functions of `src/aes_ecb.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_ecb_encrypt:
	.option push
	.option arch, +m, +c
	addi sp, sp, -32
	addi t0, sp, 0
	sd ra, 0(t0)
	sd a4, 8(t0)
	call {vg_aes_encrypt_blocks}
	addi t0, sp, 0
	sd a0, 16(t0)
	ld a0, 8(t0)
	addi a1, zero, 2047
	addi a1, a1, 1
	call {vg_zeroize}
	addi t0, sp, 0
	ld a0, 16(t0)
	ld ra, 0(t0)
	addi sp, sp, 32
	addi t0, zero, 0
	addi sp, sp, -32
	addi t1, sp, 0
	sd t0, 0(t1)
	sd t0, 8(t1)
	sd t0, 16(t1)
	sd t0, 24(t1)
	addi sp, sp, 32
	addi a0, zero, 0
	addi a1, zero, 0
	addi a2, zero, 0
	addi a3, zero, 0
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	addi a7, zero, 0
	addi t0, zero, 0
	addi t1, zero, 0
	addi t2, zero, 0
	addi t3, zero, 0
	addi t4, zero, 0
	addi t5, zero, 0
	addi t6, zero, 0
	ret
	.option pop

vg_aes_ecb_decrypt:
	.option push
	.option arch, +m, +c
	addi sp, sp, -32
	addi t0, sp, 0
	sd ra, 0(t0)
	sd a4, 8(t0)
	call {vg_aes_decrypt_blocks}
	addi t0, sp, 0
	sd a0, 16(t0)
	ld a0, 8(t0)
	addi a1, zero, 2047
	addi a1, a1, 1
	call {vg_zeroize}
	addi t0, sp, 0
	ld a0, 16(t0)
	ld ra, 0(t0)
	addi sp, sp, 32
	addi t0, zero, 0
	addi sp, sp, -32
	addi t1, sp, 0
	sd t0, 0(t1)
	sd t0, 8(t1)
	sd t0, 16(t1)
	sd t0, 24(t1)
	addi sp, sp, 32
	addi a0, zero, 0
	addi a1, zero, 0
	addi a2, zero, 0
	addi a3, zero, 0
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	addi a7, zero, 0
	addi t0, zero, 0
	addi t1, zero, 0
	addi t2, zero, 0
	addi t3, zero, 0
	addi t4, zero, 0
	addi t5, zero, 0
	addi t6, zero, 0
	ret
	.option pop
