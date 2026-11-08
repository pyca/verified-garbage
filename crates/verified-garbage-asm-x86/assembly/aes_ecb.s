// The functions of `src/aes_ecb.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_ecb_encrypt_aesni:
	lea esp, [esp-28]
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+36]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+40]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+44]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+48]
	mov DWORD PTR [esp+16], eax
	call {vg_aes_encrypt_blocks_aesni}
	mov DWORD PTR [esp+20], eax
	mov DWORD PTR [esp+24], edx
	mov eax, DWORD PTR [esp+48]
	mov DWORD PTR [esp], eax
	mov eax, 2048
	mov DWORD PTR [esp+4], eax
	call {vg_zeroize}
	mov eax, DWORD PTR [esp+20]
	mov edx, DWORD PTR [esp+24]
	lea esp, [esp+28]
	ret
	.p2align 6

vg_aes_ecb_decrypt_aesni:
	lea esp, [esp-28]
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+36]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+40]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+44]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+48]
	mov DWORD PTR [esp+16], eax
	call {vg_aes_decrypt_blocks_aesni}
	mov DWORD PTR [esp+20], eax
	mov DWORD PTR [esp+24], edx
	mov eax, DWORD PTR [esp+48]
	mov DWORD PTR [esp], eax
	mov eax, 2048
	mov DWORD PTR [esp+4], eax
	call {vg_zeroize}
	mov eax, DWORD PTR [esp+20]
	mov edx, DWORD PTR [esp+24]
	lea esp, [esp+28]
	ret
	.p2align 6

vg_aes_ecb_encrypt:
	lea esp, [esp-28]
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+36]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+40]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+44]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+48]
	mov DWORD PTR [esp+16], eax
	call {vg_aes_encrypt_blocks}
	mov DWORD PTR [esp+20], eax
	mov DWORD PTR [esp+24], edx
	mov eax, DWORD PTR [esp+48]
	mov DWORD PTR [esp], eax
	mov eax, 2048
	mov DWORD PTR [esp+4], eax
	call {vg_zeroize}
	mov eax, DWORD PTR [esp+20]
	mov edx, DWORD PTR [esp+24]
	lea esp, [esp+28]
	ret
	.p2align 6

vg_aes_ecb_decrypt:
	lea esp, [esp-28]
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+36]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+40]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+44]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+48]
	mov DWORD PTR [esp+16], eax
	call {vg_aes_decrypt_blocks}
	mov DWORD PTR [esp+20], eax
	mov DWORD PTR [esp+24], edx
	mov eax, DWORD PTR [esp+48]
	mov DWORD PTR [esp], eax
	mov eax, 2048
	mov DWORD PTR [esp+4], eax
	call {vg_zeroize}
	mov eax, DWORD PTR [esp+20]
	mov edx, DWORD PTR [esp+24]
	lea esp, [esp+28]
	ret
	.p2align 6
