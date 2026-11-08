// The functions of `src/aes_cbc.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_cbc_encrypt_aesni:
	lea esp, [esp-32]
	mov eax, DWORD PTR [esp+36]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+40]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+44]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+48]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+52]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+56]
	mov DWORD PTR [esp+20], eax
	call {vg_aes_cbc_encrypt_unwiped_aesni}
	mov DWORD PTR [esp+24], eax
	mov DWORD PTR [esp+28], edx
	mov eax, DWORD PTR [esp+56]
	mov DWORD PTR [esp], eax
	mov eax, 2176
	mov DWORD PTR [esp+4], eax
	call {vg_zeroize}
	mov eax, DWORD PTR [esp+24]
	mov edx, DWORD PTR [esp+28]
	lea esp, [esp+32]
	ret
	.p2align 6

vg_aes_cbc_decrypt_aesni:
	lea esp, [esp-32]
	mov eax, DWORD PTR [esp+36]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+40]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+44]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+48]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+52]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+56]
	mov DWORD PTR [esp+20], eax
	call {vg_aes_cbc_decrypt_unwiped_aesni}
	mov DWORD PTR [esp+24], eax
	mov DWORD PTR [esp+28], edx
	mov eax, DWORD PTR [esp+56]
	mov DWORD PTR [esp], eax
	mov eax, 2176
	mov DWORD PTR [esp+4], eax
	call {vg_zeroize}
	mov eax, DWORD PTR [esp+24]
	mov edx, DWORD PTR [esp+28]
	lea esp, [esp+32]
	ret
	.p2align 6

vg_aes_cbc_encrypt:
	lea esp, [esp-32]
	mov eax, DWORD PTR [esp+36]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+40]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+44]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+48]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+52]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+56]
	mov DWORD PTR [esp+20], eax
	call {vg_aes_cbc_encrypt_unwiped}
	mov DWORD PTR [esp+24], eax
	mov DWORD PTR [esp+28], edx
	mov eax, DWORD PTR [esp+56]
	mov DWORD PTR [esp], eax
	mov eax, 2176
	mov DWORD PTR [esp+4], eax
	call {vg_zeroize}
	mov eax, DWORD PTR [esp+24]
	mov edx, DWORD PTR [esp+28]
	lea esp, [esp+32]
	ret
	.p2align 6

vg_aes_cbc_decrypt:
	lea esp, [esp-32]
	mov eax, DWORD PTR [esp+36]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+40]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+44]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+48]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+52]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+56]
	mov DWORD PTR [esp+20], eax
	call {vg_aes_cbc_decrypt_unwiped}
	mov DWORD PTR [esp+24], eax
	mov DWORD PTR [esp+28], edx
	mov eax, DWORD PTR [esp+56]
	mov DWORD PTR [esp], eax
	mov eax, 2176
	mov DWORD PTR [esp+4], eax
	call {vg_zeroize}
	mov eax, DWORD PTR [esp+24]
	mov edx, DWORD PTR [esp+28]
	lea esp, [esp+32]
	ret
	.p2align 6
