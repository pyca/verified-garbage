// The functions of `src/scrypt.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_scrypt:
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	mov eax, DWORD PTR [esp+40]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+44]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+48]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+52]
	mov DWORD PTR [esp+12], eax
	mov eax, 1
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+60]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+64]
	ror eax, 25
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [esp+28], eax
	call {vg_pbkdf2_hmac_sha256_scratch}
	mov eax, DWORD PTR [esp+60]
	mov DWORD PTR [esp+32], eax
20:
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+56]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+56]
	add eax, 2
	mov DWORD PTR [esp+20], eax
	call {vg_scrypt_romix}
	mov ecx, DWORD PTR [esp+56]
	ror ecx, 25
	mov eax, DWORD PTR [esp+32]
	add eax, ecx
	mov edx, DWORD PTR [esp+64]
	ror edx, 25
	add edx, DWORD PTR [esp+60]
	mov DWORD PTR [esp+32], eax
	cmp eax, edx
	jne 20b
	mov eax, DWORD PTR [esp+40]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+44]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+60]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+64]
	ror eax, 25
	mov DWORD PTR [esp+12], eax
	mov eax, 1
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [esp+28], eax
	call {vg_pbkdf2_hmac_sha256_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	ret
	.p2align 6

vg_scrypt_shani:
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	mov eax, DWORD PTR [esp+40]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+44]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+48]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+52]
	mov DWORD PTR [esp+12], eax
	mov eax, 1
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+60]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+64]
	ror eax, 25
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [esp+28], eax
	call {vg_pbkdf2_hmac_sha256_scratch_shani}
	mov eax, DWORD PTR [esp+60]
	mov DWORD PTR [esp+32], eax
20:
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+56]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+56]
	add eax, 2
	mov DWORD PTR [esp+20], eax
	call {vg_scrypt_romix}
	mov ecx, DWORD PTR [esp+56]
	ror ecx, 25
	mov eax, DWORD PTR [esp+32]
	add eax, ecx
	mov edx, DWORD PTR [esp+64]
	ror edx, 25
	add edx, DWORD PTR [esp+60]
	mov DWORD PTR [esp+32], eax
	cmp eax, edx
	jne 20b
	mov eax, DWORD PTR [esp+40]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+44]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+60]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+64]
	ror eax, 25
	mov DWORD PTR [esp+12], eax
	mov eax, 1
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [esp+28], eax
	call {vg_pbkdf2_hmac_sha256_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	ret
	.p2align 6
