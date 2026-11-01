// The functions of `src/internal/vg_mldsa_expand_mask_poly.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_expand_mask_poly:
	push ebx
	push esi
	push edi
	push ebp
	mov esi, DWORD PTR [esp+32]
	mov ebx, esi
	add ebx, 0
	mov eax, 0
	mov ecx, 50
20:
	mov DWORD PTR [ebx], eax
	add ebx, 4
	sub ecx, 1
	jne 20b
	mov eax, esi
	mov ecx, 136
	mov edx, 0
	mov ebx, DWORD PTR [esp+20]
	mov ebp, 66
	mov edi, esi
	add edi, 200
	push edi
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_keccak_absorb_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, esi
	mov ecx, 136
	mov edx, 66
	mov ebx, 31
	mov edi, esi
	add edi, 200
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_keccak_pad_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, esi
	mov ecx, 136
	mov edx, 0
	mov ebx, esi
	add ebx, 840
	mov ebp, 640
	mov edi, esi
	add edi, 200
	push edi
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_keccak_squeeze_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+28]
	mov eax, DWORD PTR [esp+24]
	cmp eax, 131072
	je 21f
	add esi, 840
	mov ecx, 64
23:
	mov eax, DWORD PTR [esi]
	and eax, 1048575
	mov edx, 524288
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [edi], edx
	mov eax, DWORD PTR [esi+2]
	shr eax, 4
	and eax, 1048575
	mov edx, 524288
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [edi+4], edx
	mov eax, DWORD PTR [esi+5]
	and eax, 1048575
	mov edx, 524288
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [edi+8], edx
	mov eax, DWORD PTR [esi+7]
	shr eax, 4
	and eax, 1048575
	mov edx, 524288
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [edi+12], edx
	add esi, 10
	add edi, 16
	sub ecx, 1
	jne 23b
	jmp 22f
21:
	add esi, 840
	mov ecx, 64
24:
	mov eax, DWORD PTR [esi]
	and eax, 262143
	mov edx, 131072
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [edi], edx
	mov eax, DWORD PTR [esi+2]
	shr eax, 2
	and eax, 262143
	mov edx, 131072
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [edi+4], edx
	mov eax, DWORD PTR [esi+4]
	shr eax, 4
	and eax, 262143
	mov edx, 131072
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [edi+8], edx
	mov eax, DWORD PTR [esi+6]
	shr eax, 6
	and eax, 262143
	mov edx, 131072
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [edi+12], edx
	add esi, 9
	add edi, 16
	sub ecx, 1
	jne 24b
22:
	mov esi, DWORD PTR [esp+8]
	mov edi, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	ret
	.p2align 6
