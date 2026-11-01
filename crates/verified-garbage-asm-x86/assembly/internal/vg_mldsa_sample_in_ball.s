// The functions of `src/internal/vg_mldsa_sample_in_ball.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_sample_in_ball:
	push ebx
	push esi
	push edi
	push ebp
	mov esi, DWORD PTR [esp+36]
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
	mov ebp, DWORD PTR [esp+24]
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
	mov edx, DWORD PTR [esp+24]
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
	mov ebp, 272
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
	mov ebp, DWORD PTR [esp+32]
	mov eax, 0
	mov edi, ebp
	mov ecx, 256
21:
	mov DWORD PTR [edi], eax
	add edi, 4
	sub ecx, 1
	jne 21b
	mov edi, 256
	sub edi, DWORD PTR [esp+28]
	mov eax, DWORD PTR [esi+840]
	mov edx, DWORD PTR [esi+844]
	mov DWORD PTR [esp+24], eax
	mov DWORD PTR [esp+28], edx
	add esi, 848
	mov ecx, 264
22:
	cmp edi, 256
	jb 23f
	jmp 24f
23:
	movzx eax, BYTE PTR [esi]
	cmp edi, eax
	jb 25f
	add eax, eax
	add eax, eax
	add eax, ebp
	mov edx, edi
	add edx, edx
	add edx, edx
	add edx, ebp
	mov ebx, DWORD PTR [eax]
	mov DWORD PTR [edx], ebx
	mov ebx, DWORD PTR [esp+24]
	test ebx, 1
	je 27f
	mov edx, 8380416
	jmp 28f
27:
	mov edx, 1
28:
	mov DWORD PTR [eax], edx
	mov edx, DWORD PTR [esp+28]
	mov eax, edx
	shr ebx, 1
	and edx, 1
	ror edx, 1
	add ebx, edx
	shr eax, 1
	mov DWORD PTR [esp+24], ebx
	mov DWORD PTR [esp+28], eax
	add edi, 1
	jmp 26f
25:
26:
24:
	add esi, 1
	sub ecx, 1
	jne 22b
	mov eax, edi
	shr eax, 8
	mov esi, DWORD PTR [esp+8]
	mov edi, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	ret
	.p2align 6
