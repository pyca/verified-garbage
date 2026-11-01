// The functions of `src/internal/vg_mldsa_make_hint.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_make_hint:
	push ebx
	push esi
	push edi
	push ebp
	mov edx, DWORD PTR [esp+28]
	mov esi, DWORD PTR [esp+20]
	mov edi, DWORD PTR [esp+24]
	mov ebp, DWORD PTR [esp+32]
	mov eax, ebp
	add eax, 1024
	mov DWORD PTR [esp+28], eax
	mov ecx, 0
	cmp edx, 261888
	je 20f
22:
	mov eax, DWORD PTR [edi]
	add eax, 127
	shr eax, 7
	mov edx, 11275
	mul edx
	add eax, 8388608
	shr eax, 24
	sub eax, 44
	sbb edx, edx
	and edx, 44
	add eax, edx
	mov ebx, eax
	mov eax, DWORD PTR [edi]
	add eax, DWORD PTR [esi]
	sub eax, 8380417
	sbb edx, edx
	and edx, 8380417
	add eax, edx
	add eax, 127
	shr eax, 7
	mov edx, 11275
	mul edx
	add eax, 8388608
	shr eax, 24
	sub eax, 44
	sbb edx, edx
	and edx, 44
	add eax, edx
	xor eax, ebx
	add eax, 63
	shr eax, 6
	add ecx, eax
	mov DWORD PTR [ebp], eax
	add esi, 4
	add edi, 4
	add ebp, 4
	cmp ebp, DWORD PTR [esp+28]
	jne 22b
	jmp 21f
20:
23:
	mov eax, DWORD PTR [edi]
	add eax, 127
	shr eax, 7
	mov edx, 1025
	mul edx
	add eax, 2097152
	shr eax, 22
	sub eax, 16
	sbb edx, edx
	and edx, 16
	add eax, edx
	mov ebx, eax
	mov eax, DWORD PTR [edi]
	add eax, DWORD PTR [esi]
	sub eax, 8380417
	sbb edx, edx
	and edx, 8380417
	add eax, edx
	add eax, 127
	shr eax, 7
	mov edx, 1025
	mul edx
	add eax, 2097152
	shr eax, 22
	sub eax, 16
	sbb edx, edx
	and edx, 16
	add eax, edx
	xor eax, ebx
	add eax, 63
	shr eax, 6
	add ecx, eax
	mov DWORD PTR [ebp], eax
	add esi, 4
	add edi, 4
	add ebp, 4
	cmp ebp, DWORD PTR [esp+28]
	jne 23b
21:
	mov eax, ecx
	mov esi, DWORD PTR [esp+8]
	mov edi, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	ret
	.p2align 6
