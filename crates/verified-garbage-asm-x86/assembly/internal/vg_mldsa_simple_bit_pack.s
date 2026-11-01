// The functions of `src/internal/vg_mldsa_simple_bit_pack.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_simple_bit_pack:
	push ebx
	push esi
	push edi
	push ebp
	mov esi, DWORD PTR [esp+20]
	mov edi, DWORD PTR [esp+28]
	mov eax, DWORD PTR [esp+24]
	cmp eax, 15
	je 20f
	cmp eax, 43
	je 22f
	mov ecx, 64
24:
	mov ebx, 0
	mov eax, DWORD PTR [esi]
	add ebx, eax
	mov BYTE PTR [edi], bl
	shr ebx, 8
	mov eax, DWORD PTR [esi+4]
	ror eax, 30
	add ebx, eax
	mov BYTE PTR [edi+1], bl
	shr ebx, 8
	mov eax, DWORD PTR [esi+8]
	ror eax, 28
	add ebx, eax
	mov BYTE PTR [edi+2], bl
	shr ebx, 8
	mov eax, DWORD PTR [esi+12]
	ror eax, 26
	add ebx, eax
	mov BYTE PTR [edi+3], bl
	shr ebx, 8
	mov BYTE PTR [edi+4], bl
	shr ebx, 8
	add esi, 16
	add edi, 5
	sub ecx, 1
	jne 24b
	jmp 23f
22:
	mov ecx, 64
25:
	mov ebx, 0
	mov eax, DWORD PTR [esi]
	add ebx, eax
	mov eax, DWORD PTR [esi+4]
	ror eax, 26
	add ebx, eax
	mov BYTE PTR [edi], bl
	shr ebx, 8
	mov eax, DWORD PTR [esi+8]
	ror eax, 28
	add ebx, eax
	mov BYTE PTR [edi+1], bl
	shr ebx, 8
	mov eax, DWORD PTR [esi+12]
	ror eax, 30
	add ebx, eax
	mov BYTE PTR [edi+2], bl
	shr ebx, 8
	add esi, 16
	add edi, 3
	sub ecx, 1
	jne 25b
23:
	jmp 21f
20:
	mov ecx, 128
26:
	mov ebx, 0
	mov eax, DWORD PTR [esi]
	add ebx, eax
	mov eax, DWORD PTR [esi+4]
	ror eax, 28
	add ebx, eax
	mov BYTE PTR [edi], bl
	shr ebx, 8
	add esi, 8
	add edi, 1
	sub ecx, 1
	jne 26b
21:
	mov esi, DWORD PTR [esp+8]
	mov edi, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	ret
	.p2align 6
