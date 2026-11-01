// The functions of `src/internal/vg_mlkem_compress_encode.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem_compress_encode:
	push ebx
	push esi
	push edi
	push ebp
	mov esi, DWORD PTR [esp+20]
	mov edi, DWORD PTR [esp+28]
	mov eax, DWORD PTR [esp+24]
	cmp eax, 1
	je 20f
	cmp eax, 4
	je 22f
	mov ecx, 64
24:
	mov eax, DWORD PTR [esi+12]
	mov edx, 161271
	mul edx
	add eax, 262080
	shr eax, 19
	and eax, 1023
	mov ebp, eax
	mov ebx, eax
	and ebx, 3
	mov eax, DWORD PTR [esi+8]
	mov edx, 161271
	mul edx
	add eax, 262080
	shr eax, 19
	and eax, 1023
	ror ebx, 22
	add ebx, eax
	mov eax, DWORD PTR [esi+4]
	mov edx, 161271
	mul edx
	add eax, 262080
	shr eax, 19
	and eax, 1023
	ror ebx, 22
	add ebx, eax
	mov eax, DWORD PTR [esi]
	mov edx, 161271
	mul edx
	add eax, 262080
	shr eax, 19
	and eax, 1023
	ror ebx, 22
	add ebx, eax
	mov eax, ebx
	mov BYTE PTR [edi], al
	shr eax, 8
	mov BYTE PTR [edi+1], al
	shr eax, 8
	mov BYTE PTR [edi+2], al
	shr eax, 8
	mov BYTE PTR [edi+3], al
	shr ebp, 2
	mov eax, ebp
	mov BYTE PTR [edi+4], al
	add esi, 16
	add edi, 5
	sub ecx, 1
	jne 24b
	jmp 23f
22:
	mov ecx, 128
25:
	mov eax, DWORD PTR [esi+4]
	mov edx, 2520
	mul edx
	add eax, 262080
	shr eax, 19
	and eax, 15
	mov ebx, eax
	mov eax, DWORD PTR [esi]
	mov edx, 2520
	mul edx
	add eax, 262080
	shr eax, 19
	and eax, 15
	ror ebx, 28
	add ebx, eax
	mov BYTE PTR [edi], bl
	add esi, 8
	add edi, 1
	sub ecx, 1
	jne 25b
23:
	jmp 21f
20:
	mov ecx, 32
26:
	mov eax, DWORD PTR [esi+28]
	mov edx, 315
	mul edx
	add eax, 262080
	shr eax, 19
	and eax, 1
	mov ebx, eax
	mov eax, DWORD PTR [esi+24]
	mov edx, 315
	mul edx
	add eax, 262080
	shr eax, 19
	and eax, 1
	ror ebx, 31
	add ebx, eax
	mov eax, DWORD PTR [esi+20]
	mov edx, 315
	mul edx
	add eax, 262080
	shr eax, 19
	and eax, 1
	ror ebx, 31
	add ebx, eax
	mov eax, DWORD PTR [esi+16]
	mov edx, 315
	mul edx
	add eax, 262080
	shr eax, 19
	and eax, 1
	ror ebx, 31
	add ebx, eax
	mov eax, DWORD PTR [esi+12]
	mov edx, 315
	mul edx
	add eax, 262080
	shr eax, 19
	and eax, 1
	ror ebx, 31
	add ebx, eax
	mov eax, DWORD PTR [esi+8]
	mov edx, 315
	mul edx
	add eax, 262080
	shr eax, 19
	and eax, 1
	ror ebx, 31
	add ebx, eax
	mov eax, DWORD PTR [esi+4]
	mov edx, 315
	mul edx
	add eax, 262080
	shr eax, 19
	and eax, 1
	ror ebx, 31
	add ebx, eax
	mov eax, DWORD PTR [esi]
	mov edx, 315
	mul edx
	add eax, 262080
	shr eax, 19
	and eax, 1
	ror ebx, 31
	add ebx, eax
	mov BYTE PTR [edi], bl
	add esi, 32
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
