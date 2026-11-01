// The functions of `src/internal/vg_mlkem1024_compress_encode.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem1024_compress_encode:
	push ebx
	push esi
	push edi
	push ebp
	mov esi, DWORD PTR [esp+20]
	mov edi, DWORD PTR [esp+28]
	mov eax, DWORD PTR [esp+24]
	cmp eax, 5
	je 20f
	mov ecx, 32
22:
	mov eax, DWORD PTR [esi+8]
	mov edx, 322542
	mul edx
	add eax, 261888
	shr eax, 19
	and eax, 2047
	mov ebp, eax
	shr ebp, 10
	mov ebx, eax
	and ebx, 1023
	mov eax, DWORD PTR [esi+4]
	mov edx, 322542
	mul edx
	add eax, 261888
	shr eax, 19
	and eax, 2047
	ror ebx, 21
	add ebx, eax
	mov eax, DWORD PTR [esi]
	mov edx, 322542
	mul edx
	add eax, 261888
	shr eax, 19
	and eax, 2047
	ror ebx, 21
	add ebx, eax
	mov eax, ebx
	mov BYTE PTR [edi], al
	shr eax, 8
	mov BYTE PTR [edi+1], al
	shr eax, 8
	mov BYTE PTR [edi+2], al
	shr eax, 8
	mov BYTE PTR [edi+3], al
	mov eax, DWORD PTR [esi+20]
	mov edx, 322542
	mul edx
	add eax, 261888
	shr eax, 19
	and eax, 2047
	mov ebx, eax
	and ebx, 511
	mov eax, DWORD PTR [esi+16]
	mov edx, 322542
	mul edx
	add eax, 261888
	shr eax, 19
	and eax, 2047
	ror ebx, 21
	add ebx, eax
	mov eax, DWORD PTR [esi+12]
	mov edx, 322542
	mul edx
	add eax, 261888
	shr eax, 19
	and eax, 2047
	ror ebx, 21
	add ebx, eax
	ror ebx, 31
	add ebx, ebp
	mov eax, ebx
	mov BYTE PTR [edi+4], al
	shr eax, 8
	mov BYTE PTR [edi+5], al
	shr eax, 8
	mov BYTE PTR [edi+6], al
	shr eax, 8
	mov BYTE PTR [edi+7], al
	mov eax, DWORD PTR [esi+20]
	mov edx, 322542
	mul edx
	add eax, 261888
	shr eax, 19
	and eax, 2047
	shr eax, 9
	mov ebp, eax
	mov eax, DWORD PTR [esi+28]
	mov edx, 322542
	mul edx
	add eax, 261888
	shr eax, 19
	and eax, 2047
	mov ebx, eax
	mov eax, DWORD PTR [esi+24]
	mov edx, 322542
	mul edx
	add eax, 261888
	shr eax, 19
	and eax, 2047
	ror ebx, 21
	add ebx, eax
	ror ebx, 30
	add ebx, ebp
	mov eax, ebx
	mov BYTE PTR [edi+8], al
	shr eax, 8
	mov BYTE PTR [edi+9], al
	shr eax, 8
	mov BYTE PTR [edi+10], al
	add esi, 32
	add edi, 11
	sub ecx, 1
	jne 22b
	jmp 21f
20:
	mov ecx, 32
23:
	mov eax, DWORD PTR [esi+28]
	mov edx, 5040
	mul edx
	add eax, 261888
	shr eax, 19
	and eax, 31
	mov ebp, eax
	ror ebp, 29
	mov eax, DWORD PTR [esi+24]
	mov edx, 5040
	mul edx
	add eax, 261888
	shr eax, 19
	and eax, 31
	mov ebx, eax
	and ebx, 3
	shr eax, 2
	add ebp, eax
	mov eax, DWORD PTR [esi+20]
	mov edx, 5040
	mul edx
	add eax, 261888
	shr eax, 19
	and eax, 31
	ror ebx, 27
	add ebx, eax
	mov eax, DWORD PTR [esi+16]
	mov edx, 5040
	mul edx
	add eax, 261888
	shr eax, 19
	and eax, 31
	ror ebx, 27
	add ebx, eax
	mov eax, DWORD PTR [esi+12]
	mov edx, 5040
	mul edx
	add eax, 261888
	shr eax, 19
	and eax, 31
	ror ebx, 27
	add ebx, eax
	mov eax, DWORD PTR [esi+8]
	mov edx, 5040
	mul edx
	add eax, 261888
	shr eax, 19
	and eax, 31
	ror ebx, 27
	add ebx, eax
	mov eax, DWORD PTR [esi+4]
	mov edx, 5040
	mul edx
	add eax, 261888
	shr eax, 19
	and eax, 31
	ror ebx, 27
	add ebx, eax
	mov eax, DWORD PTR [esi]
	mov edx, 5040
	mul edx
	add eax, 261888
	shr eax, 19
	and eax, 31
	ror ebx, 27
	add ebx, eax
	mov eax, ebx
	mov BYTE PTR [edi], al
	shr eax, 8
	mov BYTE PTR [edi+1], al
	shr eax, 8
	mov BYTE PTR [edi+2], al
	shr eax, 8
	mov BYTE PTR [edi+3], al
	mov eax, ebp
	mov BYTE PTR [edi+4], al
	add esi, 32
	add edi, 5
	sub ecx, 1
	jne 23b
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
