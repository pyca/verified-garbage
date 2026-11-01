// The functions of `src/internal/vg_mlkem1024_decode_decompress.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem1024_decode_decompress:
	push ebx
	push esi
	push edi
	push ebp
	mov esi, DWORD PTR [esp+20]
	mov edi, DWORD PTR [esp+32]
	mov eax, DWORD PTR [esp+28]
	cmp eax, 5
	je 20f
	mov ecx, 32
22:
	movzx ebx, BYTE PTR [esi+3]
	movzx eax, BYTE PTR [esi+2]
	ror ebx, 24
	add ebx, eax
	movzx eax, BYTE PTR [esi+1]
	ror ebx, 24
	add ebx, eax
	movzx eax, BYTE PTR [esi]
	ror ebx, 24
	add ebx, eax
	mov eax, ebx
	and eax, 2047
	mov edx, 3329
	mul edx
	add eax, 1024
	shr eax, 11
	mov DWORD PTR [edi], eax
	mov eax, ebx
	shr eax, 11
	and eax, 2047
	mov edx, 3329
	mul edx
	add eax, 1024
	shr eax, 11
	mov DWORD PTR [edi+4], eax
	movzx edx, BYTE PTR [esi+4]
	and edx, 1
	ror edx, 22
	mov eax, ebx
	shr eax, 22
	add eax, edx
	mov edx, 3329
	mul edx
	add eax, 1024
	shr eax, 11
	mov DWORD PTR [edi+8], eax
	movzx ebx, BYTE PTR [esi+7]
	movzx eax, BYTE PTR [esi+6]
	ror ebx, 24
	add ebx, eax
	movzx eax, BYTE PTR [esi+5]
	ror ebx, 24
	add ebx, eax
	movzx eax, BYTE PTR [esi+4]
	ror ebx, 24
	add ebx, eax
	mov eax, ebx
	shr eax, 1
	and eax, 2047
	mov edx, 3329
	mul edx
	add eax, 1024
	shr eax, 11
	mov DWORD PTR [edi+12], eax
	mov eax, ebx
	shr eax, 12
	and eax, 2047
	mov edx, 3329
	mul edx
	add eax, 1024
	shr eax, 11
	mov DWORD PTR [edi+16], eax
	movzx edx, BYTE PTR [esi+8]
	and edx, 3
	ror edx, 23
	mov eax, ebx
	shr eax, 23
	add eax, edx
	mov edx, 3329
	mul edx
	add eax, 1024
	shr eax, 11
	mov DWORD PTR [edi+20], eax
	movzx ebx, BYTE PTR [esi+10]
	movzx eax, BYTE PTR [esi+9]
	ror ebx, 24
	add ebx, eax
	movzx eax, BYTE PTR [esi+8]
	ror ebx, 24
	add ebx, eax
	mov eax, ebx
	shr eax, 2
	and eax, 2047
	mov edx, 3329
	mul edx
	add eax, 1024
	shr eax, 11
	mov DWORD PTR [edi+24], eax
	mov eax, ebx
	shr eax, 13
	and eax, 2047
	mov edx, 3329
	mul edx
	add eax, 1024
	shr eax, 11
	mov DWORD PTR [edi+28], eax
	add esi, 11
	add edi, 32
	sub ecx, 1
	jne 22b
	jmp 21f
20:
	mov ecx, 32
23:
	movzx ebx, BYTE PTR [esi+3]
	movzx eax, BYTE PTR [esi+2]
	ror ebx, 24
	add ebx, eax
	movzx eax, BYTE PTR [esi+1]
	ror ebx, 24
	add ebx, eax
	movzx eax, BYTE PTR [esi]
	ror ebx, 24
	add ebx, eax
	mov eax, ebx
	and eax, 31
	mov edx, 3329
	mul edx
	add eax, 16
	shr eax, 5
	mov DWORD PTR [edi], eax
	mov eax, ebx
	shr eax, 5
	and eax, 31
	mov edx, 3329
	mul edx
	add eax, 16
	shr eax, 5
	mov DWORD PTR [edi+4], eax
	mov eax, ebx
	shr eax, 10
	and eax, 31
	mov edx, 3329
	mul edx
	add eax, 16
	shr eax, 5
	mov DWORD PTR [edi+8], eax
	mov eax, ebx
	shr eax, 15
	and eax, 31
	mov edx, 3329
	mul edx
	add eax, 16
	shr eax, 5
	mov DWORD PTR [edi+12], eax
	mov eax, ebx
	shr eax, 20
	and eax, 31
	mov edx, 3329
	mul edx
	add eax, 16
	shr eax, 5
	mov DWORD PTR [edi+16], eax
	mov eax, ebx
	shr eax, 25
	and eax, 31
	mov edx, 3329
	mul edx
	add eax, 16
	shr eax, 5
	mov DWORD PTR [edi+20], eax
	movzx edx, BYTE PTR [esi+4]
	and edx, 7
	ror edx, 30
	mov eax, ebx
	shr eax, 30
	add eax, edx
	mov edx, 3329
	mul edx
	add eax, 16
	shr eax, 5
	mov DWORD PTR [edi+24], eax
	movzx ebx, BYTE PTR [esi+4]
	mov eax, ebx
	shr eax, 3
	and eax, 31
	mov edx, 3329
	mul edx
	add eax, 16
	shr eax, 5
	mov DWORD PTR [edi+28], eax
	add esi, 5
	add edi, 32
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
