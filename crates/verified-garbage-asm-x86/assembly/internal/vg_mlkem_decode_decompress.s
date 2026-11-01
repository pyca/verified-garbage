// The functions of `src/internal/vg_mlkem_decode_decompress.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem_decode_decompress:
	push ebx
	push esi
	push edi
	push ebp
	mov esi, DWORD PTR [esp+20]
	mov edi, DWORD PTR [esp+32]
	mov eax, DWORD PTR [esp+28]
	cmp eax, 1
	je 20f
	cmp eax, 4
	je 22f
	mov ecx, 64
24:
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
	and eax, 1023
	mov edx, 3329
	mul edx
	add eax, 512
	shr eax, 10
	mov DWORD PTR [edi], eax
	mov eax, ebx
	shr eax, 10
	and eax, 1023
	mov edx, 3329
	mul edx
	add eax, 512
	shr eax, 10
	mov DWORD PTR [edi+4], eax
	mov eax, ebx
	shr eax, 20
	and eax, 1023
	mov edx, 3329
	mul edx
	add eax, 512
	shr eax, 10
	mov DWORD PTR [edi+8], eax
	mov eax, ebx
	shr eax, 30
	movzx edx, BYTE PTR [esi+4]
	add edx, edx
	add edx, edx
	add eax, edx
	mov edx, 3329
	mul edx
	add eax, 512
	shr eax, 10
	mov DWORD PTR [edi+12], eax
	add esi, 5
	add edi, 16
	sub ecx, 1
	jne 24b
	jmp 23f
22:
	mov ecx, 128
25:
	movzx ebx, BYTE PTR [esi]
	mov eax, ebx
	and eax, 15
	mov edx, 3329
	mul edx
	add eax, 8
	shr eax, 4
	mov DWORD PTR [edi], eax
	mov eax, ebx
	shr eax, 4
	and eax, 15
	mov edx, 3329
	mul edx
	add eax, 8
	shr eax, 4
	mov DWORD PTR [edi+4], eax
	add esi, 1
	add edi, 8
	sub ecx, 1
	jne 25b
23:
	jmp 21f
20:
	mov ecx, 32
26:
	movzx ebx, BYTE PTR [esi]
	mov eax, ebx
	and eax, 1
	mov edx, 3329
	mul edx
	add eax, 1
	shr eax, 1
	mov DWORD PTR [edi], eax
	mov eax, ebx
	shr eax, 1
	and eax, 1
	mov edx, 3329
	mul edx
	add eax, 1
	shr eax, 1
	mov DWORD PTR [edi+4], eax
	mov eax, ebx
	shr eax, 2
	and eax, 1
	mov edx, 3329
	mul edx
	add eax, 1
	shr eax, 1
	mov DWORD PTR [edi+8], eax
	mov eax, ebx
	shr eax, 3
	and eax, 1
	mov edx, 3329
	mul edx
	add eax, 1
	shr eax, 1
	mov DWORD PTR [edi+12], eax
	mov eax, ebx
	shr eax, 4
	and eax, 1
	mov edx, 3329
	mul edx
	add eax, 1
	shr eax, 1
	mov DWORD PTR [edi+16], eax
	mov eax, ebx
	shr eax, 5
	and eax, 1
	mov edx, 3329
	mul edx
	add eax, 1
	shr eax, 1
	mov DWORD PTR [edi+20], eax
	mov eax, ebx
	shr eax, 6
	and eax, 1
	mov edx, 3329
	mul edx
	add eax, 1
	shr eax, 1
	mov DWORD PTR [edi+24], eax
	mov eax, ebx
	shr eax, 7
	and eax, 1
	mov edx, 3329
	mul edx
	add eax, 1
	shr eax, 1
	mov DWORD PTR [edi+28], eax
	add esi, 1
	add edi, 32
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
