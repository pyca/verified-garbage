// The functions of `src/internal/vg_mldsa_bit_unpack.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_bit_unpack:
	push ebx
	push esi
	push edi
	push ebp
	mov esi, DWORD PTR [esp+20]
	mov edi, DWORD PTR [esp+36]
	mov eax, DWORD PTR [esp+32]
	cmp eax, 2
	je 20f
	cmp eax, 4
	je 22f
	cmp eax, 4096
	je 24f
	cmp eax, 131072
	je 26f
	mov ecx, 128
28:
	mov ebx, 0
	movzx eax, BYTE PTR [esi]
	add ebx, eax
	movzx eax, BYTE PTR [esi+1]
	ror eax, 24
	add ebx, eax
	movzx eax, BYTE PTR [esi+2]
	ror eax, 16
	add ebx, eax
	mov eax, ebx
	and eax, 1048575
	shr ebx, 20
	mov edx, 524288
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [edi], edx
	movzx eax, BYTE PTR [esi+3]
	ror eax, 28
	add ebx, eax
	movzx eax, BYTE PTR [esi+4]
	ror eax, 20
	add ebx, eax
	mov eax, ebx
	and eax, 1048575
	shr ebx, 20
	mov edx, 524288
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [edi+4], edx
	add esi, 5
	add edi, 8
	sub ecx, 1
	jne 28b
	jmp 27f
26:
	mov ecx, 64
29:
	mov ebx, 0
	movzx eax, BYTE PTR [esi]
	add ebx, eax
	movzx eax, BYTE PTR [esi+1]
	ror eax, 24
	add ebx, eax
	movzx eax, BYTE PTR [esi+2]
	ror eax, 16
	add ebx, eax
	mov eax, ebx
	and eax, 262143
	shr ebx, 18
	mov edx, 131072
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [edi], edx
	movzx eax, BYTE PTR [esi+3]
	ror eax, 26
	add ebx, eax
	movzx eax, BYTE PTR [esi+4]
	ror eax, 18
	add ebx, eax
	mov eax, ebx
	and eax, 262143
	shr ebx, 18
	mov edx, 131072
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [edi+4], edx
	movzx eax, BYTE PTR [esi+5]
	ror eax, 28
	add ebx, eax
	movzx eax, BYTE PTR [esi+6]
	ror eax, 20
	add ebx, eax
	mov eax, ebx
	and eax, 262143
	shr ebx, 18
	mov edx, 131072
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [edi+8], edx
	movzx eax, BYTE PTR [esi+7]
	ror eax, 30
	add ebx, eax
	movzx eax, BYTE PTR [esi+8]
	ror eax, 22
	add ebx, eax
	mov eax, ebx
	and eax, 262143
	shr ebx, 18
	mov edx, 131072
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [edi+12], edx
	add esi, 9
	add edi, 16
	sub ecx, 1
	jne 29b
27:
	jmp 25f
24:
	mov ecx, 32
210:
	mov ebx, 0
	movzx eax, BYTE PTR [esi]
	add ebx, eax
	movzx eax, BYTE PTR [esi+1]
	ror eax, 24
	add ebx, eax
	mov eax, ebx
	and eax, 8191
	shr ebx, 13
	mov edx, 4096
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [edi], edx
	movzx eax, BYTE PTR [esi+2]
	ror eax, 29
	add ebx, eax
	movzx eax, BYTE PTR [esi+3]
	ror eax, 21
	add ebx, eax
	mov eax, ebx
	and eax, 8191
	shr ebx, 13
	mov edx, 4096
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [edi+4], edx
	movzx eax, BYTE PTR [esi+4]
	ror eax, 26
	add ebx, eax
	mov eax, ebx
	and eax, 8191
	shr ebx, 13
	mov edx, 4096
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [edi+8], edx
	movzx eax, BYTE PTR [esi+5]
	ror eax, 31
	add ebx, eax
	movzx eax, BYTE PTR [esi+6]
	ror eax, 23
	add ebx, eax
	mov eax, ebx
	and eax, 8191
	shr ebx, 13
	mov edx, 4096
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [edi+12], edx
	movzx eax, BYTE PTR [esi+7]
	ror eax, 28
	add ebx, eax
	movzx eax, BYTE PTR [esi+8]
	ror eax, 20
	add ebx, eax
	mov eax, ebx
	and eax, 8191
	shr ebx, 13
	mov edx, 4096
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [edi+16], edx
	movzx eax, BYTE PTR [esi+9]
	ror eax, 25
	add ebx, eax
	mov eax, ebx
	and eax, 8191
	shr ebx, 13
	mov edx, 4096
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [edi+20], edx
	movzx eax, BYTE PTR [esi+10]
	ror eax, 30
	add ebx, eax
	movzx eax, BYTE PTR [esi+11]
	ror eax, 22
	add ebx, eax
	mov eax, ebx
	and eax, 8191
	shr ebx, 13
	mov edx, 4096
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [edi+24], edx
	movzx eax, BYTE PTR [esi+12]
	ror eax, 27
	add ebx, eax
	mov eax, ebx
	and eax, 8191
	shr ebx, 13
	mov edx, 4096
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [edi+28], edx
	add esi, 13
	add edi, 32
	sub ecx, 1
	jne 210b
25:
	jmp 23f
22:
	mov ecx, 128
211:
	mov ebx, 0
	movzx eax, BYTE PTR [esi]
	add ebx, eax
	mov eax, ebx
	and eax, 15
	shr ebx, 4
	mov edx, 4
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [edi], edx
	mov eax, ebx
	and eax, 15
	shr ebx, 4
	mov edx, 4
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [edi+4], edx
	add esi, 1
	add edi, 8
	sub ecx, 1
	jne 211b
23:
	jmp 21f
20:
	mov ecx, 32
212:
	mov ebx, 0
	movzx eax, BYTE PTR [esi]
	add ebx, eax
	mov eax, ebx
	and eax, 7
	shr ebx, 3
	mov edx, 2
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [edi], edx
	mov eax, ebx
	and eax, 7
	shr ebx, 3
	mov edx, 2
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [edi+4], edx
	movzx eax, BYTE PTR [esi+1]
	ror eax, 30
	add ebx, eax
	mov eax, ebx
	and eax, 7
	shr ebx, 3
	mov edx, 2
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [edi+8], edx
	mov eax, ebx
	and eax, 7
	shr ebx, 3
	mov edx, 2
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [edi+12], edx
	mov eax, ebx
	and eax, 7
	shr ebx, 3
	mov edx, 2
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [edi+16], edx
	movzx eax, BYTE PTR [esi+2]
	ror eax, 31
	add ebx, eax
	mov eax, ebx
	and eax, 7
	shr ebx, 3
	mov edx, 2
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [edi+20], edx
	mov eax, ebx
	and eax, 7
	shr ebx, 3
	mov edx, 2
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [edi+24], edx
	mov eax, ebx
	and eax, 7
	shr ebx, 3
	mov edx, 2
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [edi+28], edx
	add esi, 3
	add edi, 32
	sub ecx, 1
	jne 212b
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
