// The functions of `src/internal/vg_mldsa_bit_pack.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_bit_pack:
	push ebx
	push esi
	push edi
	push ebp
	mov esi, DWORD PTR [esp+20]
	mov edi, DWORD PTR [esp+32]
	mov eax, DWORD PTR [esp+28]
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
	mov eax, 524288
	sub eax, DWORD PTR [esi]
	sbb edx, edx
	and edx, 8380417
	add eax, edx
	add ebx, eax
	mov BYTE PTR [edi], bl
	shr ebx, 8
	mov BYTE PTR [edi+1], bl
	shr ebx, 8
	mov eax, 524288
	sub eax, DWORD PTR [esi+4]
	sbb edx, edx
	and edx, 8380417
	add eax, edx
	ror eax, 28
	add ebx, eax
	mov BYTE PTR [edi+2], bl
	shr ebx, 8
	mov BYTE PTR [edi+3], bl
	shr ebx, 8
	mov BYTE PTR [edi+4], bl
	shr ebx, 8
	add esi, 8
	add edi, 5
	sub ecx, 1
	jne 28b
	jmp 27f
26:
	mov ecx, 64
29:
	mov ebx, 0
	mov eax, 131072
	sub eax, DWORD PTR [esi]
	sbb edx, edx
	and edx, 8380417
	add eax, edx
	add ebx, eax
	mov BYTE PTR [edi], bl
	shr ebx, 8
	mov BYTE PTR [edi+1], bl
	shr ebx, 8
	mov eax, 131072
	sub eax, DWORD PTR [esi+4]
	sbb edx, edx
	and edx, 8380417
	add eax, edx
	ror eax, 30
	add ebx, eax
	mov BYTE PTR [edi+2], bl
	shr ebx, 8
	mov BYTE PTR [edi+3], bl
	shr ebx, 8
	mov eax, 131072
	sub eax, DWORD PTR [esi+8]
	sbb edx, edx
	and edx, 8380417
	add eax, edx
	ror eax, 28
	add ebx, eax
	mov BYTE PTR [edi+4], bl
	shr ebx, 8
	mov BYTE PTR [edi+5], bl
	shr ebx, 8
	mov eax, 131072
	sub eax, DWORD PTR [esi+12]
	sbb edx, edx
	and edx, 8380417
	add eax, edx
	ror eax, 26
	add ebx, eax
	mov BYTE PTR [edi+6], bl
	shr ebx, 8
	mov BYTE PTR [edi+7], bl
	shr ebx, 8
	mov BYTE PTR [edi+8], bl
	shr ebx, 8
	add esi, 16
	add edi, 9
	sub ecx, 1
	jne 29b
27:
	jmp 25f
24:
	mov ecx, 32
210:
	mov ebx, 0
	mov eax, 4096
	sub eax, DWORD PTR [esi]
	sbb edx, edx
	and edx, 8380417
	add eax, edx
	add ebx, eax
	mov BYTE PTR [edi], bl
	shr ebx, 8
	mov eax, 4096
	sub eax, DWORD PTR [esi+4]
	sbb edx, edx
	and edx, 8380417
	add eax, edx
	ror eax, 27
	add ebx, eax
	mov BYTE PTR [edi+1], bl
	shr ebx, 8
	mov BYTE PTR [edi+2], bl
	shr ebx, 8
	mov eax, 4096
	sub eax, DWORD PTR [esi+8]
	sbb edx, edx
	and edx, 8380417
	add eax, edx
	ror eax, 30
	add ebx, eax
	mov BYTE PTR [edi+3], bl
	shr ebx, 8
	mov eax, 4096
	sub eax, DWORD PTR [esi+12]
	sbb edx, edx
	and edx, 8380417
	add eax, edx
	ror eax, 25
	add ebx, eax
	mov BYTE PTR [edi+4], bl
	shr ebx, 8
	mov BYTE PTR [edi+5], bl
	shr ebx, 8
	mov eax, 4096
	sub eax, DWORD PTR [esi+16]
	sbb edx, edx
	and edx, 8380417
	add eax, edx
	ror eax, 28
	add ebx, eax
	mov BYTE PTR [edi+6], bl
	shr ebx, 8
	mov BYTE PTR [edi+7], bl
	shr ebx, 8
	mov eax, 4096
	sub eax, DWORD PTR [esi+20]
	sbb edx, edx
	and edx, 8380417
	add eax, edx
	ror eax, 31
	add ebx, eax
	mov BYTE PTR [edi+8], bl
	shr ebx, 8
	mov eax, 4096
	sub eax, DWORD PTR [esi+24]
	sbb edx, edx
	and edx, 8380417
	add eax, edx
	ror eax, 26
	add ebx, eax
	mov BYTE PTR [edi+9], bl
	shr ebx, 8
	mov BYTE PTR [edi+10], bl
	shr ebx, 8
	mov eax, 4096
	sub eax, DWORD PTR [esi+28]
	sbb edx, edx
	and edx, 8380417
	add eax, edx
	ror eax, 29
	add ebx, eax
	mov BYTE PTR [edi+11], bl
	shr ebx, 8
	mov BYTE PTR [edi+12], bl
	shr ebx, 8
	add esi, 32
	add edi, 13
	sub ecx, 1
	jne 210b
25:
	jmp 23f
22:
	mov ecx, 128
211:
	mov ebx, 0
	mov eax, 4
	sub eax, DWORD PTR [esi]
	sbb edx, edx
	and edx, 8380417
	add eax, edx
	add ebx, eax
	mov eax, 4
	sub eax, DWORD PTR [esi+4]
	sbb edx, edx
	and edx, 8380417
	add eax, edx
	ror eax, 28
	add ebx, eax
	mov BYTE PTR [edi], bl
	shr ebx, 8
	add esi, 8
	add edi, 1
	sub ecx, 1
	jne 211b
23:
	jmp 21f
20:
	mov ecx, 32
212:
	mov ebx, 0
	mov eax, 2
	sub eax, DWORD PTR [esi]
	sbb edx, edx
	and edx, 8380417
	add eax, edx
	add ebx, eax
	mov eax, 2
	sub eax, DWORD PTR [esi+4]
	sbb edx, edx
	and edx, 8380417
	add eax, edx
	ror eax, 29
	add ebx, eax
	mov eax, 2
	sub eax, DWORD PTR [esi+8]
	sbb edx, edx
	and edx, 8380417
	add eax, edx
	ror eax, 26
	add ebx, eax
	mov BYTE PTR [edi], bl
	shr ebx, 8
	mov eax, 2
	sub eax, DWORD PTR [esi+12]
	sbb edx, edx
	and edx, 8380417
	add eax, edx
	ror eax, 31
	add ebx, eax
	mov eax, 2
	sub eax, DWORD PTR [esi+16]
	sbb edx, edx
	and edx, 8380417
	add eax, edx
	ror eax, 28
	add ebx, eax
	mov eax, 2
	sub eax, DWORD PTR [esi+20]
	sbb edx, edx
	and edx, 8380417
	add eax, edx
	ror eax, 25
	add ebx, eax
	mov BYTE PTR [edi+1], bl
	shr ebx, 8
	mov eax, 2
	sub eax, DWORD PTR [esi+24]
	sbb edx, edx
	and edx, 8380417
	add eax, edx
	ror eax, 30
	add ebx, eax
	mov eax, 2
	sub eax, DWORD PTR [esi+28]
	sbb edx, edx
	and edx, 8380417
	add eax, edx
	ror eax, 27
	add ebx, eax
	mov BYTE PTR [edi+2], bl
	shr ebx, 8
	add esi, 32
	add edi, 3
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
