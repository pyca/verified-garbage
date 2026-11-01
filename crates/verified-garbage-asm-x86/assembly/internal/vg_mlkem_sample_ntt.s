// The functions of `src/internal/vg_mlkem_sample_ntt.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem_sample_ntt:
	push ebx
	push esi
	push edi
	push ebp
	mov esi, DWORD PTR [esp+28]
	mov ebx, esi
	add ebx, 840
	mov eax, 0
	mov ecx, 50
20:
	mov DWORD PTR [ebx], eax
	add ebx, 4
	sub ecx, 1
	jne 20b
	mov eax, esi
	add eax, 840
	mov ecx, 168
	mov edx, 0
	mov ebx, DWORD PTR [esp+20]
	mov ebp, 34
	mov edi, esi
	add edi, 1040
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
	add eax, 840
	mov ecx, 168
	mov edx, 34
	mov ebx, 31
	mov edi, esi
	add edi, 1040
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
	add eax, 840
	mov ecx, 168
	mov edx, 0
	mov ebx, esi
	mov ebp, 840
	mov edi, esi
	add edi, 1040
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
	mov edi, DWORD PTR [esp+24]
	mov ecx, 0
	mov ebp, 280
21:
	movzx eax, BYTE PTR [esi]
	movzx edx, BYTE PTR [esi+1]
	mov ebx, edx
	and edx, 15
	ror edx, 24
	add eax, edx
	shr ebx, 4
	movzx edx, BYTE PTR [esi+2]
	ror edx, 28
	add ebx, edx
	cmp ecx, 256
	jb 22f
	jmp 23f
22:
	cmp eax, 3329
	jb 24f
	jmp 25f
24:
	mov DWORD PTR [edi], eax
	add edi, 4
	add ecx, 1
25:
	cmp ecx, 256
	jb 26f
	jmp 27f
26:
	cmp ebx, 3329
	jb 28f
	jmp 29f
28:
	mov DWORD PTR [edi], ebx
	add edi, 4
	add ecx, 1
29:
27:
23:
	add esi, 3
	sub ebp, 1
	jne 21b
	mov eax, ecx
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
