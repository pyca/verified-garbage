// The functions of `src/internal/vg_mldsa_rej_ntt_poly.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_rej_ntt_poly:
	push ebx
	push esi
	push edi
	push ebp
	mov esi, DWORD PTR [esp+28]
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
	mov ecx, 168
	mov edx, 0
	mov ebx, DWORD PTR [esp+20]
	mov ebp, 34
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
	mov ecx, 168
	mov edx, 34
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
	mov ecx, 168
	mov edx, 0
	mov ebx, esi
	add ebx, 840
	mov ebp, 1008
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
	add esi, 840
	mov edi, DWORD PTR [esp+24]
	mov ecx, 0
	mov ebp, 336
21:
	movzx eax, BYTE PTR [esi]
	movzx edx, BYTE PTR [esi+1]
	ror edx, 24
	add eax, edx
	movzx edx, BYTE PTR [esi+2]
	and edx, 127
	ror edx, 16
	add eax, edx
	cmp ecx, 256
	jb 22f
	jmp 23f
22:
	cmp eax, 8380417
	jb 24f
	jmp 25f
24:
	mov DWORD PTR [edi], eax
	add edi, 4
	add ecx, 1
25:
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
