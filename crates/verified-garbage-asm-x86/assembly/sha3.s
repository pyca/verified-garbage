// The functions of `src/sha3.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_keccak_absorb:
	lea esp, [esp-668]
	mov eax, DWORD PTR [esp+672]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+676]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+680]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+684]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+688]
	mov DWORD PTR [esp+20], eax
	mov eax, esp
	add eax, 28
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+512], ebx
	mov DWORD PTR [eax+516], esi
	mov DWORD PTR [eax+520], edi
	mov DWORD PTR [eax+524], ebp
	mov ebp, eax
	mov ebx, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+12]
	add ecx, ebx
	mov DWORD PTR [ebp+528], ecx
	mov ecx, DWORD PTR [esp+8]
	mov DWORD PTR [ebp+532], ecx
	mov esi, DWORD PTR [esp+16]
	mov edi, DWORD PTR [esp+20]
	test edi, edi
	je 20f
22:
	mov ecx, DWORD PTR [ebp+528]
	mov edx, DWORD PTR [ebp+532]
	movzx eax, BYTE PTR [esi]
	xor eax, DWORD PTR [ecx]
	mov BYTE PTR [ecx], al
	add ecx, 1
	mov DWORD PTR [ebp+528], ecx
	mov DWORD PTR [ebp+532], edx
	add esi, 1
	sub edi, 1
	mov eax, ecx
	sub eax, ebx
	cmp eax, edx
	je 23f
	jmp 24f
23:
	mov DWORD PTR [ebp+528], ebx
	push ebp
	push ebx
	call {vg_keccak_f1600}
	pop eax
	pop eax
24:
	test edi, edi
	jne 22b
	jmp 21f
20:
21:
	mov eax, DWORD PTR [ebp+528]
	sub eax, ebx
	mov ecx, ebp
	mov ebx, DWORD PTR [ecx+512]
	mov esi, DWORD PTR [ecx+516]
	mov edi, DWORD PTR [ecx+520]
	mov ebp, DWORD PTR [ecx+524]
	lea esp, [esp+668]
	ret
	.p2align 6

vg_keccak_absorb_scratch:
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+512], ebx
	mov DWORD PTR [eax+516], esi
	mov DWORD PTR [eax+520], edi
	mov DWORD PTR [eax+524], ebp
	mov ebp, eax
	mov ebx, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+12]
	add ecx, ebx
	mov DWORD PTR [ebp+528], ecx
	mov ecx, DWORD PTR [esp+8]
	mov DWORD PTR [ebp+532], ecx
	mov esi, DWORD PTR [esp+16]
	mov edi, DWORD PTR [esp+20]
	test edi, edi
	je 20f
22:
	mov ecx, DWORD PTR [ebp+528]
	mov edx, DWORD PTR [ebp+532]
	movzx eax, BYTE PTR [esi]
	xor eax, DWORD PTR [ecx]
	mov BYTE PTR [ecx], al
	add ecx, 1
	mov DWORD PTR [ebp+528], ecx
	mov DWORD PTR [ebp+532], edx
	add esi, 1
	sub edi, 1
	mov eax, ecx
	sub eax, ebx
	cmp eax, edx
	je 23f
	jmp 24f
23:
	mov DWORD PTR [ebp+528], ebx
	push ebp
	push ebx
	call {vg_keccak_f1600}
	pop eax
	pop eax
24:
	test edi, edi
	jne 22b
	jmp 21f
20:
21:
	mov eax, DWORD PTR [ebp+528]
	sub eax, ebx
	mov ecx, ebp
	mov ebx, DWORD PTR [ecx+512]
	mov esi, DWORD PTR [ecx+516]
	mov edi, DWORD PTR [ecx+520]
	mov ebp, DWORD PTR [ecx+524]
	ret
	.p2align 6

vg_keccak_pad:
	lea esp, [esp-664]
	mov eax, DWORD PTR [esp+668]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+672]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+676]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+680]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+512], ebx
	mov DWORD PTR [eax+516], esi
	mov esi, eax
	mov ecx, DWORD PTR [esp+4]
	mov eax, DWORD PTR [esp+8]
	mov edx, DWORD PTR [esp+12]
	add edx, ecx
	movzx ebx, BYTE PTR [edx]
	xor ebx, DWORD PTR [esp+16]
	mov BYTE PTR [edx], bl
	mov edx, ecx
	add edx, eax
	sub edx, 1
	movzx ebx, BYTE PTR [edx]
	xor ebx, 128
	mov BYTE PTR [edx], bl
	push esi
	push ecx
	call {vg_keccak_f1600}
	pop eax
	pop eax
	mov ebx, DWORD PTR [esi+512]
	mov esi, DWORD PTR [esi+516]
	lea esp, [esp+664]
	ret
	.p2align 6

vg_keccak_squeeze:
	lea esp, [esp-668]
	mov eax, DWORD PTR [esp+672]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+676]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+680]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+684]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+688]
	mov DWORD PTR [esp+20], eax
	mov eax, esp
	add eax, 28
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+512], ebx
	mov DWORD PTR [eax+516], esi
	mov DWORD PTR [eax+520], edi
	mov DWORD PTR [eax+524], ebp
	mov ebp, eax
	mov ebx, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+12]
	add ecx, ebx
	mov DWORD PTR [ebp+528], ecx
	mov ecx, DWORD PTR [esp+8]
	mov DWORD PTR [ebp+532], ecx
	mov esi, DWORD PTR [esp+16]
	mov edi, DWORD PTR [esp+20]
	test edi, edi
	je 20f
22:
	mov ecx, DWORD PTR [ebp+528]
	mov edx, DWORD PTR [ebp+532]
	mov eax, ecx
	sub eax, ebx
	cmp eax, edx
	je 23f
	jmp 24f
23:
	mov DWORD PTR [ebp+528], ebx
	push ebp
	push ebx
	call {vg_keccak_f1600}
	pop eax
	pop eax
24:
	mov ecx, DWORD PTR [ebp+528]
	mov edx, DWORD PTR [ebp+532]
	movzx eax, BYTE PTR [ecx]
	mov BYTE PTR [esi], al
	add ecx, 1
	mov DWORD PTR [ebp+528], ecx
	mov DWORD PTR [ebp+532], edx
	add esi, 1
	sub edi, 1
	jne 22b
	jmp 21f
20:
21:
	mov eax, DWORD PTR [ebp+528]
	sub eax, ebx
	mov ecx, ebp
	mov ebx, DWORD PTR [ecx+512]
	mov esi, DWORD PTR [ecx+516]
	mov edi, DWORD PTR [ecx+520]
	mov ebp, DWORD PTR [ecx+524]
	lea esp, [esp+668]
	ret
	.p2align 6
