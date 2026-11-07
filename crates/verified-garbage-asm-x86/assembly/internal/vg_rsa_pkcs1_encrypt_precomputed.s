// The functions of `src/internal/vg_rsa_pkcs1_encrypt_precomputed.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_pkcs1_encrypt_precomputed:
	push ebx
	push ebp
	push esi
	push edi
	lea esp, [esp-1072]
	mov edi, esp
	add edi, 48
	mov esi, DWORD PTR [esp+1124]
	mov ecx, DWORD PTR [esp+1128]
	mov eax, 0
	mov BYTE PTR [edi], al
	mov eax, 2
	mov BYTE PTR [edi+1], al
	add edi, 2
	mov ebx, 0
20:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [edi], al
	sub eax, 1
	sbb eax, eax
	or ebx, eax
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 20b
	mov eax, 0
	mov BYTE PTR [edi], al
	add edi, 1
	mov DWORD PTR [esp+40], ebx
	mov ebx, edi
	mov esi, DWORD PTR [esp+1116]
	mov ecx, DWORD PTR [esp+1120]
	cmp ecx, 0
	je 21f
23:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 23b
	jmp 22f
21:
22:
	mov eax, DWORD PTR [esp+1092]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+1104]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+1140]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+1144]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+1108]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+1112]
	mov DWORD PTR [esp+20], eax
	mov eax, esp
	add eax, 48
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+1104]
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+1132]
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+1136]
	mov DWORD PTR [esp+36], eax
	call {vg_rsa_public_precomputed_checked}
	mov ebx, DWORD PTR [esp+40]
	xor ebx, -1
	mov edi, eax
	and edi, ebx
	mov esi, DWORD PTR [esp+1092]
	mov ecx, DWORD PTR [esp+1104]
24:
	movzx edx, BYTE PTR [esi]
	and edx, ebx
	mov BYTE PTR [esi], dl
	add esi, 1
	sub ecx, 1
	jne 24b
	mov esi, esp
	add esi, 48
	mov ecx, DWORD PTR [esp+1104]
	mov eax, 0
25:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 25b
	mov eax, edi
	lea esp, [esp+1072]
	mov edi, DWORD PTR [esp]
	mov esi, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp+8]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	ret
	.p2align 6
