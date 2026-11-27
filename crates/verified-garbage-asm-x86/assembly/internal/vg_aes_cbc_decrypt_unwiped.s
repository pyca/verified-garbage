// The functions of `src/internal/vg_aes_cbc_decrypt_unwiped.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_cbc_decrypt_unwiped:
	lea esp, [esp-1084]
	mov eax, DWORD PTR [esp+1088]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+1092]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+1096]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+1100]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+1104]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+1108]
	mov DWORD PTR [esp+24], eax
	mov eax, esp
	add eax, 32
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [eax+1024], ebx
	mov DWORD PTR [eax+1028], esi
	mov DWORD PTR [eax+1032], edi
	mov DWORD PTR [eax+1036], ebp
	mov esi, DWORD PTR [esp+16]
	mov edi, DWORD PTR [esp+20]
	test edi, edi
	je 20f
22:
	mov ebx, 64
	cmp edi, 64
	jb 23f
	jmp 24f
23:
	mov ebx, edi
24:
	mov ebp, DWORD PTR [esp+12]
	movdqu xmm0, XMMWORD PTR [ebp]
	mov eax, esi
	mov edx, DWORD PTR [esp+28]
	mov ecx, ebx
25:
	movdqu XMMWORD PTR [edx], xmm0
	movdqu xmm0, XMMWORD PTR [eax]
	add eax, 16
	add edx, 16
	sub ecx, 1
	jne 25b
	movdqu XMMWORD PTR [ebp], xmm0
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edx, esi
	mov ebp, DWORD PTR [esp+24]
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_decrypt_blocks}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [esp+28]
	mov ecx, ebx
26:
	movdqu xmm0, XMMWORD PTR [esi]
	movdqu xmm1, XMMWORD PTR [edx]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [esi], xmm0
	add esi, 16
	add edx, 16
	sub ecx, 1
	jne 26b
	sub edi, ebx
	jne 22b
	jmp 21f
20:
21:
	mov eax, DWORD PTR [esp+28]
	mov ebx, DWORD PTR [eax+1024]
	mov esi, DWORD PTR [eax+1028]
	mov edi, DWORD PTR [eax+1032]
	mov ebp, DWORD PTR [eax+1036]
	lea esp, [esp+1084]
	ret
	.p2align 6
