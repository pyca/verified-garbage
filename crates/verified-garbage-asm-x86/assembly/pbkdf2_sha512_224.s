// The functions of `src/pbkdf2_sha512_224.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_pbkdf2_hmac_sha512_224:
	lea esp, [esp-3444]
	mov eax, DWORD PTR [esp+3448]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+3452]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+3456]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+3460]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+3464]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+3468]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+3472]
	mov DWORD PTR [esp+28], eax
	mov eax, esp
	add eax, 36
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [eax+1872], ebx
	mov DWORD PTR [eax+1876], esi
	mov DWORD PTR [eax+1880], edi
	mov DWORD PTR [eax+1884], ebp
	mov ebp, eax
	mov ecx, DWORD PTR [esp+8]
	cmp ecx, 129
	jae 20f
	mov edx, DWORD PTR [esp+4]
	jmp 21f
20:
	mov edi, ebp
	add edi, 2464
	push edi
	call {vg_sha512_224_init}
	pop eax
	mov eax, 0
	mov esi, 0
	mov ecx, DWORD PTR [esp+8]
	mov edx, DWORD PTR [esp+4]
	push ebp
	push ecx
	push edx
	push eax
	push esi
	push edi
	call {vg_sha512_update_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+8]
	mov ecx, 0
	mov edx, ebp
	add edx, 2712
	push ebp
	push edx
	push ecx
	push eax
	push edi
	call {vg_sha512_finalize_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, ebp
	add edx, 2712
	mov ecx, 28
21:
	mov edi, ebp
	add edi, 1888
	mov esi, ebp
	add esi, 2080
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call {vg_hmac_sha512_224_init_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ecx, 0
22:
	mov eax, ebp
	add eax, ecx
	movzx edx, BYTE PTR [eax+1888]
	mov eax, ebp
	add eax, ecx
	mov BYTE PTR [eax+2272], dl
	add ecx, 1
	cmp ecx, 192
	jne 22b
	mov edi, ebp
	add edi, 2272
	mov eax, 0
	mov esi, 128
	mov ecx, DWORD PTR [esp+16]
	mov edx, DWORD PTR [esp+12]
	push ebp
	push ecx
	push edx
	push eax
	push esi
	push edi
	call {vg_sha512_update_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1
	bswap eax
	mov DWORD PTR [ebp+2776], eax
	mov ebx, 0
	mov ecx, DWORD PTR [esp+28]
	test ecx, ecx
	je 23f
25:
	mov ecx, 0
26:
	mov eax, ebp
	add eax, ecx
	movzx edx, BYTE PTR [eax+2272]
	mov eax, ebp
	add eax, ecx
	mov BYTE PTR [eax+2464], dl
	add ecx, 1
	cmp ecx, 192
	jne 26b
	mov edi, ebp
	add edi, 2464
	mov esi, DWORD PTR [esp+16]
	add esi, 128
	mov eax, 0
	mov ecx, 4
	mov edx, ebp
	add edx, 2776
	push ebp
	push ecx
	push edx
	push eax
	push esi
	push edi
	call {vg_sha512_update_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, ebp
	add edx, 2464
	mov esi, ebp
	add esi, 2080
	mov eax, DWORD PTR [esp+16]
	add eax, 132
	mov ecx, 0
	mov edi, ebp
	add edi, 2656
	push ebp
	push edi
	push ecx
	push eax
	push esi
	push edx
	call {vg_hmac_sha512_224_finalize_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ecx, 0
27:
	mov eax, ebp
	add eax, ecx
	movzx edx, BYTE PTR [eax+2656]
	mov eax, ebp
	add eax, ecx
	mov BYTE PTR [eax+2684], dl
	add ecx, 1
	cmp ecx, 28
	jne 27b
	mov esi, ebp
	add esi, 1888
	mov eax, ebp
	add eax, 2656
	mov ecx, DWORD PTR [esp+20]
	sub ecx, 1
	mov edx, ebp
	add edx, 2684
	push ebp
	push edx
	push ecx
	push eax
	push esi
	call {vg_pbkdf2_hmac_sha512_224_iterate}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ecx, DWORD PTR [esp+28]
	sub ecx, ebx
	cmp ecx, 28
	jb 28f
	mov ecx, 28
	jmp 29f
28:
29:
	mov esi, ecx
	mov edi, DWORD PTR [esp+24]
	add edi, ebx
	mov ecx, 0
210:
	mov eax, ebp
	add eax, ecx
	movzx edx, BYTE PTR [eax+2684]
	mov eax, edi
	add eax, ecx
	mov BYTE PTR [eax], dl
	add ecx, 1
	cmp ecx, esi
	jne 210b
	add ebx, esi
	mov eax, DWORD PTR [ebp+2776]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [ebp+2776], eax
	mov eax, DWORD PTR [esp+28]
	cmp ebx, eax
	jne 25b
	jmp 24f
23:
24:
	mov eax, ebp
	mov ebx, DWORD PTR [eax+1872]
	mov esi, DWORD PTR [eax+1876]
	mov edi, DWORD PTR [eax+1880]
	mov ebp, DWORD PTR [eax+1884]
	lea esp, [esp+3444]
	ret
	.p2align 6
