// The functions of `src/pbkdf2_md5.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_pbkdf2_hmac_md5:
	lea esp, [esp-1060]
	mov eax, DWORD PTR [esp+1064]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+1068]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+1072]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+1076]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+1080]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+1084]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+1088]
	mov DWORD PTR [esp+28], eax
	mov eax, esp
	add eax, 36
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [eax+384], ebx
	mov DWORD PTR [eax+388], esi
	mov DWORD PTR [eax+392], edi
	mov DWORD PTR [eax+396], ebp
	mov ebp, eax
	mov ecx, DWORD PTR [esp+8]
	cmp ecx, 65
	jae 20f
	mov edx, DWORD PTR [esp+4]
	jmp 21f
20:
	mov edi, ebp
	add edi, 640
	push edi
	call {vg_md5_init}
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
	call {vg_md5_update_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+8]
	mov ecx, 0
	mov edx, ebp
	add edx, 752
	push ebp
	push edx
	push ecx
	push eax
	push edi
	call {vg_md5_finalize_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, ebp
	add edx, 752
	mov ecx, 16
21:
	mov edi, ebp
	add edi, 400
	mov esi, ebp
	add esi, 480
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call {vg_hmac_md5_init_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ecx, 0
22:
	mov eax, ebp
	add eax, ecx
	movzx edx, BYTE PTR [eax+400]
	mov eax, ebp
	add eax, ecx
	mov BYTE PTR [eax+560], dl
	add ecx, 1
	cmp ecx, 80
	jne 22b
	mov edi, ebp
	add edi, 560
	mov eax, 0
	mov esi, 64
	mov ecx, DWORD PTR [esp+16]
	mov edx, DWORD PTR [esp+12]
	push ebp
	push ecx
	push edx
	push eax
	push esi
	push edi
	call {vg_md5_update_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1
	bswap eax
	mov DWORD PTR [ebp+768], eax
	mov ebx, 0
	mov ecx, DWORD PTR [esp+28]
	test ecx, ecx
	je 23f
25:
	mov ecx, 0
26:
	mov eax, ebp
	add eax, ecx
	movzx edx, BYTE PTR [eax+560]
	mov eax, ebp
	add eax, ecx
	mov BYTE PTR [eax+640], dl
	add ecx, 1
	cmp ecx, 80
	jne 26b
	mov edi, ebp
	add edi, 640
	mov esi, DWORD PTR [esp+16]
	add esi, 64
	mov eax, 0
	mov ecx, 4
	mov edx, ebp
	add edx, 768
	push ebp
	push ecx
	push edx
	push eax
	push esi
	push edi
	call {vg_md5_update_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, ebp
	add edx, 640
	mov esi, ebp
	add esi, 480
	mov eax, DWORD PTR [esp+16]
	add eax, 68
	mov ecx, 0
	mov edi, ebp
	add edi, 720
	push ebp
	push edi
	push ecx
	push eax
	push esi
	push edx
	call {vg_hmac_md5_finalize_scratch}
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
	movzx edx, BYTE PTR [eax+720]
	mov eax, ebp
	add eax, ecx
	mov BYTE PTR [eax+736], dl
	add ecx, 1
	cmp ecx, 16
	jne 27b
	mov esi, ebp
	add esi, 400
	mov eax, ebp
	add eax, 720
	mov ecx, DWORD PTR [esp+20]
	sub ecx, 1
	mov edx, ebp
	add edx, 736
	push ebp
	push edx
	push ecx
	push eax
	push esi
	call {vg_pbkdf2_hmac_md5_iterate}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ecx, DWORD PTR [esp+28]
	sub ecx, ebx
	cmp ecx, 16
	jb 28f
	mov ecx, 16
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
	movzx edx, BYTE PTR [eax+736]
	mov eax, edi
	add eax, ecx
	mov BYTE PTR [eax], dl
	add ecx, 1
	cmp ecx, esi
	jne 210b
	add ebx, esi
	mov eax, DWORD PTR [ebp+768]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [ebp+768], eax
	mov eax, DWORD PTR [esp+28]
	cmp ebx, eax
	jne 25b
	jmp 24f
23:
24:
	mov eax, ebp
	mov ebx, DWORD PTR [eax+384]
	mov esi, DWORD PTR [eax+388]
	mov edi, DWORD PTR [eax+392]
	mov ebp, DWORD PTR [eax+396]
	lea esp, [esp+1060]
	ret
	.p2align 6
