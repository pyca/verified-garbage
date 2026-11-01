// The functions of `src/pbkdf2_sha256.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_pbkdf2_hmac_sha256:
	lea esp, [esp-1636]
	mov eax, DWORD PTR [esp+1640]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+1644]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+1648]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+1652]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+1656]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+1660]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+1664]
	mov DWORD PTR [esp+28], eax
	mov eax, esp
	add eax, 36
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [eax+832], ebx
	mov DWORD PTR [eax+836], esi
	mov DWORD PTR [eax+840], edi
	mov DWORD PTR [eax+844], ebp
	mov ebp, eax
	mov ecx, DWORD PTR [esp+8]
	cmp ecx, 65
	jae 20f
	mov edx, DWORD PTR [esp+4]
	jmp 21f
20:
	mov edi, ebp
	add edi, 1136
	push edi
	call {vg_sha256_init}
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
	call {vg_sha256_update_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+8]
	mov ecx, 0
	mov edx, ebp
	add edx, 1296
	push ebp
	push edx
	push ecx
	push eax
	push edi
	call {vg_sha256_finalize_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, ebp
	add edx, 1296
	mov ecx, 32
21:
	mov edi, ebp
	add edi, 848
	mov esi, ebp
	add esi, 944
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call {vg_hmac_sha256_init_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ecx, 0
22:
	mov eax, ebp
	add eax, ecx
	movzx edx, BYTE PTR [eax+848]
	mov eax, ebp
	add eax, ecx
	mov BYTE PTR [eax+1040], dl
	add ecx, 1
	cmp ecx, 96
	jne 22b
	mov edi, ebp
	add edi, 1040
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
	call {vg_sha256_update_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1
	bswap eax
	mov DWORD PTR [ebp+1328], eax
	mov ebx, 0
	mov ecx, DWORD PTR [esp+28]
	test ecx, ecx
	je 23f
25:
	mov ecx, 0
26:
	mov eax, ebp
	add eax, ecx
	movzx edx, BYTE PTR [eax+1040]
	mov eax, ebp
	add eax, ecx
	mov BYTE PTR [eax+1136], dl
	add ecx, 1
	cmp ecx, 96
	jne 26b
	mov edi, ebp
	add edi, 1136
	mov esi, DWORD PTR [esp+16]
	add esi, 64
	mov eax, 0
	mov ecx, 4
	mov edx, ebp
	add edx, 1328
	push ebp
	push ecx
	push edx
	push eax
	push esi
	push edi
	call {vg_sha256_update_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, ebp
	add edx, 1136
	mov esi, ebp
	add esi, 944
	mov eax, DWORD PTR [esp+16]
	add eax, 68
	mov ecx, 0
	mov edi, ebp
	add edi, 1232
	push ebp
	push edi
	push ecx
	push eax
	push esi
	push edx
	call {vg_hmac_sha256_finalize_scratch}
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
	movzx edx, BYTE PTR [eax+1232]
	mov eax, ebp
	add eax, ecx
	mov BYTE PTR [eax+1264], dl
	add ecx, 1
	cmp ecx, 32
	jne 27b
	mov esi, ebp
	add esi, 848
	mov eax, ebp
	add eax, 1232
	mov ecx, DWORD PTR [esp+20]
	sub ecx, 1
	mov edx, ebp
	add edx, 1264
	push ebp
	push edx
	push ecx
	push eax
	push esi
	call {vg_pbkdf2_hmac_sha256_iterate}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ecx, DWORD PTR [esp+28]
	sub ecx, ebx
	cmp ecx, 32
	jb 28f
	mov ecx, 32
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
	movzx edx, BYTE PTR [eax+1264]
	mov eax, edi
	add eax, ecx
	mov BYTE PTR [eax], dl
	add ecx, 1
	cmp ecx, esi
	jne 210b
	add ebx, esi
	mov eax, DWORD PTR [ebp+1328]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [ebp+1328], eax
	mov eax, DWORD PTR [esp+28]
	cmp ebx, eax
	jne 25b
	jmp 24f
23:
24:
	mov eax, ebp
	mov ebx, DWORD PTR [eax+832]
	mov esi, DWORD PTR [eax+836]
	mov edi, DWORD PTR [eax+840]
	mov ebp, DWORD PTR [eax+844]
	lea esp, [esp+1636]
	ret
	.p2align 6

vg_pbkdf2_hmac_sha256_shani:
	lea esp, [esp-1636]
	mov eax, DWORD PTR [esp+1640]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+1644]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+1648]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+1652]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+1656]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+1660]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+1664]
	mov DWORD PTR [esp+28], eax
	mov eax, esp
	add eax, 36
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [eax+832], ebx
	mov DWORD PTR [eax+836], esi
	mov DWORD PTR [eax+840], edi
	mov DWORD PTR [eax+844], ebp
	mov ebp, eax
	mov ecx, DWORD PTR [esp+8]
	cmp ecx, 65
	jae 20f
	mov edx, DWORD PTR [esp+4]
	jmp 21f
20:
	mov edi, ebp
	add edi, 1136
	push edi
	call {vg_sha256_init}
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
	call {vg_sha256_update_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+8]
	mov ecx, 0
	mov edx, ebp
	add edx, 1296
	push ebp
	push edx
	push ecx
	push eax
	push edi
	call {vg_sha256_finalize_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, ebp
	add edx, 1296
	mov ecx, 32
21:
	mov edi, ebp
	add edi, 848
	mov esi, ebp
	add esi, 944
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call {vg_hmac_sha256_init_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ecx, 0
22:
	mov eax, ebp
	add eax, ecx
	movzx edx, BYTE PTR [eax+848]
	mov eax, ebp
	add eax, ecx
	mov BYTE PTR [eax+1040], dl
	add ecx, 1
	cmp ecx, 96
	jne 22b
	mov edi, ebp
	add edi, 1040
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
	call {vg_sha256_update_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1
	bswap eax
	mov DWORD PTR [ebp+1328], eax
	mov ebx, 0
	mov ecx, DWORD PTR [esp+28]
	test ecx, ecx
	je 23f
25:
	mov ecx, 0
26:
	mov eax, ebp
	add eax, ecx
	movzx edx, BYTE PTR [eax+1040]
	mov eax, ebp
	add eax, ecx
	mov BYTE PTR [eax+1136], dl
	add ecx, 1
	cmp ecx, 96
	jne 26b
	mov edi, ebp
	add edi, 1136
	mov esi, DWORD PTR [esp+16]
	add esi, 64
	mov eax, 0
	mov ecx, 4
	mov edx, ebp
	add edx, 1328
	push ebp
	push ecx
	push edx
	push eax
	push esi
	push edi
	call {vg_sha256_update_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, ebp
	add edx, 1136
	mov esi, ebp
	add esi, 944
	mov eax, DWORD PTR [esp+16]
	add eax, 68
	mov ecx, 0
	mov edi, ebp
	add edi, 1232
	push ebp
	push edi
	push ecx
	push eax
	push esi
	push edx
	call {vg_hmac_sha256_finalize_scratch_shani}
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
	movzx edx, BYTE PTR [eax+1232]
	mov eax, ebp
	add eax, ecx
	mov BYTE PTR [eax+1264], dl
	add ecx, 1
	cmp ecx, 32
	jne 27b
	mov esi, ebp
	add esi, 848
	mov eax, ebp
	add eax, 1232
	mov ecx, DWORD PTR [esp+20]
	sub ecx, 1
	mov edx, ebp
	add edx, 1264
	push ebp
	push edx
	push ecx
	push eax
	push esi
	call {vg_pbkdf2_hmac_sha256_iterate_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ecx, DWORD PTR [esp+28]
	sub ecx, ebx
	cmp ecx, 32
	jb 28f
	mov ecx, 32
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
	movzx edx, BYTE PTR [eax+1264]
	mov eax, edi
	add eax, ecx
	mov BYTE PTR [eax], dl
	add ecx, 1
	cmp ecx, esi
	jne 210b
	add ebx, esi
	mov eax, DWORD PTR [ebp+1328]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [ebp+1328], eax
	mov eax, DWORD PTR [esp+28]
	cmp ebx, eax
	jne 25b
	jmp 24f
23:
24:
	mov eax, ebp
	mov ebx, DWORD PTR [eax+832]
	mov esi, DWORD PTR [eax+836]
	mov edi, DWORD PTR [eax+840]
	mov ebp, DWORD PTR [eax+844]
	lea esp, [esp+1636]
	ret
	.p2align 6
