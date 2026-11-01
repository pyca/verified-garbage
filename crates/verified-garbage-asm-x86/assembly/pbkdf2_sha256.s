// The functions of `src/pbkdf2_sha256.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_pbkdf2_hmac_sha256_iterate:
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+160], ebx
	mov DWORD PTR [eax+164], esi
	mov DWORD PTR [eax+168], edi
	mov DWORD PTR [eax+172], ebp
	mov ebp, eax
	mov esi, DWORD PTR [esp+4]
	mov edi, DWORD PTR [esp+12]
	mov ebx, ebp
	add ebx, 176
	mov edx, DWORD PTR [esp+8]
	mov ecx, DWORD PTR [edx]
	mov DWORD PTR [ebx+32], ecx
	mov ecx, DWORD PTR [edx+4]
	mov DWORD PTR [ebx+36], ecx
	mov ecx, DWORD PTR [edx+8]
	mov DWORD PTR [ebx+40], ecx
	mov ecx, DWORD PTR [edx+12]
	mov DWORD PTR [ebx+44], ecx
	mov ecx, DWORD PTR [edx+16]
	mov DWORD PTR [ebx+48], ecx
	mov ecx, DWORD PTR [edx+20]
	mov DWORD PTR [ebx+52], ecx
	mov ecx, DWORD PTR [edx+24]
	mov DWORD PTR [ebx+56], ecx
	mov ecx, DWORD PTR [edx+28]
	mov DWORD PTR [ebx+60], ecx
	mov ecx, 128
	mov DWORD PTR [ebx+64], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+68], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+72], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+76], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+80], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+84], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+88], ecx
	mov ecx, 196608
	mov DWORD PTR [ebx+92], ecx
	test edi, edi
	je 20f
22:
	mov ecx, DWORD PTR [esi]
	mov DWORD PTR [ebx], ecx
	mov ecx, DWORD PTR [esi+4]
	mov DWORD PTR [ebx+4], ecx
	mov ecx, DWORD PTR [esi+8]
	mov DWORD PTR [ebx+8], ecx
	mov ecx, DWORD PTR [esi+12]
	mov DWORD PTR [ebx+12], ecx
	mov ecx, DWORD PTR [esi+16]
	mov DWORD PTR [ebx+16], ecx
	mov ecx, DWORD PTR [esi+20]
	mov DWORD PTR [ebx+20], ecx
	mov ecx, DWORD PTR [esi+24]
	mov DWORD PTR [ebx+24], ecx
	mov ecx, DWORD PTR [esi+28]
	mov DWORD PTR [ebx+28], ecx
	mov eax, ebx
	add eax, 32
	mov ecx, 1
	push ebp
	push ecx
	push eax
	push ebx
	call {vg_sha256_compress}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, ebx
	add eax, 32
	mov ecx, DWORD PTR [ebx]
	bswap ecx
	mov DWORD PTR [eax], ecx
	mov ecx, DWORD PTR [ebx+4]
	bswap ecx
	mov DWORD PTR [eax+4], ecx
	mov ecx, DWORD PTR [ebx+8]
	bswap ecx
	mov DWORD PTR [eax+8], ecx
	mov ecx, DWORD PTR [ebx+12]
	bswap ecx
	mov DWORD PTR [eax+12], ecx
	mov ecx, DWORD PTR [ebx+16]
	bswap ecx
	mov DWORD PTR [eax+16], ecx
	mov ecx, DWORD PTR [ebx+20]
	bswap ecx
	mov DWORD PTR [eax+20], ecx
	mov ecx, DWORD PTR [ebx+24]
	bswap ecx
	mov DWORD PTR [eax+24], ecx
	mov ecx, DWORD PTR [ebx+28]
	bswap ecx
	mov DWORD PTR [eax+28], ecx
	mov ecx, DWORD PTR [esi+96]
	mov DWORD PTR [ebx], ecx
	mov ecx, DWORD PTR [esi+100]
	mov DWORD PTR [ebx+4], ecx
	mov ecx, DWORD PTR [esi+104]
	mov DWORD PTR [ebx+8], ecx
	mov ecx, DWORD PTR [esi+108]
	mov DWORD PTR [ebx+12], ecx
	mov ecx, DWORD PTR [esi+112]
	mov DWORD PTR [ebx+16], ecx
	mov ecx, DWORD PTR [esi+116]
	mov DWORD PTR [ebx+20], ecx
	mov ecx, DWORD PTR [esi+120]
	mov DWORD PTR [ebx+24], ecx
	mov ecx, DWORD PTR [esi+124]
	mov DWORD PTR [ebx+28], ecx
	mov eax, ebx
	add eax, 32
	mov ecx, 1
	push ebp
	push ecx
	push eax
	push ebx
	call {vg_sha256_compress}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, ebx
	add eax, 32
	mov ecx, DWORD PTR [ebx]
	bswap ecx
	mov DWORD PTR [eax], ecx
	mov ecx, DWORD PTR [ebx+4]
	bswap ecx
	mov DWORD PTR [eax+4], ecx
	mov ecx, DWORD PTR [ebx+8]
	bswap ecx
	mov DWORD PTR [eax+8], ecx
	mov ecx, DWORD PTR [ebx+12]
	bswap ecx
	mov DWORD PTR [eax+12], ecx
	mov ecx, DWORD PTR [ebx+16]
	bswap ecx
	mov DWORD PTR [eax+16], ecx
	mov ecx, DWORD PTR [ebx+20]
	bswap ecx
	mov DWORD PTR [eax+20], ecx
	mov ecx, DWORD PTR [ebx+24]
	bswap ecx
	mov DWORD PTR [eax+24], ecx
	mov ecx, DWORD PTR [ebx+28]
	bswap ecx
	mov DWORD PTR [eax+28], ecx
	mov edx, DWORD PTR [esp+16]
	mov ecx, DWORD PTR [ebx+32]
	xor ecx, DWORD PTR [edx]
	mov DWORD PTR [edx], ecx
	mov ecx, DWORD PTR [ebx+36]
	xor ecx, DWORD PTR [edx+4]
	mov DWORD PTR [edx+4], ecx
	mov ecx, DWORD PTR [ebx+40]
	xor ecx, DWORD PTR [edx+8]
	mov DWORD PTR [edx+8], ecx
	mov ecx, DWORD PTR [ebx+44]
	xor ecx, DWORD PTR [edx+12]
	mov DWORD PTR [edx+12], ecx
	mov ecx, DWORD PTR [ebx+48]
	xor ecx, DWORD PTR [edx+16]
	mov DWORD PTR [edx+16], ecx
	mov ecx, DWORD PTR [ebx+52]
	xor ecx, DWORD PTR [edx+20]
	mov DWORD PTR [edx+20], ecx
	mov ecx, DWORD PTR [ebx+56]
	xor ecx, DWORD PTR [edx+24]
	mov DWORD PTR [edx+24], ecx
	mov ecx, DWORD PTR [ebx+60]
	xor ecx, DWORD PTR [edx+28]
	mov DWORD PTR [edx+28], ecx
	sub edi, 1
	jne 22b
	jmp 21f
20:
21:
	mov eax, ebp
	mov ebx, DWORD PTR [eax+160]
	mov esi, DWORD PTR [eax+164]
	mov edi, DWORD PTR [eax+168]
	mov ebp, DWORD PTR [eax+172]
	ret
	.p2align 6

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

vg_pbkdf2_hmac_sha256_scratch:
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
	ret
	.p2align 6

vg_pbkdf2_hmac_sha256_iterate_shani:
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+160], ebx
	mov DWORD PTR [eax+164], esi
	mov DWORD PTR [eax+168], edi
	mov DWORD PTR [eax+172], ebp
	mov ebp, eax
	mov esi, DWORD PTR [esp+4]
	mov edi, DWORD PTR [esp+12]
	mov ebx, ebp
	add ebx, 176
	mov edx, DWORD PTR [esp+8]
	mov ecx, DWORD PTR [edx]
	mov DWORD PTR [ebx+32], ecx
	mov ecx, DWORD PTR [edx+4]
	mov DWORD PTR [ebx+36], ecx
	mov ecx, DWORD PTR [edx+8]
	mov DWORD PTR [ebx+40], ecx
	mov ecx, DWORD PTR [edx+12]
	mov DWORD PTR [ebx+44], ecx
	mov ecx, DWORD PTR [edx+16]
	mov DWORD PTR [ebx+48], ecx
	mov ecx, DWORD PTR [edx+20]
	mov DWORD PTR [ebx+52], ecx
	mov ecx, DWORD PTR [edx+24]
	mov DWORD PTR [ebx+56], ecx
	mov ecx, DWORD PTR [edx+28]
	mov DWORD PTR [ebx+60], ecx
	mov ecx, 128
	mov DWORD PTR [ebx+64], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+68], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+72], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+76], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+80], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+84], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+88], ecx
	mov ecx, 196608
	mov DWORD PTR [ebx+92], ecx
	test edi, edi
	je 20f
22:
	mov ecx, DWORD PTR [esi]
	mov DWORD PTR [ebx], ecx
	mov ecx, DWORD PTR [esi+4]
	mov DWORD PTR [ebx+4], ecx
	mov ecx, DWORD PTR [esi+8]
	mov DWORD PTR [ebx+8], ecx
	mov ecx, DWORD PTR [esi+12]
	mov DWORD PTR [ebx+12], ecx
	mov ecx, DWORD PTR [esi+16]
	mov DWORD PTR [ebx+16], ecx
	mov ecx, DWORD PTR [esi+20]
	mov DWORD PTR [ebx+20], ecx
	mov ecx, DWORD PTR [esi+24]
	mov DWORD PTR [ebx+24], ecx
	mov ecx, DWORD PTR [esi+28]
	mov DWORD PTR [ebx+28], ecx
	mov eax, ebx
	add eax, 32
	mov ecx, 1
	push ebp
	push ecx
	push eax
	push ebx
	call {vg_sha256_compress_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, ebx
	add eax, 32
	mov ecx, DWORD PTR [ebx]
	bswap ecx
	mov DWORD PTR [eax], ecx
	mov ecx, DWORD PTR [ebx+4]
	bswap ecx
	mov DWORD PTR [eax+4], ecx
	mov ecx, DWORD PTR [ebx+8]
	bswap ecx
	mov DWORD PTR [eax+8], ecx
	mov ecx, DWORD PTR [ebx+12]
	bswap ecx
	mov DWORD PTR [eax+12], ecx
	mov ecx, DWORD PTR [ebx+16]
	bswap ecx
	mov DWORD PTR [eax+16], ecx
	mov ecx, DWORD PTR [ebx+20]
	bswap ecx
	mov DWORD PTR [eax+20], ecx
	mov ecx, DWORD PTR [ebx+24]
	bswap ecx
	mov DWORD PTR [eax+24], ecx
	mov ecx, DWORD PTR [ebx+28]
	bswap ecx
	mov DWORD PTR [eax+28], ecx
	mov ecx, DWORD PTR [esi+96]
	mov DWORD PTR [ebx], ecx
	mov ecx, DWORD PTR [esi+100]
	mov DWORD PTR [ebx+4], ecx
	mov ecx, DWORD PTR [esi+104]
	mov DWORD PTR [ebx+8], ecx
	mov ecx, DWORD PTR [esi+108]
	mov DWORD PTR [ebx+12], ecx
	mov ecx, DWORD PTR [esi+112]
	mov DWORD PTR [ebx+16], ecx
	mov ecx, DWORD PTR [esi+116]
	mov DWORD PTR [ebx+20], ecx
	mov ecx, DWORD PTR [esi+120]
	mov DWORD PTR [ebx+24], ecx
	mov ecx, DWORD PTR [esi+124]
	mov DWORD PTR [ebx+28], ecx
	mov eax, ebx
	add eax, 32
	mov ecx, 1
	push ebp
	push ecx
	push eax
	push ebx
	call {vg_sha256_compress_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, ebx
	add eax, 32
	mov ecx, DWORD PTR [ebx]
	bswap ecx
	mov DWORD PTR [eax], ecx
	mov ecx, DWORD PTR [ebx+4]
	bswap ecx
	mov DWORD PTR [eax+4], ecx
	mov ecx, DWORD PTR [ebx+8]
	bswap ecx
	mov DWORD PTR [eax+8], ecx
	mov ecx, DWORD PTR [ebx+12]
	bswap ecx
	mov DWORD PTR [eax+12], ecx
	mov ecx, DWORD PTR [ebx+16]
	bswap ecx
	mov DWORD PTR [eax+16], ecx
	mov ecx, DWORD PTR [ebx+20]
	bswap ecx
	mov DWORD PTR [eax+20], ecx
	mov ecx, DWORD PTR [ebx+24]
	bswap ecx
	mov DWORD PTR [eax+24], ecx
	mov ecx, DWORD PTR [ebx+28]
	bswap ecx
	mov DWORD PTR [eax+28], ecx
	mov edx, DWORD PTR [esp+16]
	mov ecx, DWORD PTR [ebx+32]
	xor ecx, DWORD PTR [edx]
	mov DWORD PTR [edx], ecx
	mov ecx, DWORD PTR [ebx+36]
	xor ecx, DWORD PTR [edx+4]
	mov DWORD PTR [edx+4], ecx
	mov ecx, DWORD PTR [ebx+40]
	xor ecx, DWORD PTR [edx+8]
	mov DWORD PTR [edx+8], ecx
	mov ecx, DWORD PTR [ebx+44]
	xor ecx, DWORD PTR [edx+12]
	mov DWORD PTR [edx+12], ecx
	mov ecx, DWORD PTR [ebx+48]
	xor ecx, DWORD PTR [edx+16]
	mov DWORD PTR [edx+16], ecx
	mov ecx, DWORD PTR [ebx+52]
	xor ecx, DWORD PTR [edx+20]
	mov DWORD PTR [edx+20], ecx
	mov ecx, DWORD PTR [ebx+56]
	xor ecx, DWORD PTR [edx+24]
	mov DWORD PTR [edx+24], ecx
	mov ecx, DWORD PTR [ebx+60]
	xor ecx, DWORD PTR [edx+28]
	mov DWORD PTR [edx+28], ecx
	sub edi, 1
	jne 22b
	jmp 21f
20:
21:
	mov eax, ebp
	mov ebx, DWORD PTR [eax+160]
	mov esi, DWORD PTR [eax+164]
	mov edi, DWORD PTR [eax+168]
	mov ebp, DWORD PTR [eax+172]
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

vg_pbkdf2_hmac_sha256_scratch_shani:
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
	ret
	.p2align 6
