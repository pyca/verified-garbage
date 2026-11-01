// The functions of `src/pbkdf2_sha1.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_pbkdf2_hmac_sha1:
	lea esp, [esp-1156]
	mov eax, DWORD PTR [esp+1160]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+1164]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+1168]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+1172]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+1176]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+1180]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+1184]
	mov DWORD PTR [esp+28], eax
	mov eax, esp
	add eax, 36
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [eax+448], ebx
	mov DWORD PTR [eax+452], esi
	mov DWORD PTR [eax+456], edi
	mov DWORD PTR [eax+460], ebp
	mov ebp, eax
	mov ecx, DWORD PTR [esp+8]
	cmp ecx, 65
	jae 20f
	mov edx, DWORD PTR [esp+4]
	jmp 21f
20:
	mov edi, ebp
	add edi, 716
	push edi
	call {vg_sha1_init}
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
	call {vg_sha1_update_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+8]
	mov ecx, 0
	mov edx, ebp
	add edx, 840
	push ebp
	push edx
	push ecx
	push eax
	push edi
	call {vg_sha1_finalize_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, ebp
	add edx, 840
	mov ecx, 20
21:
	mov edi, ebp
	add edi, 464
	mov esi, ebp
	add esi, 548
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call {vg_hmac_sha1_init_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ecx, 0
22:
	mov eax, ebp
	add eax, ecx
	movzx edx, BYTE PTR [eax+464]
	mov eax, ebp
	add eax, ecx
	mov BYTE PTR [eax+632], dl
	add ecx, 1
	cmp ecx, 84
	jne 22b
	mov edi, ebp
	add edi, 632
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
	call {vg_sha1_update_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1
	bswap eax
	mov DWORD PTR [ebp+860], eax
	mov ebx, 0
	mov ecx, DWORD PTR [esp+28]
	test ecx, ecx
	je 23f
25:
	mov ecx, 0
26:
	mov eax, ebp
	add eax, ecx
	movzx edx, BYTE PTR [eax+632]
	mov eax, ebp
	add eax, ecx
	mov BYTE PTR [eax+716], dl
	add ecx, 1
	cmp ecx, 84
	jne 26b
	mov edi, ebp
	add edi, 716
	mov esi, DWORD PTR [esp+16]
	add esi, 64
	mov eax, 0
	mov ecx, 4
	mov edx, ebp
	add edx, 860
	push ebp
	push ecx
	push edx
	push eax
	push esi
	push edi
	call {vg_sha1_update_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, ebp
	add edx, 716
	mov esi, ebp
	add esi, 548
	mov eax, DWORD PTR [esp+16]
	add eax, 68
	mov ecx, 0
	mov edi, ebp
	add edi, 800
	push ebp
	push edi
	push ecx
	push eax
	push esi
	push edx
	call {vg_hmac_sha1_finalize_scratch}
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
	movzx edx, BYTE PTR [eax+800]
	mov eax, ebp
	add eax, ecx
	mov BYTE PTR [eax+820], dl
	add ecx, 1
	cmp ecx, 20
	jne 27b
	mov esi, ebp
	add esi, 464
	mov eax, ebp
	add eax, 800
	mov ecx, DWORD PTR [esp+20]
	sub ecx, 1
	mov edx, ebp
	add edx, 820
	push ebp
	push edx
	push ecx
	push eax
	push esi
	call {vg_pbkdf2_hmac_sha1_iterate}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ecx, DWORD PTR [esp+28]
	sub ecx, ebx
	cmp ecx, 20
	jb 28f
	mov ecx, 20
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
	movzx edx, BYTE PTR [eax+820]
	mov eax, edi
	add eax, ecx
	mov BYTE PTR [eax], dl
	add ecx, 1
	cmp ecx, esi
	jne 210b
	add ebx, esi
	mov eax, DWORD PTR [ebp+860]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [ebp+860], eax
	mov eax, DWORD PTR [esp+28]
	cmp ebx, eax
	jne 25b
	jmp 24f
23:
24:
	mov eax, ebp
	mov ebx, DWORD PTR [eax+448]
	mov esi, DWORD PTR [eax+452]
	mov edi, DWORD PTR [eax+456]
	mov ebp, DWORD PTR [eax+460]
	lea esp, [esp+1156]
	ret
	.p2align 6

vg_pbkdf2_hmac_sha1_shani:
	lea esp, [esp-1156]
	mov eax, DWORD PTR [esp+1160]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+1164]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+1168]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+1172]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+1176]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+1180]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+1184]
	mov DWORD PTR [esp+28], eax
	mov eax, esp
	add eax, 36
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [eax+448], ebx
	mov DWORD PTR [eax+452], esi
	mov DWORD PTR [eax+456], edi
	mov DWORD PTR [eax+460], ebp
	mov ebp, eax
	mov ecx, DWORD PTR [esp+8]
	cmp ecx, 65
	jae 20f
	mov edx, DWORD PTR [esp+4]
	jmp 21f
20:
	mov edi, ebp
	add edi, 716
	push edi
	call {vg_sha1_init}
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
	call {vg_sha1_update_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+8]
	mov ecx, 0
	mov edx, ebp
	add edx, 840
	push ebp
	push edx
	push ecx
	push eax
	push edi
	call {vg_sha1_finalize_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, ebp
	add edx, 840
	mov ecx, 20
21:
	mov edi, ebp
	add edi, 464
	mov esi, ebp
	add esi, 548
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call {vg_hmac_sha1_init_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ecx, 0
22:
	mov eax, ebp
	add eax, ecx
	movzx edx, BYTE PTR [eax+464]
	mov eax, ebp
	add eax, ecx
	mov BYTE PTR [eax+632], dl
	add ecx, 1
	cmp ecx, 84
	jne 22b
	mov edi, ebp
	add edi, 632
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
	call {vg_sha1_update_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1
	bswap eax
	mov DWORD PTR [ebp+860], eax
	mov ebx, 0
	mov ecx, DWORD PTR [esp+28]
	test ecx, ecx
	je 23f
25:
	mov ecx, 0
26:
	mov eax, ebp
	add eax, ecx
	movzx edx, BYTE PTR [eax+632]
	mov eax, ebp
	add eax, ecx
	mov BYTE PTR [eax+716], dl
	add ecx, 1
	cmp ecx, 84
	jne 26b
	mov edi, ebp
	add edi, 716
	mov esi, DWORD PTR [esp+16]
	add esi, 64
	mov eax, 0
	mov ecx, 4
	mov edx, ebp
	add edx, 860
	push ebp
	push ecx
	push edx
	push eax
	push esi
	push edi
	call {vg_sha1_update_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, ebp
	add edx, 716
	mov esi, ebp
	add esi, 548
	mov eax, DWORD PTR [esp+16]
	add eax, 68
	mov ecx, 0
	mov edi, ebp
	add edi, 800
	push ebp
	push edi
	push ecx
	push eax
	push esi
	push edx
	call {vg_hmac_sha1_finalize_scratch_shani}
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
	movzx edx, BYTE PTR [eax+800]
	mov eax, ebp
	add eax, ecx
	mov BYTE PTR [eax+820], dl
	add ecx, 1
	cmp ecx, 20
	jne 27b
	mov esi, ebp
	add esi, 464
	mov eax, ebp
	add eax, 800
	mov ecx, DWORD PTR [esp+20]
	sub ecx, 1
	mov edx, ebp
	add edx, 820
	push ebp
	push edx
	push ecx
	push eax
	push esi
	call {vg_pbkdf2_hmac_sha1_iterate_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ecx, DWORD PTR [esp+28]
	sub ecx, ebx
	cmp ecx, 20
	jb 28f
	mov ecx, 20
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
	movzx edx, BYTE PTR [eax+820]
	mov eax, edi
	add eax, ecx
	mov BYTE PTR [eax], dl
	add ecx, 1
	cmp ecx, esi
	jne 210b
	add ebx, esi
	mov eax, DWORD PTR [ebp+860]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [ebp+860], eax
	mov eax, DWORD PTR [esp+28]
	cmp ebx, eax
	jne 25b
	jmp 24f
23:
24:
	mov eax, ebp
	mov ebx, DWORD PTR [eax+448]
	mov esi, DWORD PTR [eax+452]
	mov edi, DWORD PTR [eax+456]
	mov ebp, DWORD PTR [eax+460]
	lea esp, [esp+1156]
	ret
	.p2align 6
