// The functions of `src/internal/vg_argon2_hprime.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_argon2_hprime:
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+840], ebx
	mov DWORD PTR [eax+844], esi
	mov DWORD PTR [eax+848], edi
	mov ebx, eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [ebx+856], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [ebx+860], eax
	mov DWORD PTR [ebx+832], eax
	mov edx, DWORD PTR [ebx+860]
	cmp edx, 65
	jb 20f
	mov edx, 64
	jmp 21f
20:
21:
	mov eax, 0
	mov ecx, ebx
	push eax
	push ecx
	push edx
	push ebx
	call {vg_blake2b_init}
	pop eax
	pop eax
	pop eax
	pop eax
	mov ecx, 0
	mov edx, 0
	mov esi, ebx
	add esi, 832
	mov edi, 4
	mov eax, ebx
	add eax, 192
	push eax
	push edi
	push esi
	push edx
	push ecx
	push ebx
	call {vg_blake2b_update_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ecx, 4
	mov edx, 0
	mov esi, DWORD PTR [esp+4]
	mov edi, DWORD PTR [esp+8]
	mov eax, ebx
	add eax, 192
	push eax
	push edi
	push esi
	push edx
	push ecx
	push ebx
	call {vg_blake2b_update_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ecx, DWORD PTR [esp+8]
	mov edx, 0
	add ecx, 4
	adc edx, 0
	mov eax, ebx
	add eax, 192
	mov esi, ebx
	add esi, 768
	push eax
	push esi
	push edx
	push ecx
	push ebx
	call {vg_blake2b_finalize_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [ebx+860]
	cmp eax, 65
	jb 22f
	mov esi, 32
	mov edx, ebx
	add edx, 768
	mov edi, DWORD PTR [ebx+856]
24:
	movzx eax, BYTE PTR [edx]
	mov BYTE PTR [edi], al
	add edx, 1
	add edi, 1
	sub esi, 1
	jne 24b
	mov DWORD PTR [ebx+856], edi
	mov eax, DWORD PTR [ebx+860]
	sub eax, 32
	mov DWORD PTR [ebx+860], eax
	mov eax, DWORD PTR [ebx+860]
	cmp eax, 65
	jb 25f
27:
	mov edx, 64
	mov eax, 0
	mov ecx, ebx
	push eax
	push ecx
	push edx
	push ebx
	call {vg_blake2b_init}
	pop eax
	pop eax
	pop eax
	pop eax
	mov ecx, 0
	mov edx, 0
	mov esi, ebx
	add esi, 768
	mov edi, 64
	mov eax, ebx
	add eax, 192
	push eax
	push edi
	push esi
	push edx
	push ecx
	push ebx
	call {vg_blake2b_update_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ecx, 64
	mov edx, 0
	mov eax, ebx
	add eax, 192
	mov esi, ebx
	add esi, 768
	push eax
	push esi
	push edx
	push ecx
	push ebx
	call {vg_blake2b_finalize_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, 32
	mov edx, ebx
	add edx, 768
	mov edi, DWORD PTR [ebx+856]
28:
	movzx eax, BYTE PTR [edx]
	mov BYTE PTR [edi], al
	add edx, 1
	add edi, 1
	sub esi, 1
	jne 28b
	mov DWORD PTR [ebx+856], edi
	mov eax, DWORD PTR [ebx+860]
	sub eax, 32
	mov DWORD PTR [ebx+860], eax
	mov eax, DWORD PTR [ebx+860]
	cmp eax, 65
	jae 27b
	jmp 26f
25:
26:
	mov edx, DWORD PTR [ebx+860]
	mov eax, 0
	mov ecx, ebx
	push eax
	push ecx
	push edx
	push ebx
	call {vg_blake2b_init}
	pop eax
	pop eax
	pop eax
	pop eax
	mov ecx, 0
	mov edx, 0
	mov esi, ebx
	add esi, 768
	mov edi, 64
	mov eax, ebx
	add eax, 192
	push eax
	push edi
	push esi
	push edx
	push ecx
	push ebx
	call {vg_blake2b_update_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ecx, 64
	mov edx, 0
	mov eax, ebx
	add eax, 192
	mov esi, ebx
	add esi, 768
	push eax
	push esi
	push edx
	push ecx
	push ebx
	call {vg_blake2b_finalize_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	jmp 23f
22:
23:
	mov esi, DWORD PTR [ebx+860]
	mov edx, ebx
	add edx, 768
	mov edi, DWORD PTR [ebx+856]
29:
	movzx eax, BYTE PTR [edx]
	mov BYTE PTR [edi], al
	add edx, 1
	add edi, 1
	sub esi, 1
	jne 29b
	mov DWORD PTR [ebx+856], edi
	mov edi, DWORD PTR [ebx+848]
	mov esi, DWORD PTR [ebx+844]
	mov ebx, DWORD PTR [ebx+840]
	ret
	.p2align 6
