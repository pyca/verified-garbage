// The functions of `src/internal/vg_scrypt_romix.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_scrypt_romix:
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+128], ebx
	mov DWORD PTR [eax+132], esi
	mov DWORD PTR [eax+136], edi
	mov DWORD PTR [eax+140], ebp
	mov eax, DWORD PTR [esp+8]
	mov ecx, 1
	mov edx, DWORD PTR [esp+16]
	add edx, edx
20:
	add eax, eax
	add ecx, ecx
	cmp eax, edx
	jne 20b
	shr ecx, 1
	mov ebp, ecx
	mov ebx, ecx
	mov esi, DWORD PTR [esp+12]
21:
	mov eax, DWORD PTR [esp+8]
	mov ecx, 8
	mul ecx
	mov edx, eax
	mov eax, DWORD PTR [esp+4]
	mov ecx, esi
22:
	movdqu xmm0, XMMWORD PTR [eax]
	movdqu XMMWORD PTR [ecx], xmm0
	add eax, 16
	add ecx, 16
	sub edx, 1
	jne 22b
	mov eax, DWORD PTR [esp+20]
	mov ecx, DWORD PTR [esp+8]
	mov edx, DWORD PTR [esp+4]
	push eax
	push ecx
	push edx
	push ecx
	push esi
	call {vg_scrypt_blockmix}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+8]
	mov ecx, 128
	mul ecx
	add esi, eax
	sub ebx, 1
	jne 21b
	mov ebx, ebp
23:
	mov eax, DWORD PTR [esp+8]
	mov ecx, 128
	mul ecx
	mov edi, eax
	mov ecx, DWORD PTR [esp+4]
	add eax, ecx
	sub eax, 64
	mov eax, DWORD PTR [eax]
	mov ecx, ebp
	sub ecx, 1
	and eax, ecx
	mul edi
	mov ecx, DWORD PTR [esp+12]
	add ecx, eax
	mov eax, DWORD PTR [esp+4]
	mov edx, DWORD PTR [esp+20]
	add edx, 192
	shr edi, 4
24:
	movdqu xmm0, XMMWORD PTR [eax]
	movdqu xmm1, XMMWORD PTR [ecx]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edx], xmm0
	add eax, 16
	add ecx, 16
	add edx, 16
	sub edi, 1
	jne 24b
	mov esi, DWORD PTR [esp+20]
	add esi, 192
	mov eax, DWORD PTR [esp+20]
	mov ecx, DWORD PTR [esp+8]
	mov edx, DWORD PTR [esp+4]
	push eax
	push ecx
	push edx
	push ecx
	push esi
	call {vg_scrypt_blockmix}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebx, 1
	jne 23b
	mov eax, DWORD PTR [esp+20]
	mov ebx, DWORD PTR [eax+128]
	mov esi, DWORD PTR [eax+132]
	mov edi, DWORD PTR [eax+136]
	mov ebp, DWORD PTR [eax+140]
	ret
	.p2align 6
