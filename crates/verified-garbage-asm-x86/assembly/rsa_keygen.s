// The functions of `src/rsa_keygen.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_generate_init:
	mov edx, DWORD PTR [esp+4]
	mov DWORD PTR [edx], ebx
	mov ebx, edx
	mov eax, 0
	mov DWORD PTR [ebx+32], eax
	mov DWORD PTR [ebx+36], eax
	mov ecx, DWORD PTR [esp+12]
	mov edx, DWORD PTR [esp+16]
	cmp edx, 0
	je 20f
22:
	movzx eax, BYTE PTR [ecx]
	mov DWORD PTR [ebx+44], eax
	mov eax, DWORD PTR [ebx+32]
	shr eax, 24
	or eax, DWORD PTR [ebx+36]
	mov DWORD PTR [ebx+36], eax
	mov eax, DWORD PTR [ebx+32]
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, DWORD PTR [ebx+44]
	mov DWORD PTR [ebx+32], eax
	add ecx, 1
	sub edx, 1
	jne 22b
	jmp 21f
20:
21:
	mov eax, DWORD PTR [ebx+36]
	cmp eax, 1
	sbb ecx, ecx
	xor ecx, -1
	mov edx, DWORD PTR [ebx+32]
	mov eax, edx
	and eax, 1
	cmp eax, 1
	sbb eax, eax
	or ecx, eax
	cmp edx, 3
	sbb eax, eax
	or ecx, eax
	mov DWORD PTR [ebx+40], ecx
	mov eax, edx
	xor eax, 3
	cmp eax, 1
	sbb eax, eax
	mov DWORD PTR [ebx+36], eax
	mov eax, DWORD PTR [esp+8]
	cmp eax, 512
	sbb ecx, ecx
	cmp eax, 8193
	sbb edx, edx
	xor edx, -1
	or ecx, edx
	mov eax, ecx
	and eax, 1
	add eax, 1
	mov edx, DWORD PTR [ebx+40]
	xor edx, -1
	and eax, edx
	mov DWORD PTR [ebx+44], eax
	or ecx, DWORD PTR [ebx+40]
	xor ecx, -1
	mov DWORD PTR [ebx+40], ecx
	mov ecx, DWORD PTR [esp+8]
	shr ecx, 7
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	and ecx, DWORD PTR [ebx+40]
	mov DWORD PTR [ebx+8], ecx
	mov eax, 0
	mov DWORD PTR [ebx+4], eax
	mov DWORD PTR [ebx+12], eax
	mov DWORD PTR [ebx+20], eax
	mov DWORD PTR [ebx+28], eax
	mov DWORD PTR [ebx+48], eax
	mov eax, 32769
	mul ecx
	mov DWORD PTR [ebx+16], eax
	mov eax, ecx
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	mov DWORD PTR [ebx+24], eax
	mov eax, ecx
	add eax, eax
	add eax, eax
	add eax, eax
	mov edx, eax
	add eax, eax
	add eax, edx
	and eax, DWORD PTR [ebx+36]
	mov DWORD PTR [ebx+36], eax
	mov eax, 40
	mul ecx
	add eax, DWORD PTR [ebx+36]
	mov ecx, eax
	mov eax, DWORD PTR [ebx+32]
	and eax, DWORD PTR [ebx+40]
	bswap eax
	mov DWORD PTR [ebx+52], eax
	mov eax, 4
	and eax, DWORD PTR [ebx+40]
	mov DWORD PTR [ebx+40], eax
	mov eax, 0
	mov DWORD PTR [ebx+32], eax
	mov DWORD PTR [ebx+36], eax
	mov eax, DWORD PTR [ebx+44]
	mov edx, 0
	mov DWORD PTR [ebx+44], edx
	mov edx, DWORD PTR [esp+4]
	mov ebx, DWORD PTR [edx]
	mov DWORD PTR [edx], ecx
	ret
	.p2align 6

vg_rsa_generate:
	push ebx
	push ebp
	push esi
	push edi
	mov eax, DWORD PTR [esp+48]
	mov ebp, DWORD PTR [eax+8]
	mov esi, 0
	mov ebx, 4
	mov ecx, DWORD PTR [eax+52]
	xor ecx, 50331648
	or ecx, DWORD PTR [eax+48]
	cmp ecx, 1
	sbb ecx, ecx
	mov edx, ebp
	add edx, edx
	add edx, edx
	add edx, edx
	mov edi, edx
	add edi, edi
	add edi, edx
	and edi, ecx
	mov eax, 40
	mul ebp
	add edi, eax
	mov edx, DWORD PTR [esp+20]
	mov ecx, ebp
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
20:
	mov BYTE PTR [edx], al
	add edx, 1
	sub ecx, 1
	jne 20b
	mov edx, DWORD PTR [esp+20]
	mov ecx, ebp
	add ecx, ecx
	add ecx, ecx
	add edx, ecx
	add edx, ebp
	mov eax, 0
21:
	mov BYTE PTR [edx], al
	add edx, 1
	sub ecx, 1
	jne 21b
22:
	lea esp, [esp-48]
	mov eax, DWORD PTR [esp+96]
	mov ecx, DWORD PTR [eax+32]
	mov edx, 0
	sub edx, ecx
	and edx, ebp
	mov DWORD PTR [esp+24], edx
	mov ecx, ebp
	add ecx, ecx
	add ecx, ecx
	add ecx, DWORD PTR [esp+68]
	mov DWORD PTR [esp+20], ecx
	add ecx, edx
	mov DWORD PTR [esp], ecx
	mov DWORD PTR [esp+4], ebp
	mov ecx, DWORD PTR [esp+76]
	mov DWORD PTR [esp+8], ecx
	mov ecx, eax
	add ecx, 48
	mov DWORD PTR [esp+12], ecx
	mov ecx, 8
	mov DWORD PTR [esp+16], ecx
	mov ecx, DWORD PTR [esp+84]
	sub ecx, esi
	mov DWORD PTR [esp+32], ecx
	cmp ecx, 1
	sbb edx, edx
	and edx, esi
	mov ecx, DWORD PTR [esp+80]
	add ecx, esi
	sub ecx, edx
	mov DWORD PTR [esp+28], ecx
	mov ecx, DWORD PTR [esp+88]
	mov DWORD PTR [esp+36], ecx
	mov ecx, DWORD PTR [esp+92]
	mov DWORD PTR [esp+40], ecx
	mov DWORD PTR [esp+44], eax
	call {vg_rsa_prime_search}
	lea esp, [esp+48]
	mov edx, DWORD PTR [esp+28]
	mov ecx, DWORD PTR [edx]
	add esi, ecx
	cmp eax, 0
	je 23f
	cmp eax, 3
	je 25f
	cmp ecx, 0
	je 27f
	mov eax, DWORD PTR [esp+48]
	mov ecx, DWORD PTR [eax+32]
	cmp ecx, 0
	je 29f
	lea esp, [esp-72]
	mov ecx, DWORD PTR [esp+92]
	mov edx, ebp
	add edx, edx
	mov DWORD PTR [esp], ecx
	mov DWORD PTR [esp+4], edx
	add ecx, edx
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+12], edx
	add ecx, edx
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ebp
	add ecx, ebp
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+28], ebp
	add ecx, ebp
	mov DWORD PTR [esp+32], ecx
	mov DWORD PTR [esp+36], ebp
	add ecx, ebp
	mov DWORD PTR [esp+40], ecx
	mov DWORD PTR [esp+44], ebp
	add ecx, ebp
	mov DWORD PTR [esp+48], ecx
	mov DWORD PTR [esp+52], ebp
	mov ecx, DWORD PTR [esp+120]
	add ecx, 48
	mov DWORD PTR [esp+56], ecx
	mov ecx, 8
	mov DWORD PTR [esp+60], ecx
	mov ecx, DWORD PTR [esp+112]
	mov DWORD PTR [esp+64], ecx
	mov ecx, DWORD PTR [esp+116]
	mov DWORD PTR [esp+68], ecx
	call {vg_rsa_keygen_key}
	lea esp, [esp+72]
	cmp eax, 1
	je 211f
	cmp eax, 2
	je 213f
	mov edx, DWORD PTR [esp+20]
	mov ecx, ebp
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ebp
	mov eax, 0
215:
	mov BYTE PTR [edx], al
	add edx, 1
	sub ecx, 1
	jne 215b
	mov eax, DWORD PTR [esp+48]
	mov ecx, 0
	mov DWORD PTR [eax+32], ecx
	mov DWORD PTR [eax+36], ecx
	mov DWORD PTR [eax+40], ecx
	mov DWORD PTR [eax+44], ecx
	mov ebx, 2
	jmp 214f
213:
	mov eax, DWORD PTR [esp+48]
	mov DWORD PTR [eax], edi
	mov ecx, 0
	mov DWORD PTR [eax+4], ecx
	mov ecx, 0
	mov DWORD PTR [eax+32], ecx
	mov ebx, 4
214:
	jmp 212f
211:
	mov eax, DWORD PTR [esp+48]
	mov ecx, 0
	mov DWORD PTR [eax+32], ecx
	mov DWORD PTR [eax+36], ecx
	mov DWORD PTR [eax+40], ecx
	mov DWORD PTR [eax+44], ecx
	mov ebx, 1
212:
	jmp 210f
29:
	mov eax, DWORD PTR [esp+48]
	mov DWORD PTR [eax], edi
	mov ecx, 0
	mov DWORD PTR [eax+4], ecx
	mov ecx, 1
	mov DWORD PTR [eax+32], ecx
	mov ebx, 4
210:
	jmp 28f
27:
	mov edx, DWORD PTR [esp+20]
	mov ecx, ebp
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ebp
	mov eax, 0
216:
	mov BYTE PTR [edx], al
	add edx, 1
	sub ecx, 1
	jne 216b
	mov eax, DWORD PTR [esp+48]
	mov ecx, 0
	mov DWORD PTR [eax+32], ecx
	mov DWORD PTR [eax+36], ecx
	mov DWORD PTR [eax+40], ecx
	mov DWORD PTR [eax+44], ecx
	mov ebx, 3
28:
	jmp 26f
25:
	mov eax, DWORD PTR [esp+48]
	mov ecx, DWORD PTR [eax+44]
	cmp ecx, 1
	sbb ecx, ecx
	mov edx, DWORD PTR [eax+40]
	cmp edx, 2
	sbb edx, edx
	and ecx, edx
	test ecx, ecx
	jne 217f
	mov ecx, DWORD PTR [eax+40]
	sub ecx, 1
	mov DWORD PTR [eax+40], ecx
	mov ecx, DWORD PTR [eax+44]
	sbb ecx, 0
	mov DWORD PTR [eax+44], ecx
	mov eax, DWORD PTR [esp+48]
	mov DWORD PTR [eax], edi
	mov ecx, 0
	mov DWORD PTR [eax+4], ecx
	mov ecx, 0
	mov DWORD PTR [eax+32], ecx
	mov ebx, 4
	jmp 218f
217:
	mov edx, DWORD PTR [esp+20]
	mov ecx, ebp
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ebp
	mov eax, 0
219:
	mov BYTE PTR [edx], al
	add edx, 1
	sub ecx, 1
	jne 219b
	mov eax, DWORD PTR [esp+48]
	mov ecx, 0
	mov DWORD PTR [eax+32], ecx
	mov DWORD PTR [eax+36], ecx
	mov DWORD PTR [eax+40], ecx
	mov DWORD PTR [eax+44], ecx
	mov ebx, 3
218:
26:
	jmp 24f
23:
	mov ebx, 0
24:
	cmp ebx, 4
	je 22b
	mov edx, DWORD PTR [esp+28]
	mov DWORD PTR [edx], esi
	mov ecx, 0
	mov DWORD PTR [edx+4], ecx
	mov eax, ebx
	mov edi, DWORD PTR [esp]
	mov esi, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp+8]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	ret
	.p2align 6
