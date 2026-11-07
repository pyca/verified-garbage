// The functions of `src/internal/vg_rsa_prime_search.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_prime_search:
	push ebx
	push ebp
	push esi
	push edi
	mov eax, DWORD PTR [esp+64]
	mov edi, DWORD PTR [eax]
	mov esi, 0
	mov ebp, 0
	mov ebx, 4
20:
	cmp edi, 0
	je 21f
	mov eax, DWORD PTR [esp+52]
	sub eax, esi
	cmp eax, DWORD PTR [esp+24]
	jb 23f
	lea esp, [esp-44]
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+92]
	add eax, esi
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+96]
	sub eax, esi
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+100]
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [esp+104]
	mov DWORD PTR [esp+40], eax
	call {vg_rsa_keygen_candidate}
	lea esp, [esp+44]
	mov edx, DWORD PTR [esp+28]
	mov ecx, DWORD PTR [edx]
	cmp eax, 1
	je 25f
	cmp eax, 0
	je 27f
	cmp ecx, 0
	je 29f
	add esi, ecx
	cmp eax, 3
	je 211f
	jmp 212f
211:
	sub edi, 1
212:
	jmp 210f
29:
	mov edi, 0
	mov ebp, 0
	mov ebx, 3
	mov edx, DWORD PTR [esp+20]
	mov ecx, DWORD PTR [esp+24]
	mov eax, 0
213:
	mov BYTE PTR [edx], al
	add edx, 1
	sub ecx, 1
	jne 213b
210:
	jmp 28f
27:
	mov ecx, DWORD PTR [esp+24]
	mov eax, 32769
	mul ecx
	mov ebp, eax
	mov eax, DWORD PTR [esp+52]
	sub eax, esi
	cmp eax, ebp
	je 214f
	mov ecx, DWORD PTR [esp+24]
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	cmp eax, ecx
	sbb edx, edx
	xor ecx, eax
	and ecx, edx
	xor eax, ecx
	add eax, eax
	cmp ebp, eax
	sbb edx, edx
	xor ebp, eax
	and ebp, edx
	xor eax, ebp
	mov ebp, eax
	mov ebx, 0
	jmp 215f
214:
	mov edi, 0
	mov ebp, 0
	mov ebx, 3
	mov edx, DWORD PTR [esp+20]
	mov ecx, DWORD PTR [esp+24]
	mov eax, 0
216:
	mov BYTE PTR [edx], al
	add edx, 1
	sub ecx, 1
	jne 216b
215:
28:
	jmp 26f
25:
	add esi, ecx
	mov edi, 0
	mov ebp, 0
	mov ebx, 1
26:
	jmp 24f
23:
	mov edx, DWORD PTR [esp+20]
	mov ecx, DWORD PTR [esp+24]
	mov eax, 0
217:
	mov BYTE PTR [edx], al
	add edx, 1
	sub ecx, 1
	jne 217b
	mov ecx, DWORD PTR [esp+24]
	mov eax, 32769
	mul ecx
	mov ebp, eax
	mov eax, DWORD PTR [esp+52]
	sub eax, esi
	cmp eax, ebp
	je 218f
	mov ecx, DWORD PTR [esp+24]
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	cmp eax, ecx
	sbb edx, edx
	xor ecx, eax
	and ecx, edx
	xor eax, ecx
	add eax, eax
	cmp ebp, eax
	sbb edx, edx
	xor ebp, eax
	and ebp, edx
	xor eax, ebp
	mov ebp, eax
	mov ebx, 0
	jmp 219f
218:
	mov edi, 0
	mov ebp, 0
	mov ebx, 3
	mov edx, DWORD PTR [esp+20]
	mov ecx, DWORD PTR [esp+24]
	mov eax, 0
220:
	mov BYTE PTR [edx], al
	add edx, 1
	sub ecx, 1
	jne 220b
219:
24:
	jmp 22f
21:
	mov edi, 0
	mov ebp, 0
	mov ebx, 3
	mov edx, DWORD PTR [esp+20]
	mov ecx, DWORD PTR [esp+24]
	mov eax, 0
221:
	mov BYTE PTR [edx], al
	add edx, 1
	sub ecx, 1
	jne 221b
22:
	cmp ebx, 4
	je 20b
	mov ecx, DWORD PTR [esp+24]
	mov eax, 32769
	mul ecx
	mov edx, DWORD PTR [esp+64]
	mov DWORD PTR [edx], edi
	mov DWORD PTR [edx+8], ecx
	mov DWORD PTR [edx+16], eax
	mov DWORD PTR [edx+24], ebp
	mov eax, 0
	mov DWORD PTR [edx+4], eax
	mov DWORD PTR [edx+12], eax
	mov DWORD PTR [edx+20], eax
	mov DWORD PTR [edx+28], eax
	mov edx, DWORD PTR [esp+28]
	mov DWORD PTR [edx], esi
	mov DWORD PTR [edx+4], eax
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
