// The functions of `src/internal/vg_rsa_public_precompute_core.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_public_precompute_core:
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], ebp
	mov DWORD PTR [eax+8], esi
	mov DWORD PTR [eax+12], edi
	mov edi, eax
	mov esi, DWORD PTR [esp+12]
	mov ecx, DWORD PTR [esp+16]
	movzx eax, BYTE PTR [esi]
	mov ebx, esi
	add ebx, ecx
	sub ebx, 1
	movzx edx, BYTE PTR [ebx]
	mov ebx, eax
	sub ebx, 1
	shr ebx, 31
	mov ebp, ecx
	sub ebp, 64
	ror ebp, 24
	add ebp, eax
	sub ebp, 128
	shr ebp, 31
	and edx, 1
	xor edx, 1
	or ebx, edx
	or ebx, ebp
	cmp ebx, 0
	je 20f
	mov esi, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, 0
22:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 22b
	jmp 21f
20:
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [esp+8], eax
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov ebp, edi
	add ebp, 256
	mov eax, 0
23:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 23b
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov ebx, edi
	add ebx, 256
	mov esi, DWORD PTR [esp+12]
	mov ecx, DWORD PTR [esp+16]
	add esi, ecx
	sub esi, 1
24:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	sub esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 24b
	mov ebx, DWORD PTR [edi+256]
	mov ecx, ebx
	mov eax, ebx
	mul ecx
	mov ebp, 2
	sub ebp, eax
	mov eax, ecx
	mul ebp
	mov ecx, eax
	mov eax, ebx
	mul ecx
	mov ebp, 2
	sub ebp, eax
	mov eax, ecx
	mul ebp
	mov ecx, eax
	mov eax, ebx
	mul ecx
	mov ebp, 2
	sub ebp, eax
	mov eax, ecx
	mul ebp
	mov ecx, eax
	mov eax, ebx
	mul ecx
	mov ebp, 2
	sub ebp, eax
	mov eax, ecx
	mul ebp
	mov ecx, eax
	mov eax, 0
	sub eax, ecx
	mov DWORD PTR [edi+152], eax
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov ebx, edi
	add ebx, 256
	mov ecx, DWORD PTR [esp+8]
	add ecx, 3
	shr ecx, 2
	add ecx, ecx
	add ecx, ecx
	add ebx, ecx
	sub ebx, 12
	mov eax, DWORD PTR [ebx+8]
	mov esi, 1
	mov edx, 31
25:
	mov ecx, eax
	shr ecx, 31
	sub ecx, 1
	mov ebp, eax
	and ebp, ecx
	add eax, ebp
	mov ebp, esi
	and ebp, ecx
	add esi, ebp
	sub edx, 1
	jne 25b
	mov DWORD PTR [edi+160], esi
	mov ecx, eax
	mov eax, DWORD PTR [ebx+4]
	mul esi
	add ecx, edx
	mov DWORD PTR [edi+164], ecx
	mov ebp, eax
	mov eax, DWORD PTR [ebx]
	mul esi
	add ebp, edx
	mov DWORD PTR [edi+192], ebp
	mov esi, DWORD PTR [edi+164]
	mov edx, esi
	xor edx, -1
	mov ecx, 0
	mov edi, 32
26:
	add edx, edx
	sbb ebp, ebp
	add edx, 1
	mov eax, edx
	sub eax, esi
	sbb ebx, ebx
	xor ebx, -1
	or ebx, ebp
	mov eax, esi
	and eax, ebx
	sub edx, eax
	add ecx, ecx
	sub ecx, ebx
	sub edi, 1
	jne 26b
	mov edi, DWORD PTR [esp+20]
	mov DWORD PTR [edi+168], ecx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov ebp, edi
	add ebp, 256
	add ebp, ecx
	add ebp, ecx
	add ebp, ecx
	add ebp, ecx
	mov eax, 0
27:
	mov DWORD PTR [ebp], eax
	add ebp, 4
	sub ecx, 4
	jne 27b
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov eax, edi
	add eax, 256
	add eax, ecx
	add eax, ecx
	add eax, ecx
	add eax, ecx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 3
	shr ecx, 2
	add ecx, ecx
	add ecx, ecx
	add eax, ecx
	sub eax, 4
	mov edx, 1
	mov DWORD PTR [eax], edx
	mov eax, DWORD PTR [esp+8]
	add eax, 7
	shr eax, 3
	add eax, eax
	add eax, eax
	add eax, eax
	mov ecx, eax
	add eax, ecx
	add eax, eax
	add eax, ecx
	shr eax, 4
	add eax, 1
	mov edx, DWORD PTR [esp+8]
	add edx, 3
	shr edx, 2
	add edx, edx
	add edx, edx
	shr edx, 2
	sub eax, edx
	mov DWORD PTR [edi+176], eax
28:
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov ebx, edi
	add ebx, 256
	add ebx, ecx
	add ebx, ecx
	add ebx, ecx
	add ebx, ecx
	mov ecx, DWORD PTR [esp+8]
	add ecx, 3
	shr ecx, 2
	add ecx, ecx
	add ecx, ecx
	add ebx, ecx
	sub ebx, 16
	mov esi, DWORD PTR [edi+160]
	mov eax, DWORD PTR [ebx]
	mul esi
	mov ecx, edx
	mov eax, DWORD PTR [ebx+4]
	mul esi
	add eax, ecx
	mov ebp, eax
	mov ecx, edx
	mov eax, DWORD PTR [ebx+8]
	mul esi
	add eax, ecx
	mov ecx, edx
	mov ebx, DWORD PTR [ebx+12]
	mov DWORD PTR [edi+184], ebp
	mov ebp, eax
	mov eax, ebx
	mul esi
	add eax, ecx
	mov DWORD PTR [edi+188], eax
	mov ecx, DWORD PTR [edi+164]
	sub ecx, eax
	cmp ecx, 1
	sbb ecx, ecx
	mov DWORD PTR [edi+172], ecx
	xor ecx, -1
	and eax, ecx
	mov ecx, eax
	mov eax, DWORD PTR [edi+168]
	mul ecx
	add eax, ebp
	adc edx, ecx
	mov ebx, edx
	add ebx, 1
	mov ecx, eax
	mov eax, ebx
	mov esi, DWORD PTR [edi+164]
	mul esi
	mov edx, ebp
	sub edx, eax
	cmp ecx, edx
	sbb eax, eax
	add ebx, eax
	and eax, esi
	add edx, eax
	mov eax, esi
	sub eax, 1
	cmp eax, edx
	adc ebx, 0
	or ebx, DWORD PTR [edi+172]
	mov DWORD PTR [edi+180], ebx
	mov ecx, DWORD PTR [edi+180]
	mov eax, DWORD PTR [edi+192]
	mul ecx
	mov ebx, eax
	mov esi, edx
	mov eax, DWORD PTR [edi+164]
	mul ecx
	add eax, esi
	adc edx, 0
	mov esi, DWORD PTR [edi+184]
	sub esi, ebx
	sbb ebp, eax
	mov eax, DWORD PTR [edi+188]
	sbb eax, edx
	mov edx, eax
	add edx, edx
	sbb edx, edx
	add ecx, edx
	mov ebx, edx
	and ebx, DWORD PTR [edi+192]
	and edx, DWORD PTR [edi+164]
	add esi, ebx
	adc ebp, edx
	adc eax, 0
	mov edx, eax
	add edx, edx
	sbb edx, edx
	add ecx, edx
	mov ebx, edx
	and ebx, DWORD PTR [edi+192]
	and edx, DWORD PTR [edi+164]
	add esi, ebx
	adc ebp, edx
	adc eax, 0
	mov DWORD PTR [edi+180], ecx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ebx, edi
	add ebx, 256
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov esi, edi
	add esi, 256
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ebp, edi
	add ebp, 256
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov ecx, DWORD PTR [edi+180]
	mov eax, DWORD PTR [ebx]
	mul ecx
	mov DWORD PTR [ebp+4], edx
	mov edx, 0
	sub edx, eax
	mov DWORD PTR [ebp], edx
	sbb eax, eax
	mov edx, DWORD PTR [ebp+4]
	sub edx, eax
	mov DWORD PTR [ebp+4], edx
	mov edi, DWORD PTR [esp+8]
	add edi, 3
	shr edi, 2
	add edi, edi
	add edi, edi
	sub edi, 4
	add ebx, 4
	add ebp, 4
29:
	mov eax, DWORD PTR [ebx]
	mul ecx
	add eax, DWORD PTR [ebp]
	adc edx, 0
	mov DWORD PTR [ebp+4], edx
	mov edx, DWORD PTR [esi]
	sub edx, eax
	mov DWORD PTR [ebp], edx
	sbb eax, eax
	mov edx, DWORD PTR [ebp+4]
	sub edx, eax
	mov DWORD PTR [ebp+4], edx
	add ebx, 4
	add esi, 4
	add ebp, 4
	sub edi, 4
	jne 29b
	mov edx, DWORD PTR [esi]
	sub edx, DWORD PTR [ebp]
	mov DWORD PTR [ebp], edx
	mov edi, DWORD PTR [esp+20]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ebx, edi
	add ebx, 256
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ebp, edi
	add ebp, 256
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 3
	shr edi, 2
	add edi, edi
	add edi, edi
	mov eax, ebp
	add eax, edi
	mov eax, DWORD PTR [eax]
	add eax, eax
	sbb ecx, ecx
	mov esi, 0
210:
	mov eax, DWORD PTR [ebx]
	and eax, ecx
	add esi, esi
	adc eax, DWORD PTR [ebp]
	mov DWORD PTR [ebp], eax
	sbb esi, esi
	add ebx, 4
	add ebp, 4
	sub edi, 4
	jne 210b
	mov eax, DWORD PTR [ebp]
	sub eax, esi
	mov DWORD PTR [ebp], eax
	mov edi, DWORD PTR [esp+20]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov esi, edi
	add esi, 256
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	add esi, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ebp, edi
	add ebp, 256
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edi, DWORD PTR [esp+8]
	add edi, 3
	shr edi, 2
	add edi, edi
	add edi, edi
211:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp], eax
	add esi, 4
	add ebp, 4
	sub edi, 4
	jne 211b
	mov edi, DWORD PTR [esp+20]
	mov eax, DWORD PTR [edi+176]
	sub eax, 1
	mov DWORD PTR [edi+176], eax
	jne 28b
	mov esi, DWORD PTR [esp+8]
	add esi, 7
	shr esi, 3
	add esi, esi
	add esi, esi
	add esi, esi
	shr esi, 3
	and esi, 1
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	je 212f
214:
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ebp, edi
	add ebp, 256
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ebx, edi
	add ebx, 256
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov ecx, 0
215:
	mov eax, DWORD PTR [ebx]
	add ecx, ecx
	adc eax, eax
	mov DWORD PTR [ebp], eax
	sbb ecx, ecx
	add ebx, 4
	add ebp, 4
	sub edx, 4
	jne 215b
	mov eax, 0
	sub eax, ecx
	mov DWORD PTR [ebp], eax
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, edi
	add eax, 256
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ebp, edi
	add ebp, 256
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ebx, edi
	add ebx, 256
	mov edi, eax
	mov ecx, 0
216:
	mov eax, DWORD PTR [ebp]
	add ecx, ecx
	sbb eax, DWORD PTR [ebx]
	mov DWORD PTR [edi], eax
	sbb ecx, ecx
	add ebp, 4
	add ebx, 4
	add edi, 4
	sub edx, 4
	jne 216b
	mov eax, DWORD PTR [ebp]
	add ecx, ecx
	sbb eax, 0
	sbb eax, eax
	mov ecx, eax
	mov edi, DWORD PTR [esp+20]
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ebp, edi
	add ebp, 256
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	add ebp, edx
	mov edx, DWORD PTR [esp+8]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov ebx, edi
	add ebx, 256
	add ebx, edx
	add ebx, edx
	add ebx, edx
	add ebx, edx
	mov edi, edx
217:
	mov eax, DWORD PTR [ebx]
	mov edx, DWORD PTR [ebp]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [ebx], eax
	add ebp, 4
	add ebx, 4
	sub edi, 4
	jne 217b
	mov edi, DWORD PTR [esp+20]
	sub esi, 1
	jne 214b
	jmp 213f
212:
213:
	mov esi, 2
218:
	lea esp, [esp-36]
	mov edx, DWORD PTR [esp+44]
	add edx, 7
	shr edx, 3
	add edx, edx
	add edx, edx
	add edx, edx
	mov eax, DWORD PTR [esp+60]
	mov DWORD PTR [esp+4], eax
	mov DWORD PTR [esp], edi
	mov eax, edx
	shr eax, 3
	mov DWORD PTR [esp+8], eax
	mov eax, 256
	mov DWORD PTR [esp+12], eax
	mov eax, 152
	mov DWORD PTR [esp+16], eax
	mov eax, 256
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+20], eax
	mov eax, 256
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+24], eax
	mov eax, 256
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+28], eax
	mov eax, 256
	add eax, edx
	add eax, edx
	add eax, edx
	add eax, edx
	mov DWORD PTR [esp+32], eax
	call {vg_rsa_mont_mul_at}
	lea esp, [esp+36]
	sub esi, 1
	jne 218b
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov esi, edi
	add esi, 256
	mov ebp, DWORD PTR [esp+4]
219:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp], eax
	add esi, 4
	add ebp, 4
	sub ecx, 4
	jne 219b
	mov ecx, DWORD PTR [esp+8]
	add ecx, 7
	shr ecx, 3
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov esi, edi
	add esi, 256
	add esi, ecx
	add esi, ecx
	add esi, ecx
	add esi, ecx
	mov ebp, DWORD PTR [esp+4]
	add ebp, ecx
220:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp], eax
	add esi, 4
	add ebp, 4
	sub ecx, 4
	jne 220b
	mov eax, 1
21:
	mov ebx, DWORD PTR [edi]
	mov ebp, DWORD PTR [edi+4]
	mov esi, DWORD PTR [edi+8]
	mov edi, DWORD PTR [edi+12]
	ret
	.p2align 6
